use reqwest::Response;
use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored, DoesNotDivide, OtherError};
use crate::algebraic::Factor::Numeric;
use crate::algebraic::NumberStatus::{
    FullyFactored, PartlyFactoredComposite, Prime, UnfactoredComposite, Unknown,
};
use crate::algebraic::{FactorFinder, NumberStatusExt, ProcessedStatusApiResponse};
use crate::monitor::Monitor;
use crate::{
    EXIT_TIME, FAILED_U_SUBMISSIONS_OUT, FactorSubmission, MAX_CPU_BUDGET_TENTHS,
    MAX_ID_EQUAL_TO_VALUE, ReportFactorResult, SUBMIT_FACTOR_MAX_ATTEMPTS,
};
use crate::{Factor, NumberSpecifier, NumberStatusApiResponse, RETRY_DELAY};
use hipstr::HipStr;
use async_backtrace::framed;
use atomic_time::AtomicInstant;
use core::cell::RefCell;
use curl::easy::{Easy2, Handler, WriteError};
use governor::middleware::StateInformationMiddleware;
use governor::{DefaultDirectRateLimiter, Quota, RateLimiter};
use itertools::Itertools;
use log::{debug, error, info, warn};
use quick_cache::unsync::Cache;
use quick_cache::unsync::DefaultLifecycle;
use quick_cache::{DefaultHashBuilder, UnitWeighter};
use regex::{Regex, RegexBuilder};
use reqwest::{Client};
use serde_json::from_str;
use std::io::Write;
use std::mem::swap;
use std::num::NonZeroU32;
use std::os::unix::prelude::CommandExt;
use std::process::{Command, exit};
use std::sync::Arc;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::time::Duration;
use futures_util::TryFutureExt;
use tokio::sync::Semaphore;
use tokio::task::block_in_place;
use tokio::time::{Instant, sleep, sleep_until};
use urlencoding::encode;

pub const MAX_RETRIES: usize = 40;
const MAX_RETRIES_WITH_FALLBACK: usize = 10;

const CONNECT_TIMEOUT: Duration = Duration::from_mins(1);
const E2E_TIMEOUT: Duration = Duration::from_mins(2);

const REQWEST_MAX_URL_LEN: usize = (u16::MAX - 1) as usize;

thread_local! {
    static CURL_CLIENT: RefCell<Easy2<Collector>> = RefCell::new(Easy2::new(Collector(Vec::new())));
}

struct Collector(Vec<u8>);

impl Handler for Collector {
    fn write(&mut self, data: &[u8]) -> Result<usize, WriteError> {
        self.0.extend_from_slice(data);
        Ok(data.len())
    }
}

impl Collector {
    fn take_all(&mut self) -> Vec<u8> {
        let mut out = Vec::new();
        swap(&mut self.0, &mut out);
        out
    }
}

type BasicCache<K, V> = Cache<K, V, UnitWeighter, DefaultHashBuilder, DefaultLifecycle<K, V>>;

pub trait FactorDbClient {
    async fn parse_resource_limits(
        &self,
        bases_before_next_cpu_check: &mut usize,
        resources_text: &str,
    ) -> Option<ResourceLimits>;
    /// Executes a GET request with a large reasonable default number of retries, or else
    /// restarts the process if that request consistently fails.
    async fn retrying_get_and_decode(&self, url: HipStr<'_>, retry_delay: Duration) -> HipStr<'static>;
    async fn try_get_and_decode(&self, url: HipStr<'_>) -> Option<HipStr<'static>>;
    async fn try_get_resource_limits(
        &self,
        bases_before_next_cpu_check: &mut usize,
    ) -> Option<ResourceLimits>;
    fn read_ids_and_exprs<'a>(&self, haystack: &'a str) -> impl Iterator<Item = (u128, &'a str)>;
    async fn try_get_expression_form(&mut self, entry_id: u128) -> Option<HipStr<'static>>;
    async fn known_factors_as_digits(
        &mut self,
        id: NumberSpecifier<&str, &str>,
        include_ff: bool,
        get_digits_as_fallback: bool,
    ) -> ProcessedStatusApiResponse;
    fn cached_factors(&self, id: NumberSpecifier<&str, &str>)
    -> Option<ProcessedStatusApiResponse>;
    async fn try_report_factor(
        &self,
        u_id: NumberSpecifier<&str, &str>,
        factor: Factor<&str, &str>,
    ) -> ReportFactorResult;
    async fn report_numeric_factor(&self, u_id: u128, factor: u128) -> ReportFactorResult;
}

#[derive(Clone)]
pub struct RealFactorDbClient {
    resources_regex: Arc<Regex>,
    http: Client,
    rate_limiter: Arc<DefaultDirectRateLimiter<StateInformationMiddleware>>,
    requests_left_last_check: Arc<AtomicU32>,
    requests_per_hour: u32,
    request_semaphore: Arc<Semaphore>,
    all_threads_blocked_until: Arc<AtomicInstant>,
    shutdown_receiver: Monitor,
    id_and_expr_regex: Arc<Regex>,
    digits_fallback_regex: Arc<Regex>,
    expression_form_regex: Arc<Regex>,
    by_id_cache: BasicCache<u128, ProcessedStatusApiResponse>,
    by_expr_cache: BasicCache<HipStr<'static>, ProcessedStatusApiResponse>,
    expression_form_cache: BasicCache<u128, HipStr<'static>>,
}

pub struct ResourceLimits {
    pub cpu_tenths_spent: usize,
    pub resets_at: Instant,
}

impl RealFactorDbClient {
    pub fn new(
        requests_per_hour: NonZeroU32,
        max_concurrent_requests: usize,
        shutdown_receiver: Monitor,
    ) -> Self {
        let rate_limiter =
            RateLimiter::direct(Quota::per_hour(requests_per_hour)).with_middleware();
        let resources_regex =
            RegexBuilder::new("Page requests(?:[^0-9])+([0-9,]+).*CPU.*>([0-9]+)\\.([0-9]) seconds.*600\\.0 seconds.*([0-6][0-9]):([0-6][0-9])")
                .multi_line(true)
                .dot_matches_new_line(true)
                .build()
                .unwrap();
        let id_and_expr_regex =
            Regex::new("index\\.php\\?id=([0-9]+)\"><font[^>]*>([^<]+)</font>").unwrap();
        let http = Client::builder()
            .pool_max_idle_per_host(max_concurrent_requests)
            .timeout(E2E_TIMEOUT)
            .connect_timeout(CONNECT_TIMEOUT)
            .build()
            .unwrap();
        let digits_fallback_regex =
            RegexBuilder::new("<tr><td>Number</td>[^<]*<td[^>]*>([0-9br<>\\pZ]+)")
                .multi_line(true)
                .dot_matches_new_line(true)
                .build()
                .unwrap();
        let expression_form_regex = Regex::new("name=\"query\" value=\"([^\"]+)\"").unwrap();
        // Governor rate-limiters start out with their full burst capacity and recharge starting
        // immediately, but this would lead to twice the allowed number of requests in our first hour,
        // so we make it start nearly empty instead.
        rate_limiter
            .check_n(6050u32.try_into().unwrap())
            .unwrap()
            .unwrap();
        let requests_left_last_check = AtomicU32::new(requests_per_hour.get());
        Self {
            resources_regex: resources_regex.into(),
            http,
            rate_limiter: rate_limiter.into(),
            requests_per_hour: requests_per_hour.get(),
            requests_left_last_check: requests_left_last_check.into(),
            request_semaphore: Semaphore::const_new(max_concurrent_requests).into(),
            all_threads_blocked_until: AtomicInstant::now().into(),
            shutdown_receiver,
            id_and_expr_regex: id_and_expr_regex.into(),
            digits_fallback_regex: digits_fallback_regex.into(),
            expression_form_regex: expression_form_regex.into(),
            by_id_cache: Cache::new(256),
            by_expr_cache: Cache::new(128),
            expression_form_cache: Cache::new(128),
        }
    }

    #[framed]
    async fn try_get_and_decode_core(&self, url: HipStr<'_>) -> Option<HipStr<'static>> {
        self.rate_limiter.until_ready().await;
        let permit = self.request_semaphore.acquire().await.unwrap();
        let result = if url.len() > REQWEST_MAX_URL_LEN {
            let result = block_in_place(|| {
                CURL_CLIENT.with_borrow_mut(|curl| {
                    curl.get(true)
                        .and_then(|_| curl.connect_timeout(CONNECT_TIMEOUT))
                        .and_then(|_| curl.timeout(E2E_TIMEOUT))
                        .and_then(|_| curl.url(&url))
                        .and_then(|_| curl.perform())
                        .map_err(anyhow::Error::from)
                        .and_then(|_| {
                            let response_code = curl.response_code()?;
                            if response_code != 200 {
                                error!("Error reading {url}: HTTP response code {response_code}");
                            }
                            let response_body = curl.get_mut().take_all();
                            curl.reset();
                            Ok(response_body)
                        })
                })
            });
            drop(permit);
            result.and_then(|response_body| Ok(String::from_utf8(response_body)?))
        } else {
            let result = self
                .http
                .get(url.as_str())
                .header("Referer", "https://factordb.com")
                .send()
                .and_then(Response::text)
                .await;
            drop(permit);
            result.map_err(|e| anyhow::Error::from(e.without_url()))
        };
        match result {
            Err(e) => {
                error!("Error reading {url}: {e}");
                None
            }
            Ok(text) => {
                if text.contains("502 Proxy Error") {
                    error!("502 error from {url}");
                    None
                } else {
                    Some(text.into())
                }
            }
        }
    }

    #[framed]
    async fn retrying_get_and_decode_or<'a>(
        &self,
        url: HipStr<'_>,
        retry_delay: Duration,
        alt_url_supplier: impl FnOnce() -> HipStr<'a>,
    ) -> Result<HipStr<'static>, HipStr<'static>> {
        for _ in 0..MAX_RETRIES_WITH_FALLBACK {
            if let Some(value) = self.try_get_and_decode(url.clone()).await {
                return Ok(value);
            }
            sleep(retry_delay).await;
        }
        let alt_url = alt_url_supplier();
        warn!("Giving up on reaching {url} and falling back to {alt_url}");
        Err(self.retrying_get_and_decode(alt_url, retry_delay).await)
    }
}

impl FactorDbClient for RealFactorDbClient {
    #[framed]
    async fn parse_resource_limits(
        &self,
        bases_before_next_cpu_check: &mut usize,
        resources_text: &str,
    ) -> Option<ResourceLimits> {
        let now = Instant::now();
        let Some(captures) = self.resources_regex.captures_iter(resources_text).next() else {
            *bases_before_next_cpu_check = 1;
            return None;
        };
        let (
            _,
            [
                requests,
                cpu_seconds,
                cpu_tenths_within_second,
                minutes_to_reset,
                seconds_within_minute_to_reset,
            ],
        ) = captures.extract();
        let requests = requests.replace(",", "").parse::<u32>().unwrap();
        let requests_left = self.requests_per_hour - requests;
        let prev_requests_left = self
            .requests_left_last_check
            .swap(requests, Ordering::AcqRel);
        if prev_requests_left > requests_left
            && let Ok(state) = self.rate_limiter.check()
        {
            let limiter_burst_capacity = state.remaining_burst_capacity();
            if let Some(excess) = limiter_burst_capacity.checked_sub(requests_left)
                && let Some(excess) = NonZeroU32::new(excess)
            {
                warn!("{excess} more requests consumed than expected");
                self.rate_limiter.until_n_ready(excess).await.unwrap();
            }
        }
        // info!("Resources parsed: {}, {}, {}, {}",
        //     cpu_seconds, cpu_tenths_within_second, minutes_to_reset, seconds_within_minute_to_reset);
        let cpu_tenths_spent = cpu_seconds.parse::<usize>().unwrap() * 10
            + cpu_tenths_within_second.parse::<usize>().unwrap();
        CPU_TENTHS_SPENT_LAST_CHECK.store(cpu_tenths_spent, Release);
        let seconds_to_reset = minutes_to_reset.parse::<u64>().unwrap() * 60
            + seconds_within_minute_to_reset.parse::<u64>().unwrap();
        let resets_at = now + Duration::from_secs(seconds_to_reset);
        Some(ResourceLimits {
            cpu_tenths_spent,
            resets_at,
        })
    }

    /// Executes a GET request with a large reasonable default number of retries, or else
    /// restarts the process if that request consistently fails.
    #[framed]
    async fn retrying_get_and_decode(&self, url: HipStr<'_>, retry_delay: Duration) -> HipStr<'static> {
        for _ in 0..MAX_RETRIES {
            if let Some(value) = self.try_get_and_decode(url.clone()).await {
                return value;
            }
            sleep(retry_delay).await;
        }
        let mut shutdown_receiver = self.shutdown_receiver.clone();
        let mut raw_args = std::env::args_os();
        let cmd = raw_args.next().unwrap();
        if shutdown_receiver.check_for_shutdown() {
            error!("Retried {url} too many times after shutdown was signaled; exiting");
            exit(0);
        } else {
            error!("Retried {url} too many times; restarting");
            let e = Command::new(cmd).args(raw_args).exec();
            panic!("Failed to restart: {e}");
        }
    }

    #[framed]
    async fn try_get_and_decode(&self, url: HipStr<'_>) -> Option<HipStr<'static>> {
        sleep_until(self.all_threads_blocked_until.load(Acquire).into()).await;
        let response = self.try_get_and_decode_core(url).await?;
        let mut temp_bases = usize::MAX;
        if let Some(ResourceLimits { resets_at, .. }) =
            self.parse_resource_limits(&mut temp_bases, &response).await
        {
            self.all_threads_blocked_until
                .store(resets_at.into(), Release);
            if EXIT_TIME
                .get()
                .is_some_and(|exit_time| exit_time <= &resets_at)
            {
                error!("Resource limits reached and won't reset during this process's lifespan");
                exit(0);
            } else if let Some(throttling_duration) =
                resets_at.checked_duration_since(Instant::now())
            {
                warn!("Resource limits reached; throttling for {throttling_duration:?}");
            }
            return None;
        }
        Some(response)
    }

    #[framed]
    async fn try_get_resource_limits(
        &self,
        bases_before_next_cpu_check: &mut usize,
    ) -> Option<ResourceLimits> {
        let response = self
            .try_get_and_decode_core("https://factordb.com/res.php".into())
            .await?;
        self.parse_resource_limits(bases_before_next_cpu_check, &response)
            .await
    }

    fn read_ids_and_exprs<'a>(&self, haystack: &'a str) -> impl Iterator<Item = (u128, &'a str)> {
        self.id_and_expr_regex
            .captures_iter(haystack)
            .flat_map(move |capture| {
                let Some(id) = capture.get(1) else {
                    error!("Failed to get ID for expression in\n{haystack}");
                    return None;
                };
                let id = match id.as_str().parse::<u128>() {
                    Ok(id) => id,
                    Err(e) => {
                        error!("Failed to parse ID {}: {e}", id.as_str());
                        return None;
                    }
                };
                let Some(expr) = capture.get(2) else {
                    error!("Failed to get expression for ID {id} in\n{haystack}");
                    return None;
                };
                Some((id, expr.as_str()))
            })
            .unique()
    }

    #[inline]
    #[framed]
    async fn try_get_expression_form(&mut self, entry_id: u128) -> Option<HipStr<'static>> {
        if entry_id <= MAX_ID_EQUAL_TO_VALUE {
            return Some(entry_id.to_string().into());
        }
        if let Some(response) = self.expression_form_cache.get(&entry_id) {
            info!("Expression-form cache hit for {entry_id}");
            return Some(response.clone());
        }
        let response = self
            .try_get_and_decode(format!("https://factordb.com/index.php?id={entry_id}").into())
            .await?;
        let expression_form: HipStr = self
            .expression_form_regex
            .captures(&response)?
            .get(1)?
            .as_str()
            .into();
        self.expression_form_cache
            .insert(entry_id, expression_form.clone());
        Some(expression_form)
    }

    #[inline]
    fn cached_factors(
        &self,
        mut id: NumberSpecifier<&str, &str>,
    ) -> Option<ProcessedStatusApiResponse> {
        if let Id(entry_id) = id
            && entry_id <= MAX_ID_EQUAL_TO_VALUE
        {
            id = Expression(Numeric(entry_id));
        }
        if let Expression(Numeric(n)) = id {
            debug!("Specially handling numeric expression {n}");
            let factors = FactorFinder::find_factors_of_u128(n).into_boxed_slice();
            return Some(ProcessedStatusApiResponse {
                status: Some(if factors.len() > 1 {
                    FullyFactored
                } else {
                    Prime
                }),
                factors,
                id: Numeric::<&str, &str>(n).known_id(),
            });
        }
        let cached = match id {
            Id(id) => self.by_id_cache.get(&id).or_else(||
                self.expression_form_cache.get(&id).and_then(|expr| self.by_expr_cache.get(expr.as_str()))).cloned(),
            Expression(Factor::Expression(expr)) =>
                self.by_expr_cache.get(expr).cloned(),
            _ => None,
        };
        if cached.is_some() {
            info!("Factor cache hit for {id}");
        }
        cached
    }

    #[inline]
    #[framed]
    async fn known_factors_as_digits(
        &mut self,
        id: NumberSpecifier<&str, &str>,
        include_ff: bool,
        get_digits_as_fallback: bool,
    ) -> ProcessedStatusApiResponse {
        debug!("known_factors_as_digits: id={id:?}");
        if let Some(cached) = self.cached_factors(id.clone()) {
            return cached;
        }
        let mut expr_key = None;
        let response = match id {
            Id(id) => {
                let url = format!("https://factordb.com/api?id={id}").into();
                if get_digits_as_fallback {
                    self.retrying_get_and_decode_or(url, RETRY_DELAY, || {
                        format!("https://factordb.com/index.php?showid={id}").into()
                    })
                    .await
                    .map_err(Some)
                } else {
                    self.try_get_and_decode(url).await.ok_or(None)
                }
            }
            Expression(ref expr) => {
                if let Factor::Expression(expr) = expr {
                    expr_key = Some(expr);
                }
                let url =
                    format!("https://factordb.com/api?query={}", encode(&expr.as_str())).into();
                self.try_get_and_decode(url).await.ok_or(None)
            }
        };
        debug!("{id}: Got API response:\n{response:?}");
        let mut processed = match response {
            Ok(api_response) => match from_str::<NumberStatusApiResponse>(&api_response) {
                Err(e) => {
                    error!("{id}: Failed to decode API response: {e}: {api_response}");
                    ProcessedStatusApiResponse::default()
                }
                Ok(NumberStatusApiResponse {
                    status,
                    factors,
                    id: recvd_id,
                }) => {
                    let recvd_id_parsed = recvd_id.to_string().parse::<u128>().ok();
                    debug!("Parsed received ID {recvd_id} as {recvd_id_parsed:?}");
                    info!(
                        "{recvd_id_parsed:?} ({id}): Fetched status of {status} and {} factors of sizes {}",
                        factors.len(),
                        factors.iter().map(|(digits, _)| digits.len()).join(",")
                    );
                    let status = match &*status {
                        "FF" => Some(FullyFactored),
                        "P" | "PRP" => Some(Prime),
                        "C" => Some(UnfactoredComposite),
                        "CF" => Some(PartlyFactoredComposite),
                        "U" => Some(Unknown),
                        x => {
                            error!("{recvd_id:?} ({id}): Unrecognized number status code: {x}");
                            None
                        }
                    };
                    let factors = {
                        let mut factors: Vec<_> = factors
                            .into_iter()
                            .map(|(factor, _exponent)| Factor::from(factor))
                            .collect();
                        factors.sort();
                        factors.dedup();
                        factors
                    };
                    ProcessedStatusApiResponse {
                        status,
                        factors: factors.into_boxed_slice(),
                        id: recvd_id_parsed,
                    }
                }
            },
            Err(None) => ProcessedStatusApiResponse {
                status: None,
                id: None,
                factors: Box::new([]),
            },
            Err(Some(fallback_response)) => {
                let factors = self
                    .digits_fallback_regex
                    .captures(&fallback_response)
                    .and_then(|c| c.get(1))
                    .map(|digits_cell| {
                        vec![
                            digits_cell
                                .as_str()
                                .chars()
                                .filter(char::is_ascii_digit)
                                .collect::<String>()
                                .into(),
                        ]
                    })
                    .unwrap_or_default();
                ProcessedStatusApiResponse {
                    status: None,
                    factors: factors.into_boxed_slice(),
                    id: None,
                }
            }
        };
        if processed.status.is_known_fully_factored() && !processed.factors.is_empty() {
            if let Some(id) = processed
                .id
                .or(if let Id(id) = id { Some(id) } else { None })
            {
                self.by_id_cache.insert(id, processed.clone());
            }
            if let Some(expr) = expr_key {
                self.by_expr_cache.insert(HipStr::from(*expr), processed.clone());
            }
        }
        if !include_ff && processed.status.is_known_fully_factored() {
            processed.factors = Box::default();
        }
        processed
    }

    #[framed]
    async fn try_report_factor(
        &self,
        u_id: NumberSpecifier<&str, &str>,
        factor: Factor<&str, &str>,
    ) -> ReportFactorResult {
        let (id, number) = match u_id {
            Expression(Numeric(_)) => return AlreadyFullyFactored,
            Expression(Factor::BigNumber(x)) => (None, Some(x)),
            Expression(Factor::Expression(x)) => (None, Some(x)),
            Id(id) => (Some(id), None),
        };
        self.rate_limiter.until_ready().await;
        let permit = self.request_semaphore.acquire().await.unwrap();
        let response = self.http.post("https://factordb.com/reportfactor.php")
                .form(&FactorSubmission {
                    id,
                    number,
                    factor: &factor.as_str(),
                }).send().and_then(Response::text).await;
        drop(permit);
        match response {
            Ok(text) => {
                info!("{u_id}: reported a factor of {factor}; response: {text}",);
                if text.contains("Error") {
                    OtherError
                } else if text.contains("submitted") {
                    Accepted
                } else if text.contains("fully factored") || text.contains("Number too small") {
                    AlreadyFullyFactored
                } else {
                    DoesNotDivide
                }
            }
            Err(e) => {
                error!("{u_id}: Failed to get response when submitting {factor}: {e}");
                sleep(RETRY_DELAY).await;
                OtherError
            }
        }
    }

    #[framed]
    async fn report_numeric_factor(&self, u_id: u128, factor: u128) -> ReportFactorResult {
        for _ in 0..SUBMIT_FACTOR_MAX_ATTEMPTS {
            let result = self.try_report_factor(Id(u_id), Numeric(factor)).await;
            if result != OtherError {
                return result;
            }
        }
        match FAILED_U_SUBMISSIONS_OUT
            .get()
            .unwrap()
            .lock()
            .await
            .write_fmt(format_args!("{u_id},{}\n", factor))
        {
            Ok(_) => warn!("{u_id}: wrote {factor} to failed submissions file"),
            Err(e) => error!("{u_id}: failed to write {factor} to failed submissions file: {e}"),
        }
        OtherError // factor that we failed to submit may still have been valid
    }
}

pub static CPU_TENTHS_SPENT_LAST_CHECK: AtomicUsize = AtomicUsize::new(MAX_CPU_BUDGET_TENTHS);
