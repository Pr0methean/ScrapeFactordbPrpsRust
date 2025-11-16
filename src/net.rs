use crate::{Factor, NumberSpecifier, NumberStatusApiResponse, MAX_ID_EQUAL_TO_VALUE, RETRY_DELAY};
use crate::shutdown::Shutdown;
use crate::{EXIT_TIME, MAX_CPU_BUDGET_TENTHS};
use anyhow::Error;
use arcstr::{literal, ArcStr};
use atomic_time::AtomicInstant;
use curl::easy::{Easy2, Handler, WriteError};
use governor::middleware::StateInformationMiddleware;
use governor::{DefaultDirectRateLimiter, Quota, RateLimiter};
use log::{debug, error, info, warn};
use regex::{Regex, RegexBuilder};
use reqwest::{Client, RequestBuilder};
use serde::Serialize;
use std::mem::swap;
use std::num::NonZeroU32;
use std::os::unix::prelude::CommandExt;
use std::process::{exit, Command};
use std::sync::Arc;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::time::Duration;
use itertools::Itertools;
use serde_json::from_str;
use tokio::sync::{Mutex, Semaphore};
use tokio::time::{sleep, sleep_until, Instant};
use urlencoding::encode;
use crate::algebraic::Factor::Numeric;
use crate::algebraic::NumberStatus::{FullyFactored, PartlyFactoredComposite, Prime, UnfactoredComposite, Unknown};
use crate::algebraic::{FactorFinder, ProcessedStatusApiResponse};

pub const MAX_RETRIES: usize = 40;
const MAX_RETRIES_WITH_FALLBACK: usize = 10;

const CONNECT_TIMEOUT: Duration = Duration::from_secs(30);
const E2E_TIMEOUT: Duration = Duration::from_secs(60);

const REQWEST_MAX_URL_LEN: usize = (u16::MAX - 1) as usize;

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

#[derive(Clone)]
pub struct FactorDbClient {
    resources_regex: Arc<Regex>,
    http: Client,
    rate_limiter: Arc<DefaultDirectRateLimiter<StateInformationMiddleware>>,
    requests_left_last_check: Arc<AtomicU32>,
    requests_per_hour: u32,
    request_semaphore: Arc<Semaphore>,
    all_threads_blocked_until: Arc<AtomicInstant>,
    shutdown_receiver: Shutdown,
    curl_client: Arc<Mutex<Easy2<Collector>>>,
    id_and_expr_regex: Arc<Regex>,
    digits_fallback_regex: Arc<Regex>,
}

pub struct ThrottlingRequestBuilder<'a> {
    inner: Result<RequestBuilder, ArcStr>,
    client: &'a FactorDbClient,
    form: Option<Box<str>>,
}

pub struct ResourceLimits {
    pub cpu_tenths_spent: usize,
    pub resets_at: Instant,
}

impl<'a> ThrottlingRequestBuilder<'a> {
    pub fn form<T: Serialize + ?Sized>(self, payload: &T) -> Result<Self, Error> {
        match self.inner {
            Ok(request_builder) => Ok(ThrottlingRequestBuilder {
                inner: Ok(request_builder.form(payload)),
                client: self.client,
                form: None,
            }),
            Err(_) => Ok(ThrottlingRequestBuilder {
                inner: self.inner,
                client: self.client,
                form: Some(serde_urlencoded::to_string(payload)?.into_boxed_str()),
            }),
        }
    }

    pub async fn send(self) -> Result<String, Error> {
        sleep_until(self.client.all_threads_blocked_until.load(Acquire).into()).await;
        self.client.rate_limiter.until_ready().await;
        match self.client.request_semaphore.acquire().await {
            Ok(_permit) => match self.inner {
                Ok(request_builder) => request_builder
                    .send()
                    .await
                    .map_err(|e| Error::from(e.without_url()))?
                    .text()
                    .await
                    .map_err(|e| Error::from(e.without_url())),
                Err(url) => {
                    let mut curl = self.client.curl_client.lock().await;
                    let url = url.clone();
                    if let Some(form) = self.form {
                        curl.post_fields_copy(form.as_bytes())?;
                    }
                    let response_text = curl
                        .post(true)
                        .and_then(|_| curl.url(&url))
                        .and_then(|_| curl.perform())
                        .map_err(anyhow::Error::from)
                        .and_then(|_| {
                            let response_code = curl.response_code()?;
                            if response_code != 200 {
                                error!("Error reading {url}: HTTP response code {response_code}")
                            }
                            Ok(String::from_utf8(curl.get_mut().take_all())?)
                        });
                    Ok(response_text?)
                }
            },
            Err(e) => Err(e.into()),
        }
    }
}

impl FactorDbClient {
    pub fn new(
        requests_per_hour: NonZeroU32,
        max_concurrent_requests: usize,
        shutdown_receiver: Shutdown,
    ) -> Self {
        let rate_limiter =
            RateLimiter::direct(Quota::per_hour(requests_per_hour)).with_middleware();
        let resources_regex =
            RegexBuilder::new("Page requests(?:[^0-9])+([0-9,]+).*CPU.*>([0-9]+)\\.([0-9]) seconds.*600\\.0 seconds.*([0-6][0-9]):([0-6][0-9])")
                .multi_line(true)
                .dot_matches_new_line(true)
                .build()
                .unwrap();
        let id_and_expr_regex = Regex::new("index\\.php\\?id=([0-9]+)\"><font[^>]*>([^<]+)</font>").unwrap();
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
            curl_client: Mutex::new(Easy2::new(Collector(Vec::new()))).into(),
            id_and_expr_regex: id_and_expr_regex.into(),
            digits_fallback_regex: digits_fallback_regex.into()
        }
    }

    pub async fn parse_resource_limits(
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
    pub async fn retrying_get_and_decode(&self, url: ArcStr, retry_delay: Duration) -> Box<str> {
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

    pub async fn retrying_get_and_decode_or(
        &self,
        url: ArcStr,
        retry_delay: Duration,
        alt_url_supplier: impl FnOnce() -> ArcStr,
    ) -> Result<Box<str>, Box<str>> {
        for _ in 0..MAX_RETRIES_WITH_FALLBACK {
            if let Some(value) = self.try_get_and_decode(url.clone()).await {
                return Ok(value);
            }
            sleep(retry_delay).await;
        }
        let alt_url = alt_url_supplier.call_once(());
        warn!("Giving up on reaching {url} and falling back to {alt_url}");
        Err(self.retrying_get_and_decode(alt_url, retry_delay).await)
    }

    async fn try_get_and_decode_core(&self, url: ArcStr) -> Option<Box<str>> {
        self.rate_limiter.until_ready().await;
        let permit = self.request_semaphore.acquire().await.unwrap();
        let result = if url.len() > REQWEST_MAX_URL_LEN {
            // FIXME: This blocks a Tokio thread, but it fails the borrow checker when wrapped in
            // spawn_blocking
            let mut curl = self.curl_client.lock().await;
            let url = url.clone();
            let response_text = curl
                .get(true)
                .and_then(|_| curl.url(&url))
                .and_then(|_| curl.perform())
                .map_err(anyhow::Error::from)
                .and_then(|_| {
                    let response_code = curl.response_code()?;
                    if response_code != 200 {
                        error!("Error reading {url}: HTTP response code {response_code}")
                    }
                    Ok(String::from_utf8(curl.get_mut().take_all())?)
                });
            drop(curl);
            response_text
        } else {
            let result = self
                .http
                .get(url.as_str())
                .header("Referer", "https://factordb.com")
                .send()
                .await;
            match result {
                Ok(response) => response.text().await,
                Err(e) => Err(e),
            }
                .map_err(|e| anyhow::Error::from(e.without_url()))
        };
        drop(permit);
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
                    Some(text.into_boxed_str())
                }
            }
        }
    }

    pub async fn try_get_and_decode(&self, url: ArcStr) -> Option<Box<str>> {
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

    pub async fn try_get_resource_limits(
        &self,
        bases_before_next_cpu_check: &mut usize,
    ) -> Option<ResourceLimits> {
        let response = self
            .try_get_and_decode_core(literal!("https://factordb.com/res.php"))
            .await?;
        self.parse_resource_limits(bases_before_next_cpu_check, &response)
            .await
    }

    pub fn post(&'_ self, url: ArcStr) -> ThrottlingRequestBuilder<'_> {
        ThrottlingRequestBuilder {
            inner: if url.len() <= REQWEST_MAX_URL_LEN {
                Ok(self.http.post(url.as_str()))
            } else {
                Err(url)
            },
            client: self,
            form: None,
        }
    }

    pub fn read_ids_and_exprs<'a>(&self, haystack: &'a str)
        -> impl Iterator<Item=(u128, &'a str)> {
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
    pub async fn known_factors_as_digits<
        T: AsRef<str> + std::fmt::Debug,
        U: AsRef<str> + std::fmt::Debug,
    >(
        &self,
        id: NumberSpecifier<T, U>,
        include_ff: bool,
        get_digits_as_fallback: bool,
    ) -> ProcessedStatusApiResponse {
        debug!("known_factors_as_digits: id={id:?}");
        if let NumberSpecifier::Expression(Numeric(n)) = id {
            debug!("Specially handling numeric expression {n}");
            let factors = FactorFinder::find_factors_of_u128(n).into_boxed_slice();
            return ProcessedStatusApiResponse {
                status: Some(if factors.len() > 1 {
                    Prime
                } else {
                    FullyFactored
                }),
                factors,
                id: if n <= MAX_ID_EQUAL_TO_VALUE {
                    Some(n)
                } else {
                    None
                },
            };
        }
        let response = match id {
            NumberSpecifier::Id(id) => {
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
            NumberSpecifier::Expression(ref expr) => {
                let url = format!("https://factordb.com/api?query={}", encode(&expr.as_str()));
                self.try_get_and_decode(url.into()).await.ok_or(None)
            }
        };
        debug!("{id}: Got API response:\n{response:?}");
        match response {
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
                    let status = match status.as_str() {
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
                    let factors =
                        if !include_ff && status == Some(FullyFactored) || status == Some(Prime) {
                            Box::new([])
                        } else {
                            let mut factors: Vec<_> = factors
                                .into_iter()
                                .map(|(factor, _exponent)| Factor::from(factor))
                                .collect();
                            factors.sort();
                            factors.dedup();
                            factors.into_boxed_slice()
                        };
                    ProcessedStatusApiResponse {
                        status,
                        factors,
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
                                .collect::<Box<str>>()
                                .into(),
                        ]
                            .into_boxed_slice()
                    })
                    .unwrap_or_else(|| Box::new([]));
                ProcessedStatusApiResponse {
                    status: None,
                    factors,
                    id: None,
                }
            }
        }
    }
}

pub static CPU_TENTHS_SPENT_LAST_CHECK: AtomicUsize = AtomicUsize::new(MAX_CPU_BUDGET_TENTHS);