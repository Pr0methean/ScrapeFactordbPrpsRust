use crate::{CPU_TENTHS_SPENT_LAST_CHECK, EXIT_TIME};
use anyhow::Error;
use atomic_time::AtomicInstant;
use governor::middleware::StateInformationMiddleware;
use governor::{DefaultDirectRateLimiter, Quota, RateLimiter};
use log::{error, warn};
use regex::{Regex, RegexBuilder};
use reqwest::{Client, RequestBuilder, Response};
use serde::Serialize;
use std::num::NonZeroU32;
use std::os::unix::prelude::CommandExt;
use std::process::{Command, exit};
use std::sync::Arc;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::Duration;
use tokio::sync::Semaphore;
use tokio::time::{Instant, sleep, sleep_until};

pub const MAX_RETRIES: usize = 40;
const MAX_RETRIES_WITH_FALLBACK: usize = 10;

const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);
const E2E_TIMEOUT: Duration = Duration::from_secs(30);

#[derive(Clone)]
pub struct ThrottlingHttpClient {
    resources_regex: Arc<Regex>,
    http: Client,
    rate_limiter: Arc<DefaultDirectRateLimiter<StateInformationMiddleware>>,
    requests_left_last_check: Arc<AtomicU32>,
    requests_per_hour: u32,
    request_semaphore: Arc<Semaphore>,
    all_threads_blocked_until: Arc<AtomicInstant>,
}

pub struct ThrottlingRequestBuilder<'a> {
    inner: RequestBuilder,
    client: &'a ThrottlingHttpClient,
}

impl<'a> ThrottlingRequestBuilder<'a> {
    pub fn form<T: Serialize + ?Sized>(self, payload: &T) -> Self {
        ThrottlingRequestBuilder {
            inner: self.inner.form(payload),
            client: self.client,
        }
    }

    pub async fn send(self) -> Result<Response, Error> {
        sleep_until(self.client.all_threads_blocked_until.load(Acquire).into()).await;
        self.client.rate_limiter.until_ready().await;
        match self.client.request_semaphore.acquire().await {
            Ok(_permit) => self.inner.send().await.map_err(Error::from),
            Err(e) => Err(e.into()),
        }
    }
}

impl ThrottlingHttpClient {
    pub fn new(requests_per_hour: NonZeroU32, max_concurrent_requests: usize) -> Self {
        let rate_limiter =
            RateLimiter::direct(Quota::per_hour(requests_per_hour)).with_middleware();
        let resources_regex =
            RegexBuilder::new("Page requests(?:[^0-9])+([0-9,]+).*CPU.*>([0-9]+)\\.([0-9]) seconds.*600\\.0 seconds.*([0-6][0-9]):([0-6][0-9])")
                .multi_line(true)
                .dot_matches_new_line(true)
                .build()
                .unwrap();
        let http = Client::builder()
            .pool_max_idle_per_host(2)
            .timeout(E2E_TIMEOUT)
            .connect_timeout(CONNECT_TIMEOUT)
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
        }
    }

    pub async fn parse_resource_limits(
        &self,
        bases_before_next_cpu_check: &mut u64,
        resources_text: &str,
    ) -> Option<(u64, u64)> {
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
        let cpu_tenths_spent_after = cpu_seconds.parse::<u64>().unwrap() * 10
            + cpu_tenths_within_second.parse::<u64>().unwrap();
        CPU_TENTHS_SPENT_LAST_CHECK.store(cpu_tenths_spent_after, Release);
        let seconds_to_reset = minutes_to_reset.parse::<u64>().unwrap() * 60
            + seconds_within_minute_to_reset.parse::<u64>().unwrap();
        Some((cpu_tenths_spent_after, seconds_to_reset))
    }

    /// Executes a GET request with a large reasonable default number of retries, or else
    /// restarts the process if that request consistently fails.
    pub async fn retrying_get_and_decode(&self, url: &str, retry_delay: Duration) -> Box<str> {
        for _ in 0..MAX_RETRIES {
            if let Some(value) = self.try_get_and_decode(url).await {
                return value;
            }
            sleep(retry_delay).await;
        }
        error!("Retried {url} too many times; restarting");
        let mut raw_args = std::env::args_os();
        let cmd = raw_args.next().unwrap();
        let e = Command::new(cmd).args(raw_args).exec();
        panic!("Failed to restart: {e}");
    }

    pub async fn retrying_get_and_decode_or(
        &self,
        url: &str,
        retry_delay: Duration,
        alt_url_supplier: impl FnOnce() -> String,
    ) -> Result<Box<str>, Box<str>> {
        for _ in 0..MAX_RETRIES_WITH_FALLBACK {
            if let Some(value) = self.try_get_and_decode(url).await {
                return Ok(value);
            }
            sleep(retry_delay).await;
        }
        Err(self
            .retrying_get_and_decode(&alt_url_supplier.call_once(()), retry_delay)
            .await)
    }

    async fn try_get_and_decode_core(&self, url: &str) -> Option<Box<str>> {
        self.rate_limiter.until_ready().await;
        let permit = self.request_semaphore.acquire().await.unwrap();
        let result = self
            .http
            .get(url)
            .header("Referer", "https://factordb.com")
            .send()
            .await;
        drop(permit);
        match result {
            Err(http_error) => {
                error!("Error reading {url}: {http_error}");
                None
            }
            Ok(response) => match response.text().await {
                Err(decoding_error) => {
                    error!("Error reading {url}: {decoding_error}");
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
            },
        }
    }

    #[allow(const_item_mutation)]
    pub async fn try_get_and_decode(&self, url: &str) -> Option<Box<str>> {
        sleep_until(self.all_threads_blocked_until.load(Acquire).into()).await;
        let response = self.try_get_and_decode_core(url).await?;
        if let Some((_, seconds_to_reset)) =
            self.parse_resource_limits(&mut u64::MAX, &response).await
        {
            let reset_time = Instant::now() + Duration::from_secs(seconds_to_reset);
            self.all_threads_blocked_until
                .store(reset_time.into(), Release);
            if EXIT_TIME
                .get()
                .is_some_and(|exit_time| exit_time <= &reset_time)
            {
                error!("Resource limits reached and won't reset during this process's lifespan");
                exit(0);
            } else {
                warn!("Resource limits reached; throttling for {seconds_to_reset} seconds");
            }
            return None;
        }
        Some(response)
    }

    pub async fn try_get_resource_limits(
        &self,
        bases_before_next_cpu_check: &mut u64,
    ) -> Option<(u64, u64)> {
        let response = self
            .try_get_and_decode_core("https://factordb.com/res.php")
            .await?;
        self.parse_resource_limits(bases_before_next_cpu_check, &response)
            .await
    }

    pub fn post(&'_ self, url: &str) -> ThrottlingRequestBuilder<'_> {
        ThrottlingRequestBuilder {
            inner: self.http.post(url),
            client: self,
        }
    }
}
