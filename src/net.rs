use crate::{CPU_TENTHS_SPENT_LAST_CHECK, EXIT_TIME};
use governor::{DefaultDirectRateLimiter, Quota, RateLimiter};
use log::{error, warn};
use regex::{Regex, RegexBuilder};
use reqwest::{Client, RequestBuilder};
use std::num::NonZeroU32;
use std::os::unix::prelude::CommandExt;
use std::process::{Command, exit};
use std::sync::Arc;
use std::sync::atomic::Ordering::Release;
use std::time::Duration;
use tokio::time::{Instant, sleep, sleep_until};

pub const MAX_RETRIES: usize = 40;

const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);
const E2E_TIMEOUT: Duration = Duration::from_secs(30);

#[derive(Clone)]
pub struct ThrottlingHttpClient {
    resources_regex: Arc<Regex>,
    http: Client,
    rps_limiter: Arc<DefaultDirectRateLimiter>,
}

impl ThrottlingHttpClient {
    pub fn new(rph_limit: NonZeroU32) -> Self {
        let rps_limiter = RateLimiter::direct(Quota::per_hour(rph_limit));
        let resources_regex =
            RegexBuilder::new("([0-9]+)\\.([0-9]) seconds.*([0-6][0-9]):([0-6][0-9])")
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
        rps_limiter
            .check_n(6050u32.try_into().unwrap())
            .unwrap()
            .unwrap();

        Self {
            resources_regex: resources_regex.into(),
            http,
            rps_limiter: rps_limiter.into(),
        }
    }

    pub fn parse_resource_limits(
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
                cpu_seconds,
                cpu_tenths_within_second,
                minutes_to_reset,
                seconds_within_minute_to_reset,
            ],
        ) = captures.extract();
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

    async fn try_get_and_decode_core(&self, url: &str) -> Option<Box<str>> {
        self.rps_limiter.until_ready().await;
        match self
            .http
            .get(url)
            .header("Referer", "https://factordb.com")
            .send()
            .await
        {
            Err(http_error) => {
                error!("Error reading {url}: {http_error}");
                None
            }
            Ok(body) => match body.text().await {
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
        let response = self.try_get_and_decode_core(url).await?;
        if let Some((_, seconds_to_reset)) = self.parse_resource_limits(&mut u64::MAX, &response) {
            let reset_time = Instant::now() + Duration::from_secs(seconds_to_reset);
            if EXIT_TIME
                .get()
                .is_some_and(|exit_time| exit_time <= &reset_time)
            {
                error!("Resource limits reached and won't reset during this process's lifespan");
                exit(0);
            } else {
                warn!("Resource limits reached; throttling for {seconds_to_reset} seconds");
                sleep_until(reset_time).await;
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
    }

    pub async fn post(&self, url: &str) -> RequestBuilder {
        self.rps_limiter.until_ready().await;
        self.http.post(url)
    }
}
