#![feature(duration_constructors_lite)]

use std::sync::Arc;
use anyhow::anyhow;
use expiring_bloom_rs::{ExpiringBloomFilter, FilterConfigBuilder, InMemoryFilter};
use governor::{NotUntil, Quota, RateLimiter};
use governor::clock::{DefaultClock, ReasonablyRealtime};
use governor::middleware::RateLimitingMiddleware;
use governor::state::{DirectStateStore, InMemoryState, NotKeyed};
use itertools::Itertools;
use log::{error, info, warn};
use tokio::sync::mpsc::{channel, Receiver};
use reqwest::Client;
use primitive_types::U256;
use regex::Regex;
use tokio::task;
use tokio::time::{Duration, Instant, sleep};

const MAX_START: usize = 100_000;
const RETRY_DELAY: Duration = Duration::from_secs(1);
const NETWORK_TIMEOUT: Duration = Duration::from_secs(15);
const MIN_TIME_PER_RESTART: Duration = Duration::from_hours(1);
const RESULTS_PER_PAGE: usize = 64;
const MIN_DIGITS_IN_PRP: u64 = 300;
const CHECK_ID_URL_BASE: &str = "https://factordb.com/index.php?open=Prime&ct=Proof&id=";
const TASK_BUFFER_SIZE: usize = 4 * RESULTS_PER_PAGE;
const MIN_CAPACITY_AT_START_OF_SEARCH: usize = RESULTS_PER_PAGE;
const MIN_CAPACITY_AT_RESTART: usize = TASK_BUFFER_SIZE - RESULTS_PER_PAGE;
#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
#[repr(C)]
struct PrpChecksTask {
    bases_left: U256,
    id: u128,
    digits: u64,
}

struct BuildTaskContext {
    http: Client,
    bases_regex: Regex,
    digits_regex: Regex,
    rps_limiter: Arc<RateLimiter<NotKeyed, InMemoryState, DefaultClock>>,
}

fn count_ones(u256: U256) -> u32 {
    u256.0.iter().copied().map(u64::count_ones).sum()
}

async fn retrying_get_and_decode(http: &Client, url: &str) -> Box<str> {
    loop {
        match http.get(url).send().await {
            Err(http_error) => error!("Error reading {url}: {http_error}"),
            Ok(body) => match body.text().await {
                Err(decoding_error) => error!("Error reading {url}: {decoding_error}"),
                Ok(text) => return text.into_boxed_str(),
            }
        }
        sleep(RETRY_DELAY).await;
    }
}

async fn build_task(id: &str, ctx: &BuildTaskContext) -> anyhow::Result<Option<PrpChecksTask>> {
    let BuildTaskContext { http, bases_regex, digits_regex, rps_limiter } = ctx;
    let mut bases_left = U256::MAX - 3;
    let bases_url = format!("{CHECK_ID_URL_BASE}{id}");
    rps_limiter.until_ready().await;
    let bases_text = retrying_get_and_decode(http, &bases_url).await;
    for bases in bases_regex.captures_iter(&bases_text) {
        for base in bases.iter() {
            bases_left &= !(U256::from(1) << base.unwrap().as_str().parse::<u8>()?);
        }
    }
    if bases_left == U256::from(0) {
        info!("ID {id} already has all bases checked");
        Ok(None)
    } else {
        let Some(digits_captures) = digits_regex.captures(&bases_text) else {
            return Err(anyhow!("Couldn't find digit size"));
        };
        let digits = digits_captures[1].parse()?;
        let id = id.parse()?;
        let bases_count = count_ones(bases_left);
        info!("ID {id} has {digits} digits and {bases_count} bases left to check");
        Ok(Some(PrpChecksTask { bases_left, id, digits }))
    }
}
async fn do_checks<S: DirectStateStore, T: ReasonablyRealtime, U: RateLimitingMiddleware<T::Instant, NegativeOutcome=NotUntil<T::Instant>>>(mut receiver: Receiver<PrpChecksTask>, http: Client, rps_limiter: Arc<RateLimiter<NotKeyed, S, T, U>>) {
    let config = FilterConfigBuilder::default()
        .capacity(2500)
        .false_positive_rate(0.001)
        .level_duration(Duration::from_hours(1))
        .max_levels(24)
        .build()
        .unwrap();
    let mut cpu_tenths_spent_before = u64::MAX;
    let mut filter = InMemoryFilter::new(config).unwrap();
    let cert_regex = Regex::new("(Verified|Processing)").unwrap();
    let cpu_tenths_regex = Regex::new("([0-9]+)\\.([0-9]) seconds").unwrap();
    let time_to_reset_regex = Regex::new("([0-5][0-9]):([0-6][0-9])").unwrap();
    let mut task_bytes = [0u8; size_of::<PrpChecksTask>()];
    while let Some(task) = receiver.recv().await {
        task_bytes[0..size_of::<U256>()].copy_from_slice(&task.bases_left.to_big_endian());
        task_bytes[size_of::<U256>()..(size_of::<U256>() + size_of::<u128>())].copy_from_slice(&task.id.to_ne_bytes()[..]);
        if filter.query(&task_bytes).unwrap() {
            warn!("Detected a duplicate task: ID {}", task.id);
            continue;
        } else {
            filter.insert(&task_bytes).unwrap();
        }
        let mut bases_checked = 0;
        let bases_count = count_ones(task.bases_left);
        info!("{}: {} digits, {} bases to check", task.id, task.digits, bases_count);
        let url_base = format!("https://factordb.com/index.php?id={}&open=prime&basetocheck=", task.id);
        for base in (0..=(u8::MAX as usize)).filter(|i| task.bases_left.bit(*i)) {
            let url = format!("{url_base}{base}");
            rps_limiter.until_ready().await;
            let text = retrying_get_and_decode(&http, &url).await;
            if !text.contains(">number<") {
                error!("Failed to decode result from {url}: {text}");
                break;
            }
            bases_checked += 1;
            if cert_regex.is_match(&text) {
                info!("{}: No longer PRP (has certificate)", task.id);
                break;
            }
            if text.contains("set to C") {
                info!("{}: No longer PRP (ruled out by PRP check)", task.id);
                break;
            }
            if !text.contains("PRP") {
                info!("{}: No longer PRP (solved by N-1/N+1 or factor)", task.id);
                break;
            }
            info!("{}: Checked base {}", task.id, base);
        }
        rps_limiter.until_ready().await;
        let resources_text = retrying_get_and_decode(&http, "https://factordb.com/res.php").await;
        let (_, [cpu_seconds, cpu_tenths_within_second]) = cpu_tenths_regex.captures_iter(&resources_text).next().unwrap().extract();
        let cpu_tenths_spent_after = cpu_seconds.parse::<u64>().unwrap() * 10 + cpu_tenths_within_second.parse::<u64>().unwrap();
        info!("CPU time spent this cycle: {:.1} seconds", cpu_tenths_spent_after as f64 * 0.1);
        if let Some(cpu_spent) = cpu_tenths_spent_after.checked_sub(cpu_tenths_spent_before) {
            info!("{}: CPU time was {:.1} seconds for {} bases of {} digits",
            task.id, cpu_spent as f64 * 0.1, bases_checked, task.digits)
        }
        if cpu_tenths_spent_after >= 4800 {
            let (_, [minutes_to_reset, seconds_within_minute_to_reset]) = time_to_reset_regex.captures_iter(&resources_text).next().unwrap().extract();
            let seconds_to_reset = minutes_to_reset.parse::<u64>().unwrap() * 60 + seconds_within_minute_to_reset.parse::<u64>().unwrap();
            if seconds_to_reset * 5 > (6000 - cpu_tenths_spent_after) {
                warn!("Throttling {} seconds due to high server CPU usage", seconds_to_reset);
                sleep(Duration::from_secs(seconds_to_reset)).await;
            }
        }
        cpu_tenths_spent_before = cpu_tenths_spent_after;
    }
}

#[tokio::main]
async fn main() {
    let rps_limiter = RateLimiter::direct(Quota::per_hour(5800u32.try_into().unwrap()));
    // Guardian rate-limiters start out with their full burst capacity and recharge starting
    // immediately, but this would lead to twice the allowed number of requests in our first hour,
    // so we make it start nearly empty instead.
    rps_limiter.until_n_ready(5700u32.try_into().unwrap()).await.unwrap();

    simple_log::console("info").unwrap();
    let search_url_base = format!("https://factordb.com/listtype.php?t=1&mindig={MIN_DIGITS_IN_PRP}&perpage={RESULTS_PER_PAGE}&start=");
    let id_regex = Regex::new("index\\.php\\?id=([0-9]+)").unwrap();
    let http = Client::builder()
        .pool_max_idle_per_host(2)
        .timeout(NETWORK_TIMEOUT)
        .build().unwrap();
    let (sender, receiver) = channel(TASK_BUFFER_SIZE);
    let mut start = 0;
    let mut bases_since_restart = 0;
    let mut results_since_restart: usize = 0;
    let mut next_min_restart = Instant::now() + MIN_TIME_PER_RESTART;
    let rps_limiter = Arc::new(rps_limiter);
    let ctx = BuildTaskContext {
        bases_regex: Regex::new("Bases checked[^\n]*\n[^\n]*(?:([0-9]+),? )+").unwrap(),
        digits_regex: Regex::new("&lt;([0-9]+)&gt;").unwrap(),
        http: http.clone(),
        rps_limiter: rps_limiter.clone()
    };

    task::spawn(do_checks(receiver, http.clone(), rps_limiter.clone()));
    loop {
        let _ = sender.reserve_many(MIN_CAPACITY_AT_START_OF_SEARCH).await.unwrap();
        let search_url = format!("{search_url_base}{start}");
        rps_limiter.until_ready().await;
        let results_text = retrying_get_and_decode(&http, &search_url).await;
        for id in id_regex.captures_iter(&results_text).map(|result| result[1].to_owned().into_boxed_str()).unique() {
            results_since_restart += 1;
            match build_task(&id, &ctx).await {
                Err(e) => error!("{id}: {e}"),
                Ok(None) => {},
                Ok(Some(task)) => {
                    bases_since_restart += count_ones(task.bases_left) as usize;
                    sender.send(task).await.unwrap();
                }
            }
        }
        let mut restart = false;
        start += RESULTS_PER_PAGE;
        if start > MAX_START {
            info!("Restarting: reached maximum starting index");
            restart = true;
        } else if results_since_restart >= TASK_BUFFER_SIZE
                && bases_since_restart >= (results_since_restart * 254 * 254).isqrt()
                && Instant::now() >= next_min_restart {
            info!("Restarting: triggered {bases_since_restart} bases in {results_since_restart} search results");
            restart = true;
        } else {
            info!("Continuing: triggered {bases_since_restart} bases in {results_since_restart} search results");
        }
        if restart {
            let _ = sender.reserve_many(MIN_CAPACITY_AT_RESTART).await.unwrap();
            start = 0;
            results_since_restart = 0;
            bases_since_restart = 0;
            next_min_restart = Instant::now() + MIN_TIME_PER_RESTART;
        }
    }
}
