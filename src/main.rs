#![feature(duration_constructors_lite)]
#![feature(file_buffered)]

use anyhow::anyhow;
use expiring_bloom_rs::{ExpiringBloomFilter, FilterConfigBuilder, InMemoryFilter};
use governor::clock::{DefaultClock, ReasonablyRealtime};
use governor::middleware::RateLimitingMiddleware;
use governor::state::{DirectStateStore, InMemoryState, NotKeyed};
use governor::{NotUntil, Quota, RateLimiter};
use itertools::Itertools;
use log::{error, info, warn};
use primitive_types::U256;
use regex::{Regex, RegexBuilder};
use reqwest::Client;
use std::fs::File;
use std::io::BufRead;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use tokio::sync::mpsc::{Receiver, Sender, channel};
use tokio::task;
use tokio::time::{Duration, Instant, sleep};

const MAX_START: usize = 100_000;
const RETRY_DELAY: Duration = Duration::from_secs(1);
const NETWORK_TIMEOUT: Duration = Duration::from_secs(15);
const MIN_TIME_PER_RESTART: Duration = Duration::from_hours(1);
const PRP_RESULTS_PER_PAGE: usize = 64;
const MIN_DIGITS_IN_PRP: u64 = 300;
const MIN_DIGITS_IN_U: u64 = 2001;
const U_RESULTS_PER_PAGE: usize = 6;
const CHECK_ID_URL_BASE: &str = "https://factordb.com/index.php?open=Prime&ct=Proof&id=";
const PRP_TASK_BUFFER_SIZE: usize = 4 * PRP_RESULTS_PER_PAGE;
const MIN_CAPACITY_AT_RESTART: usize = PRP_TASK_BUFFER_SIZE - PRP_RESULTS_PER_PAGE / 2;
#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
#[repr(C)]
enum CheckTaskDetails {
    Prp { bases_left: U256, digits: u64 },
    U { wait_until: Instant },
}
struct CheckTask {
    id: u128,
    details: CheckTaskDetails,
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
        match http
            .get(url)
            .header("Referer", "https://factordb.com")
            .send()
            .await
        {
            Err(http_error) => error!("Error reading {url}: {http_error}"),
            Ok(body) => match body.text().await {
                Err(decoding_error) => error!("Error reading {url}: {decoding_error}"),
                Ok(text) => return text.into_boxed_str(),
            },
        }
        sleep(RETRY_DELAY).await;
    }
}

async fn build_task(id: &str, ctx: &BuildTaskContext) -> anyhow::Result<Option<CheckTask>> {
    let BuildTaskContext {
        http,
        bases_regex,
        digits_regex,
        rps_limiter,
    } = ctx;
    let mut bases_left = U256::MAX - 3;
    let bases_url = format!("{CHECK_ID_URL_BASE}{id}");
    rps_limiter.until_ready().await;
    let bases_text = retrying_get_and_decode(http, &bases_url).await;
    if bases_text.contains(" is prime") {
        info!("ID {id}: No longer PRP (solved by N-1/N+1 or factor before queueing)");
        return Ok(None);
    }
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
        Ok(Some(CheckTask {
            id,
            details: CheckTaskDetails::Prp { bases_left, digits },
        }))
    }
}

const MAX_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 127;
const MAX_CPU_BUDGET_TENTHS: u64 = 5900;
const UNKNOWN_STATUS_CHECK_BACKOFF: Duration = Duration::from_secs(30);
static CPU_TENTHS_SPENT_LAST_CHECK: AtomicU64 = AtomicU64::new(MAX_CPU_BUDGET_TENTHS);
const CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES: u64 = 4000;

async fn do_checks<
    S: DirectStateStore,
    T: ReasonablyRealtime,
    U: RateLimitingMiddleware<T::Instant, NegativeOutcome = NotUntil<T::Instant>>,
>(
    mut receiver: Receiver<CheckTask>,
    retry_send: Sender<CheckTask>,
    http: Client,
    rps_limiter: Arc<RateLimiter<NotKeyed, S, T, U>>,
) {
    let config = FilterConfigBuilder::default()
        .capacity(2500)
        .false_positive_rate(0.001)
        .level_duration(Duration::from_hours(1))
        .max_levels(24)
        .build()
        .unwrap();
    let mut filter = InMemoryFilter::new(config).unwrap();
    let cert_regex = Regex::new("(Verified|Processing)").unwrap();
    let resources_regex =
        RegexBuilder::new("([0-9]+)\\.([0-9]) seconds.*([0-5][0-9]):([0-6][0-9])")
            .multi_line(true)
            .dot_matches_new_line(true)
            .build()
            .unwrap();
    let u_status_regex = Regex::new("(Assigned|already|Please wait|>CF?<|>P<|>PRP<|>FF<)").unwrap();
    let mut bases_before_next_cpu_check = 1;
    let mut task_bytes = [0u8; size_of::<U256>() + size_of::<u128>()];
    while let Some(CheckTask { id, details }) = receiver.recv().await {
        task_bytes[size_of::<U256>()..].copy_from_slice(&id.to_ne_bytes()[..]);
        match details {
            CheckTaskDetails::Prp { bases_left, .. } => {
                task_bytes[0..size_of::<U256>()].copy_from_slice(&bases_left.to_big_endian());
            }
            _ => {
                task_bytes[0..size_of::<U256>()].fill(0);
            }
        }
        match filter.query(&task_bytes) {
            Ok(true) => {
                warn!("Detected a duplicate task: ID {}", id);
                continue;
            }
            Ok(false) => {}
            Err(e) => error!("Bloom filter error: {}", e),
        }
        match details {
            CheckTaskDetails::Prp { bases_left, digits } => {
                filter.insert(&task_bytes).unwrap();
                let bases_count = count_ones(bases_left);
                info!("{}: {} digits, {} bases to check", id, digits, bases_count);
                let url_base = format!(
                    "https://factordb.com/index.php?id={id}&open=prime&basetocheck=");
                for base in (0..=(u8::MAX as usize)).filter(|i| bases_left.bit(*i)) {
                    let url = format!("{url_base}{base}");
                    rps_limiter.until_ready().await;
                    let text = retrying_get_and_decode(&http, &url).await;
                    if !text.contains(">number<") {
                        error!("Failed to decode result from {url}: {text}");
                        break;
                    }
                    info!("{}: Checked base {}", id, base);
                    throttle_if_necessary(
                        &http,
                        &rps_limiter,
                        &resources_regex,
                        &mut bases_before_next_cpu_check,
                    )
                    .await;
                    if cert_regex.is_match(&text) {
                        info!("{}: No longer PRP (has certificate)", id);
                        break;
                    }
                    if text.contains("set to C") {
                        info!("{}: No longer PRP (ruled out by PRP check)", id);
                        break;
                    }
                    if !text.contains("PRP") {
                        info!("{}: No longer PRP (solved by N-1/N+1 or factor)", id);
                        break;
                    }
                }
            }
            CheckTaskDetails::U { wait_until } => {
                throttle_if_necessary(
                    &http,
                    &rps_limiter,
                    &resources_regex,
                    &mut bases_before_next_cpu_check,
                ).await;
                let remaining_wait = wait_until.saturating_duration_since(Instant::now());
                if remaining_wait > Duration::ZERO {
                    let remaining_secs = remaining_wait.as_secs();
                    warn!("Waiting {remaining_secs} seconds to start an unknown-status task");
                    retry_send.send(CheckTask {
                            id,
                            details: CheckTaskDetails::U { wait_until },
                        }).await.unwrap();
                } else {
                    let url = format!("https://factordb.com/index.php?id={id}&prp=Assign+to+worker");
                    let result = retrying_get_and_decode(&http, &url).await;
                    let Some(status) = u_status_regex.captures_iter(&result).next() else {
                        error!("Failed to decode status for {id} from result: {result}");
                        continue;
                    };
                    match status.get(1) {
                        None => error!("Failed to decode status for {id}: {result}"),
                        Some(matched_status) => match matched_status.as_str() {
                            "Assigned" => {
                                filter.insert(&task_bytes).unwrap();
                                info!(
                                    "Assigned PRP check for unknown-status number with ID {id}"
                                )
                            }
                            "Please wait" => {
                                warn!(
                                    "Got 'please wait' for unknown-status number with ID {id}"
                                );
                                let next_try = Instant::now() + UNKNOWN_STATUS_CHECK_BACKOFF;
                                retry_send.send(CheckTask {
                                        id,
                                        details: CheckTaskDetails::U {
                                            wait_until: next_try,
                                        },
                                    }).await.unwrap();
                            }
                            _ => {
                                filter.insert(&task_bytes).unwrap();
                                warn!(
                                    "Unknown-status number with ID {id} is already being checked"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

async fn throttle_if_necessary<
    S: DirectStateStore,
    T: ReasonablyRealtime,
    U: RateLimitingMiddleware<T::Instant, NegativeOutcome = NotUntil<T::Instant>>,
>(
    http: &Client,
    rps_limiter: &Arc<RateLimiter<NotKeyed, S, T, U>>,
    resources_regex: &Regex,
    bases_before_next_cpu_check: &mut u64,
) {
    *bases_before_next_cpu_check -= 1;
    if *bases_before_next_cpu_check != 0 {
        return;
    }
    sleep(Duration::from_secs(10)).await; // allow for delay in CPU accounting
    rps_limiter.until_ready().await;
    let resources_text = retrying_get_and_decode(&http, "https://factordb.com/res.php").await;
    // info!("Resources fetched");
    let Some(captures) = resources_regex.captures_iter(&resources_text).next() else {
        error!("Failed to parse resource limits");
        *bases_before_next_cpu_check = 1;
        return;
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
    CPU_TENTHS_SPENT_LAST_CHECK.store(cpu_tenths_spent_after, Ordering::Release);
    let seconds_to_reset = minutes_to_reset.parse::<u64>().unwrap() * 60
        + seconds_within_minute_to_reset.parse::<u64>().unwrap();
    let tenths_remaining = MAX_CPU_BUDGET_TENTHS.saturating_sub(cpu_tenths_spent_after);
    let tenths_remaining_minus_reserve = tenths_remaining.saturating_sub(seconds_to_reset / 10);
    let bases_remaining =
        (tenths_remaining_minus_reserve / 10).min(MAX_BASES_BETWEEN_RESOURCE_CHECKS);
    if bases_remaining < 8 {
        warn!(
            "CPU time spent this cycle: {:.1} seconds. Throttling {} seconds due to high server CPU usage",
            cpu_tenths_spent_after as f64 * 0.1,
            seconds_to_reset
        );
        sleep(Duration::from_secs(seconds_to_reset)).await;
        *bases_before_next_cpu_check = MAX_BASES_BETWEEN_RESOURCE_CHECKS;
        CPU_TENTHS_SPENT_LAST_CHECK.store(0, Ordering::Release);
    } else {
        info!(
            "CPU time spent this cycle: {:.1} seconds; checking again after {} bases",
            cpu_tenths_spent_after as f64 * 0.1,
            bases_remaining
        );
        *bases_before_next_cpu_check = bases_remaining;
    }
}

#[tokio::main]
async fn main() {
    let rps_limiter = RateLimiter::direct(Quota::per_hour(6000u32.try_into().unwrap()));
    // Guardian rate-limiters start out with their full burst capacity and recharge starting
    // immediately, but this would lead to twice the allowed number of requests in our first hour,
    // so we make it start nearly empty instead.
    rps_limiter
        .until_n_ready(5800u32.try_into().unwrap())
        .await
        .unwrap();
    let (retry_send, mut retry_recv) = channel(PRP_TASK_BUFFER_SIZE);
    simple_log::console("info").unwrap();
    let prp_search_url_base = format!(
        "https://factordb.com/listtype.php?t=1&mindig={MIN_DIGITS_IN_PRP}&perpage={PRP_RESULTS_PER_PAGE}&start="
    );
    let u_search_url_base = format!(
        "https://factordb.com/listtype.php?t=2&mindig={MIN_DIGITS_IN_U}&perpage={U_RESULTS_PER_PAGE}&start="
    );
    let id_regex = Regex::new("index\\.php\\?id=([0-9]+)").unwrap();
    let http = Client::builder()
        .pool_max_idle_per_host(2)
        .timeout(NETWORK_TIMEOUT)
        .build()
        .unwrap();
    let (prp_sender, prp_receiver) = channel(PRP_TASK_BUFFER_SIZE);
    let mut prp_start = 0;
    let mut u_start = 0;
    let mut dump_file_index = 3;
    let mut dump_file = File::open_buffered(format!("U{dump_file_index:0>6}.csv")).unwrap();
    let mut dump_file_lines_read = 0;
    let mut line = String::new();
    let mut bases_since_restart = 0;
    let mut results_since_restart: usize = 0;
    let mut next_min_restart = Instant::now() + MIN_TIME_PER_RESTART;
    let rps_limiter = Arc::new(rps_limiter);
    let ctx = BuildTaskContext {
        bases_regex: Regex::new("Bases checked[^\n]*\n[^\n]*(?:([0-9]+),? )+").unwrap(),
        digits_regex: Regex::new("&lt;([0-9]+)&gt;").unwrap(),
        http: http.clone(),
        rps_limiter: rps_limiter.clone(),
    };

    task::spawn(do_checks(
        prp_receiver,
        retry_send,
        http.clone(),
        rps_limiter.clone(),
    ));
    loop {
        let search_url = format!("{prp_search_url_base}{prp_start}");
        rps_limiter.until_ready().await;
        let results_text = retrying_get_and_decode(&http, &search_url).await;
        for id in id_regex
            .captures_iter(&results_text)
            .map(|result| result[1].to_owned().into_boxed_str())
            .unique()
        {
            results_since_restart += 1;
            match build_task(&id, &ctx).await {
                Err(e) => error!("{id}: {e}"),
                Ok(None) => {}
                Ok(Some(task)) => {
                    while let Ok(permit) = prp_sender.try_reserve() && let Ok(task) = retry_recv.try_recv() {
                        info!("Moving retried task with ID {} to main queue (nonblocking)", task.id);
                        permit.send(task);
                    }
                    if let CheckTask {
                        details: CheckTaskDetails::Prp { bases_left, .. },
                        ..
                    } = task
                    {
                        bases_since_restart += count_ones(bases_left) as usize;
                    }
                    prp_sender.send(task).await.unwrap();
                    let now = Instant::now();
                    let cpu_tenths_spent = CPU_TENTHS_SPENT_LAST_CHECK.load(Ordering::Acquire);
                    if cpu_tenths_spent >= CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES {
                        info!("Using dump file, because {:.1} seconds CPU time has already been spent this cycle",
                            cpu_tenths_spent as f64 * 0.1);
                        let mut lines_read = 0;
                        while lines_read < U_RESULTS_PER_PAGE {
                            line.clear();
                            while line.len() == 0 {
                                let mut next_file = false;
                                match dump_file.read_line(&mut line) {
                                    Ok(0) => next_file = true,
                                    Ok(_) => {}
                                    Err(e) => {
                                        error!("Reading unknown-status dump file: {e}");
                                        next_file = true;
                                    }
                                }
                                if next_file {
                                    dump_file_index += 1;
                                    info!("Opening new dump file: {dump_file_index}");
                                    dump_file =
                                        File::open_buffered(format!("U{dump_file_index:0>6}.csv")).unwrap();
                                    dump_file_lines_read = 0;
                                }
                            }
                            let id = line.split(",").next().unwrap();
                            prp_sender.send(CheckTask {
                                    id: id.parse().unwrap(),
                                    details: CheckTaskDetails::U { wait_until: now },
                                }).await.unwrap();
                            info!("Queued check of unknown-status number with ID {id} from dump file");
                            lines_read += 1;
                            dump_file_lines_read += 1;
                        }
                        info!("{dump_file_lines_read} lines read from dump file {dump_file_index}");
                    } else {
                        info!("Using search to find unknown-status numbers, because only {:.1} seconds CPU time has been spent this cycle",
                            cpu_tenths_spent as f64 * 0.1);
                        let search_url = format!("{u_search_url_base}{u_start}");
                        rps_limiter.until_ready().await;
                        let results_text = retrying_get_and_decode(&http, &search_url).await;
                        for id in id_regex
                            .captures_iter(&results_text)
                            .map(|result| result[1].to_owned().into_boxed_str())
                            .unique()
                        {
                            prp_sender.send(CheckTask {
                                    id: id.parse().unwrap(),
                                    details: CheckTaskDetails::U { wait_until: now },
                                }).await.unwrap();
                            info!("Queued check of unknown-status number with ID {id} from search");
                        }
                        u_start += U_RESULTS_PER_PAGE;
                    }
                }
            }
            while let Ok(task) = retry_recv.try_recv() {
                info!("Moving retried task with ID {} to main queue (blocking)", task.id);
                prp_sender.send(task).await.unwrap();
            }
        }
        let mut restart = false;
        prp_start += PRP_RESULTS_PER_PAGE;
        if prp_start > MAX_START || u_start > MAX_START {
            info!("Restarting: reached maximum starting index");
            restart = true;
        } else if results_since_restart >= PRP_TASK_BUFFER_SIZE
            && bases_since_restart >= (results_since_restart * 254 * 254).isqrt()
            && Instant::now() >= next_min_restart
        {
            info!(
                "Restarting: triggered {bases_since_restart} bases in {results_since_restart} search results"
            );
            restart = true;
        } else {
            info!(
                "Continuing: triggered {bases_since_restart} bases in {results_since_restart} search results"
            );
        }
        if restart {
            let _ = prp_sender
                .reserve_many(MIN_CAPACITY_AT_RESTART)
                .await
                .unwrap();
            prp_start = 0;
            u_start = 0;
            results_since_restart = 0;
            bases_since_restart = 0;
            next_min_restart = Instant::now() + MIN_TIME_PER_RESTART;
        }
    }
}
