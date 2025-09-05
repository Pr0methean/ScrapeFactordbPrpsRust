#![allow(stable_features)]
#![feature(duration_constructors_lite)]
#![feature(file_buffered)]

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
use std::io::{BufRead, BufReader};
use std::ops::Add;
use std::process::exit;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use tokio::sync::mpsc::{Permit, PermitIterator, Receiver, Sender, channel, error::TrySendError};
use tokio::time::{Duration, Instant, sleep, sleep_until};
use tokio::{select, task};
use tokio::sync::OnceCell;

const MAX_START: usize = 100_000;
const RETRY_DELAY: Duration = Duration::from_secs(1);
const NETWORK_TIMEOUT: Duration = Duration::from_secs(15);
const MIN_TIME_PER_RESTART: Duration = Duration::from_hours(1);
const PRP_RESULTS_PER_PAGE: usize = 64;
const MIN_DIGITS_IN_PRP: u64 = 300;
const MIN_DIGITS_IN_U: u64 = 2001;
const U_RESULTS_PER_PAGE: usize = 3;
const CHECK_ID_URL_BASE: &str = "https://factordb.com/index.php?open=Prime&ct=Proof&id=";
const PRP_TASK_BUFFER_SIZE: usize = 2 * PRP_RESULTS_PER_PAGE;
const U_TASK_BUFFER_SIZE: usize = 16;
const MIN_CAPACITY_AT_PRP_RESTART: usize = PRP_TASK_BUFFER_SIZE - PRP_RESULTS_PER_PAGE / 2;
const MIN_CAPACITY_AT_U_RESTART: usize = U_TASK_BUFFER_SIZE / 2;
static EXIT_TIME: OnceCell<Instant> = OnceCell::const_new();

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
#[repr(u8)]
enum CheckTaskType {
    Prp, U
}
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
struct CheckTask {
    id: u128,
    source_file: Option<u64>,
    task_type: CheckTaskType,
}

struct BuildTaskContext {
    http: Client,
    bases_regex: Regex,
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
                Ok(text) => {
                    if text.contains("502 Proxy Error") {
                        error!("502 error from {url}");
                    } else {
                        return text.into_boxed_str();
                    }
                }
            },
        }
        sleep(RETRY_DELAY).await;
    }
}

async fn get_prp_remaining_bases(id: &str, ctx: &BuildTaskContext) -> U256 {
    let BuildTaskContext {
        http,
        bases_regex,
        rps_limiter,
    } = ctx;
    let mut bases_left = U256::MAX - 3;
    let bases_url = format!("{CHECK_ID_URL_BASE}{id}");
    rps_limiter.until_ready().await;
    let bases_text = retrying_get_and_decode(http, &bases_url).await;
    if bases_text.contains(" is prime") {
        info!("ID {id}: No longer PRP (solved by N-1/N+1 or factor before queueing)");
        return U256::from(0);
    }
    for bases in bases_regex.captures_iter(&bases_text) {
        for base in bases.iter() {
            let Ok(base) = base.unwrap().as_str().parse::<u8>() else {
                error!("Invalid PRP-check base: {:?}", base);
                continue;
            };
            bases_left &= !(U256::from(1) << base);
        }
    }
    if bases_left == U256::from(0) {
        info!("ID {id} already has all bases checked");
    }
    bases_left
}

const MAX_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 127;

const MIN_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 4;

const MAX_CPU_BUDGET_TENTHS: u64 = 6000;
const UNKNOWN_STATUS_CHECK_BACKOFF: Duration = Duration::from_secs(15);
const UNKNOWN_STATUS_CHECK_MAX_BLOCKING_WAIT: Duration = Duration::from_millis(1500);
static CPU_TENTHS_SPENT_LAST_CHECK: AtomicU64 = AtomicU64::new(MAX_CPU_BUDGET_TENTHS);
static NO_RESERVE: AtomicBool = AtomicBool::new(false);
const CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES: u64 = 5000;

async fn do_checks(
    prp_sender: Sender<CheckTask>,
    mut prp_receiver: Receiver<CheckTask>,
    mut u_receiver: Receiver<CheckTask>,
    http: Client,
    rps_limiter: Arc<RateLimiter<NotKeyed, InMemoryState, DefaultClock>>,
) {
    let mut next_unknown_attempt = Instant::now();
    let mut retry = None;
    let cert_regex = Regex::new("(Verified|Processing)").unwrap();
    let resources_regex =
        RegexBuilder::new("([0-9]+)\\.([0-9]) seconds.*([0-6][0-9]):([0-6][0-9])")
            .multi_line(true)
            .dot_matches_new_line(true)
            .build()
            .unwrap();
    let ctx = BuildTaskContext {
        bases_regex: Regex::new("Bases checked[^\n]*\n[^\n]*(?:([0-9]+),? )+").unwrap(),
        http: http.clone(),
        rps_limiter: rps_limiter.clone(),
    };
    let mut bases_before_next_cpu_check = 1;
    throttle_if_necessary(
        &http,
        &rps_limiter,
        &resources_regex,
        &mut bases_before_next_cpu_check,
        false,
    )
    .await;
    let u_status_regex = Regex::new("(Assigned|already|Please wait|>CF?<|>P<|>PRP<|>FF<)").unwrap();
    while let Some(CheckTask {id, task_type, source_file}) = prp_receiver.recv().await {
        match task_type {
            CheckTaskType::Prp => {
                let bases_left = get_prp_remaining_bases(&id.to_string(), &ctx).await;
                if bases_left == U256::from(0) {
                    continue;
                }
                let bases_count = count_ones(bases_left);
                info!("{}: {} bases to check", id, bases_count);
                let url_base =
                    format!("https://factordb.com/index.php?id={id}&open=prime&basetocheck=");
                for base in (0..=(u8::MAX as usize)).filter(|i| bases_left.bit(*i)) {
                    let url = format!("{url_base}{base}");
                    rps_limiter.until_ready().await;
                    let text = retrying_get_and_decode(&http, &url).await;
                    if !text.contains(">number<") {
                        error!("Failed to decode result from {url}: {text}");
                        break;
                    }
                    throttle_if_necessary(
                        &http,
                        &rps_limiter,
                        &resources_regex,
                        &mut bases_before_next_cpu_check,
                        true,
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
                    if next_unknown_attempt <= Instant::now() {
                        if let Some(CheckTask {
                            id,
                            task_type: CheckTaskType::U,
                            source_file
                        }) = retry
                        {
                            if try_handle_unknown(
                                &http,
                                &u_status_regex,
                                id,
                                &mut next_unknown_attempt,
                                source_file,
                                &rps_limiter,
                            )
                            .await
                            {
                                retry = None;
                            }
                        }
                        if retry == None {
                            while let Ok(CheckTask {id, task_type, source_file }) = u_receiver.try_recv() {
                                if task_type != CheckTaskType::U {
                                    prp_sender.send(CheckTask {id, task_type, source_file }).await.unwrap();
                                    break;
                                };
                                if !try_handle_unknown(
                                    &http,
                                    &u_status_regex,
                                    id,
                                    &mut next_unknown_attempt,
                                    source_file,
                                    &rps_limiter,
                                )
                                .await
                                {
                                    retry = Some(CheckTask {id, task_type, source_file });
                                    break;
                                }
                            }
                        }
                    }
                }
                info!("{}: {} bases checked", id, bases_count);
            }
            CheckTaskType::U => {
                throttle_if_necessary(
                    &http,
                    &rps_limiter,
                    &resources_regex,
                    &mut bases_before_next_cpu_check,
                    true,
                )
                .await;
                if !try_handle_unknown(
                    &http,
                    &u_status_regex,
                    id,
                    &mut next_unknown_attempt,
                    source_file,
                    &rps_limiter,
                )
                .await
                {
                    if retry.is_none() {
                        retry = Some(CheckTask {id, task_type, source_file});
                    } else if prp_sender.try_send(CheckTask {id, task_type, source_file}).is_err() {
                        warn!("Dropping task for ID {} because the retry buffer and queue are both full", id);
                    }
                }
            }
        }
    }
}

async fn try_handle_unknown<
    S: DirectStateStore,
    T: ReasonablyRealtime,
    U: RateLimitingMiddleware<T::Instant, NegativeOutcome = NotUntil<T::Instant>>,
>(
    http: &Client,
    u_status_regex: &Regex,
    id: u128,
    next_attempt: &mut Instant,
    source_file: Option<u64>,
    rate_limiter: &Arc<RateLimiter<NotKeyed, S, T, U>>,
) -> bool {
    let remaining_wait = next_attempt.saturating_duration_since(Instant::now());
    if remaining_wait > UNKNOWN_STATUS_CHECK_MAX_BLOCKING_WAIT {
        let remaining_secs = remaining_wait.as_secs();
        warn!("Waiting {remaining_secs} seconds to start an unknown-status task");
        false
    } else {
        if remaining_wait > Duration::ZERO {
        sleep(remaining_wait).await;
            }
        let url = format!("https://factordb.com/index.php?id={id}&prp=Assign+to+worker");
        rate_limiter.until_ready().await;
        let result = retrying_get_and_decode(&http, &url).await;
        if let Some(status) = u_status_regex.captures_iter(&result).next() {
            match status.get(1) {
                None => {
                    error!("Failed to decode status for {id}: {result}");
                    false
                }
                Some(matched_status) => match matched_status.as_str() {
                    "Assigned" => {
                        info!("Assigned PRP check for unknown-status number with ID {id} from dump file {source_file:?}");
                        true
                    }
                    "Please wait" => {
                        warn!("Got 'please wait' for unknown-status number with ID {id}");
                        *next_attempt = Instant::now() + UNKNOWN_STATUS_CHECK_BACKOFF;
                        false
                    }
                    _ => {
                        warn!("Unknown-status number with ID {id} from dump file {source_file:?} is already being checked");
                        true
                    }
                },
            }
        } else {
            error!("Failed to decode status for {id} from result: {result}");
            false
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
    sleep_first: bool,
) {
    *bases_before_next_cpu_check -= 1;
    if *bases_before_next_cpu_check != 0 {
        return;
    }
    if sleep_first {
        sleep(Duration::from_secs(10)).await; // allow for delay in CPU accounting
    }
    rps_limiter.until_ready().await;
    let resources_text = retrying_get_and_decode(&http, "https://factordb.com/res.php").await;
    let cpu_check_time = Instant::now();
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
    let cpu_tenths_spent_after =
        cpu_seconds.parse::<u64>().unwrap() * 10 + cpu_tenths_within_second.parse::<u64>().unwrap();
    CPU_TENTHS_SPENT_LAST_CHECK.store(cpu_tenths_spent_after, Ordering::Release);
    let seconds_to_reset = minutes_to_reset.parse::<u64>().unwrap() * 60
        + seconds_within_minute_to_reset.parse::<u64>().unwrap();
    let mut tenths_remaining = MAX_CPU_BUDGET_TENTHS.saturating_sub(cpu_tenths_spent_after);
    if !NO_RESERVE.load(Ordering::Acquire) {
        tenths_remaining = tenths_remaining.saturating_sub(seconds_to_reset * seconds_to_reset / 36000);
    }
    let mut bases_remaining =
        (tenths_remaining / 10).min(MAX_BASES_BETWEEN_RESOURCE_CHECKS);
    if bases_remaining <= MIN_BASES_BETWEEN_RESOURCE_CHECKS / 2 {
        warn!(
            "CPU time spent this cycle: {:.1} seconds. Throttling {} seconds due to high server CPU usage",
            cpu_tenths_spent_after as f64 * 0.1,
            seconds_to_reset
        );
        let cpu_reset_time = cpu_check_time.add(Duration::from_secs(seconds_to_reset));
        if EXIT_TIME.get().is_some_and(|exit_time| *exit_time <= cpu_reset_time) {
            warn!("Throttling won't end before program exit; exiting now");
            exit(0);
        }
        sleep_until(cpu_reset_time).await;
        *bases_before_next_cpu_check = MAX_BASES_BETWEEN_RESOURCE_CHECKS;
        CPU_TENTHS_SPENT_LAST_CHECK.store(0, Ordering::Release);
    } else {
        if bases_remaining < MIN_BASES_BETWEEN_RESOURCE_CHECKS {
            bases_remaining = MIN_BASES_BETWEEN_RESOURCE_CHECKS;
        }
        info!(
            "CPU time spent this cycle: {:.1} seconds; reset in {} seconds; checking again after {} bases",
            cpu_tenths_spent_after as f64 * 0.1,
            seconds_to_reset,
            bases_remaining
        );
        *bases_before_next_cpu_check = bases_remaining;
    }
}

#[tokio::main]
async fn main() {
    let is_no_reserve = std::env::var("NO_RESERVE").is_ok();
    NO_RESERVE.store(is_no_reserve, Ordering::Release);
    let mut config_builder = FilterConfigBuilder::default()
        .capacity(2500)
        .false_positive_rate(0.001);
    if std::env::var("CI").is_ok() {
        config_builder = config_builder
            .level_duration(Duration::from_hours(24))
            .max_levels(7);
        EXIT_TIME.set(Instant::now().add(Duration::from_mins(330))).unwrap();
    }
    let config = config_builder.build().unwrap();
    let mut prp_filter = InMemoryFilter::new(config.clone()).unwrap();
    let mut u_filter = InMemoryFilter::new(config).unwrap();
    let rps_limiter = RateLimiter::direct(Quota::per_hour(6100u32.try_into().unwrap()));
    // Guardian rate-limiters start out with their full burst capacity and recharge starting
    // immediately, but this would lead to twice the allowed number of requests in our first hour,
    // so we make it start nearly empty instead.
    rps_limiter
        .until_n_ready(6050u32.try_into().unwrap())
        .await
        .unwrap();
    let id_regex = Regex::new("index\\.php\\?id=([0-9]+)").unwrap();
    let http = Client::builder()
        .pool_max_idle_per_host(2)
        .timeout(NETWORK_TIMEOUT)
        .build()
        .unwrap();
    let (prp_sender, prp_receiver) = channel(PRP_TASK_BUFFER_SIZE);
    let (u_sender, u_receiver) = channel(U_TASK_BUFFER_SIZE);
    let rps_limiter = Arc::new(rps_limiter);
    task::spawn(do_checks(
        prp_sender.clone(),
        prp_receiver,
        u_receiver,
        http.clone(),
        rps_limiter.clone(),
    ));
    simple_log::console("info").unwrap();
    let prp_search_url_base = format!(
        "https://factordb.com/listtype.php?t=1&mindig={MIN_DIGITS_IN_PRP}&perpage={PRP_RESULTS_PER_PAGE}&start="
    );
    let u_search_url_base = format!(
        "https://factordb.com/listtype.php?t=2&mindig={MIN_DIGITS_IN_U}&perpage={U_RESULTS_PER_PAGE}&start="
    );
    let mut prp_start = 0;
    let mut u_start = 1;
    let mut dump_file_index = 0;
    let mut dump_file = File::open_buffered("/dev/null").unwrap();
    let mut dump_file_lines_read = 0;
    let mut line = String::new();
    let mut bases_since_restart = 0;
    let mut results_since_restart: usize = 0;
    let mut next_min_restart = Instant::now() + MIN_TIME_PER_RESTART;
    // Use PRP queue so that the first unknown numbers will start immediately
    queue_unknown_from_dump_file(
        &prp_sender,
        &mut dump_file_index,
        &mut dump_file,
        &mut dump_file_lines_read,
        &mut line,
        None,
    )
    .await;
    let mut u_permits = prp_sender.reserve_many(U_RESULTS_PER_PAGE).await.unwrap();
    queue_unknowns_from_search(
        &id_regex,
        &http,
        &rps_limiter,
        &u_search_url_base,
        &mut u_start,
        &mut u_permits,
        &mut u_filter
    )
    .await;
    let mut restart_prp = false;
    let mut restart_u = false;
    info!("{dump_file_lines_read} lines read from dump file {dump_file_index}");
    loop {
        select! {
            _ = prp_sender.reserve_many(if restart_prp {
                MIN_CAPACITY_AT_PRP_RESTART
            } else {
                PRP_RESULTS_PER_PAGE
            }) => {
                if restart_prp {
                    restart_prp = false;
                    prp_start = 0;
                    results_since_restart = 0;
                    bases_since_restart = 0;
                    next_min_restart = Instant::now() + MIN_TIME_PER_RESTART;
                }
                let prp_search_url = format!("{prp_search_url_base}{prp_start}");
                rps_limiter.until_ready().await;
                let results_text = retrying_get_and_decode(&http, &prp_search_url).await;
                for prp_id in id_regex
                    .captures_iter(&results_text)
                    .map(|result| result[1].to_owned().into_boxed_str())
                    .unique()
                {
                    let Ok(prp_id) = prp_id.parse::<u128>() else {
                        error!("Invalid PRP ID found: {}", prp_id);
                        continue;
                    };
                    let prp_id_bytes = prp_id.to_ne_bytes();
                    if prp_filter.query(&prp_id_bytes).unwrap() {
                        warn!("Skipping duplicate PRP ID: {}", prp_id);
                        continue;
                    }
                    prp_filter.insert(&prp_id_bytes).unwrap();
                    let prp_task = CheckTask {
                        id: prp_id,
                        task_type: CheckTaskType::Prp,
                        source_file: None
                    };
                    results_since_restart += 1;
                    let unsent_prp_task = match prp_sender.try_send(prp_task) {
                        Ok(()) => None,
                        Err(TrySendError::Full(prp_id)) => Some(prp_id),
                        Err(TrySendError::Closed(_)) => unreachable!()
                    };
                    queue_unknowns(&id_regex, &http, &u_sender, &rps_limiter, &u_search_url_base, &mut u_start, &mut dump_file_index, &mut dump_file, &mut dump_file_lines_read, &mut line, &mut u_filter).await;
                    if let Some(prp_task) = unsent_prp_task {
                        prp_sender.send(prp_task).await.unwrap();
                    }
                    info!("Queued check of probable prime with ID {prp_id} from search");
                }
                prp_start += PRP_RESULTS_PER_PAGE;
                if prp_start > MAX_START || u_start > MAX_START {
                    info!("Restarting PRP search: reached maximum starting index");
                    restart_prp = true;
                } else if results_since_restart >= PRP_TASK_BUFFER_SIZE
                    && Instant::now() >= next_min_restart
                {
                    info!(
                        "Restarting PRP search: triggered {bases_since_restart} bases in {results_since_restart} search results"
                    );
                    restart_prp = true;
                }
            }
            _ = u_sender.reserve_many(if restart_u {
                MIN_CAPACITY_AT_U_RESTART
            } else {
                U_RESULTS_PER_PAGE
            }) => {
                if restart_u {
                    u_start = 1;
                    restart_u = false;
                }
                queue_unknowns(&id_regex, &http, &u_sender, &rps_limiter, &u_search_url_base, &mut u_start, &mut dump_file_index, &mut dump_file, &mut dump_file_lines_read, &mut line, &mut u_filter).await;
                if u_start > MAX_START {
                    info!("Restarting U search: searched {u_start} unknowns");
                    restart_u = true;
                }
            }
        }
    }
}

async fn queue_unknowns(
    id_regex: &Regex,
    http: &Client,
    u_sender: &Sender<CheckTask>,
    rps_limiter: &Arc<RateLimiter<NotKeyed, InMemoryState, DefaultClock>>,
    u_search_url_base: &String,
    mut u_start: &mut usize,
    mut dump_file_index: &mut u64,
    mut dump_file: &mut BufReader<File>,
    mut dump_file_lines_read: &mut i32,
    mut line: &mut String,
    u_filter: &mut InMemoryFilter
) {
    while let Ok(mut u_permits) = u_sender.try_reserve_many(U_RESULTS_PER_PAGE) {
        let mut cpu_tenths_spent = CPU_TENTHS_SPENT_LAST_CHECK.load(Ordering::Acquire);
        let use_search = if cpu_tenths_spent >= CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES {
            info!(
                "Using only dump file, because {:.1} seconds CPU time has already been spent this cycle",
                cpu_tenths_spent as f64 * 0.1
            );
            false
        } else {
            cpu_tenths_spent = CPU_TENTHS_SPENT_LAST_CHECK.load(Ordering::Acquire);
            if cpu_tenths_spent >= CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES {
                info!(
                    "Using only dump file, because {:.1} seconds CPU time has already been spent this cycle",
                    cpu_tenths_spent as f64 * 0.1
                );
                false
            } else {
                info!(
                    "Using search to find unknown-status numbers, because only {:.1} seconds CPU time has been spent this cycle",
                    cpu_tenths_spent as f64 * 0.1
                );
                true
            }
        };
        if use_search {
            queue_unknowns_from_search(
                &id_regex,
                &http,
                &rps_limiter,
                &u_search_url_base,
                &mut u_start,
                &mut u_permits,
                u_filter
            )
            .await;
        } else {
            for _ in 0..U_RESULTS_PER_PAGE {
                queue_unknown_from_dump_file(
                    &u_sender,
                    &mut dump_file_index,
                    &mut dump_file,
                    &mut dump_file_lines_read,
                    &mut line,
                    u_permits.next(),
                )
                .await;
            }
        }
        info!("{dump_file_lines_read} lines read from dump file {dump_file_index}");
    }
}

async fn queue_unknowns_from_search(
    id_regex: &Regex,
    http: &Client,
    rps_limiter: &Arc<RateLimiter<NotKeyed, InMemoryState, DefaultClock>>,
    u_search_url_base: &String,
    u_start: &mut usize,
    u_permits: &mut PermitIterator<'_, CheckTask>,
    u_filter: &mut InMemoryFilter
) {
    let u_search_url = format!("{u_search_url_base}{u_start}");
    rps_limiter.until_ready().await;
    let results_text = retrying_get_and_decode(&http, &u_search_url).await;
    for u_id in id_regex
        .captures_iter(&results_text)
        .map(|result| result[1].to_owned().into_boxed_str())
        .unique()
    {
        let Ok(u_id) = u_id.parse::<u128>() else {
            error!("Invalid unknown-status number ID in search results: {}", u_id);
            continue;
        };
        let u_id_bytes = u_id.to_ne_bytes();
        if u_filter.query(&u_id_bytes).unwrap() {
            warn!("Skipping duplicate U ID: {}", u_id);
            continue;
        }
        u_filter.insert(&u_id_bytes).unwrap();
        u_permits.next().unwrap().send(CheckTask {
            id: u_id,
            task_type: CheckTaskType::U,
            source_file: None,
        });
        info!("Queued check of unknown-status number with ID {u_id} from search");
    }
    *u_start += U_RESULTS_PER_PAGE;
}

async fn queue_unknown_from_dump_file(
    u_sender: &Sender<CheckTask>,
    dump_file_index: &mut u64,
    dump_file: &mut BufReader<File>,
    dump_file_lines_read: &mut i32,
    mut line: &mut String,
    permit: Option<Permit<'_, CheckTask>>,
) {
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
        while next_file {
            *dump_file_index += 1;
            info!("Opening new dump file: {dump_file_index}");
            match File::open_buffered(format!("U{dump_file_index:0>6}.csv")) {
                Ok(new_file) => {
                    *dump_file = new_file;
                    next_file = false;
                    *dump_file_lines_read = 0;
                }
                Err(e) => warn!("Skipping dump file {dump_file_index}: {e}"),
            }
        }
    }
    let id = line.split(",").next().unwrap();
    if id.is_empty() {
        warn!("Skipping an empty line in dump file {}", *dump_file_index);
    } else {
        let task = CheckTask {
            id: id.parse().expect(&format!("Invalid ID {} in dump file {}", id, *dump_file_index)),
            source_file: Some(*dump_file_index),
            task_type: CheckTaskType::U,
        };
        if let Some(permit) = permit {
            permit.send(task);
        } else {
            u_sender.send(task).await.unwrap();
        }
        info!("Queued check of unknown-status number with ID {id} from dump file");
    }
    *dump_file_lines_read += 1;
}
