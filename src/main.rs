#![allow(stable_features)]
#![feature(duration_constructors_lite)]
#![feature(file_buffered)]

mod algebraic;
mod channel;
mod net;

use crate::UnknownPrpCheckResult::{
    Assigned, IneligibleForPrpCheck, OtherRetryableFailure, PleaseWait,
};
use crate::algebraic::{Factor, FactorFinder};
use channel::PushbackReceiver;
use compact_str::{CompactString, ToCompactString};
use const_format::formatcp;
use expiring_bloom_rs::{ExpiringBloomFilter, FilterConfigBuilder, InMemoryFilter};
use futures_util::StreamExt;
use futures_util::future::join_all;
use itertools::Itertools;
use log::{error, info, warn};
use net::ThrottlingHttpClient;
use primitive_types::U256;
use rand::seq::SliceRandom;
use rand::{Rng, rng};
use regex::Regex;
use serde::{Deserialize, Serialize};
use serde_json::{Value, from_str};
use std::collections::{HashSet, VecDeque};
use std::fs::File;
use std::io::Write;
use std::num::{NonZeroU32, NonZeroUsize};
use std::ops::Add;
use std::process::exit;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::sync::atomic::{AtomicBool, AtomicU64};
use tokio::signal::unix::{SignalKind, signal};
use tokio::sync::mpsc::{PermitIterator, Sender, channel};
use tokio::sync::{Mutex, OnceCell};
use tokio::time::{Duration, Instant, sleep, timeout};
use tokio::{select, task};
use tokio_stream::iter;
use urlencoding::encode;

const MAX_START: usize = 100_000;
const RETRY_DELAY: Duration = Duration::from_secs(1);
const SEARCH_RETRY_DELAY: Duration = Duration::from_secs(10);
const UNPARSEABLE_RESPONSE_RETRY_DELAY: Duration = Duration::from_secs(10);
const NETWORK_TIMEOUT: Duration = Duration::from_secs(15);
const PRP_RESULTS_PER_PAGE: usize = 32;
const MIN_DIGITS_IN_PRP: usize = 300;
const U_RESULTS_PER_PAGE: usize = 1;
const PRP_TASK_BUFFER_SIZE: usize = 4 * PRP_RESULTS_PER_PAGE;
const U_TASK_BUFFER_SIZE: usize = 256;
const C_RESULTS_PER_PAGE: usize = 5000;
const C_TASK_BUFFER_SIZE: usize = 256;
const C_MIN_DIGITS: usize = 91;
const C_MAX_DIGITS: usize = 300;
const PRP_SEARCH_URL_BASE: &str = formatcp!(
    "https://factordb.com/listtype.php?t=1&mindig={MIN_DIGITS_IN_PRP}&perpage={PRP_RESULTS_PER_PAGE}&start="
);
const U_SEARCH_URL_BASE: &str =
    formatcp!("https://factordb.com/listtype.php?t=2&perpage={U_RESULTS_PER_PAGE}&start=");
const C_SEARCH_URL_BASE: &str =
    formatcp!("https://factordb.com/listtype.php?t=3&perpage={C_RESULTS_PER_PAGE}&start=");
const SUBMIT_U_FACTOR_MAX_ATTEMPTS: usize = 10;
static EXIT_TIME: OnceCell<Instant> = OnceCell::const_new();
static COMPOSITES_OUT: OnceCell<Mutex<File>> = OnceCell::const_new();
static FAILED_U_SUBMISSIONS_OUT: OnceCell<Mutex<File>> = OnceCell::const_new();
static HAVE_DISPATCHED_TO_YAFU: AtomicBool = AtomicBool::new(false);

enum UnknownPrpCheckResult {
    Assigned,
    PleaseWait,
    OtherRetryableFailure,
    IneligibleForPrpCheck,
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
#[repr(u8)]
enum CheckTaskType {
    Prp,
    U,
}
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
struct CheckTask {
    id: u128,
    task_type: CheckTaskType,
}

#[derive(Debug, Deserialize, Serialize)]
struct NumberStatusApiResponse {
    id: Value,
    status: CompactString,
    factors: Box<[(CompactString, u128)]>,
}

#[derive(Serialize)]
struct FactorSubmission<'a> {
    id: u128,
    factor: &'a str,
}

fn count_ones(u256: U256) -> u32 {
    u256.0.iter().copied().map(u64::count_ones).sum()
}

async fn composites_while_waiting(
    end: Instant,
    http: &ThrottlingHttpClient,
    c_receiver: &mut PushbackReceiver<u128>,
    c_filter: &mut InMemoryFilter,
) {
    let Some(mut remaining) = end.checked_duration_since(Instant::now()) else {
        return;
    };
    info!("Processing composites for {remaining:?} while other work is waiting");
    loop {
        let Ok(id) = timeout(remaining, c_receiver.recv()).await else {
            warn!("Timed out waiting for a composite number to check");
            return;
        };
        if c_filter.query(&id.to_ne_bytes()).unwrap() {
            info!("{id}: Skipping duplicate C");
            continue;
        }
        let check_succeeded = check_composite(http, id).await;
        if let Some(out) = COMPOSITES_OUT.get() {
            if !HAVE_DISPATCHED_TO_YAFU.load(Acquire) {
                c_filter.insert(&id.to_ne_bytes()).unwrap();
                if dispatch_composite(http, id, out).await {
                    HAVE_DISPATCHED_TO_YAFU.store(true, Release);
                }
            } else if !check_succeeded {
                if c_receiver.try_send(id) {
                    info!("{id}: Requeued C");
                } else {
                    c_filter.insert(&id.to_ne_bytes()).unwrap();
                    let http = http.clone();
                    task::spawn(async move { dispatch_composite(&http, id, out).await });
                }
            }
        } else if !check_succeeded {
            if c_receiver.try_send(id) {
                info!("{id}: Requeued C");
            } else {
                error!("{id}: Dropping C");
            }
        }
        match end.checked_duration_since(Instant::now()) {
            None => {
                info!("Out of time while processing composites");
                return;
            }
            Some(new_remaining) => remaining = new_remaining,
        };
    }
}

#[derive(Debug)]
enum NumberSpecifier<'a> {
    Id(u128),
    Expression(&'a str),
}

async fn known_factors_as_digits(
    http: &ThrottlingHttpClient,
    id: NumberSpecifier<'_>,
) -> Result<Box<[Factor]>, ()> {
    let url = match id {
        NumberSpecifier::Id(id) => format!("https://factordb.com/api?id={id}"),
        NumberSpecifier::Expression(ref expr) => {
            format!("https://factordb.com/api?query={}", encode(expr))
        }
    };
    let api_response = http.retrying_get_and_decode(&url, RETRY_DELAY).await;
    drop(url);
    match from_str::<NumberStatusApiResponse>(&api_response) {
        Err(e) => {
            error!("{id:?}: Failed to decode API response: {e}: {api_response}");
            Err(())
        }
        Ok(api_response) => {
            let NumberStatusApiResponse {
                status, factors, ..
            } = api_response;
            info!("{id:?}: Fetched status of {status}");
            if status == "FF" {
                Ok(Box::new([]))
            } else {
                let factors: Vec<_> = factors
                    .into_iter()
                    .map(|(factor, _exponent)| Factor::from(factor))
                    .collect();
                if factors.len() > 1 {
                    info!(
                        "{id:?}: Composite with known factors: {}",
                        factors.iter().join(",")
                    );
                }
                Ok(factors.into_boxed_slice())
            }
        }
    }
}

async fn dispatch_composite(http: &ThrottlingHttpClient, id: u128, out: &Mutex<File>) -> bool {
    match known_factors_as_digits(http, NumberSpecifier::Id(id)).await {
        Err(()) => false,
        Ok(factors) => {
            iter(factors.clone())
                .for_each(async |factor| {
                    if let Factor::String(s) = factor {
                        let _ = check_last_digit(http, id, &s).await;
                    }
                })
                .await;
            let mut out = out.lock().await;
            let mut result = factors
                .into_iter()
                .map(|factor| out.write_fmt(format_args!("{factor}\n")))
                .flat_map(Result::err)
                .take(1);
            if let Some(error) = result.next() {
                error!("{id}: Failed to write factor to FIFO: {error}");
                false
            } else {
                info!("{id}: Dispatched C to yafu");
                true
            }
        }
    }
}

async fn check_composite(http: &ThrottlingHttpClient, id: u128) -> bool {
    if http
        .try_get_and_decode(&format!("https://factordb.com/sequences.php?check={id}"))
        .await
        .is_some()
    {
        info!("Checked composite with ID {id}");
        true
    } else {
        false
    }
}

async fn get_prp_remaining_bases(
    id: u128,
    http: &ThrottlingHttpClient,
    bases_regex: &Regex,
    nm1_regex: &Regex,
    np1_regex: &Regex,
    c_receiver: &mut PushbackReceiver<u128>,
    c_filter: &mut InMemoryFilter,
) -> Result<U256, ()> {
    let mut bases_left = U256::MAX - 3;
    let bases_text = http
        .retrying_get_and_decode(
            &format!("https://factordb.com/frame_prime.php?id={id}"),
            RETRY_DELAY,
        )
        .await;
    if bases_text.contains("Proven") {
        info!("{id}: No longer PRP");
    }
    if let Some(captures) = nm1_regex.captures(&bases_text) {
        let nm1_id = captures[1].parse::<u128>().unwrap();
        if known_factors_as_digits(http, NumberSpecifier::Id(nm1_id)).await == Ok(Box::new([])) {
            info!("{id}: N-1 (ID {nm1_id}) is fully factored!");
            let _ = http
                .retrying_get_and_decode(
                    &format!("https://factordb.com/index.php?open=Prime&nm1=Proof&id={id}"),
                    RETRY_DELAY,
                )
                .await;
            return Ok(U256::from(0));
        }
    } else {
        error!("{id}: N-1 ID not found: {bases_text}");
    }
    if let Some(captures) = np1_regex.captures(&bases_text) {
        let np1_id = captures[1].parse::<u128>().unwrap();
        if known_factors_as_digits(http, NumberSpecifier::Id(np1_id)).await == Ok(Box::new([])) {
            info!("{id}: N+1 (ID {np1_id}) is fully factored!");
            let _ = http
                .retrying_get_and_decode(
                    &format!("https://factordb.com/index.php?open=Prime&np1=Proof&id={id}"),
                    RETRY_DELAY,
                )
                .await;
            return Ok(U256::from(0));
        }
    } else {
        error!("{id}: N+1 ID not found: {bases_text}");
    }
    let status_text = http
        .retrying_get_and_decode(
            &format!("https://factordb.com/index.php?open=Prime&ct=Proof&id={id}"),
            RETRY_DELAY,
        )
        .await;
    if !status_text.contains("&lt;") {
        error!("{id}: Failed to decode status for PRP: {status_text}");
        composites_while_waiting(
            Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY,
            http,
            c_receiver,
            c_filter,
        )
        .await;
        return Err(());
    }
    if status_text.contains(" is prime") || !status_text.contains("PRP") {
        info!("{id}: No longer PRP");
        return Ok(U256::from(0));
    }
    if let Some(bases) = bases_regex.captures(&bases_text) {
        for base in bases[1].split(", ") {
            let Ok(base) = base.parse::<u8>() else {
                error!("Invalid PRP-check base: {:?}", base);
                continue;
            };
            bases_left &= !(U256::from(1) << base);
        }
        info!("{id}: {} bases left to check", count_ones(bases_left));
    } else {
        info!("{id}: no bases checked yet");
    }
    if bases_left == U256::from(0) {
        info!("{id}: all bases already checked");
    }
    Ok(bases_left)
}

const MAX_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 127;

const MIN_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 4;

const MAX_CPU_BUDGET_TENTHS: u64 = 6000;
const UNKNOWN_STATUS_CHECK_BACKOFF: Duration = Duration::from_secs(15);
static CPU_TENTHS_SPENT_LAST_CHECK: AtomicU64 = AtomicU64::new(MAX_CPU_BUDGET_TENTHS);
static NO_RESERVE: AtomicBool = AtomicBool::new(false);
const CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES: u64 = 5000;

async fn do_checks(
    mut prp_receiver: PushbackReceiver<CheckTask>,
    mut u_receiver: PushbackReceiver<CheckTask>,
    mut c_receiver: PushbackReceiver<u128>,
    mut c_filter: InMemoryFilter,
    http: ThrottlingHttpClient,
) {
    let mut next_unknown_attempt = Instant::now();
    let mut retry = None;
    let cert_regex = Regex::new("(Verified|Processing)").unwrap();
    let many_digits_regex =
        Regex::new("&lt;([2-9]|[0-9]+[0-9])[0-9][0-9][0-9][0-9][0-9]&gt;").unwrap();
    let bases_regex = Regex::new("Bases checked[^\n]*\n[^\n]*([0-9, ]+)").unwrap();
    let nm1_regex = Regex::new("id=([0-9]+)\">N-1<").unwrap();
    let np1_regex = Regex::new("id=([0-9]+)\">N-1<").unwrap();
    let mut bases_before_next_cpu_check = 1;
    let u_status_regex = Regex::new("(Assigned|already|Please wait|>CF?<|>P<|>PRP<|>FF<)").unwrap();
    throttle_if_necessary(
        &http,
        &mut c_receiver,
        &mut bases_before_next_cpu_check,
        false,
        &mut c_filter,
    )
    .await;
    loop {
        let prp_task = prp_receiver.try_recv();
        let u_tasks = if next_unknown_attempt <= Instant::now() {
            retry
                .take()
                .into_iter()
                .chain(u_receiver.try_recv().into_iter())
        } else {
            None.into_iter().chain(None.into_iter())
        };
        let mut task_done = false;
        let tasks = prp_task.into_iter().chain(u_tasks);
        for CheckTask { id, task_type } in tasks {
            task_done = true;
            match task_type {
                CheckTaskType::Prp => {
                    let mut stopped_early = false;
                    let Ok(bases_left) = get_prp_remaining_bases(
                        id,
                        &http,
                        &bases_regex,
                        &nm1_regex,
                        &np1_regex,
                        &mut c_receiver,
                        &mut c_filter,
                    )
                    .await
                    else {
                        if prp_receiver.try_send(CheckTask { id, task_type }) {
                            info!("{id}: Requeued PRP");
                        } else {
                            error!("{id}: Dropping PRP");
                        }
                        continue;
                    };
                    if bases_left == U256::from(0) {
                        continue;
                    }
                    let url_base =
                        format!("https://factordb.com/index.php?id={id}&open=prime&basetocheck=");
                    for base in (0..=(u8::MAX as usize)).filter(|i| bases_left.bit(*i)) {
                        let url = format!("{url_base}{base}");
                        let text = http.retrying_get_and_decode(&url, RETRY_DELAY).await;
                        if !text.contains(">number<") {
                            error!("Failed to decode result from {url}: {text}");
                            if prp_receiver.try_send(CheckTask { id, task_type }) {
                                info!("{id}: Requeued PRP");
                            } else {
                                error!("{id}: Dropping PRP");
                            }
                            composites_while_waiting(
                                Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY,
                                &http,
                                &mut c_receiver,
                                &mut c_filter,
                            )
                            .await;
                            break;
                        }
                        throttle_if_necessary(
                            &http,
                            &mut c_receiver,
                            &mut bases_before_next_cpu_check,
                            true,
                            &mut c_filter,
                        )
                        .await;
                        if cert_regex.is_match(&text) {
                            info!("{}: No longer PRP (has certificate)", id);
                            stopped_early = true;
                            break;
                        }
                        if text.contains("set to C") {
                            info!("{}: No longer PRP (ruled out by PRP check)", id);
                            stopped_early = true;
                            break;
                        }
                        if !text.contains("PRP") {
                            info!("{}: No longer PRP (solved by N-1/N+1 or factor)", id);
                            stopped_early = true;
                            break;
                        }
                    }
                    if !stopped_early {
                        info!("{}: all bases now checked", id);
                    }
                }
                CheckTaskType::U => {
                    throttle_if_necessary(
                        &http,
                        &mut c_receiver,
                        &mut bases_before_next_cpu_check,
                        true,
                        &mut c_filter,
                    )
                    .await;
                    match try_handle_unknown(
                        &http,
                        &mut c_receiver,
                        &u_status_regex,
                        &many_digits_regex,
                        id,
                        &mut next_unknown_attempt,
                        &mut c_filter,
                    )
                    .await
                    {
                        Assigned | IneligibleForPrpCheck => {}
                        PleaseWait => {
                            if retry.is_none() {
                                retry = Some(CheckTask { id, task_type });
                                info!("{id}: put U in retry buffer");
                            } else if u_receiver.try_send(CheckTask { id, task_type }) {
                                info!("{id}: Requeued U");
                            } else {
                                error!(
                                    "{id}: Dropping U after 'please wait' because the retry buffer and queue are both full",
                                );
                            }
                        }
                        OtherRetryableFailure => {
                            if u_receiver.try_send(CheckTask { id, task_type }) {
                                info!("{id}: Requeued U");
                            } else if retry.is_none() {
                                retry = Some(CheckTask { id, task_type });
                                info!("{id}: put U in retry buffer");
                            } else {
                                error!(
                                    "{id}: Dropping U after error because the retry buffer and queue are both full",
                                );
                            }
                        }
                    }
                }
            }
        }
        if !task_done {
            composites_while_waiting(
                Instant::now() + Duration::from_secs(1),
                &http,
                &mut c_receiver,
                &mut c_filter,
            )
            .await;
            continue;
        }
    }
}

async fn try_handle_unknown(
    http: &ThrottlingHttpClient,
    c_receiver: &mut PushbackReceiver<u128>,
    u_status_regex: &Regex,
    many_digits_regex: &Regex,
    id: u128,
    next_attempt: &mut Instant,
    c_filter: &mut InMemoryFilter,
) -> UnknownPrpCheckResult {
    composites_while_waiting(*next_attempt, http, c_receiver, c_filter).await;
    let url = format!("https://factordb.com/index.php?id={id}&prp=Assign+to+worker");
    let result = http.retrying_get_and_decode(&url, RETRY_DELAY).await;
    if let Some(status) = u_status_regex.captures_iter(&result).next() {
        match status.get(1) {
            None => {
                if many_digits_regex.is_match(&result) {
                    warn!("{id}: U is too large for a PRP check!");
                    IneligibleForPrpCheck
                } else {
                    error!("{id}: Failed to decode status for U: {result}");
                    *next_attempt = Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY;
                    OtherRetryableFailure
                }
            }
            Some(matched_status) => match matched_status.as_str() {
                "Assigned" => {
                    info!("Assigned PRP check for unknown-status number with ID {id}");
                    Assigned
                }
                "Please wait" => {
                    warn!("{id}: Got 'please wait' for U");
                    *next_attempt = Instant::now() + UNKNOWN_STATUS_CHECK_BACKOFF;
                    PleaseWait
                }
                _ => {
                    warn!("{id}: U is already being checked");
                    Assigned
                }
            },
        }
    } else if many_digits_regex.is_match(&result) {
        warn!("{id}: U is too large for a PRP check!");
        IneligibleForPrpCheck
    } else {
        error!("{id}: Failed to decode status for U from result: {result}");
        *next_attempt = Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY;
        PleaseWait
    }
}

async fn throttle_if_necessary(
    http: &ThrottlingHttpClient,
    c_receiver: &mut PushbackReceiver<u128>,
    bases_before_next_cpu_check: &mut u64,
    sleep_first: bool,
    c_filter: &mut InMemoryFilter,
) {
    *bases_before_next_cpu_check -= 1;
    if *bases_before_next_cpu_check != 0 {
        return;
    }
    if sleep_first {
        composites_while_waiting(
            Instant::now() + Duration::from_secs(10),
            http,
            c_receiver,
            c_filter,
        )
        .await; // allow for delay in CPU accounting
    }
    let cpu_check_time = Instant::now();
    // info!("Resources fetched");
    let Some((cpu_tenths_spent_after, seconds_to_reset)) = http
        .try_get_resource_limits(bases_before_next_cpu_check)
        .await
    else {
        error!("Failed to parse resource limits");
        return;
    };
    let mut tenths_remaining = MAX_CPU_BUDGET_TENTHS.saturating_sub(cpu_tenths_spent_after);
    if !NO_RESERVE.load(Acquire) {
        tenths_remaining =
            tenths_remaining.saturating_sub(seconds_to_reset * seconds_to_reset / 18000);
    }
    let mut bases_remaining = (tenths_remaining / 10).min(MAX_BASES_BETWEEN_RESOURCE_CHECKS);
    if bases_remaining <= MIN_BASES_BETWEEN_RESOURCE_CHECKS / 2 {
        warn!(
            "CPU time spent this cycle: {:.1} seconds. Throttling {} seconds due to high server CPU usage",
            cpu_tenths_spent_after as f64 * 0.1,
            seconds_to_reset
        );
        let cpu_reset_time = cpu_check_time.add(Duration::from_secs(seconds_to_reset));
        if EXIT_TIME
            .get()
            .is_some_and(|exit_time| *exit_time <= cpu_reset_time)
        {
            warn!("Throttling won't end before program exit; exiting now");
            exit(0);
        }
        composites_while_waiting(cpu_reset_time, http, c_receiver, c_filter).await;
        *bases_before_next_cpu_check = MAX_BASES_BETWEEN_RESOURCE_CHECKS;
        CPU_TENTHS_SPENT_LAST_CHECK.store(0, Release);
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

async fn queue_composites(
    waiting_c: &mut VecDeque<u128>,
    id_regex: &Regex,
    http: &ThrottlingHttpClient,
    c_sender: &Sender<u128>,
    digits: Option<NonZeroUsize>,
) -> usize {
    let mut c_sent = 0;
    let mut rng = rng();
    let start = if digits.is_some_and(|digits| digits.get() < C_MIN_DIGITS) {
        0
    } else {
        rng.random_range(0..=MAX_START)
    };
    let digits = digits.unwrap_or_else(|| {
        rng.random_range(C_MIN_DIGITS..=C_MAX_DIGITS)
            .try_into()
            .unwrap()
    });
    info!("Retrieving {digits}-digit composites starting from {start}");
    let composites_page = http
        .retrying_get_and_decode(
            &format!("{C_SEARCH_URL_BASE}{start}&mindig={digits}"),
            RETRY_DELAY,
        )
        .await;
    info!("C search results retrieved");
    let c_ids = id_regex
        .captures_iter(&composites_page)
        .map(|capture| capture.get(1).unwrap().as_str().parse::<u128>().ok())
        .unique();
    let mut c_buffered = 0usize;
    for c_id in c_ids {
        let Some(c_id) = c_id else {
            error!("Invalid composite number ID in search results");
            continue;
        };
        if c_sender.try_send(c_id).is_err() {
            waiting_c.push_back(c_id);
            c_buffered += 1;
        } else {
            c_sent += 1;
        }
    }
    if c_buffered > 0 {
        let (a, b) = waiting_c.as_mut_slices();
        a.shuffle(&mut rng);
        b.shuffle(&mut rng);
        info!("Shuffled C buffer");
    } else {
        while let Some(c) = waiting_c.pop_front() {
            if c_sender.try_send(c).is_err() {
                waiting_c.push_front(c);
                break;
            }
            c_sent += 1;
        }
    }
    c_sent
}

#[tokio::main]
async fn main() {
    let is_no_reserve = std::env::var("NO_RESERVE").is_ok();
    NO_RESERVE.store(is_no_reserve, Release);
    let mut c_digits = None;
    let mut u_digits = None;
    let mut prp_start = if let Ok(run_number) = std::env::var("RUN") {
        let run_number = run_number.parse::<usize>().unwrap();
        let mut c_digits_value = C_MAX_DIGITS - (run_number % (C_MAX_DIGITS - C_MIN_DIGITS + 2));
        if c_digits_value == C_MIN_DIGITS - 1 {
            c_digits_value = 1;
        }
        c_digits = Some(c_digits_value.try_into().unwrap());
        let u_digits_value =
            U_MAX_DIGITS - ((run_number * 100) % (U_MAX_DIGITS - U_MIN_DIGITS + 1));
        u_digits = Some(u_digits_value.try_into().unwrap());
        (run_number * 100) % (MAX_START + 1)
    } else {
        rng().random_range(0..=MAX_START)
    };
    let rph_limit: NonZeroU32 = if is_no_reserve { 6400 } else { 6100 }.try_into().unwrap();
    let http = ThrottlingHttpClient::new(rph_limit);
    let id_regex = Regex::new("index\\.php\\?id=([0-9]+)").unwrap();

    let (prp_sender, prp_receiver) = channel(PRP_TASK_BUFFER_SIZE);
    let (u_sender, u_receiver) = channel(U_TASK_BUFFER_SIZE);
    let (c_sender, c_raw_receiver) = channel(C_TASK_BUFFER_SIZE);
    let c_receiver = PushbackReceiver::new(c_raw_receiver, &c_sender);
    let mut config_builder = FilterConfigBuilder::default()
        .capacity(2500)
        .false_positive_rate(0.001)
        .level_duration(Duration::from_hours(24));
    if std::env::var("CI").is_ok() {
        config_builder = config_builder.max_levels(1);
        EXIT_TIME
            .set(Instant::now().add(Duration::from_mins(355)))
            .unwrap();
        COMPOSITES_OUT
            .get_or_init(async || {
                Mutex::new(File::options().append(true).open("composites").unwrap())
            })
            .await;
    } else {
        config_builder = config_builder.max_levels(7);
    }
    let config = config_builder.build().unwrap();
    let c_filter = InMemoryFilter::new(config.clone()).unwrap();
    task::spawn(do_checks(
        PushbackReceiver::new(prp_receiver, &prp_sender),
        PushbackReceiver::new(u_receiver, &u_sender),
        c_receiver,
        c_filter,
        http.clone(),
    ));
    FAILED_U_SUBMISSIONS_OUT
        .get_or_init(async || {
            Mutex::new(
                File::options()
                    .create(true)
                    .append(true)
                    .open("failed-u-submissions.csv")
                    .unwrap(),
            )
        })
        .await;
    let mut prp_filter = InMemoryFilter::new(config.clone()).unwrap();
    let mut u_filter = InMemoryFilter::new(config).unwrap();
    simple_log::console("info").unwrap();
    let mut waiting_c = VecDeque::with_capacity(C_RESULTS_PER_PAGE - 1);
    let algebraic_factors_regex = Regex::new("id=([0-9]+).*?<font[^>]*>([^<]+)</font>").unwrap();
    let factor_finder = FactorFinder::new();
    // Use PRP queue so that the first unknown number will start sooner
    let _ = try_queue_unknowns(
        &algebraic_factors_regex,
        &http,
        u_digits,
        prp_sender.reserve_many(PRP_TASK_BUFFER_SIZE).await.unwrap(),
        &mut u_filter,
        &factor_finder,
    )
    .await;
    queue_composites(&mut waiting_c, &id_regex, &http, &c_sender, c_digits).await;
    let mut sigterm =
        signal(SignalKind::terminate()).expect("Failed to create SIGTERM signal stream");
    loop {
        select! {
            c_permit = c_sender.reserve() => {
                let c = waiting_c.pop_front();
                let mut c_sent = 1usize;
                match c {
                    Some(c) => {
                        c_permit.unwrap().send(c);
                        while let Some(c) = waiting_c.pop_front() {
                            if c_sender.try_send(c).is_err() {
                                waiting_c.push_front(c);
                                break;
                            }
                            c_sent += 1;
                        }
                    }
                    None => {
                        c_sent = queue_composites(&mut waiting_c, &id_regex, &http, &c_sender, c_digits).await;
                    }
                }
                info!("{c_sent} C's sent to channel; {} now in buffer", waiting_c.len());
            }
            prp_permits = prp_sender.reserve_many(PRP_RESULTS_PER_PAGE) => {
                let prp_search_url = format!("{PRP_SEARCH_URL_BASE}{prp_start}");
                let results_text = http.retrying_get_and_decode(&prp_search_url, SEARCH_RETRY_DELAY).await;
                info!("PRP search results retrieved");
                let mut prp_permits = prp_permits.unwrap();
                for prp_id in id_regex
                    .captures_iter(&results_text)
                    .map(|result| result[1].parse::<u128>().ok())
                    .unique()
                {
                    let Some(prp_id) = prp_id else {
                        error!("Invalid PRP ID found");
                        continue;
                    };
                    let prp_id_bytes = prp_id.to_ne_bytes();
                    if prp_filter.query(&prp_id_bytes).unwrap() {
                        warn!("{prp_id}: Skipping duplicate PRP");
                        continue;
                    }
                    prp_filter.insert(&prp_id_bytes).unwrap();
                    let prp_task = CheckTask {
                        id: prp_id,
                        task_type: CheckTaskType::Prp,
                    };
                    prp_permits.next().unwrap().send(prp_task);
                    info!("{prp_id}: Queued PRP from search");
                    if let Ok(u_permits) = u_sender.try_reserve_many(U_RESULTS_PER_PAGE) {
                        queue_unknowns(&algebraic_factors_regex, &http, u_digits, u_permits, &mut u_filter, &factor_finder).await;
                    }
                }
                prp_start += PRP_RESULTS_PER_PAGE;
                if prp_start > MAX_START {
                    info!("Restarting PRP search: reached maximum starting index");
                    prp_start = 0;
                }
            }
            u_permits = u_sender.reserve_many(U_RESULTS_PER_PAGE) => {
                queue_unknowns(&algebraic_factors_regex, &http, u_digits, u_permits.unwrap(), &mut u_filter, &factor_finder).await;
            }
            _ = sigterm.recv() => {
                warn!("Received SIGTERM; exiting");
                exit(0);
            }
        }
    }
}

async fn queue_unknowns(
    algebraic_factors_regex: &Regex,
    http: &ThrottlingHttpClient,
    u_digits: Option<NonZeroUsize>,
    u_permits: PermitIterator<'_, CheckTask>,
    u_filter: &mut InMemoryFilter,
    factor_finder: &FactorFinder,
) {
    if CPU_TENTHS_SPENT_LAST_CHECK.load(Acquire) >= CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES {
        return;
    }
    let mut permits = Some(u_permits);
    while let Some(u_permits) = permits.take() {
        if let Err(u_permits) = try_queue_unknowns(
            algebraic_factors_regex,
            http,
            u_digits,
            u_permits,
            u_filter,
            factor_finder,
        )
        .await
        {
            permits = Some(u_permits);
            sleep(RETRY_DELAY).await; // Can't do composites_while_waiting because we're on main thread, and child thread owns c_receiver
        }
    }
}

const U_MIN_DIGITS: usize = 2001;
const U_MAX_DIGITS: usize = 199_999;

async fn try_queue_unknowns<'a>(
    algebraic_factors_regex: &Regex,
    http: &ThrottlingHttpClient,
    u_digits: Option<NonZeroUsize>,
    mut u_permits: PermitIterator<'a, CheckTask>,
    u_filter: &mut InMemoryFilter,
    factor_finder: &FactorFinder,
) -> Result<(), PermitIterator<'a, CheckTask>> {
    let mut rng = rng();
    let digits = u_digits.unwrap_or_else(|| {
        rng.random_range(U_MIN_DIGITS..=U_MAX_DIGITS)
            .try_into()
            .unwrap()
    });
    let u_start = rng.random_range(0..=MAX_START);
    let u_search_url = format!("{U_SEARCH_URL_BASE}{u_start}&mindig={}", digits.get());
    let Some(results_text) = http.try_get_and_decode(&u_search_url).await else {
        return Err(u_permits);
    };
    info!("U search results retrieved");
    let ids = algebraic_factors_regex
        .captures_iter(&results_text)
        .map(|result| {
            (
                result[1].parse::<u128>().ok(),
                result.get(2).unwrap().range(),
            )
        })
        .unique();
    let mut ids_found = false;
    for (u_id, digits_or_expr_range) in ids {
        let Some(u_id) = u_id else {
            error!("Skipping an invalid ID in U search results");
            continue;
        };
        ids_found = true;
        let u_id_bytes = u_id.to_ne_bytes();
        if u_filter.query(&u_id_bytes).unwrap() {
            warn!("{u_id}: Skipping duplicate U");
            continue;
        }
        let digits_or_expr = &results_text[digits_or_expr_range];
        let mut algebraic = if digits_or_expr.contains("...") {
            info!("{u_id}: U represented as digits: {digits_or_expr}");
            factor_last_digit(digits_or_expr)
                .into_iter()
                .collect::<HashSet<Factor>>()
        } else {
            info!("{u_id}: U represented as expression: {digits_or_expr}");
            if digits_or_expr.contains('/') {
                // Factor finding may give some results that have already been divided out
                join_all(
                    factor_finder
                        .find_factors(digits_or_expr)
                        .into_iter()
                        .map(async |factor| match factor {
                            Factor::Numeric(n) => Box::new([Factor::Numeric(n)]),
                            Factor::String(s) => {
                                if let Ok(factors) =
                                    known_factors_as_digits(http, NumberSpecifier::Expression(&s))
                                        .await
                                    && factors.len() > 1
                                {
                                    factors
                                } else {
                                    Box::new([Factor::String(s)])
                                }
                            }
                        })
                        .collect::<Vec<_>>(),
                )
                .await
                .into_iter()
                .flatten()
                .collect()
            } else {
                factor_finder
                    .find_factors(digits_or_expr)
                    .into_iter()
                    .collect()
            }
        };
        let url = format!("https://factordb.com/frame_moreinfo.php?id={u_id}");
        let result = http.retrying_get_and_decode(&url, RETRY_DELAY).await;
        info!("{u_id}: Checking for listed algebraic factors");
        // Links before the "Is factor of" header are algebraic factors; links after it aren't
        if let Some(listed_algebraic) = result.split("Is factor of").next() {
            let algebraic_factors = algebraic_factors_regex.captures_iter(listed_algebraic);
            for factor in algebraic_factors {
                let factor_id = &factor[1];
                let factor_digits_or_expr = &factor[2];
                if factor_digits_or_expr.contains("...") {
                    // Link text isn't an expression for the factor, so we need to look up its value
                    info!(
                        "{u_id}: Algebraic factor {factor_id} represented as digits with ellipsis: {factor_digits_or_expr}"
                    );
                    if let Ok(factor_id) = factor_id.parse::<u128>() {
                        if let Ok(factors) =
                            known_factors_as_digits(http, NumberSpecifier::Id(factor_id)).await
                        {
                            for factor in factors.into_iter() {
                                if let Factor::String(s) = &factor {
                                    factor_last_digit(s).into_iter().for_each(|factor| {
                                        let _ = algebraic.insert(factor);
                                    });
                                }
                                algebraic.insert(factor);
                            }
                        }
                    } else {
                        error!("{u_id}: Invalid ID for algebraic factor: {factor_id}")
                    }
                } else if factor_digits_or_expr.chars().all(|char| char.is_digit(10)) {
                    info!(
                        "{u_id}: Algebraic factor {factor_id} represented in full as digits: {factor_digits_or_expr}"
                    );
                    algebraic.insert(factor_digits_or_expr.into());
                } else {
                    info!(
                        "{u_id}: Algebraic factor {factor_id} represented as expression: {factor_digits_or_expr}"
                    );
                    algebraic.insert(factor_digits_or_expr.into());
                }
            }
        } else {
            error!("{u_id}: Invalid result when checking for algebraic factors: {result}");
        };
        if !algebraic.is_empty() {
            info!("{u_id}: {} algebraic factors to submit", algebraic.len());
        }
        let mut algebraic_submitted = false;
        for factor in algebraic {
            algebraic_submitted |= report_factor_of_u(http, u_id, &factor).await;
        }
        if algebraic_submitted {
            info!("{u_id}: Skipping PRP check because algebraic factors were found");
        } else {
            info!("{u_id}: No algebraic factors found");
            u_filter.insert(&u_id_bytes).unwrap();
            u_permits.next().unwrap().send(CheckTask {
                id: u_id,
                task_type: CheckTaskType::U,
            });
            info!("{u_id}: Queued U");
        }
    }
    if ids_found {
        Ok(())
    } else {
        error!("Couldn't parse IDs from search result: {results_text}");
        Err(u_permits)
    }
}

fn factor_last_digit(string_with_last_digit: &str) -> Box<[Factor]> {
    match string_with_last_digit.chars().last() {
        Some('0') => Box::new([Factor::Numeric(2), Factor::Numeric(5)]),
        Some('5') => Box::new([Factor::Numeric(5)]),
        Some('2' | '4' | '6' | '8') => Box::new([Factor::Numeric(2)]),
        Some('1' | '3' | '7' | '9') => Box::new([]),
        x => {
            error!("Invalid last digit: {x:?}");
            Box::new([])
        }
    }
}

async fn check_last_digit(
    http: &ThrottlingHttpClient,
    u_id: u128,
    string_with_last_digit: &str,
) -> bool {
    let mut accepted = false;
    let factors = factor_last_digit(string_with_last_digit);
    for factor in factors {
        if report_factor_of_u(http, u_id, &factor).await {
            accepted = true;
        }
    }
    accepted
}

async fn report_factor_of_u(http: &ThrottlingHttpClient, u_id: u128, factor: &Factor) -> bool {
    for _ in 0..SUBMIT_U_FACTOR_MAX_ATTEMPTS {
        match http
            .post("https://factordb.com/reportfactor.php")
            .form(&FactorSubmission {
                id: u_id,
                factor: &factor.to_compact_string(),
            })
            .send()
            .await
        {
            Ok(response) => {
                let response = response.text().await;
                match response {
                    Ok(text) => {
                        info!("{u_id}: reported a factor of {factor}; response: {text}",);
                        if !text.contains("Error") {
                            return text.contains("submitted");
                        }
                    }
                    Err(e) => {
                        error!("{u_id}: Failed to get response: {e}");
                    }
                }
            }
            Err(e) => {
                error!("{u_id}: failed to submit factor {factor}: {e}")
            }
        }
        sleep(RETRY_DELAY).await;
    }
    match FAILED_U_SUBMISSIONS_OUT
        .get()
        .unwrap()
        .lock()
        .await
        .write_fmt(format_args!("{u_id},{factor}\n"))
    {
        Ok(_) => warn!("{u_id}: wrote {factor} to failed submissions file"),
        Err(e) => error!("{u_id}: failed to write {factor} to failed submissions file: {e}"),
    }
    true // factor that we failed to submit may still have been valid
}
