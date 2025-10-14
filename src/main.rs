#![allow(stable_features)]
#![feature(duration_constructors_lite)]
#![feature(file_buffered)]

use compact_str::CompactString;
use const_format::formatcp;
use expiring_bloom_rs::{ExpiringBloomFilter, FilterConfigBuilder, InMemoryFilter};
use governor::clock::DefaultClock;
use governor::state::{InMemoryState, NotKeyed};
use governor::{Quota, RateLimiter};
use itertools::Itertools;
use log::{error, info, warn};
use primitive_types::U256;
use rand::seq::SliceRandom;
use rand::{Rng, rng};
use regex::{Regex, RegexBuilder};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::from_str;
use std::collections::VecDeque;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::num::{NonZeroU32, NonZeroUsize};
use std::ops::Add;
use std::process::exit;
use std::sync::Arc;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::sync::atomic::{AtomicBool, AtomicU64};
use tokio::signal::unix::{SignalKind, signal};
use tokio::sync::mpsc::{OwnedPermit, Permit, PermitIterator, Receiver, Sender, channel};
use tokio::sync::{Mutex, OnceCell};
use tokio::time::{Duration, Instant, sleep, sleep_until, timeout};
use tokio::{select, task};
use crate::UnknownPrpCheckResult::{Assigned, IneligibleForPrpCheck, OtherRetryableFailure, PleaseWait};

const MAX_START: usize = 100_000;
const RETRY_DELAY: Duration = Duration::from_secs(1);
const SEARCH_RETRY_DELAY: Duration = Duration::from_secs(10);
const UNPARSEABLE_RESPONSE_RETRY_DELAY: Duration = Duration::from_secs(10);
const NETWORK_TIMEOUT: Duration = Duration::from_secs(15);
const MIN_TIME_PER_RESTART: Duration = Duration::from_hours(1);
const PRP_RESULTS_PER_PAGE: usize = 32;
const MIN_DIGITS_IN_PRP: u64 = 300;
const U_RESULTS_PER_PAGE: usize = 1;
const CHECK_ID_URL_BASE: &str = "https://factordb.com/index.php?open=Prime&ct=Proof&id=";
const PRP_TASK_BUFFER_SIZE: usize = 4 * PRP_RESULTS_PER_PAGE;
const U_TASK_BUFFER_SIZE: usize = 16;
const C_RESULTS_PER_PAGE: usize = 5000;
const C_TASK_BUFFER_SIZE: usize = 256;
const C_MIN_DIGITS: usize = 91;
const C_MAX_DIGITS: usize = 300;
const MIN_CAPACITY_AT_PRP_RESTART: usize = PRP_TASK_BUFFER_SIZE - PRP_RESULTS_PER_PAGE / 2;
const PRP_SEARCH_URL_BASE: &str = formatcp!(
    "https://factordb.com/listtype.php?t=1&mindig={MIN_DIGITS_IN_PRP}&perpage={PRP_RESULTS_PER_PAGE}&start="
);
const U_SEARCH_URL_BASE: &str = formatcp!(
    "https://factordb.com/listtype.php?t=2&perpage={U_RESULTS_PER_PAGE}&start="
);
const C_SEARCH_URL_BASE: &str =
    formatcp!("https://factordb.com/listtype.php?t=3&perpage={C_RESULTS_PER_PAGE}&start=");
static EXIT_TIME: OnceCell<Instant> = OnceCell::const_new();
static COMPOSITES_OUT: OnceCell<Mutex<File>> = OnceCell::const_new();
static HAVE_DISPATCHED_TO_YAFU: AtomicBool = AtomicBool::new(false);

enum UnknownPrpCheckResult {
    Assigned,
    PleaseWait,
    OtherRetryableFailure,
    IneligibleForPrpCheck
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
    source_file: Option<usize>,
    task_type: CheckTaskType,
}

#[derive(Debug, Deserialize, Serialize)]
struct NumberStatusApiResponse {
    id: u128,
    status: CompactString,
    factors: Box<[(CompactString, u128)]>,
}

struct PushbackReceiver<T> {
    sender: Sender<T>,
    receiver: Receiver<T>,
    permit: Option<OwnedPermit<T>>,
}

impl<T> PushbackReceiver<T> {
    fn new(receiver: Receiver<T>, sender: &Sender<T>) -> Self {
        let sender = sender.clone();
        let permit = sender.clone().try_reserve_owned().ok();
        PushbackReceiver {
            receiver,
            sender,
            permit,
        }
    }

    async fn recv(&mut self) -> T {
        drop(self.permit.take());
        let result = self.receiver.recv().await.unwrap();
        self.permit = self.sender.clone().try_reserve_owned().ok();
        result
    }

    fn try_recv(&mut self) -> Option<T> {
        drop(self.permit.take());
        let result = self.receiver.try_recv().ok()?;
        self.permit = self.sender.clone().try_reserve_owned().ok();
        Some(result)
    }

    fn try_send(&mut self, value: T) -> bool {
        if let Some(permit) = self.permit.take() {
            permit.send(value);
            self.permit = self.sender.clone().try_reserve_owned().ok();
            true
        } else {
            let result = self.sender.try_send(value).is_ok();
            if result {
                self.permit = self.sender.clone().try_reserve_owned().ok();
            }
            result
        }
    }
}

#[derive(Clone)]
struct ThrottlingHttpClient {
    resources_regex: Arc<Regex>,
    http: Client,
    rps_limiter: SimpleRateLimiter,
}

impl ThrottlingHttpClient {
    fn parse_resource_limits(
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
    async fn retrying_get_and_decode(&self, url: &str, retry_delay: Duration) -> Box<str> {
        loop {
            if let Some(value) = self.try_get_and_decode(url).await {
                return value;
            }
            sleep(retry_delay).await;
        }
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
    async fn try_get_and_decode(&self, url: &str) -> Option<Box<str>> {
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

    async fn try_get_resource_limits(
        &self,
        bases_before_next_cpu_check: &mut u64,
    ) -> Option<(u64, u64)> {
        let response = self
            .try_get_and_decode_core("https://factordb.com/res.php")
            .await?;
        self.parse_resource_limits(bases_before_next_cpu_check, &response)
    }
}

type SimpleRateLimiter = Arc<RateLimiter<NotKeyed, InMemoryState, DefaultClock>>;

struct DumpFileState {
    reader: BufReader<File>,
    index: usize,
    lines_read: usize
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
        let check_succeeded = check_composite(http, id).await;
        if let Some(out) = COMPOSITES_OUT.get() {
            if !HAVE_DISPATCHED_TO_YAFU.load(Acquire) {
                c_filter.insert(&id.to_ne_bytes()).unwrap();
                if dispatch_composite(http.clone(), id, out).await {
                    HAVE_DISPATCHED_TO_YAFU.store(true, Release);
                }
            } else if !check_succeeded && !c_filter.query(&id.to_ne_bytes()).unwrap() {
                if c_receiver.try_send(id) {
                    info!("{id}: Requeued C");
                } else {
                    c_filter.insert(&id.to_ne_bytes()).unwrap();
                    tokio::spawn(dispatch_composite(http.clone(), id, out));
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

async fn dispatch_composite(http: ThrottlingHttpClient, id: u128, out: &Mutex<File>) -> bool {
    let api_response = http
        .retrying_get_and_decode(&format!("https://factordb.com/api?id={id}"), RETRY_DELAY)
        .await;
    match from_str::<NumberStatusApiResponse>(&api_response) {
        Err(e) => {
            error!("{id}: Failed to decode API response: {e}: {api_response}");
            false
        }
        Ok(api_response) => {
            let NumberStatusApiResponse {
                status, factors, ..
            } = api_response;
            info!("{id}: Fetched status of {status} (previously C)");
            if status == "FF" {
                false
            } else {
                let mut out = out.lock().await;
                let factors: Vec<_> = factors
                    .into_iter()
                    .map(|(factor, _exponent)| factor)
                    .collect();
                info!("{id}: Composite with factors: {}", factors.iter().join(","));
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
    c_receiver: &mut PushbackReceiver<u128>,
    c_filter: &mut InMemoryFilter
) -> Result<U256, ()> {
    let mut bases_left = U256::MAX - 3;
    let bases_url = format!("{CHECK_ID_URL_BASE}{id}");
    let bases_text = http.retrying_get_and_decode(&bases_url, RETRY_DELAY).await;
    if !bases_text.contains("&lt;") {
        error!("{id}: Failed to decode status for PRP: {bases_text}");
        composites_while_waiting(
            Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY,
            http,
            c_receiver,
            c_filter
        )
        .await;
        return Err(());
    }
    if bases_text.contains(" is prime") || !bases_text.contains("PRP") {
        info!("{id}: No longer PRP (solved by N-1/N+1 or factor before queueing)");
        return Ok(U256::from(0));
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
    Ok(bases_left)
}

const MAX_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 127;

const MIN_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 4;

const MAX_CPU_BUDGET_TENTHS: u64 = 6000;
const UNKNOWN_STATUS_CHECK_BACKOFF: Duration = Duration::from_secs(15);
static CPU_TENTHS_SPENT_LAST_CHECK: AtomicU64 = AtomicU64::new(MAX_CPU_BUDGET_TENTHS);
static NO_RESERVE: AtomicBool = AtomicBool::new(false);
const CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES: u64 = 4000;

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
    let bases_regex = Regex::new("Bases checked[^\n]*\n[^\n]*(?:([0-9]+),? )+").unwrap();
    let mut bases_before_next_cpu_check = 1;
    let u_status_regex = Regex::new("(Assigned|already|Please wait|>CF?<|>P<|>PRP<|>FF<)").unwrap();
    throttle_if_necessary(
        &http,
        &mut c_receiver,
        &mut bases_before_next_cpu_check,
        false,
        &mut c_filter
    ).await;
    loop {
        let prp_task = prp_receiver.try_recv();
        let u_tasks = if next_unknown_attempt <= Instant::now() {
            retry.take().into_iter().chain(u_receiver.try_recv().into_iter())
        } else {
            None.into_iter().chain(None.into_iter())
        };
        let mut task_done = false;
        let tasks = prp_task.into_iter().chain(u_tasks);
        for CheckTask {
            id,
            task_type,
            source_file,
        } in tasks {
            task_done = true;
            match task_type {
                CheckTaskType::Prp => {
                    let mut stopped_early = false;
                    let Ok(bases_left) =
                        get_prp_remaining_bases(id, &http, &bases_regex, &mut c_receiver, &mut c_filter).await
                    else {
                        if prp_receiver.try_send(CheckTask {
                            id,
                            task_type,
                            source_file,
                        }) {
                            info!("{id}: Requeued PRP");
                        } else {
                            error!("{id}: Dropping PRP");
                        }
                        continue;
                    };
                    if bases_left == U256::from(0) {
                        continue;
                    }
                    let bases_count = count_ones(bases_left);
                    info!("{}: {} bases to check", id, bases_count);
                    let url_base =
                        format!("https://factordb.com/index.php?id={id}&open=prime&basetocheck=");
                    for base in (0..=(u8::MAX as usize)).filter(|i| bases_left.bit(*i)) {
                        let url = format!("{url_base}{base}");
                        let text = http.retrying_get_and_decode(&url, RETRY_DELAY).await;
                        if !text.contains(">number<") {
                            error!("Failed to decode result from {url}: {text}");
                            if prp_receiver.try_send(CheckTask {
                                id,
                                task_type,
                                source_file,
                            }) {
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
                            &mut c_filter
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
                        info!("{}: {} bases checked", id, bases_count);
                    }
                }
                CheckTaskType::U => {
                    throttle_if_necessary(
                        &http,
                        &mut c_receiver,
                        &mut bases_before_next_cpu_check,
                        true,
                        &mut c_filter
                    )
                        .await;
                    match try_handle_unknown(
                        &http,
                        &mut c_receiver,
                        &u_status_regex,
                        &many_digits_regex,
                        id,
                        &mut next_unknown_attempt,
                        source_file,
                        &mut c_filter,
                    ).await
                    {
                        Assigned | IneligibleForPrpCheck => {},
                        PleaseWait => {
                            if retry.is_none() {
                                retry = Some(CheckTask {
                                    id,
                                    task_type,
                                    source_file,
                                });
                                info!("{id}: put U in retry buffer");
                            } else if u_receiver.try_send(CheckTask {
                                    id,
                                    task_type,
                                    source_file,
                                }) {
                                info!("{id}: Requeued U");
                            } else if retry.is_none() {
                                retry = Some(CheckTask {
                                    id,
                                    task_type,
                                    source_file,
                                });
                                info!("{id}: put U in retry buffer");
                            } else {
                                error!(
                                    "Dropping unknown check with ID {} because the retry buffer and queue are both full",
                                    id
                                );
                            }
                        },
                        OtherRetryableFailure => {
                            if source_file.is_some() {
                                error!(
                                    "Dropping unknown check with ID {} because it came from a dump file",
                                    id
                                );
                            } else if retry.is_none() {
                                retry = Some(CheckTask {
                                    id,
                                    task_type,
                                    source_file,
                                });
                                info!("{id}: put U in retry buffer");
                            } else if u_receiver.try_send(CheckTask {
                                id,
                                task_type,
                                source_file,
                            }) {
                                info!("{id}: Requeued U");
                            } else {
                                error!(
                                    "Dropping unknown check with ID {} because the retry buffer and queue are both full",
                                    id
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
                &mut c_filter
            ).await;
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
    source_file: Option<usize>,
    c_filter: &mut InMemoryFilter
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
                    info!(
                        "Assigned PRP check for unknown-status number with ID {id} from dump file {source_file:?}"
                    );
                    Assigned
                }
                "Please wait" => {
                    warn!("Got 'please wait' for unknown-status number with ID {id}");
                    *next_attempt = Instant::now() + UNKNOWN_STATUS_CHECK_BACKOFF;
                    PleaseWait
                }
                _ => {
                    warn!(
                        "Unknown-status number with ID {id} from dump file {source_file:?} is already being checked"
                    );
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
        composites_while_waiting(Instant::now() + Duration::from_secs(10), http, c_receiver, c_filter).await; // allow for delay in CPU accounting
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
    digits: Option<NonZeroUsize>
) -> usize {
    let mut c_sent = 0;
    let mut rng = rng();
    let digits = digits.unwrap_or_else(|| rng.random_range(C_MIN_DIGITS..=C_MAX_DIGITS).try_into().unwrap());
    let start = rng.random_range(0..=100_000);
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
    let c_digits = std::env::var("RUN").ok()
        .map(|run_number_str| run_number_str.parse::<usize>().unwrap())
        .map(|run_number| NonZeroUsize::try_from(C_MIN_DIGITS + (run_number % (C_MAX_DIGITS - C_MIN_DIGITS - 1))).unwrap());
    let rph_limit: NonZeroU32 = if is_no_reserve { 6400 } else { 6100 }.try_into().unwrap();
    let rps_limiter = RateLimiter::direct(Quota::per_hour(rph_limit));
    let id_regex = Regex::new("index\\.php\\?id=([0-9]+)").unwrap();
    let id_and_last_digit_regex = Regex::new("index\\.php\\?id=([0-9]+).*(\\.\\.[0-9][024568])?").unwrap();
    let resources_regex =
        RegexBuilder::new("([0-9]+)\\.([0-9]) seconds.*([0-6][0-9]):([0-6][0-9])")
            .multi_line(true)
            .dot_matches_new_line(true)
            .build()
            .unwrap();
    let http = Client::builder()
        .pool_max_idle_per_host(2)
        .timeout(NETWORK_TIMEOUT)
        .build()
        .unwrap();

    // Guardian rate-limiters start out with their full burst capacity and recharge starting
    // immediately, but this would lead to twice the allowed number of requests in our first hour,
    // so we make it start nearly empty instead.
    rps_limiter
        .until_n_ready(6050u32.try_into().unwrap())
        .await
        .unwrap();

    let rps_limiter = Arc::new(rps_limiter);
    let http = ThrottlingHttpClient {
        resources_regex: resources_regex.into(),
        http,
        rps_limiter,
    };
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
                Mutex::new(
                    File::options()
                        .append(true)
                        .open("composites")
                        .unwrap(),
                )
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
    let mut prp_filter = InMemoryFilter::new(config.clone()).unwrap();
    let mut u_filter = InMemoryFilter::new(config).unwrap();
    simple_log::console("info").unwrap();
    let mut prp_start = 0;
    let mut dump_file_state = DumpFileState {
        reader: File::open_buffered("/dev/null").unwrap(),
        lines_read: 0,
        index: 0
    };
    let mut line = String::new();
    let mut bases_since_restart = 0;
    let mut results_since_restart: usize = 0;
    let mut next_min_restart = Instant::now() + MIN_TIME_PER_RESTART;
    let mut waiting_c = VecDeque::with_capacity(C_RESULTS_PER_PAGE - 1);

    // Use PRP queue so that the first unknown number will start sooner
    queue_unknowns(
        &id_and_last_digit_regex,
        &http,
        prp_sender.reserve_many(PRP_TASK_BUFFER_SIZE).await.unwrap(),
        &mut dump_file_state,
        &mut line,
        &mut u_filter
    ).await;
    queue_composites(&mut waiting_c, &id_regex, &http, &c_sender, c_digits).await;
    let mut restart_prp = false;
    info!("{} lines read from dump file {}", dump_file_state.lines_read, dump_file_state.index);
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
                info!("{c_sent} composites sent to channel; {} now in buffer", waiting_c.len());
            }
            prp_permits = prp_sender.reserve_many(if restart_prp {
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
                    prp_permits.next().unwrap().send(prp_task);
                    info!("Queued check of probable prime with ID {prp_id} from search");
                    if let Ok(u_permits) = u_sender.try_reserve_many(U_RESULTS_PER_PAGE) {
                        queue_unknowns(&id_and_last_digit_regex, &http, u_permits, &mut dump_file_state, &mut line, &mut u_filter).await;
                    }
                }
                prp_start += PRP_RESULTS_PER_PAGE;
                if prp_start > MAX_START {
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
            u_permits = u_sender.reserve_many(U_RESULTS_PER_PAGE) => {
                queue_unknowns(&id_and_last_digit_regex, &http, u_permits.unwrap(), &mut dump_file_state, &mut line, &mut u_filter).await;
            }
            _ = sigterm.recv() => {
                warn!("Received SIGTERM; exiting");
                exit(0);
            }
        }
    }
}

async fn queue_unknowns(
    id_and_last_digit_regex: &Regex,
    http: &ThrottlingHttpClient,
    u_permits: PermitIterator<'_, CheckTask>,
    dump_file_state: &mut DumpFileState,
    line: &mut String,
    u_filter: &mut InMemoryFilter,
) {
    let mut cpu_tenths_spent = CPU_TENTHS_SPENT_LAST_CHECK.load(Acquire);
    let use_search = if cpu_tenths_spent >= CPU_TENTHS_TO_THROTTLE_UNKNOWN_SEARCHES {
        info!(
            "Using only dump file, because {:.1} seconds CPU time has already been spent this cycle",
            cpu_tenths_spent as f64 * 0.1
        );
        false
    } else {
        cpu_tenths_spent = CPU_TENTHS_SPENT_LAST_CHECK.load(Acquire);
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
    let mut permits = Some(u_permits);
    if use_search
        && let Err(u_permits) =
            queue_unknowns_from_search(id_and_last_digit_regex, http, permits.take().unwrap(), u_filter)
                .await
    {
        permits = Some(u_permits);
    }
    if let Some(mut u_permits) = permits.take() {
        for _ in 0..U_RESULTS_PER_PAGE {
            queue_unknown_from_dump_file(
                u_permits.next().unwrap(),
                dump_file_state,
                line,
            );
        }
    }
    info!("{} lines read from dump file {}", dump_file_state.lines_read, dump_file_state.index);
}

async fn queue_unknowns_from_search<'a>(
    id_and_last_digit_regex: &Regex,
    http: &ThrottlingHttpClient,
    mut u_permits: PermitIterator<'a, CheckTask>,
    u_filter: &mut InMemoryFilter,
) -> Result<(), PermitIterator<'a, CheckTask>> {
    let mut rng = rng();
    let u_digits = rng.random_range(2001..=200_000);
    let u_start = rng.random_range(0..=100_000);
    let u_search_url = format!("{U_SEARCH_URL_BASE}{u_start}&mindig={u_digits}");
    let Some(results_text) = http.try_get_and_decode(&u_search_url).await else {
        return Err(u_permits);
    };
    info!("U search results retrieved");
    let ids = id_and_last_digit_regex
        .captures_iter(&results_text)
        .map(|result| (result[1].parse::<u128>().ok(), result.get(2).map(|m| m.as_str())))
        .unique();
    let mut ids_found = false;
    for (u_id, last_digit) in ids {
        let Some(u_id) = u_id else {
            error!("Skipping an invalid ID in U search results");
            continue;
        };
        ids_found = true;
        if let Some(last_digit) = last_digit {
            let mut even = false;
            let mut divides5 = false;
            match last_digit.chars().last() {
                Some('0') => {
                    even = true;
                    divides5 = true;
                }
                Some('5') => {
                    divides5 = true;
                }
                Some('2' | '4' | '6' | '8') => {
                    even = true;
                }
                x => {
                    error!("{u_id}: Invalid last digit: {x:?}");
                }
            }
            if even {
                match http.http.post("https://factordb.com/reportfactor.php")
                    .body(format!("id={u_id}&factor=2"))
                    .send().await {
                    Ok(response) => info!("{u_id}: reported a factor of 2; response: {:?}", response.text().await),
                    Err(e) => error!("{u_id}: this U has a factor of 2 that we failed to report: {e}"),
                }
            }
            if divides5 {
                match http.http.post("https://factordb.com/reportfactor.php")
                    .body(format!("id={u_id}&factor=5"))
                    .send().await {
                    Ok(response) => info!("{u_id}: reported a factor of 5; response: {:?}", response.text().await),
                    Err(e) => error!("{u_id}: this U has a factor of 5 that we failed to report: {e}"),
                }
            }
        } else {
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
    }
    if ids_found {
        Ok(())
    } else {
        error!("Couldn't parse IDs from search result: {results_text}");
        Err(u_permits)
    }
}

fn queue_unknown_from_dump_file(
    u_permit: Permit<'_, CheckTask>,
    dump_file_state: &mut DumpFileState,
    line: &mut String,
) {
    while line.is_empty() {
        let mut next_file = false;
        match dump_file_state.reader.read_line(line) {
            Ok(0) => next_file = true,
            Ok(_) => {}
            Err(e) => {
                error!("Reading unknown-status dump file: {e}");
                next_file = true;
            }
        }
        while next_file {
            dump_file_state.index += 1;
            info!("Opening new dump file: {}", dump_file_state.index);
            match File::open_buffered(format!("U{:0>6}.csv", dump_file_state.index)) {
                Ok(new_file) => {
                    dump_file_state.reader = new_file;
                    next_file = false;
                    dump_file_state.lines_read = 0;
                }
                Err(e) => warn!("Skipping dump file {}: {e}", dump_file_state.index),
            }
        }
    }
    if line.is_empty() {
        return;
    }
    let id = line.split(",").next().unwrap();
    if id.is_empty() {
        warn!("Skipping an empty line in dump file {}", dump_file_state.index);
    } else {
        let task = CheckTask {
            id: id
                .parse()
                .unwrap_or_else(|_| panic!("Invalid ID {} in dump file {}", id, dump_file_state.index)),
            source_file: Some(dump_file_state.index),
            task_type: CheckTaskType::U,
        };
        u_permit.send(task);
        info!("Queued check of unknown-status number with ID {id} from dump file");
    }
    line.clear();
    dump_file_state.lines_read += 1;
}
