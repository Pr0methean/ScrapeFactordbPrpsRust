#![allow(stable_features)]
#![feature(duration_constructors_lite)]
#![feature(file_buffered)]
#![feature(const_destruct)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]

mod algebraic;
mod channel;
mod net;

use crate::NumberSpecifier::{Expression, Id};
use crate::SubfactorHandling::{AlreadySubmitted, ByExpression, ById, Irreducible};
use crate::UnknownPrpCheckResult::{
    Assigned, IneligibleForPrpCheck, OtherRetryableFailure, PleaseWait,
};
use crate::algebraic::Factor::Numeric;
use crate::algebraic::{Factor, FactorFinder};
use channel::PushbackReceiver;
use compact_str::{CompactString, ToCompactString};
use const_format::formatcp;
use expiring_bloom_rs::{ExpiringBloomFilter, FilterConfigBuilder, InMemoryFilter};
use itertools::Itertools;
use log::{error, info, warn};
use net::ThrottlingHttpClient;
use primitive_types::U256;
use rand::seq::SliceRandom;
use rand::{Rng, rng};
use regex::Regex;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::btree_map::Entry::Vacant;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::num::{NonZeroU32, NonZeroU128};
use std::ops::Add;
use std::process::exit;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::sync::atomic::{AtomicBool, AtomicU64};
use tokio::signal::unix::{SignalKind, signal};
use tokio::sync::mpsc::error::TrySendError::Full;
use tokio::sync::mpsc::{OwnedPermit, PermitIterator, Sender, channel};
use tokio::sync::{oneshot, Mutex, OnceCell};
use tokio::time::{Duration, Instant, sleep, sleep_until, timeout};
use tokio::{select, task};
use tokio::sync::oneshot::Receiver;

const MAX_START: u128 = 100_000;
const RETRY_DELAY: Duration = Duration::from_secs(3);
const SEARCH_RETRY_DELAY: Duration = Duration::from_secs(10);
const UNPARSEABLE_RESPONSE_RETRY_DELAY: Duration = Duration::from_secs(10);
const PRP_RESULTS_PER_PAGE: u128 = 32;
const MIN_DIGITS_IN_PRP: usize = 300;
const U_RESULTS_PER_PAGE: usize = 1;
const PRP_TASK_BUFFER_SIZE: usize = (4 * PRP_RESULTS_PER_PAGE) as usize;
const U_TASK_BUFFER_SIZE: usize = 256;
const C_RESULTS_PER_PAGE: usize = 5000;
const C_TASK_BUFFER_SIZE: usize = 256;
const C_MIN_DIGITS: u128 = 91;
const C_MAX_DIGITS: u128 = 300;

const U_MIN_DIGITS: u128 = 2001;
const U_MAX_DIGITS: u128 = 199_999;
const PRP_SEARCH_URL_BASE: &str = formatcp!(
    "https://factordb.com/listtype.php?t=1&mindig={MIN_DIGITS_IN_PRP}&perpage={PRP_RESULTS_PER_PAGE}&start="
);
const U_SEARCH_URL_BASE: &str =
    formatcp!("https://factordb.com/listtype.php?t=2&perpage={U_RESULTS_PER_PAGE}&start=");
const SUBMIT_FACTOR_MAX_ATTEMPTS: usize = 5;
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

#[derive(Clone, Eq)]
struct CompositeCheckTask {
    id: u128,
    digits_or_expr: CompactString,
}

impl PartialEq<Self> for CompositeCheckTask {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Hash for CompositeCheckTask {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state)
    }
}

#[derive(Debug, Deserialize, Serialize)]
struct NumberStatusApiResponse {
    id: Value,
    status: CompactString,
    factors: Box<[(CompactString, u128)]>,
}

#[derive(Serialize)]
struct FactorSubmission<'a> {
    id: Option<u128>,
    number: Option<&'a str>,
    factor: &'a str,
}

async fn composites_while_waiting(
    end: Instant,
    http: &ThrottlingHttpClient,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    c_filter: &mut InMemoryFilter,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
) {
    let Some(mut remaining) = end.checked_duration_since(Instant::now()) else {
        return;
    };
    info!("Processing composites for {remaining:?} while other work is waiting");
    loop {
        let Ok((CompositeCheckTask { id, digits_or_expr }, return_permit)) =
            timeout(remaining, c_receiver.recv()).await
        else {
            warn!("Timed out waiting for a composite number to check");
            return;
        };
        check_composite(
            http,
            c_filter,
            factor_finder,
            id_and_expr_regex,
            id,
            digits_or_expr,
            return_permit,
        )
        .await;
        match end.checked_duration_since(Instant::now()) {
            None => {
                info!("Out of time while processing composites");
                return;
            }
            Some(new_remaining) => remaining = new_remaining,
        };
    }
}

async fn check_composite(
    http: &ThrottlingHttpClient,
    c_filter: &mut InMemoryFilter,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
    id: u128,
    digits_or_expr: CompactString,
    return_permit: OwnedPermit<CompositeCheckTask>,
) -> bool {
    if c_filter.query(&id.to_ne_bytes()).unwrap() {
        info!("{id}: Skipping duplicate C");
        return true;
    }
    let mut checks_triggered = if http
        .try_get_and_decode(&format!("https://factordb.com/sequences.php?check={id}"))
        .await
        .is_some()
    {
        info!("{id}: Checked C");
        true
    } else {
        false
    };
    // First, convert the composite to digits
    match factor_finder
        .known_factors_as_digits(http, Id(id), false)
        .await
    {
        Err(()) => {
            return_permit.send(CompositeCheckTask { id, digits_or_expr });
            info!("{id}: Requeued C");
            false
        }
        Ok(factors) => {
            if factors.is_empty() {
                warn!("{id}: Already fully factored");
                return true;
            }
            let subfactors_may_have_algebraic = factors.len() > 1;
            let mut factors: BTreeMap<Factor, SubfactorHandling> = factors
                .into_iter()
                .map(|factor| (factor, AlreadySubmitted))
                .collect();
            // Only look up listed algebraic factors once, since we only have the one ID and not the
            // IDs of any known factors
            get_known_algebraic_factors(http, id, factor_finder, id_and_expr_regex, &mut factors)
                .await;
            let mut factors_found = false;
            for (factor, subfactor_handling) in factors.iter() {
                if let Factor::String(s) = factor {
                    // If we have a subfactor's ID, we can submit factors to it instead of to the
                    // bigger factor, and it may have algebraic factors that we can find separately.
                    let (id_for_submission, may_have_separate_listed_algebraic) =
                        if let ById(factor_id) = subfactor_handling {
                            if http
                                .try_get_and_decode(&format!(
                                    "https://factordb.com/sequences.php?check={factor_id}"
                                ))
                                .await
                                .is_some()
                            {
                                info!("{id}: Checked C subfactor {factor_id}");
                                checks_triggered = true;
                            }
                            (*factor_id, subfactors_may_have_algebraic)
                        } else {
                            (id, false)
                        };
                    factors_found |= find_and_submit_factors(
                        http,
                        id_for_submission,
                        s,
                        factor_finder,
                        id_and_expr_regex,
                        true,
                        !may_have_separate_listed_algebraic,
                    )
                    .await
                        || (*subfactor_handling != AlreadySubmitted
                            && report_factor_of_u(http, id, factor).await);
                }
            }
            if factors_found {
                info!("{id}: Skipping further C checks because factors were found");
                return true;
            }
            let mut dispatched = false;
            if let Some(out) = COMPOSITES_OUT.get() {
                let mut out = out.lock().await;
                let mut result = factors
                    .into_keys()
                    .map(|factor| out.write_fmt(format_args!("{factor}\n")))
                    .flat_map(Result::err)
                    .take(1);
                if let Some(error) = result.next() {
                    error!("{id}: Failed to write factor to FIFO: {error}");
                } else {
                    info!("{id}: Dispatched C to yafu");
                    HAVE_DISPATCHED_TO_YAFU.store(true, Release);
                    dispatched = true;
                }
            }
            if !dispatched && !checks_triggered {
                return_permit.send(CompositeCheckTask { id, digits_or_expr });
                info!("{id}: Requeued C");
                false
            } else {
                true
            }
        }
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
enum NumberSpecifier<'a> {
    Id(u128),
    Expression(&'a str),
}

async fn get_prp_remaining_bases(
    id: u128,
    http: &ThrottlingHttpClient,
    bases_regex: &Regex,
    nm1_regex: &Regex,
    np1_regex: &Regex,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    c_filter: &mut InMemoryFilter,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
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
    let mut nm1_id_if_available = None;
    let mut nm1_divides_3 = false;
    if let Some(captures) = nm1_regex.captures(&bases_text) {
        let nm1_id = captures[1].parse::<u128>().unwrap();
        nm1_id_if_available = Some(nm1_id);
        let nm1_result = factor_finder
            .known_factors_as_digits(http, Id(nm1_id), false)
            .await;
        if let Ok(nm1_factors) = nm1_result {
            match nm1_factors.len() {
                0 => {
                    info!("{id}: N-1 (ID {nm1_id}) is fully factored!");
                    let _ = http
                        .retrying_get_and_decode(
                            &format!("https://factordb.com/index.php?open=Prime&nm1=Proof&id={id}"),
                            RETRY_DELAY,
                        )
                        .await;
                    return Ok(U256::from(0));
                }
                1 => {
                    // no known factors, but N-1 must be even if N is PRP
                    report_factor_of_u(http, nm1_id, &Numeric(2)).await;
                    nm1_divides_3 = report_factor_of_u(http, nm1_id, &Numeric(3)).await;
                }
                _ => {
                    nm1_divides_3 = nm1_factors[0] == Numeric(3)
                        || nm1_factors[1] == Numeric(3)
                        || report_factor_of_u(http, nm1_id, &Numeric(3)).await;
                }
            }
        }
    } else {
        error!("{id}: N-1 ID not found: {bases_text}");
    }
    if let Some(captures) = np1_regex.captures(&bases_text) {
        let np1_id = captures[1].parse::<u128>().unwrap();
        let np1_result = factor_finder
            .known_factors_as_digits(http, Id(np1_id), false)
            .await;
        if let Ok(np1_factors) = np1_result {
            match np1_factors.len() {
                0 => {
                    info!("{id}: N+1 (ID {np1_id}) is fully factored!");
                    let _ = http
                        .retrying_get_and_decode(
                            &format!("https://factordb.com/index.php?open=Prime&np1=Proof&id={id}"),
                            RETRY_DELAY,
                        )
                        .await;
                    return Ok(U256::from(0));
                }
                1 => {
                    // no known factors, but N+1 must be even if N is PRP
                    report_factor_of_u(http, np1_id, &Numeric(2)).await;
                    if !nm1_divides_3 {
                        // N wouldn't be PRP if it divided 3, so if N-1 doesn't divide 3 then N+1 does
                        if !report_factor_of_u(http, np1_id, &Numeric(3)).await
                            && let Some(nm1_id) = nm1_id_if_available
                        {
                            error!(
                                "{id}: N is PRP, but 3 rejected as factor of both N-1 (ID {nm1_id}) and N+1 (ID {np1_id})"
                            );
                        }
                    }
                }
                _ => {
                    if !nm1_divides_3
                        && np1_factors[0] != Numeric(3)
                        && np1_factors[1] != Numeric(3)
                    {
                        // N wouldn't be PRP if it divided 3, so if N-1 doesn't divide 3 then N+1 does
                        if !report_factor_of_u(http, np1_id, &Numeric(3)).await
                            && let Some(nm1_id) = nm1_id_if_available
                        {
                            error!(
                                "{id}: N is PRP, but 3 rejected as factor of both N-1 (ID {nm1_id}) and N+1 (ID {np1_id})"
                            );
                        }
                    }
                }
            }
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
            factor_finder,
            id_and_expr_regex,
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
        info!(
            "{id}: {} bases left to check",
            bases_left
                .0
                .iter()
                .copied()
                .map(u64::count_ones)
                .sum::<u32>()
        );
    } else {
        info!("{id}: no bases checked yet");
    }
    if bases_left == U256::from(0) {
        info!("{id}: all bases already checked");
    }
    Ok(bases_left)
}

const MAX_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 127;

const MIN_BASES_BETWEEN_RESOURCE_CHECKS: u64 = 16;

const MAX_CPU_BUDGET_TENTHS: u64 = 6000;
const UNKNOWN_STATUS_CHECK_BACKOFF: Duration = Duration::from_mins(5);
static CPU_TENTHS_SPENT_LAST_CHECK: AtomicU64 = AtomicU64::new(MAX_CPU_BUDGET_TENTHS);
static NO_RESERVE: AtomicBool = AtomicBool::new(false);

#[inline]
async fn do_checks(
    mut prp_receiver: PushbackReceiver<CheckTask>,
    mut u_receiver: PushbackReceiver<CheckTask>,
    mut c_receiver: PushbackReceiver<CompositeCheckTask>,
    mut c_filter: InMemoryFilter,
    http: ThrottlingHttpClient,
    factor_finder: FactorFinder,
    id_and_expr_regex: Regex,
    mut termination_receiver: Receiver<()>
) {
    let mut next_unknown_attempt = Instant::now();
    let mut retry = None;
    let cert_regex = Regex::new("(Verified|Processing)").unwrap();
    let many_digits_regex =
        Regex::new("&lt;([2-9]|[0-9]+[0-9])[0-9][0-9][0-9][0-9][0-9]&gt;").unwrap();
    let bases_regex = Regex::new("Bases checked[^\n]*\n[^\n]*([0-9, ]+)").unwrap();
    let nm1_regex = Regex::new("id=([0-9]+)\">N-1<").unwrap();
    let np1_regex = Regex::new("id=([0-9]+)\">N\\+1<").unwrap();
    let mut bases_before_next_cpu_check = 1;
    let u_status_regex = Regex::new("(Assigned|already|Please wait|>CF?<|>P<|>PRP<|>FF<)").unwrap();
    throttle_if_necessary(
        &http,
        &mut c_receiver,
        &mut bases_before_next_cpu_check,
        false,
        &mut c_filter,
        &factor_finder,
        &id_and_expr_regex,
    )
    .await;
    let mut successful_select_end = Instant::now();
    loop {
        let task = select! {
            biased;
            _ = &mut termination_receiver => {
                warn!("Received termination signal; exiting");
                return;
            }
            // Nested select should prevent bias between U, PRP and C, but keep bias in favor of SIGTERM
            _ = sleep(Duration::ZERO) => {
                select! {
                    // Duplicate termination recv so we won't stall inside the inner select
                    _ = &mut termination_receiver => {
                        warn!("Received termination signal; exiting");
                        return;
                    }
                    _ = sleep_until(next_unknown_attempt) => {
                        if retry.is_some() {
                            info!("Ready to retry a U after {:?}", Instant::now() - successful_select_end);
                            retry.take()
                        } else {
                            u_receiver.try_recv().inspect(|_| {
                                info!("Ready to check a U after {:?}", Instant::now() - successful_select_end);
                            })
                        }
                    }
                    prp_task = prp_receiver.recv() => {
                        info!("Ready to check a PRP after {:?}", Instant::now() - successful_select_end);
                        Some(prp_task)
                    }
                    c_task = c_receiver.recv() => {
                        info!("Ready to check a C after {:?}", Instant::now() - successful_select_end);
                        let (CompositeCheckTask {id, digits_or_expr}, return_permit) = c_task;
                        check_composite(&http, &mut c_filter, &factor_finder, &id_and_expr_regex, id, digits_or_expr, return_permit).await;
                        successful_select_end = Instant::now();
                        None
                    }
                }
            }
        };
        if let Some((CheckTask { id, task_type }, task_return_permit)) = task {
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
                        &factor_finder,
                        &id_and_expr_regex,
                    )
                    .await
                    else {
                        task_return_permit.send(CheckTask { id, task_type });
                        info!("{id}: Requeued PRP");
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
                            task_return_permit.send(CheckTask { id, task_type });
                            info!("{id}: Requeued PRP");
                            composites_while_waiting(
                                Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY,
                                &http,
                                &mut c_receiver,
                                &mut c_filter,
                                &factor_finder,
                                &id_and_expr_regex,
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
                            &factor_finder,
                            &id_and_expr_regex,
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
                        &factor_finder,
                        &id_and_expr_regex,
                    )
                    .await;
                    match try_handle_unknown(
                        &http,
                        &u_status_regex,
                        &many_digits_regex,
                        id,
                        &mut next_unknown_attempt,
                    )
                    .await
                    {
                        Assigned | IneligibleForPrpCheck => {}
                        PleaseWait => {
                            if retry.is_none() {
                                retry = Some((CheckTask { id, task_type }, task_return_permit));
                                info!("{id}: put U in retry buffer");
                            } else {
                                task_return_permit.send(CheckTask { id, task_type });
                                info!("{id}: Requeued U");
                            }
                        }
                        OtherRetryableFailure => {
                            task_return_permit.send(CheckTask { id, task_type });
                            info!("{id}: Requeued U");
                        }
                    }
                }
            }
            successful_select_end = Instant::now();
        }
    }
}

#[inline]
async fn try_handle_unknown(
    http: &ThrottlingHttpClient,
    u_status_regex: &Regex,
    many_digits_regex: &Regex,
    id: u128,
    next_attempt: &mut Instant,
) -> UnknownPrpCheckResult {
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
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    bases_before_next_cpu_check: &mut u64,
    sleep_first: bool,
    c_filter: &mut InMemoryFilter,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
) -> bool {
    *bases_before_next_cpu_check -= 1;
    if *bases_before_next_cpu_check != 0 {
        return false;
    }
    if sleep_first {
        composites_while_waiting(
            Instant::now() + Duration::from_secs(10),
            http,
            c_receiver,
            c_filter,
            factor_finder,
            id_and_expr_regex,
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
        return false;
    };
    let mut tenths_remaining = MAX_CPU_BUDGET_TENTHS.saturating_sub(cpu_tenths_spent_after);
    if !NO_RESERVE.load(Acquire) {
        tenths_remaining =
            tenths_remaining.saturating_sub(seconds_to_reset * seconds_to_reset / 18000);
    }
    let mut bases_remaining = (tenths_remaining / 10).min(MAX_BASES_BETWEEN_RESOURCE_CHECKS);
    if bases_remaining <= MIN_BASES_BETWEEN_RESOURCE_CHECKS {
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
        composites_while_waiting(
            cpu_reset_time,
            http,
            c_receiver,
            c_filter,
            factor_finder,
            id_and_expr_regex,
        )
        .await;
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
    true
}

async fn queue_composites(
    waiting_c: &mut VecDeque<CompositeCheckTask>,
    id_and_expr_regex: &Regex,
    http: &ThrottlingHttpClient,
    c_sender: &Sender<CompositeCheckTask>,
    digits: Option<NonZeroU128>,
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
    let mut results_per_page = C_RESULTS_PER_PAGE;
    let mut composites_page = None;
    while composites_page.is_none() && results_per_page > 0 {
        composites_page = http.try_get_and_decode(
            &format!("https://factordb.com/listtype.php?t=3&perpage={results_per_page}&start={start}&mindig={digits}")
        ).await;
        if composites_page.is_none() {
            results_per_page >>= 1;
            sleep(RETRY_DELAY).await;
        }
    }
    let Some(composites_page) = composites_page else {
        return 0;
    };
    info!("C search results retrieved");
    let c_ids = id_and_expr_regex
        .captures_iter(&composites_page)
        .flat_map(|capture| {
            Some(CompositeCheckTask {
                id: capture[1].parse::<u128>().ok()?,
                digits_or_expr: capture[2].into(),
            })
        })
        .unique();
    let mut c_buffered = 0usize;
    for check_task in c_ids {
        if let Err(Full(check_task)) = c_sender.try_send(check_task) {
            waiting_c.push_back(check_task);
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
        while let Some(check_task) = waiting_c.pop_front() {
            if let Err(Full(check_task)) = c_sender.try_send(check_task) {
                waiting_c.push_front(check_task);
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
    let mut c_digits = std::env::var("C_DIGITS")
        .ok()
        .and_then(|s| s.parse::<NonZeroU128>().ok());
    let mut u_digits = std::env::var("U_DIGITS")
        .ok()
        .and_then(|s| s.parse::<NonZeroU128>().ok());
    let mut prp_start = std::env::var("PRP_START")
        .ok()
        .and_then(|s| s.parse::<u128>().ok());
    simple_log::console("info").unwrap();
    if let Ok(run_number) = std::env::var("RUN") {
        let run_number = run_number.parse::<u128>().unwrap();
        if c_digits.is_none() {
            let mut c_digits_value =
                C_MAX_DIGITS - ((run_number * 19) % (C_MAX_DIGITS - C_MIN_DIGITS + 2));
            if c_digits_value == C_MIN_DIGITS - 1 {
                c_digits_value = 1;
            }
            c_digits = Some(c_digits_value.try_into().unwrap());
        }
        if u_digits.is_none() {
            let u_digits_value =
                U_MAX_DIGITS - ((run_number * 19793) % (U_MAX_DIGITS - U_MIN_DIGITS + 1));
            u_digits = Some(u_digits_value.try_into().unwrap());
        }
        if prp_start.is_none() {
            prp_start = Some((run_number * 9973) % (MAX_START + 1));
        }
        info!("Run number is {run_number}");
    }
    match c_digits {
        Some(c_digits) => info!("C's will be {c_digits} digits"),
        None => info!("C's will be random sizes"),
    }
    match u_digits {
        Some(u_digits) => info!("U's will be {u_digits} digits"),
        None => info!("U's will be random sizes"),
    }
    let mut prp_start = prp_start.unwrap_or_else(|| rng().random_range(0..=MAX_START));
    info!("PRP initial start is {prp_start}");
    let rph_limit: NonZeroU32 = if is_no_reserve { 6400 } else { 6100 }.try_into().unwrap();
    let mut max_concurrent_requests = 2usize;
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
        max_concurrent_requests = 3;
    } else {
        config_builder = config_builder.max_levels(7);
    }
    let config = config_builder.build().unwrap();
    let c_filter = InMemoryFilter::new(config.clone()).unwrap();
    let id_and_expr_regex =
        Regex::new("index\\.php\\?id=([0-9]+).*?<font[^>]*>([^<]+)</font>").unwrap();
    let factor_finder = FactorFinder::new();
    let http = ThrottlingHttpClient::new(rph_limit, max_concurrent_requests);
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
    let mut waiting_c = VecDeque::with_capacity(C_RESULTS_PER_PAGE - 1);
    let (termination_sender, termination_receiver) = oneshot::channel();
    // Use PRP queue so that the first unknown number will start sooner
    while try_queue_unknowns(
        &id_and_expr_regex,
        &http,
        u_digits,
        prp_sender
            .reserve_many(PRP_RESULTS_PER_PAGE as usize)
            .await
            .unwrap(),
        &mut u_filter,
        &factor_finder,
    )
    .await
    .is_err()
        && queue_composites(
            &mut waiting_c,
            &id_and_expr_regex,
            &http,
            &c_sender,
            c_digits,
        )
        .await
            == 0
    {}
    task::spawn(do_checks(
        PushbackReceiver::new(prp_receiver, &prp_sender),
        PushbackReceiver::new(u_receiver, &u_sender),
        c_receiver,
        c_filter,
        http.clone(),
        factor_finder.clone(),
        id_and_expr_regex.clone(),
        termination_receiver,
    ));
    let mut sigterm =
        signal(SignalKind::terminate()).expect("Failed to create SIGTERM signal stream");
    loop {
        let select_start = Instant::now();
        select! {
            biased;
            _ = sigterm.recv() => {
                warn!("Received SIGTERM; signaling do_checks thread to exit");
                termination_sender.send(()).unwrap();
                return;
            }
            // Nested select should prevent bias between U, PRP and C, but keep bias in favor of SIGTERM
            _ = sleep(Duration::ZERO) => select! {
                // Duplicate sigterm recv so we won't stall inside the inner select
                _ = sigterm.recv() => {
                    warn!("Received SIGTERM; signaling do_checks thread to exit");
                    termination_sender.send(()).unwrap();
                    return;
                }
                u_permits = u_sender.reserve_many(U_RESULTS_PER_PAGE) => {
                    info!("Ready to search for U's after {:?}", Instant::now() - select_start);
                    queue_unknowns(&id_and_expr_regex, &http, u_digits, u_permits.unwrap(), &mut u_filter, &factor_finder).await;
                }
                c_permit = c_sender.reserve() => {
                    info!("Ready to send C's after {:?}", Instant::now() - select_start);
                    let c = waiting_c.pop_front();
                    let mut c_sent = 1usize;
                    match c {
                        Some(c) => {
                            c_permit.unwrap().send(c);
                            while let Some(c) = waiting_c.pop_front() {
                                if let Err(Full(c)) = c_sender.try_send(c) {
                                    waiting_c.push_front(c);
                                    break;
                                }
                                c_sent += 1;
                            }
                        }
                        None => {
                            c_sent = queue_composites(&mut waiting_c, &id_and_expr_regex, &http, &c_sender, c_digits).await;
                        }
                    }
                    info!("{c_sent} C's sent to channel; {} now in buffer", waiting_c.len());
                }
                prp_permits = prp_sender.reserve_many(PRP_RESULTS_PER_PAGE as usize) => {
                    info!("Ready to search for PRP's after {:?}", Instant::now() - select_start);
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
                            queue_unknowns(&id_and_expr_regex, &http, u_digits, u_permits, &mut u_filter, &factor_finder).await;
                        }
                    }
                    prp_start += PRP_RESULTS_PER_PAGE;
                    if prp_start > MAX_START {
                        info!("Restarting PRP search: reached maximum starting index");
                        prp_start = 0;
                    }
                }
            }
        }
    }
}

async fn queue_unknowns(
    id_and_expr_regex: &Regex,
    http: &ThrottlingHttpClient,
    u_digits: Option<NonZeroU128>,
    u_permits: PermitIterator<'_, CheckTask>,
    u_filter: &mut InMemoryFilter,
    factor_finder: &FactorFinder,
) {
    let mut permits = Some(u_permits);
    while let Some(u_permits) = permits.take() {
        if let Err(u_permits) = try_queue_unknowns(
            id_and_expr_regex,
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

async fn try_queue_unknowns<'a>(
    id_and_expr_regex: &Regex,
    http: &ThrottlingHttpClient,
    u_digits: Option<NonZeroU128>,
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
    let ids = id_and_expr_regex
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
        if find_and_submit_factors(
            http,
            u_id,
            digits_or_expr,
            factor_finder,
            id_and_expr_regex,
            false,
            false,
        )
        .await
        {
            info!("{u_id}: Skipping PRP check because this former U is now CF or FF");
        } else {
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

async fn try_report_factor(
    http: &ThrottlingHttpClient,
    u_id: NumberSpecifier<'_>,
    factor: &Factor,
) -> Result<bool, ()> {
    match http
        .post("https://factordb.com/reportfactor.php")
        .form(&FactorSubmission {
            id: if let Id(id) = u_id { Some(id) } else { None },
            number: if let Expression(expr) = u_id {
                Some(expr)
            } else {
                None
            },
            factor: &factor.to_compact_string(),
        })
        .send()
        .await
    {
        Ok(response) => {
            let response = response.text().await;
            match response {
                Ok(text) => {
                    info!("{u_id:?}: reported a factor of {factor}; response: {text}",);
                    return if text.contains("Error") {
                        Err(())
                    } else {
                        Ok(text.contains("submitted"))
                    };
                }
                Err(e) => {
                    error!("{u_id:?}: Failed to get response: {e}");
                }
            }
        }
        Err(e) => {
            error!("{u_id:?}: failed to submit factor {factor}: {e}")
        }
    }
    sleep(RETRY_DELAY).await;
    Err(())
}

async fn report_factor_of_u(http: &ThrottlingHttpClient, u_id: u128, factor: &Factor) -> bool {
    for _ in 0..SUBMIT_FACTOR_MAX_ATTEMPTS {
        if let Ok(result) = try_report_factor(http, Id(u_id), factor).await {
            return result;
        }
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

#[derive(PartialEq, Eq)]
enum SubfactorHandling {
    Irreducible,
    ById(u128),
    ByExpression,
    AlreadySubmitted,
}

async fn find_and_submit_factors(
    http: &ThrottlingHttpClient,
    id: u128,
    digits_or_expr: &str,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
    skip_looking_up_known: bool,
    skip_looking_up_listed_algebraic: bool,
) -> bool {
    let mut digits_or_expr_full = Vec::new();
    let digits_or_expr_full_contains_self = if skip_looking_up_known {
        digits_or_expr_full.push(Factor::String(digits_or_expr.into()));
        true
    } else if digits_or_expr.contains("...") {
        let Ok(known_factors) = factor_finder
            .known_factors_as_digits(http, Id(id), true)
            .await
        else {
            return false;
        };
        match known_factors.len() {
            0 => {
                warn!("{id}: Already fully factored");
                return true;
            }
            1 => {
                digits_or_expr_full.extend(known_factors);
                true
            }
            _ => false,
        }
    } else {
        digits_or_expr_full.push(digits_or_expr.into());
        true
    };
    let mut all_factors = BTreeMap::new();
    let mut accepted_factors = false;
    let try_subfactors = digits_or_expr.contains('/');
    for digits_or_expr in digits_or_expr_full.into_iter() {
        let factors = factor_finder.find_unique_factors(&digits_or_expr);
        if factors.is_empty() {
            if !digits_or_expr_full_contains_self && !all_factors.contains_key(&digits_or_expr) {
                all_factors.insert(digits_or_expr, ByExpression);
            }
        } else {
            all_factors.extend(factors.into_iter().map(|factor| (factor, ByExpression)));
        }
    }
    if !skip_looking_up_listed_algebraic {
        get_known_algebraic_factors(http, id, factor_finder, id_and_expr_regex, &mut all_factors)
            .await;
    }
    let mut dest_factors: BTreeSet<Factor> = BTreeSet::new();
    let mut iters_without_progress = 0;
    while iters_without_progress < SUBMIT_FACTOR_MAX_ATTEMPTS {
        iters_without_progress += 1;
        let mut accepted_this_iter = 0usize;
        let mut did_not_divide_this_iter = 0usize;
        let mut errors_this_iter = 0usize;
        let mut new_subfactors = BTreeMap::new();
        let mut try_with_dest_factors = Vec::new();
        for (factor, subfactor_handling) in all_factors.iter_mut().rev() {
            if *subfactor_handling == AlreadySubmitted {
                continue;
            }
            match try_report_factor(http, Id(id), factor).await {
                Ok(true) => {
                    accepted_factors = true;
                    accepted_this_iter += 1;
                    iters_without_progress = 0;
                    *subfactor_handling = AlreadySubmitted;
                    if let Factor::String(_) = factor {
                        dest_factors.insert(factor.clone());
                    }
                }
                Ok(false) => {
                    if dest_factors.is_empty() {
                        did_not_divide_this_iter += 1;
                        if try_subfactors {
                            try_find_subfactors(
                                http,
                                id,
                                factor_finder,
                                id_and_expr_regex,
                                &mut new_subfactors,
                                factor,
                                subfactor_handling,
                            )
                            .await;
                        }
                        *subfactor_handling = AlreadySubmitted;
                    } else {
                        try_with_dest_factors.push((factor, subfactor_handling));
                    }
                }
                Err(()) => {
                    if !dest_factors.is_empty() {
                        try_with_dest_factors.push((factor, subfactor_handling));
                    }
                }
            }
        }
        if !dest_factors.is_empty() {
            let mut did_not_divide = vec![0usize; try_with_dest_factors.len()];
            let mut new_dest_factors = Vec::new();
            for dest_factor in dest_factors.iter() {
                for (index, (factor, subfactor_handling)) in
                    try_with_dest_factors.iter_mut().enumerate()
                {
                    if **subfactor_handling == AlreadySubmitted {
                        continue;
                    }
                    if *factor == dest_factor
                    {
                        continue;
                    }
                    match try_report_factor(http, Expression(&dest_factor.to_compact_string()), factor).await {
                        Ok(true) => {
                            **subfactor_handling = AlreadySubmitted;
                            accepted_this_iter += 1;
                            if let Factor::String(_) = factor {
                                new_dest_factors.push((*factor).clone());
                            }
                        }
                        Ok(false) => {
                            did_not_divide[index] += 1;
                        }
                        Err(()) => {}
                    }
                }
            }
            for (index, (factor, subfactor_handling)) in
                try_with_dest_factors.into_iter().enumerate()
            {
                if *subfactor_handling == AlreadySubmitted {
                    continue;
                }
                if did_not_divide[index] == dest_factors.len() {
                    *subfactor_handling = AlreadySubmitted;
                    did_not_divide_this_iter += 1;
                    if try_subfactors {
                        try_find_subfactors(
                            http,
                            id,
                            factor_finder,
                            id_and_expr_regex,
                            &mut new_subfactors,
                            factor,
                            subfactor_handling,
                        )
                        .await;
                    }
                } else {
                    errors_this_iter += 1;
                }
            }
            dest_factors.extend(new_dest_factors);
        }
        new_subfactors.retain(|key, _| !all_factors.contains_key(key));
        if new_subfactors.is_empty() && errors_this_iter == 0 {
            return accepted_factors;
        }
        let mut already_submitted_elsewhere = 0usize;
        if let Ok(already_known_factors) = factor_finder
            .known_factors_as_digits(http, Id(id), false)
            .await
        {
            if already_known_factors.is_empty() {
                info!("{id}: Already fully factored");
                return true;
            }
            if already_known_factors.len() > 1 {
                for factor in already_known_factors.into_iter().rev() {
                    let prev_handling = all_factors.get(&factor);
                    if prev_handling != Some(&AlreadySubmitted) {
                        if let Factor::String(_) = factor {
                            dest_factors.insert(factor.clone());
                            iters_without_progress = 0;
                        }
                        all_factors.insert(factor, AlreadySubmitted);
                        already_submitted_elsewhere += 1;
                        accepted_factors = true; // As long as it's no longer U or C
                    }
                }
            }
        }
        new_subfactors.retain(|key, _| !all_factors.contains_key(key));
        let new_subfactors_count = new_subfactors.len();
        if new_subfactors.is_empty() {
            if errors_this_iter == 0 {
                return accepted_factors;
            }
        } else {
            iters_without_progress = 0;
            all_factors.extend(new_subfactors);
        }
        info!(
            "{id}: This iteration: {accepted_this_iter} factors accepted, \
            {did_not_divide_this_iter} did not divide, \
            {errors_this_iter} submission errors, \
            {new_subfactors_count} new subfactors to try, \
            {already_submitted_elsewhere} submitted by someone else"
        );
    }
    for (factor, subfactor_handling) in all_factors.into_iter() {
        if subfactor_handling == AlreadySubmitted {
            continue;
        }
        match FAILED_U_SUBMISSIONS_OUT
            .get()
            .unwrap()
            .lock()
            .await
            .write_fmt(format_args!("{id},{factor}\n"))
        {
            Ok(_) => warn!("{id}: wrote {factor} to failed submissions file"),
            Err(e) => error!("{id}: failed to write {factor} to failed submissions file: {e}"),
        }
    }
    accepted_factors
}

async fn try_find_subfactors(
    http: &ThrottlingHttpClient,
    id: u128,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
    new_subfactors: &mut BTreeMap<Factor, SubfactorHandling>,
    factor: &Factor,
    subfactor_handling: &mut SubfactorHandling,
) -> bool {
    if let Numeric(_) = factor {
        let factors = factor_finder
            .find_unique_factors(factor)
            .into_iter()
            .map(|factor| (factor, Irreducible));
        let success = factors.len() > 1;
        new_subfactors.extend(factors);
        return success;
    }
    let specifier_to_get_subfactors = match subfactor_handling {
        Irreducible => {
            return false;
        }
        ById(factor_id) => {
            get_known_algebraic_factors(
                http,
                *factor_id,
                factor_finder,
                id_and_expr_regex,
                new_subfactors,
            )
            .await;
            Id(*factor_id)
        }
        ByExpression => Expression(&factor.to_compact_string()),
        AlreadySubmitted => return false,
    };
    let mut subfactors: BTreeSet<_> = factor_finder
        .find_unique_factors(factor)
        .into_iter()
        .collect();
    if let Ok(known_subfactors) = factor_finder
        .known_factors_as_digits(http, specifier_to_get_subfactors, true)
        .await
        && known_subfactors.len() > 1
    {
        subfactors.extend(known_subfactors);
    }
    let mut success = false;
    for subfactor in subfactors {
        info!("{id}: Found sub-factor {subfactor} of {factor}");
        let entry = new_subfactors.entry(subfactor);
        if let Vacant(v) = entry {
            v.insert(ByExpression);
            success = true;
        }
    }
    success
}

async fn get_known_algebraic_factors(
    http: &ThrottlingHttpClient,
    id: u128,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
    all_factors: &mut BTreeMap<Factor, SubfactorHandling>,
) {
    info!("{id}: Checking for listed algebraic factors");
    // Links before the "Is factor of" header are algebraic factors; links after it aren't
    let url = format!("https://factordb.com/frame_moreinfo.php?id={id}");
    let result = http.retrying_get_and_decode(&url, RETRY_DELAY).await;
    if let Some(listed_algebraic) = result.split("Is factor of").next() {
        let algebraic_factors = id_and_expr_regex.captures_iter(listed_algebraic);
        for factor in algebraic_factors {
            let factor_id = &factor[1];
            let factor_digits_or_expr = &factor[2];
            if factor_digits_or_expr.contains("...") {
                // Link text isn't an expression for the factor, so we need to look up its value
                info!(
                    "{id}: Algebraic factor with ID {factor_id} represented as digits with ellipsis: {factor_digits_or_expr}"
                );
                if let Ok(factor_id) = factor_id.parse::<u128>() {
                    if let Ok(subfactors) = factor_finder
                        .known_factors_as_digits(http, Id(factor_id), true)
                        .await
                    {
                        for subfactor in subfactors {
                            all_factors.entry(subfactor).or_insert(ByExpression);
                        }
                    } else {
                        error!(
                            "{id}: Skipping ellided factor with ID {factor_id} because we failed to fetch it in full"
                        );
                    }
                } else {
                    error!("{id}: Invalid ID for algebraic factor: {factor_id}");
                }
            } else {
                info!(
                    "{id}: Algebraic factor with ID {factor_id} represented in full: {factor_digits_or_expr}"
                );
                let factor = factor_digits_or_expr.into();
                let subfactor_handling = if let Ok(factor_id) = factor_id.parse::<u128>() {
                    ById(factor_id)
                } else {
                    ByExpression
                };
                all_factors.entry(factor).or_insert(subfactor_handling);
            }
        }
    }
}