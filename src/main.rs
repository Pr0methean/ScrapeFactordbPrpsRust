#![allow(stable_features)]
#![feature(duration_constructors_lite)]
#![feature(float_gamma)]
#![feature(deque_extend_front)]
extern crate core;

mod algebraic;
mod channel;
mod graph;
mod net;
mod shutdown;

use crate::FactorsKnownToFactorDb::{NotUpToDate, UpToDate};
use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored, DoesNotDivide, OtherError};
use crate::UnknownPrpCheckResult::{
    Assigned, IneligibleForPrpCheck, OtherRetryableFailure, PleaseWait,
};
use crate::algebraic::Factor::Numeric;
use crate::algebraic::NumberStatus::{FullyFactored, Prime};
use crate::algebraic::{Factor, FactorFinder, NumberStatus, ProcessedStatusApiResponse};
use crate::algebraic::{NumberStatusExt, OwnedFactor};
use crate::graph::{
    add_factor_node, get_edge, is_known_factor, propagate_divisibility, rule_out_divisibility,
};
use crate::net::ResourceLimits;
use crate::shutdown::{Shutdown, handle_signals};
use Ordering::{Equal, Greater, Less};
use channel::PushbackReceiver;
use compact_str::CompactString;
use const_format::formatcp;
use cuckoofilter::CuckooFilter;
use graph::Divisibility::{Direct, NotFactor};
use graph::DivisibilityGraph;
use gryf::Graph;
use gryf::core::GraphRef;
use gryf::core::base::VertexRef;
use gryf::core::facts::complete_graph_edge_count;
use gryf::core::id::VertexId;
use gryf::core::marker::{Directed, Incoming};
use gryf::storage::AdjMatrix;
use itertools::Itertools;
use log::{debug, error, info, warn};
use net::{CPU_TENTHS_SPENT_LAST_CHECK, FactorDbClient};
use primitive_types::U256;
use rand::seq::SliceRandom;
use rand::{Rng, rng};
use regex::Regex;
use replace_with::replace_with_or_abort;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::{self, Debug, Display, Formatter};
use std::fs::File;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io::Write;
use std::mem::replace;
use std::num::{NonZeroU32, NonZeroU128};
use std::ops::Add;
use std::panic;
use std::process::exit;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering::{Acquire, Release};
use tokio::sync::mpsc::error::TrySendError::{Closed, Full};
use tokio::sync::mpsc::{OwnedPermit, PermitIterator, Sender, channel};
use tokio::sync::{Mutex, OnceCell, oneshot};
use tokio::task::JoinHandle;
use tokio::time::{Duration, Instant, sleep, sleep_until, timeout};
use tokio::{select, task};

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
const C_TASK_BUFFER_SIZE: usize = 4096;
const C_MIN_DIGITS: u128 = 92;
const C_MAX_DIGITS: u128 = 300;

const U_MIN_DIGITS: u128 = 2001;
const U_MAX_DIGITS: u128 = 199_999;
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

#[derive(Clone, Debug, Eq)]
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
    status: Box<str>,
    factors: Box<[(Box<str>, u128)]>,
}

#[derive(Serialize)]
struct FactorSubmission<'a> {
    id: Option<u128>,
    number: Option<Cow<'a, str>>,
    factor: Cow<'a, str>,
}

async fn composites_while_waiting(
    end: Instant,
    http: &FactorDbClient,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    c_filter: &mut CuckooFilter<DefaultHasher>,
    factor_finder: &FactorFinder,
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
    http: &FactorDbClient,
    c_filter: &mut CuckooFilter<DefaultHasher>,
    factor_finder: &FactorFinder,
    id: u128,
    digits_or_expr: CompactString,
    return_permit: OwnedPermit<CompositeCheckTask>,
) -> bool {
    if c_filter.contains(&id) {
        info!("{id}: Skipping duplicate C");
        return true;
    }
    let checks_triggered = if http
        .try_get_and_decode(
            &format!("https://factordb.com/sequences.php?check={id}").into_boxed_str(),
        )
        .await
        .is_some()
    {
        info!("{id}: Checked C");
        true
    } else {
        false
    };
    // First, convert the composite to digits
    let ProcessedStatusApiResponse {
        factors, status, ..
    } = http
        .known_factors_as_digits::<&str, &str>(Id(id), false, true)
        .await;
    if factors.is_empty() {
        if status.is_known_fully_factored() {
            warn!("{id}: Already fully factored");
            true
        } else {
            return_permit.send(CompositeCheckTask { id, digits_or_expr });
            info!("{id}: Requeued C");
            false
        }
    } else {
        let mut factors_submitted = false;
        let mut factors_to_dispatch = Vec::with_capacity(factors.len());
        for factor in factors {
            if let Some(factor_str) = factor.as_str_non_u128() {
                if find_and_submit_factors(http, id, factor_str, factor_finder, true).await {
                    factors_submitted = true;
                } else {
                    factors_to_dispatch.push(factor);
                }
            }
        }
        let mut dispatched = false;
        if let Some(out) = COMPOSITES_OUT.get() {
            if factors_to_dispatch.is_empty() {
                info!("{id}: Skipping dispatch of C because already factored");
                return true;
            }
            let mut out = out.lock().await;
            let mut result = factors_to_dispatch
                .into_iter()
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
        if !dispatched && !checks_triggered && !factors_submitted {
            return_permit.send(CompositeCheckTask { id, digits_or_expr });
            info!("{id}: Requeued C");
            false
        } else {
            true
        }
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
enum NumberSpecifier<T: AsRef<str>, U: AsRef<str>> {
    Id(u128),
    Expression(Factor<T, U>),
}

impl<T: AsRef<str>, U: AsRef<str>> Display for NumberSpecifier<T, U> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Id(id) => write!(f, "ID {}", id),
            Expression(e) => write_bignum(f, &e.as_str()),
        }
    }
}

pub fn write_bignum(f: &mut Formatter, e: &str) -> fmt::Result {
    let len = e.len();
    if len < 300 {
        f.write_str(e)
    } else {
        write!(f, "{}...{}<{}>", &e[..20], &e[(len - 5)..], len)
    }
}

#[allow(clippy::too_many_arguments)]
async fn get_prp_remaining_bases(
    id: u128,
    http: &FactorDbClient,
    bases_regex: &Regex,
    nm1_regex: &Regex,
    np1_regex: &Regex,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    c_filter: &mut CuckooFilter<DefaultHasher>,
    factor_finder: &FactorFinder,
) -> Result<U256, ()> {
    let mut bases_left = U256::MAX - 3;
    let bases_text = http
        .retrying_get_and_decode(
            &format!("https://factordb.com/frame_prime.php?id={id}").into_boxed_str(),
            RETRY_DELAY,
        )
        .await;
    if bases_text.contains("Proven") {
        info!("{id}: No longer PRP");
    }
    let mut nm1_id_if_available = None;
    let mut nm1_known_to_divide_2 = false;
    let mut nm1_known_to_divide_3 = false;
    let mut np1_id_if_available = None;
    let mut np1_known_to_divide_2 = false;
    let mut np1_known_to_divide_3 = false;
    if let Some(captures) = nm1_regex.captures(&bases_text) {
        let nm1_id = captures[1].parse::<u128>().unwrap();
        nm1_id_if_available = Some(nm1_id);
        let ProcessedStatusApiResponse {
            status,
            factors: nm1_factors,
            ..
        } = http
            .known_factors_as_digits::<&str, &str>(Id(nm1_id), false, false)
            .await;
        match nm1_factors.len() {
            0 => {
                if status == Some(FullyFactored) {
                    info!("{id}: N-1 (ID {nm1_id}) is fully factored!");
                    prove_by_nm1(id, http).await;
                    return Ok(U256::from(0));
                }
            }
            _ => {
                nm1_known_to_divide_2 = nm1_factors[0].as_u128() == Some(2);
                nm1_known_to_divide_3 = nm1_factors[0].as_u128() == Some(3)
                    || nm1_factors.get(1).and_then(Factor::as_u128) == Some(3);
            }
        }
    } else {
        error!("{id}: N-1 ID not found: {bases_text}");
    }
    if let Some(captures) = np1_regex.captures(&bases_text) {
        let np1_id = captures[1].parse::<u128>().unwrap();
        np1_id_if_available = Some(np1_id);
        let ProcessedStatusApiResponse {
            status,
            factors: np1_factors,
            ..
        } = http
            .known_factors_as_digits::<&str, &str>(Id(np1_id), false, false)
            .await;
        match np1_factors.len() {
            0 => {
                if status == Some(FullyFactored) {
                    info!("{id}: N+1 (ID {np1_id}) is fully factored!");
                    prove_by_np1(id, http).await;
                    return Ok(U256::from(0));
                }
            }
            _ => {
                np1_known_to_divide_2 = np1_factors[0].as_u128() == Some(2);
                np1_known_to_divide_3 = np1_factors[0].as_u128() == Some(3)
                    || np1_factors.get(1).and_then(Factor::as_u128) == Some(3);
            }
        }
    } else {
        error!("{id}: N+1 ID not found: {bases_text}");
    }
    if let Some(nm1_id) = nm1_id_if_available
        && !nm1_known_to_divide_2
    {
        // N wouldn't be PRP if it was even, so N-1 must be even
        match http.report_factor::<&str, &str>(nm1_id, &Numeric(2)).await {
            AlreadyFullyFactored => {
                info!("{id}: N-1 (ID {nm1_id}) is fully factored!");
                prove_by_nm1(id, http).await;
                return Ok(U256::from(0));
            }
            Accepted => {}
            _ => {
                error!("{id}: PRP, but factor of 2 was rejected for N-1 (id {nm1_id})");
            }
        }
    }
    if let Some(np1_id) = np1_id_if_available
        && !np1_known_to_divide_2
    {
        // N wouldn't be PRP if it was even, so N+1 must be even
        match http.report_factor::<&str, &str>(np1_id, &Numeric(2)).await {
            AlreadyFullyFactored => {
                info!("{id}: N+1 (ID {np1_id}) is fully factored!");
                prove_by_np1(id, http).await;
                return Ok(U256::from(0));
            }
            Accepted => {}
            _ => {
                error!("{id}: PRP, but factor of 2 was rejected for N+1 (id {np1_id})");
            }
        }
    }
    if let Some(nm1_id) = nm1_id_if_available
        && let Some(np1_id) = np1_id_if_available
    {
        if !nm1_known_to_divide_3 && !np1_known_to_divide_3 {
            // N wouldn't be PRP if it was a multiple of 3, so N-1 xor N+1 must be a multiple of 3
            match http.report_factor::<&str, &str>(nm1_id, &Numeric(3)).await {
                AlreadyFullyFactored => {
                    info!("{id}: N-1 (ID {nm1_id}) is fully factored!");
                    prove_by_nm1(id, http).await;
                    return Ok(U256::from(0));
                }
                Accepted => {}
                _ => match http.report_factor::<&str, &str>(np1_id, &Numeric(3)).await {
                    AlreadyFullyFactored => {
                        info!("{id}: N+1 (ID {np1_id}) is fully factored!");
                        prove_by_np1(id, http).await;
                        return Ok(U256::from(0));
                    }
                    Accepted => {}
                    _ => {
                        error!(
                            "{id}: PRP, but factor of 3 was rejected for both N-1 (id {nm1_id}) and N+1 (id {np1_id})"
                        );
                    }
                },
            }
        }
        for id in [nm1_id, np1_id] {
            for factor in http
                .known_factors_as_digits::<&str, &str>(Id(id), false, true)
                .await
                .factors
                .into_iter()
            {
                if factor.as_str_non_u128().is_some() {
                    find_and_submit_factors(http, id, &factor.as_str(), factor_finder, true).await;
                }
            }
        }
    }
    let status_text = http
        .retrying_get_and_decode(
            &format!("https://factordb.com/index.php?open=Prime&ct=Proof&id={id}").into_boxed_str(),
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

async fn prove_by_np1(id: u128, http: &FactorDbClient) {
    let _ = http
        .retrying_get_and_decode(
            &format!("https://factordb.com/index.php?open=Prime&np1=Proof&id={id}")
                .into_boxed_str(),
            RETRY_DELAY,
        )
        .await;
}

async fn prove_by_nm1(id: u128, http: &FactorDbClient) {
    let _ = http
        .retrying_get_and_decode(
            &format!("https://factordb.com/index.php?open=Prime&nm1=Proof&id={id}")
                .into_boxed_str(),
            RETRY_DELAY,
        )
        .await;
}

const MAX_BASES_BETWEEN_RESOURCE_CHECKS: usize = 254;

const MIN_BASES_BETWEEN_RESOURCE_CHECKS: usize = 16;

const MAX_CPU_BUDGET_TENTHS: usize = 6000;
const UNKNOWN_STATUS_CHECK_BACKOFF: Duration = Duration::from_mins(5);
static NO_RESERVE: AtomicBool = AtomicBool::new(false);

#[inline]
async fn do_checks(
    mut prp_receiver: PushbackReceiver<u128>,
    mut u_receiver: PushbackReceiver<u128>,
    mut c_receiver: PushbackReceiver<CompositeCheckTask>,
    http: FactorDbClient,
    factor_finder: FactorFinder,
    mut shutdown_receiver: Shutdown,
) {
    info!("do_checks task starting");
    let mut c_filter = CuckooFilter::with_capacity(4096);
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
    )
    .await;
    let mut successful_select_end = Instant::now();
    loop {
        select! {
            _ = shutdown_receiver.recv() => {
                warn!("do_checks received shutdown signal; exiting");
                return;
            }
            _ = sleep_until(next_unknown_attempt) => {
                let Some((id, task_return_permit)) = retry.take().inspect(|_| {
                    info!("Ready to retry a U after {:?}", Instant::now() - successful_select_end);
                }).or_else(||
                    u_receiver.try_recv().inspect(|_| {
                        info!("Ready to check a U after {:?}", Instant::now() - successful_select_end);
                    }))
                else {
                    continue;
                };
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
                            retry = Some((id, task_return_permit));
                            info!("{id}: put U in retry buffer");
                        } else {
                            task_return_permit.send(id);
                            info!("{id}: Requeued U");
                        }
                    }
                    OtherRetryableFailure => {
                        task_return_permit.send(id);
                        info!("{id}: Requeued U");
                    }
                }
            }
            (id, task_return_permit) = prp_receiver.recv() => {
                info!("Ready to check a PRP after {:?}", Instant::now() - successful_select_end);
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
                )
                .await
                else {
                    task_return_permit.send(id);
                    info!("{id}: Requeued PRP");
                    continue;
                };
                if bases_left == U256::from(0) {
                    continue;
                }
                for base in (0..=(u8::MAX as usize)).filter(|i| bases_left.bit(*i)) {
                    let url = format!(
                        "https://factordb.com/index.php?id={id}&open=prime&basetocheck={base}"
                    );
                    let text = http.retrying_get_and_decode(&url, RETRY_DELAY).await;
                    if !text.contains(">number<") {
                        error!("Failed to decode result from {url}: {text}");
                        task_return_permit.send(id);
                        info!("{id}: Requeued PRP");
                        composites_while_waiting(
                            Instant::now() + UNPARSEABLE_RESPONSE_RETRY_DELAY,
                            &http,
                            &mut c_receiver,
                            &mut c_filter,
                            &factor_finder,
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
            c_task = c_receiver.recv() => {
                info!("Ready to check a C after {:?}", Instant::now() - successful_select_end);
                let (CompositeCheckTask {id, digits_or_expr}, return_permit) = c_task;
                check_composite(&http, &mut c_filter, &factor_finder, id, digits_or_expr, return_permit).await;
            }
        }
        successful_select_end = Instant::now();
    }
}

#[inline]
async fn try_handle_unknown(
    http: &FactorDbClient,
    u_status_regex: &Regex,
    many_digits_regex: &Regex,
    id: u128,
    next_attempt: &mut Instant,
) -> UnknownPrpCheckResult {
    let url =
        format!("https://factordb.com/index.php?id={id}&prp=Assign+to+worker").into_boxed_str();
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
    http: &FactorDbClient,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    bases_before_next_cpu_check: &mut usize,
    sleep_first: bool,
    c_filter: &mut CuckooFilter<DefaultHasher>,
    factor_finder: &FactorFinder,
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
        )
        .await; // allow for delay in CPU accounting
    }
    // info!("Resources fetched");
    let Some(ResourceLimits {
        cpu_tenths_spent,
        resets_at,
    }) = http
        .try_get_resource_limits(bases_before_next_cpu_check)
        .await
    else {
        error!("Failed to parse resource limits");
        return false;
    };
    let seconds_to_reset = resets_at
        .saturating_duration_since(Instant::now())
        .as_secs_f64();
    let mut tenths_remaining = MAX_CPU_BUDGET_TENTHS.saturating_sub(cpu_tenths_spent);
    if !NO_RESERVE.load(Acquire) {
        tenths_remaining = tenths_remaining
            .saturating_sub((seconds_to_reset * seconds_to_reset / 18000.0) as usize);
    }
    let mut bases_remaining = (tenths_remaining / 10).min(MAX_BASES_BETWEEN_RESOURCE_CHECKS);
    if bases_remaining <= MIN_BASES_BETWEEN_RESOURCE_CHECKS {
        warn!(
            "CPU time spent this cycle: {:.1} seconds. Throttling {} seconds due to high server CPU usage",
            cpu_tenths_spent as f64 * 0.1,
            seconds_to_reset
        );
        if EXIT_TIME
            .get()
            .is_some_and(|exit_time| *exit_time <= resets_at)
        {
            warn!("Throttling won't end before program exit; exiting now");
            exit(0);
        }
        composites_while_waiting(resets_at, http, c_receiver, c_filter, factor_finder).await;
        *bases_before_next_cpu_check = MAX_BASES_BETWEEN_RESOURCE_CHECKS;
        CPU_TENTHS_SPENT_LAST_CHECK.store(0, Release);
    } else {
        if bases_remaining < MIN_BASES_BETWEEN_RESOURCE_CHECKS {
            bases_remaining = MIN_BASES_BETWEEN_RESOURCE_CHECKS;
        }
        info!(
            "CPU time spent this cycle: {:.1} seconds; reset in {} seconds; checking again after {} bases",
            cpu_tenths_spent as f64 * 0.1,
            seconds_to_reset as usize,
            bases_remaining
        );
        *bases_before_next_cpu_check = bases_remaining;
    }
    true
}

// The reason this method returns a JoinHandle (and thus needs .await.await at the start of the
// program) is that even once the C search has completed, it may have returned more results than cam
// fit into the channel at once. In that case, we want the remaining results to wait to be pushed
// into the channel, without blocking PRP or U searches on the main thread.
#[allow(clippy::async_yields_async)]
async fn queue_composites(
    http: &FactorDbClient,
    c_sender: &Sender<CompositeCheckTask>,
    digits: Option<NonZeroU128>,
) -> JoinHandle<()> {
    let start = if digits.is_some_and(|digits| digits.get() < C_MIN_DIGITS) {
        0
    } else {
        rng().random_range(0..=MAX_START)
    };
    let digits = digits.unwrap_or_else(|| {
        rng()
            .random_range(C_MIN_DIGITS..=C_MAX_DIGITS)
            .try_into()
            .unwrap()
    });
    info!("Retrieving {digits}-digit C's starting from {start}");
    let mut results_per_page = C_RESULTS_PER_PAGE;
    let mut composites_page = None;
    while composites_page.is_none() && results_per_page > 0 {
        composites_page = http.try_get_and_decode(
            &format!("https://factordb.com/listtype.php?t=3&perpage={results_per_page}&start={start}&mindig={digits}").into_boxed_str()
        ).await;
        if composites_page.is_none() {
            results_per_page >>= 1;
            sleep(SEARCH_RETRY_DELAY).await;
        }
    }
    info!("{results_per_page} C search results retrieved");
    let Some(composites_page) = composites_page else {
        return task::spawn(async {});
    };
    let mut c_tasks: Box<[_]> = http
        .read_ids_and_exprs(&composites_page)
        .map(|(id, expr)| CompositeCheckTask {
            id,
            digits_or_expr: expr.into(),
        })
        .collect();
    c_tasks.shuffle(&mut rng());
    let c_initial = c_tasks.len();
    let c_buffered: Box<[_]> = c_tasks
        .into_iter()
        .flat_map(|c_task| match c_sender.try_send(c_task) {
            Ok(()) => None,
            Err(Closed(_)) => None,
            Err(Full(c_task)) => Some(c_task),
        })
        .collect();
    let c_sent = c_initial - c_buffered.len();
    if c_buffered.is_empty() {
        info!("Sent {c_sent} C's to channel");
        task::spawn(async {})
    } else {
        info!(
            "Sent {c_sent} C's to channel; buffering {} more",
            c_buffered.len()
        );
        let c_sender = c_sender.clone();
        task::spawn(async move {
            let count = c_buffered.len();
            let mut c_sent = 0;
            for c_task in c_buffered {
                let id = c_task.id;
                if let Err(e) = c_sender.send(c_task).await {
                    error!("{id}: Dropping C because we failed to send it to channel: {e}");
                } else {
                    c_sent += 1;
                }
                if c_sent == 1 {
                    info!("Sent first of {count} buffered C's to channel");
                }
            }
            info!("Sent {c_sent} buffered C's to channel");
            let _ = c_sender.reserve().await; // Prevent task from finishing until another C can be sent
        })
    }
}

// One worker thread for do_checks(), one for main(), one for c_buffer_task, one for handle_signals
#[tokio::main(flavor = "multi_thread", worker_threads = 4)]

async fn main() -> anyhow::Result<()> {
    let (shutdown_sender, mut shutdown_receiver) = Shutdown::new();
    let (installed_sender, installed_receiver) = oneshot::channel();
    simple_log::console("info").unwrap();
    task::spawn(handle_signals(shutdown_sender, installed_sender));
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
    if let Ok(run_number) = std::env::var("RUN") {
        let run_number = run_number.parse::<u128>()?;
        if c_digits.is_none() {
            let mut c_digits_value =
                C_MAX_DIGITS - ((run_number * 19) % (C_MAX_DIGITS - C_MIN_DIGITS + 2));
            if c_digits_value == C_MIN_DIGITS - 1 {
                c_digits_value = 1;
            }
            c_digits = Some(c_digits_value.try_into()?);
        }
        if u_digits.is_none() {
            let u_digits_value =
                U_MAX_DIGITS - ((run_number * 19793) % (U_MAX_DIGITS - U_MIN_DIGITS + 1));
            u_digits = Some(u_digits_value.try_into()?);
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
    let rph_limit: NonZeroU32 = if is_no_reserve { 6400 } else { 6100 }.try_into()?;
    let mut max_concurrent_requests = 2usize;
    let (prp_sender, prp_receiver) = channel(PRP_TASK_BUFFER_SIZE);
    let (u_sender, u_receiver) = channel(U_TASK_BUFFER_SIZE);
    let (c_sender, c_raw_receiver) = channel(C_TASK_BUFFER_SIZE);
    let c_receiver = PushbackReceiver::new(c_raw_receiver, &c_sender);
    if std::env::var("CI").is_ok() {
        EXIT_TIME.set(Instant::now().add(Duration::from_mins(355)))?;
        COMPOSITES_OUT
            .get_or_init(async || {
                Mutex::new(File::options().append(true).open("composites").unwrap())
            })
            .await;
        max_concurrent_requests = 3;
    }
    let factor_finder = FactorFinder::new();
    let http = FactorDbClient::new(
        rph_limit,
        max_concurrent_requests,
        shutdown_receiver.clone(),
    );
    let http_clone = http.clone();
    let c_sender_clone = c_sender.clone();
    let mut c_buffer_task: JoinHandle<()> = task::spawn(async move {
        queue_composites(&http_clone, &c_sender_clone, c_digits)
            .await
            .await
            .unwrap();
    });
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
    let mut prp_filter: CuckooFilter<DefaultHasher> = CuckooFilter::with_capacity(4096);
    let mut u_filter = CuckooFilter::with_capacity(4096);
    installed_receiver.await?;
    task::spawn(do_checks(
        PushbackReceiver::new(prp_receiver, &prp_sender),
        PushbackReceiver::new(u_receiver, &u_sender),
        c_receiver,
        http.clone(),
        factor_finder.clone(),
        shutdown_receiver.clone(),
    ));
    'queue_tasks: loop {
        let mut new_c_buffer_task = false;
        let select_start = Instant::now();
        select! {
            biased;
            _ = shutdown_receiver.recv() => {
                warn!("Main thread received shutdown signal; exiting");
                c_buffer_task.abort();
                return Ok(());
            }
            // C comes first because otherwise it gets starved
            _ = &mut c_buffer_task => {
                info!("Ready to send C's from new search after {:?}", Instant::now() - select_start);
                new_c_buffer_task = true;
            }
            prp_permits = prp_sender.reserve_many(PRP_RESULTS_PER_PAGE as usize) => {
                let prp_permits = prp_permits?;
                info!("Ready to search for PRP's after {:?}", Instant::now() - select_start);
                let mut results_per_page = PRP_RESULTS_PER_PAGE;
                let mut results_text = None;
                while results_text.is_none() && results_per_page > 0 {
                    let prp_search_url = format!("https://factordb.com/listtype.php?t=1&mindig={MIN_DIGITS_IN_PRP}&perpage={results_per_page}&start={prp_start}").into_boxed_str();
                    let Some(text) = http.try_get_and_decode(&prp_search_url).await else {
                        sleep(SEARCH_RETRY_DELAY).await;
                        results_per_page >>= 1;
                        continue;
                    };
                    results_text = Some(text);
                    break;
                }
                info!("{results_per_page} PRP search results retrieved");
                let Some(results_text) = results_text else {
                    continue 'queue_tasks;
                };
                for ((prp_id, _), prp_permit) in http.read_ids_and_exprs(&results_text).zip(prp_permits)
                {
                    if let Ok(false) = prp_filter.test_and_add(&prp_id) {
                        warn!("{prp_id}: Skipping duplicate PRP");
                        continue;
                    }
                    prp_permit.send(prp_id);
                    info!("{prp_id}: Queued PRP from search");
                    if let Ok(mut u_permits) = u_sender.try_reserve_many(U_RESULTS_PER_PAGE) {
                        let _ = try_queue_unknowns(&http, u_digits, &mut u_permits, &mut u_filter, &factor_finder).await;
                    }
                }
                prp_start += PRP_RESULTS_PER_PAGE;
                if prp_start > MAX_START {
                    info!("Restarting PRP search: reached maximum starting index");
                    prp_start = 0;
                }
            }
            u_permits = u_sender.reserve_many(U_RESULTS_PER_PAGE) => {
                info!("Ready to search for U's after {:?}", Instant::now() - select_start);
                let _ = try_queue_unknowns(&http, u_digits, &mut u_permits?, &mut u_filter, &factor_finder).await;
            }
        }
        if new_c_buffer_task {
            c_buffer_task = queue_composites(&http, &c_sender, c_digits).await;
        }
    }
}

async fn try_queue_unknowns<'a>(
    http: &FactorDbClient,
    u_digits: Option<NonZeroU128>,
    u_permits: &mut PermitIterator<'a, u128>,
    u_filter: &mut CuckooFilter<DefaultHasher>,
    factor_finder: &FactorFinder,
) -> Result<(), ()> {
    let mut rng = rng();
    let digits = u_digits.unwrap_or_else(|| {
        rng.random_range(U_MIN_DIGITS..=U_MAX_DIGITS)
            .try_into()
            .unwrap()
    });
    let u_start = rng.random_range(0..=MAX_START);
    let u_search_url =
        format!("{U_SEARCH_URL_BASE}{u_start}&mindig={}", digits.get()).into_boxed_str();
    let Some(results_text) = http.try_get_and_decode(&u_search_url).await else {
        return Err(());
    };
    info!("U search results retrieved");
    let ids = http.read_ids_and_exprs(&results_text);
    let mut ids_found = false;
    for ((u_id, digits_or_expr), u_permit) in ids.zip(u_permits) {
        ids_found = true;
        if u_filter.contains(&u_id) {
            warn!("{u_id}: Skipping duplicate U");
            continue;
        }
        if find_and_submit_factors(http, u_id, digits_or_expr, factor_finder, false).await {
            info!("{u_id}: Skipping PRP check because this former U is now CF or FF");
        } else {
            let _ = u_filter.add(&u_id);
            u_permit.send(u_id);
            info!("{u_id}: Queued U");
        }
    }
    if ids_found {
        Ok(())
    } else {
        error!("Couldn't parse IDs from search result: {results_text}");
        sleep(RETRY_DELAY).await; // Can't do composites_while_waiting because we're on main thread, and child thread owns c_receiver
        Err(())
    }
}

#[derive(Debug, Eq, PartialEq)]
enum ReportFactorResult {
    Accepted,
    DoesNotDivide,
    AlreadyFullyFactored,
    OtherError,
}

const MAX_ID_EQUAL_TO_VALUE: u128 = 999_999_999_999_999_999;

#[derive(Clone, Debug, Eq, PartialEq)]
enum FactorsKnownToFactorDb {
    NotQueried,
    NotUpToDate(Vec<VertexId>),
    UpToDate(Vec<VertexId>),
}

impl FactorsKnownToFactorDb {
    pub(crate) fn to_vec(&self) -> Vec<VertexId> {
        match self {
            FactorsKnownToFactorDb::NotQueried => vec![],
            NotUpToDate(factors) | UpToDate(factors) => factors.clone(),
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &VertexId> {
        static EMPTY: Vec<VertexId> = vec![];
        match self {
            FactorsKnownToFactorDb::NotQueried => EMPTY.iter(),
            NotUpToDate(factors) | UpToDate(factors) => factors.iter(),
        }
    }
}

impl FactorsKnownToFactorDb {
    fn len(&self) -> usize {
        match self {
            FactorsKnownToFactorDb::NotQueried => 0,
            NotUpToDate(factors) | UpToDate(factors) => factors.len(),
        }
    }

    fn needs_update(&self) -> bool {
        match self {
            UpToDate(_) => false,
            NotUpToDate(_) => true,
            FactorsKnownToFactorDb::NotQueried => true,
        }
    }
}

#[derive(Debug)]
struct NumberFacts {
    last_known_status: Option<NumberStatus>,
    factors_known_to_factordb: FactorsKnownToFactorDb,
    lower_bound_log10: u128,
    upper_bound_log10: u128,
    entry_id: Option<u128>,
    checked_for_listed_algebraic: bool,
    checked_in_factor_finder: bool,
    expression_form_checked_in_factor_finder: bool,
}

impl PartialEq<Self> for NumberFacts {
    fn eq(&self, other: &Self) -> bool {
        if let Some(entry_id) = self.entry_id
            && other.entry_id == Some(entry_id)
        {
            true
        } else {
            self.factors_known_to_factordb == other.factors_known_to_factordb
        }
    }
}

/// No ordering could be transitive if it treated an overlapping pair of ranges differently than a
/// nonoverlapping pair. For example:
///
/// let a = Factor::Expression("100#"); // lower bound 10, upper bound 44
/// let b = Factor::BigNumber("123456789012345678901234567890123456789012345678901234567890"); // lower bound 59, upper bound 60
/// let c = Factor::Numeric(12345678901234567890); // lower bound 19, upper bound 20
///
/// So a < b and b < c because of the nonoverlapping bounds, but then c < a because expressions sort
/// last in Factor::Ord, and we hace a cycle. By comparing the upper bounds first, we break this
/// cycle in favor of c < a < b, which is the actual numeric-value ordering. This is probably about
/// as close as we can come to a total numeric-value ordering with no bignum math and no isk of
/// cycles.
fn compare(
    number_facts_map: &BTreeMap<VertexId, NumberFacts>,
    left: &VertexRef<VertexId, OwnedFactor>,
    right: &VertexRef<VertexId, OwnedFactor>,
) -> Ordering {
    let left_facts = number_facts_map.get(&left.id).unwrap();
    let right_facts = number_facts_map.get(&right.id).unwrap();
    left_facts
        .upper_bound_log10
        .cmp(&right_facts.upper_bound_log10)
        .then_with(|| {
            left_facts
                .lower_bound_log10
                .cmp(&right_facts.lower_bound_log10)
        })
        .then_with(|| left.attr.cmp(right.attr))
}

impl NumberFacts {
    #[inline(always)]
    pub(crate) fn is_known_fully_factored(&self) -> bool {
        self.last_known_status.is_known_fully_factored()
    }
    #[inline(always)]
    pub(crate) fn is_final(&self) -> bool {
        self.is_known_fully_factored() && !self.needs_update()
    }
    #[inline(always)]
    pub(crate) fn needs_update(&self) -> bool {
        self.factors_known_to_factordb.needs_update()
    }
    fn marked_stale(self) -> Self {
        if self.is_final() {
            return self;
        }
        if let UpToDate(factors) = self.factors_known_to_factordb {
            NumberFacts {
                factors_known_to_factordb: NotUpToDate(factors),
                ..self
            }
        } else {
            self
        }
    }
    pub fn merged_with(self, other: Self) -> Self {
        NumberFacts {
            lower_bound_log10: self.lower_bound_log10.max(other.lower_bound_log10),
            upper_bound_log10: self.upper_bound_log10.min(other.upper_bound_log10),
            entry_id: self.entry_id.or(other.entry_id),
            checked_for_listed_algebraic: self.checked_for_listed_algebraic
                || other.checked_for_listed_algebraic,
            last_known_status: self.last_known_status.max(other.last_known_status),
            factors_known_to_factordb: match self
                .factors_known_to_factordb
                .len()
                .cmp(&other.factors_known_to_factordb.len())
            {
                Less => other.factors_known_to_factordb,
                Greater => self.factors_known_to_factordb,
                Equal => match self.factors_known_to_factordb {
                    UpToDate(f) => {
                        if matches!(other.factors_known_to_factordb, UpToDate(_)) {
                            UpToDate(f)
                        } else {
                            NotUpToDate(f)
                        }
                    }
                    x => x,
                },
            },
            checked_in_factor_finder: self.checked_in_factor_finder
                || other.checked_in_factor_finder,
            expression_form_checked_in_factor_finder: self.expression_form_checked_in_factor_finder
                || other.expression_form_checked_in_factor_finder,
        }
    }
}

async fn find_and_submit_factors(
    http: &FactorDbClient,
    id: u128,
    digits_or_expr: &str,
    factor_finder: &FactorFinder,
    skip_looking_up_known: bool,
) -> bool {
    let mut digits_or_expr_full = Vec::new();
    let mut divisibility_graph: DivisibilityGraph =
        Graph::new_directed_in(AdjMatrix::new()).stabilize();
    let mut number_facts_map = BTreeMap::new();
    let (root_vid, _) = if !skip_looking_up_known && !digits_or_expr.contains("...") {
        add_factor_node(
            &mut divisibility_graph,
            Factor::<&str, &str>::from(digits_or_expr),
            factor_finder,
            &mut number_facts_map,
            None,
            Some(id),
        )
    } else {
        let ProcessedStatusApiResponse {
            factors: known_factors,
            status,
            ..
        } = http
            .known_factors_as_digits::<&str, &str>(Id(id), false, true)
            .await;
        if status.is_known_fully_factored() {
            warn!("{id}: Already fully factored");
            return true;
        }
        match known_factors.len() {
            0 => add_factor_node(
                &mut divisibility_graph,
                Factor::<&str, &str>::from(digits_or_expr),
                factor_finder,
                &mut number_facts_map,
                None,
                Some(id),
            ),
            _ => {
                let (root_node, _) = add_factor_node(
                    &mut divisibility_graph,
                    Factor::from(known_factors.iter().join("*")).as_ref(),
                    factor_finder,
                    &mut number_facts_map,
                    None,
                    Some(id),
                );
                digits_or_expr_full.push(root_node);
                let root_factors = UpToDate(if known_factors.len() > 1 {
                    known_factors
                        .into_iter()
                        .map(|known_factor| {
                            let (factor_vid, added) = add_factor_node(
                                &mut divisibility_graph,
                                known_factor.as_ref(),
                                factor_finder,
                                &mut number_facts_map,
                                Some(root_node),
                                known_factor.known_id(),
                            );
                            if added {
                                propagate_divisibility(
                                    &mut divisibility_graph,
                                    factor_vid,
                                    root_node,
                                    false,
                                );
                                digits_or_expr_full.push(factor_vid);
                            } else {
                                warn!("{id}: Tried to add a duplicate node");
                            }
                            factor_vid
                        })
                        .collect()
                } else {
                    vec![root_node]
                });
                let root_facts = number_facts_map.get_mut(&root_node).unwrap();
                root_facts.factors_known_to_factordb = root_factors;
                root_facts.last_known_status = status;
                (root_node, true)
            }
        }
    };
    debug!(
        "{id}: Root node for {digits_or_expr} is {} with vertex ID {root_vid:?}",
        divisibility_graph.vertex(root_vid).unwrap()
    );
    if skip_looking_up_known {
        let root_facts = number_facts_map.get_mut(&root_vid).unwrap();
        root_facts.factors_known_to_factordb = UpToDate(vec![root_vid]);
    }
    let mut factor_found = false;
    let mut accepted_factors = 0;
    for factor_vid in digits_or_expr_full.into_iter().rev() {
        factor_found |= !add_factors_to_graph(
            http,
            factor_finder,
            &mut divisibility_graph,
            &mut number_facts_map,
            root_vid,
            factor_vid,
        )
        .await
        .is_empty();
    }
    if !factor_found {
        info!("{id}: No factors to submit");
        return false;
    }
    // Simplest case: try submitting all factors as factors of the root
    // Sort backwards so that we try to submit largest factors first
    let mut any_failed_retryably = false;
    let known_factors = divisibility_graph
        .vertices()
        .sorted_by(|v1, v2| compare(&number_facts_map, v2, v1))
        .map(|vertex| vertex.id)
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<Box<[_]>>();

    for factor_vid in known_factors.into_iter() {
        let factor = divisibility_graph.vertex(factor_vid).unwrap();
        debug!("{id}: Factor {factor} has vertex ID {factor_vid:?}");
        if factor
            .as_str_non_u128()
            .is_some_and(|expr| expr.contains("..."))
            && number_facts_map
                .get(&factor_vid)
                .unwrap()
                .entry_id
                .is_none()
        {
            // Can't submit a factor that we can't fit into a URL, but can save it in case we find
            // out the ID later
            continue;
        }
        match get_edge(&divisibility_graph, factor_vid, root_vid) {
            Some(Direct) | Some(NotFactor) => {
                // This has been submitted directly to the root already, so it's probably already been
                // factored out of all other divisors.
                continue;
            }
            _ => {}
        }
        match http
            .try_report_factor::<&str, &str, _, _>(&Id(id), factor)
            .await
        {
            AlreadyFullyFactored => return true,
            Accepted => {
                replace_with_or_abort(
                    number_facts_map.get_mut(&root_vid).unwrap(),
                    NumberFacts::marked_stale,
                );
                accepted_factors += 1;
                propagate_divisibility(&mut divisibility_graph, factor_vid, root_vid, false);
            }
            DoesNotDivide => {
                rule_out_divisibility(&mut divisibility_graph, factor_vid, root_vid);
                add_factors_to_graph(
                    http,
                    factor_finder,
                    &mut divisibility_graph,
                    &mut number_facts_map,
                    root_vid,
                    factor_vid,
                )
                .await;
            }
            OtherError => {
                add_factors_to_graph(
                    http,
                    factor_finder,
                    &mut divisibility_graph,
                    &mut number_facts_map,
                    root_vid,
                    root_vid,
                )
                .await;
                if number_facts_map
                    .get(&root_vid)
                    .unwrap()
                    .is_known_fully_factored()
                {
                    return true;
                }
                any_failed_retryably = true;
            }
        }
    }
    if !any_failed_retryably {
        info!("{id}: {accepted_factors} factors accepted in a single pass");
        return accepted_factors > 0;
    }
    let mut iters_without_progress = 0;
    // Sort backwards so that we try to submit largest factors first
    let mut factors_to_submit = divisibility_graph
        .vertices()
        .sorted_by(|v1, v2| compare(&number_facts_map, v2, v1))
        .map(|vertex| vertex.id)
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<VecDeque<_>>();
    'graph_iter: while !factors_to_submit.is_empty() {
        let node_count = divisibility_graph.vertex_count();
        let edge_count = divisibility_graph.edge_count();
        let complete_graph_edge_count = complete_graph_edge_count::<Directed>(node_count);
        if edge_count == complete_graph_edge_count
            || factors_to_submit.is_empty()
            || iters_without_progress >= node_count * SUBMIT_FACTOR_MAX_ATTEMPTS
        {
            info!("{id}: {accepted_factors} factors accepted");
            // Graph is fully connected, meaning none are left to try
            return accepted_factors > 0;
        }
        let (direct_divisors, non_factors) = divisibility_graph
            .edges()
            .map(|e| match *e.attr {
                Direct => (1, 0),
                NotFactor => (0, 1),
                _ => (0, 0),
            })
            .reduce(|(x1, y1), (x2, y2)| (x1 + x2, y1 + y2))
            .unwrap_or((0, 0));
        info!(
            "{id}: Divisibility graph has {node_count} vertices and {edge_count} edges \
            ({:.2}% fully connected). {direct_divisors} confirmed-known divides relations, \
            {non_factors} ruled out. \
        {accepted_factors} factors accepted so far. {} fully factored numbers. {} known entry IDs",
            edge_count as f64 * 100.0 / complete_graph_edge_count as f64,
            number_facts_map
                .iter()
                .filter(|(_, facts)| facts.is_known_fully_factored())
                .count(),
            number_facts_map
                .iter()
                .filter(|(_, facts)| facts.entry_id.is_some())
                .count()
        );
        while let Some(factor_vid) = factors_to_submit.pop_front()
            && iters_without_progress < node_count * SUBMIT_FACTOR_MAX_ATTEMPTS
        {
            iters_without_progress += 1;
            if is_known_factor(&divisibility_graph, factor_vid, root_vid)
                && number_facts_map.get(&factor_vid).unwrap().lower_bound_log10
                    > number_facts_map.get(&root_vid).unwrap().upper_bound_log10 / 2
            {
                // Already a known factor of root, and can't be a factor through any remaining path due to size
                continue;
            }
            // root can't be a factor of any other number we'll encounter
            rule_out_divisibility(&mut divisibility_graph, root_vid, factor_vid);
            // elided numbers and numbers over 65500 digits without an expression form can only
            // be submitted as factors, even if their IDs are known
            // however, this doesn't affect the divisibility graph because the ID may be found
            // later
            let factor = divisibility_graph.vertex(factor_vid).unwrap();
            if factor
                .as_str_non_u128()
                .is_some_and(|expr| expr.contains("..."))
            {
                factors_to_submit.push_back(factor_vid);
                continue;
            }
            let dest_factors = divisibility_graph
                .vertices()
                .sorted_by(|v1, v2| compare(&number_facts_map, v1, v2))
                .map(|vertex| vertex.id)
                .filter(|dest_vid|
                    // if factor == dest, the relation is trivial
                    factor_vid != *dest_vid
                        // if this edge exists, FactorDB already knows whether factor is a factor of dest
                        && get_edge(&divisibility_graph, factor_vid, *dest_vid).is_none())
                .collect::<Box<[_]>>();
            if dest_factors.is_empty() {
                continue;
            };
            for cofactor_vid in dest_factors.into_iter().rev() {
                // Try to submit to largest cofactors first
                if is_known_factor(&divisibility_graph, factor_vid, cofactor_vid) {
                    // This factor already known.
                    // If transitive, submit to a smaller cofactor instead.
                    // If direct, nothing left to do.
                    propagate_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid, true);
                    continue;
                }
                let facts = number_facts_map.get(&factor_vid).unwrap();
                match facts.factors_known_to_factordb {
                    UpToDate(ref already_known_factors)
                    | NotUpToDate(ref already_known_factors) => {
                        if already_known_factors.contains(&factor_vid) {
                            propagate_divisibility(
                                &mut divisibility_graph,
                                factor_vid,
                                cofactor_vid,
                                false,
                            );
                            continue;
                        } else if facts.is_final() {
                            rule_out_divisibility(
                                &mut divisibility_graph,
                                factor_vid,
                                cofactor_vid,
                            );
                            continue;
                        }
                    }
                    FactorsKnownToFactorDb::NotQueried => {}
                }
                let factor = divisibility_graph.vertex(factor_vid).unwrap();
                let cofactor = divisibility_graph.vertex(cofactor_vid).unwrap();
                if !factor.may_be_proper_divisor_of(cofactor) {
                    debug!(
                        "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                        smaller or equal or fails last-digit test"
                    );
                    rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                    continue;
                }
                // u128s are already fully factored
                if let Numeric(_) = cofactor {
                    debug!(
                        "{id}: Skipping submission of {factor} to {cofactor} because the number is too small"
                    );
                    propagate_divisibility(
                        &mut divisibility_graph,
                        factor_vid,
                        cofactor_vid,
                        false,
                    );
                    continue;
                }
                let cofactor_facts = number_facts_map.get(&cofactor_vid).unwrap();
                if cofactor_facts.is_known_fully_factored() {
                    debug!(
                        "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                    already fully factored"
                    );
                    if !cofactor_facts.needs_update() {
                        rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                    }
                    continue;
                }
                if let UpToDate(ref known_factor_vids) | NotUpToDate(ref known_factor_vids) =
                    cofactor_facts.factors_known_to_factordb
                    && !known_factor_vids.is_empty()
                {
                    let known_factor_statuses: Vec<_> = known_factor_vids
                        .iter()
                        .map(|known_factor_vid| {
                            (
                                *known_factor_vid,
                                get_edge(&divisibility_graph, factor_vid, *known_factor_vid),
                            )
                        })
                        .collect();
                    let (possible_factors, unknown_non_factors): (Vec<_>, Vec<_>) =
                        known_factor_statuses
                            .iter()
                            .filter(|(_, divisibility)| *divisibility != Some(NotFactor))
                            .partition(|(known_factor_vid, _)| {
                                factor.may_be_proper_divisor_of(
                                    divisibility_graph.vertex(known_factor_vid).unwrap(),
                                ) && facts.lower_bound_log10
                                    <= number_facts_map
                                        .get(known_factor_vid)
                                        .unwrap()
                                        .upper_bound_log10
                            });
                    if possible_factors.is_empty() {
                        // No possible path from factor to cofactor
                        for (unknown_non_factor, _) in unknown_non_factors {
                            rule_out_divisibility(
                                &mut divisibility_graph,
                                factor_vid,
                                unknown_non_factor,
                            );
                        }
                        rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                        continue;
                    } else if possible_factors
                        .into_iter()
                        .all(|(_, divisibility)| divisibility == Some(Direct))
                    {
                        // Submit to one of the known_factors instead
                        propagate_divisibility(
                            &mut divisibility_graph,
                            factor_vid,
                            cofactor_vid,
                            true,
                        );
                        continue;
                    }
                }
                let cofactor_upper_bound = cofactor_facts.upper_bound_log10.saturating_sub(
                    divisibility_graph
                        .neighbors_directed(cofactor_vid, Incoming)
                        .map(|existing_factor| {
                            number_facts_map
                                .get(&existing_factor.id)
                                .unwrap()
                                .lower_bound_log10
                        })
                        .sum(),
                );
                if facts.lower_bound_log10 > cofactor_upper_bound {
                    debug!(
                        "Skipping submission of {factor} to {cofactor} because {cofactor} is \
                        smaller based on log10 bounds"
                    );
                    rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                    continue;
                }
                if is_known_factor(&divisibility_graph, cofactor_vid, factor_vid) {
                    debug!(
                        "{id}: Skipping submission of {factor} to {cofactor} because {cofactor} is transitively a factor of {factor}"
                    );
                    // factor is transitively divisible by dest_factor
                    propagate_divisibility(&mut divisibility_graph, cofactor_vid, factor_vid, true);
                    continue;
                }
                // elided numbers and numbers over 65500 digits without an expression form can only
                // be used as dests if their IDs are known
                // however, this doesn't affect the divisibility graph because the ID may be found
                // later
                if cofactor
                    .as_str_non_u128()
                    .is_some_and(|expr| expr.contains("..."))
                    && number_facts_map
                        .get(&cofactor_vid)
                        .unwrap()
                        .entry_id
                        .is_none()
                {
                    debug!(
                        "{id}: Can't submit to {cofactor} right now because we don't know its full specifier"
                    );
                    continue;
                }
                let dest_specifier = as_specifier(cofactor_vid, cofactor, &number_facts_map);
                match http
                    .try_report_factor(
                        &dest_specifier,
                        divisibility_graph.vertex(factor_vid).unwrap(),
                    )
                    .await
                {
                    AlreadyFullyFactored => {
                        if cofactor_vid == root_vid {
                            warn!("{id}: Already fully factored");
                            return true;
                        }
                        let dest_facts = number_facts_map.get_mut(&cofactor_vid).unwrap();
                        if !dest_facts.is_known_fully_factored() {
                            mark_fully_factored(dest_facts);
                            for dest_subfactor_vid in dest_facts.factors_known_to_factordb.to_vec()
                            {
                                mark_fully_factored(
                                    number_facts_map.get_mut(&dest_subfactor_vid).unwrap(),
                                );
                            }
                        }
                        continue;
                    }
                    Accepted => {
                        replace_with_or_abort(
                            number_facts_map.get_mut(&cofactor_vid).unwrap(),
                            NumberFacts::marked_stale,
                        );
                        accepted_factors += 1;
                        iters_without_progress = 0;
                        propagate_divisibility(
                            &mut divisibility_graph,
                            factor_vid,
                            cofactor_vid,
                            false,
                        );
                        // Move newly-accepted factor to the back of the list
                        factors_to_submit.push_back(factor_vid);
                        continue 'graph_iter;
                    }
                    DoesNotDivide => {
                        rule_out_divisibility(&mut divisibility_graph, factor_vid, cofactor_vid);
                        factors_to_submit.extend_front(
                            add_factors_to_graph(
                                http,
                                factor_finder,
                                &mut divisibility_graph,
                                &mut number_facts_map,
                                root_vid,
                                factor_vid,
                            )
                            .await
                            .into_iter()
                            .sorted_by(|v1, v2| {
                                compare(
                                    &number_facts_map,
                                    &VertexRef {
                                        id: *v2,
                                        attr: divisibility_graph.vertex(v2).unwrap(),
                                    },
                                    &VertexRef {
                                        id: *v1,
                                        attr: divisibility_graph.vertex(v1).unwrap(),
                                    },
                                )
                            }),
                        );
                    }
                    OtherError => {
                        if !add_factors_to_graph(
                            http,
                            factor_finder,
                            &mut divisibility_graph,
                            &mut number_facts_map,
                            root_vid,
                            cofactor_vid,
                        )
                        .await
                        .is_empty()
                        {
                            if number_facts_map
                                .get(&root_vid)
                                .unwrap()
                                .is_known_fully_factored()
                            {
                                return true;
                            }
                            iters_without_progress = 0;
                        }
                    }
                }
            }
        }
    }

    for factor_vid in divisibility_graph
        .vertices_by_id()
        .filter(|factor_vid| *factor_vid != root_vid)
        .collect::<Box<[_]>>()
        .into_iter()
    {
        let factor = divisibility_graph.vertex(factor_vid).unwrap();
        if factor
            .as_str_non_u128()
            .is_some_and(|expr| expr.contains("..."))
        {
            debug!(
                "{id}: Skipping writing {factor} to failed-submission file because we don't know its specifier"
            );
            continue;
        }
        if is_known_factor(&divisibility_graph, factor_vid, root_vid) {
            debug!("{id}: {factor} was successfully submitted");
            continue;
        }
        match FAILED_U_SUBMISSIONS_OUT
            .get()
            .unwrap()
            .lock()
            .await
            .write_fmt(format_args!("{id},{}\n", factor))
        {
            Ok(_) => warn!("{id}: wrote {} to failed submissions file", factor),
            Err(e) => error!(
                "{id}: failed to write {} to failed submissions file: {e}",
                factor
            ),
        }
    }
    accepted_factors > 0
}

fn mark_fully_factored(facts: &mut NumberFacts) {
    facts.checked_for_listed_algebraic = true;
    facts.checked_in_factor_finder = true;
    facts.expression_form_checked_in_factor_finder = true;
    facts.last_known_status = if let UpToDate(factors) = &facts.factors_known_to_factordb
        && factors.len() == 1
    {
        Some(Prime)
    } else {
        Some(FullyFactored)
    };
}

async fn add_factors_to_graph(
    http: &FactorDbClient,
    factor_finder: &FactorFinder,
    divisibility_graph: &mut DivisibilityGraph,
    number_facts_map: &mut BTreeMap<VertexId, NumberFacts>,
    root_vid: VertexId,
    factor_vid: VertexId,
) -> Box<[VertexId]> {
    let facts = number_facts_map.get(&factor_vid).unwrap();
    let mut added = BTreeSet::new();
    let mut id = facts.entry_id;

    // First, check factordb.com/api for already-known factors
    if facts.needs_update() {
        let factor_specifier = as_specifier(
            factor_vid,
            divisibility_graph.vertex(&factor_vid).unwrap(),
            number_facts_map,
        );
        let ProcessedStatusApiResponse {
            status,
            factors: known_factors,
            id: new_id,
        } = http
            .known_factors_as_digits(factor_specifier, true, false)
            .await;
        let known_factor_count = known_factors.len();
        if known_factor_count == 1 {
            let known_factor = known_factors.iter().next().unwrap();
            let existing_factor = divisibility_graph.vertex(&factor_vid).unwrap();
            if *known_factor != *existing_factor {
                merge_equivalent_expressions(
                    factor_finder,
                    divisibility_graph,
                    Some(root_vid),
                    number_facts_map,
                    factor_vid,
                    known_factor.clone(),
                );
            }
        }
        let new_known_factors: Vec<_> = known_factors
            .into_iter()
            .map(|known_factor| {
                let (known_factor_vid, is_new) = add_factor_node(
                    divisibility_graph,
                    known_factor.as_ref(),
                    factor_finder,
                    number_facts_map,
                    Some(root_vid),
                    known_factor.known_id(),
                );
                propagate_divisibility(divisibility_graph, known_factor_vid, factor_vid, false);
                if is_new {
                    added.insert(known_factor_vid);
                }
                known_factor_vid
            })
            .collect();
        let facts = number_facts_map.get_mut(&factor_vid).unwrap();
        let old_factors: BTreeSet<_> = facts.factors_known_to_factordb.iter().collect();
        added.extend(
            new_known_factors
                .iter()
                .filter(|factor_vid| !old_factors.contains(factor_vid)),
        );
        if known_factor_count > 0 {
            facts.factors_known_to_factordb = UpToDate(new_known_factors);
        }
        facts.entry_id = facts.entry_id.or(new_id);
        if let Some(status) = status {
            facts.last_known_status = Some(status);
            if status == Prime || status == FullyFactored {
                mark_fully_factored(facts);
            }
            if status == Prime {
                for other_vertex in divisibility_graph
                    .vertices_by_id()
                    .filter(|other_vid| *other_vid != factor_vid)
                    .collect::<Box<[_]>>()
                    .into_iter()
                {
                    rule_out_divisibility(divisibility_graph, other_vertex, factor_vid);
                }
            }
        }
        id = facts.entry_id;
    }

    // Next, check factordb.com/frame_moreinfo.php for listed algebraic factors
    if let Some(id) = id {
        let facts = number_facts_map.get(&factor_vid).unwrap();
        if !facts.checked_for_listed_algebraic {
            let root = divisibility_graph.vertex(&factor_vid).unwrap();
            if let Some(known_id) = root.known_id()
                && id != known_id
            {
                error!("Tried to look up {root} using a smaller number's id {id}");
            } else {
                info!("{id}: Checking for listed algebraic factors");
                // Links before the "Is factor of" header are algebraic factors; links after it aren't
                let url =
                    format!("https://factordb.com/frame_moreinfo.php?id={id}").into_boxed_str();
                let result = http.try_get_and_decode(&url).await;
                if let Some(result) = result
                    && let Some(listed_algebraic) = result.split("Is factor of").next()
                {
                    number_facts_map
                        .get_mut(&factor_vid)
                        .unwrap()
                        .checked_for_listed_algebraic = true;
                    let algebraic_factors = http.read_ids_and_exprs(listed_algebraic);
                    for (subfactor_entry_id, factor_digits_or_expr) in algebraic_factors {
                        let factor: Factor<&str, &str> = factor_digits_or_expr.into();
                        let (subfactor_vid, is_new) = add_factor_node(
                            divisibility_graph,
                            factor,
                            factor_finder,
                            number_facts_map,
                            Some(factor_vid),
                            Some(subfactor_entry_id),
                        );
                        debug!(
                            "{id}: Factor {factor} has entry ID {subfactor_entry_id} and vertex ID {subfactor_vid:?}"
                        );
                        if is_new {
                            added.insert(subfactor_vid);
                        }
                    }
                } else {
                    error!("{id}: Failed to decode algebraic-factor list");
                }
            }
        }
    }

    // Next, check if factor_finder can find factors
    let facts = number_facts_map.get(&factor_vid).unwrap();
    if !facts.checked_in_factor_finder {
        added.extend(add_factor_finder_factor_vertices_to_graph(
            factor_finder,
            divisibility_graph,
            Some(root_vid),
            number_facts_map,
            factor_vid,
            facts.entry_id,
        ));
    }
    let facts = number_facts_map.get_mut(&factor_vid).unwrap();
    facts.checked_in_factor_finder = true;

    if let Some(entry_id) = facts.entry_id
        && !facts.expression_form_checked_in_factor_finder
        && let Some(expression_form) = http.try_get_expression_form(entry_id).await
    {
        let expression_form: Factor<&str, &str> = Factor::from(expression_form.as_str());
        added.extend(
            factor_finder
                .find_unique_factors(&expression_form)
                .into_iter()
                .map(|new_factor| {
                    add_factor_node(
                        divisibility_graph,
                        new_factor.as_ref(),
                        factor_finder,
                        number_facts_map,
                        Some(root_vid),
                        Some(entry_id),
                    )
                })
                .flat_map(|(vid, added)| if added { Some(vid) } else { None }),
        );
        let facts = number_facts_map.get_mut(&factor_vid).unwrap();
        facts.expression_form_checked_in_factor_finder = true;
    }

    added.into_iter().collect()
}

fn as_specifier<'a>(
    factor_vid: VertexId,
    factor: &'a OwnedFactor,
    number_facts_map: &BTreeMap<VertexId, NumberFacts>,
) -> NumberSpecifier<&'a str, &'a str> {
    if let Some(factor_entry_id) = number_facts_map
        .get(&factor_vid)
        .and_then(|facts| facts.entry_id)
    {
        debug!(
            "as_specifier: got entry ID {factor_entry_id} for factor {factor} with vertex ID {factor_vid:?}"
        );
        Id(factor_entry_id)
    } else {
        factor
            .known_id()
            .map(Id)
            .unwrap_or_else(|| Expression(factor.as_ref()))
    }
}

fn merge_equivalent_expressions(
    factor_finder: &FactorFinder,
    divisibility_graph: &mut DivisibilityGraph,
    root_vid: Option<VertexId>,
    number_facts_map: &mut BTreeMap<VertexId, NumberFacts>,
    factor_vid: VertexId,
    equivalent: OwnedFactor,
) -> Vec<VertexId> {
    let current = divisibility_graph.vertex(&factor_vid).unwrap();
    if equivalent == *current {
        number_facts_map
            .get(&factor_vid)
            .unwrap()
            .factors_known_to_factordb
            .to_vec()
    } else {
        info!("Merging equivalent expressions {current} and {equivalent}");
        let current_expr = current.as_str();
        let current_len = if current_expr.contains("...") {
            usize::MAX // replace elided numbers with full ones ASAP
        } else {
            current_expr.len()
        };
        let facts = number_facts_map.get_mut(&factor_vid).unwrap();
        let entry_id = facts.entry_id;
        let mut new_factor_vids = facts.factors_known_to_factordb.to_vec();
        if !replace(&mut facts.checked_in_factor_finder, true) {
            new_factor_vids.extend(add_factor_finder_factor_vertices_to_graph(
                factor_finder,
                divisibility_graph,
                root_vid,
                number_facts_map,
                factor_vid,
                entry_id,
            ));
        }
        let (new_lower_bound_log10, new_upper_bound_log10) =
            factor_finder.estimate_log10(&equivalent);
        let facts = number_facts_map.get_mut(&factor_vid).unwrap();
        facts.lower_bound_log10 = facts.lower_bound_log10.max(new_lower_bound_log10);
        facts.upper_bound_log10 = facts.upper_bound_log10.min(new_upper_bound_log10);
        let equivalent_expr = equivalent.as_str();
        if !equivalent_expr.contains("...") && equivalent_expr.len() < current_len {
            let _ = replace(
                divisibility_graph.vertex_mut(factor_vid).unwrap(),
                equivalent,
            );
        }

        // New expression may allow factor_finder to find factors it couldn't before
        let entry_id = facts.entry_id;
        new_factor_vids.extend(add_factor_finder_factor_vertices_to_graph(
            factor_finder,
            divisibility_graph,
            root_vid,
            number_facts_map,
            factor_vid,
            entry_id,
        ));
        new_factor_vids
    }
}

fn add_factor_finder_factor_vertices_to_graph(
    factor_finder: &FactorFinder,
    divisibility_graph: &mut DivisibilityGraph,
    root_vid: Option<VertexId>,
    number_facts_map: &mut BTreeMap<VertexId, NumberFacts>,
    factor_vid: VertexId,
    entry_id: Option<u128>,
) -> Vec<VertexId> {
    factor_finder
        .find_unique_factors(divisibility_graph.vertex(&factor_vid).unwrap())
        .into_iter()
        .map(|new_factor| {
            let entry_id = if new_factor == *divisibility_graph.vertex(&factor_vid).unwrap() {
                entry_id
            } else {
                new_factor.known_id()
            };
            add_factor_node(
                divisibility_graph,
                new_factor.as_ref(),
                factor_finder,
                number_facts_map,
                root_vid,
                entry_id,
            )
        })
        .flat_map(|(vid, added)| if added { Some(vid) } else { None })
        .collect()
}
