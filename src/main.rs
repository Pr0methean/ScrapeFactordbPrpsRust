#![allow(stable_features)]
#![allow(clippy::too_many_arguments)]
#![feature(duration_constructors_lite)]
#![feature(file_buffered)]
#![feature(const_destruct)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(never_type)]
#![feature(btree_set_entry)]
#![feature(str_as_str)]

mod algebraic;
mod channel;
mod net;
mod shutdown;

use crate::NumberSpecifier::{Expression, Id};
use crate::ReportFactorResult::{Accepted, AlreadyFullyFactored, DoesNotDivide, OtherError};
use crate::UnknownPrpCheckResult::{
    Assigned, IneligibleForPrpCheck, OtherRetryableFailure, PleaseWait,
};
use crate::algebraic::Factor::Numeric;
use crate::algebraic::NumberStatus::FullyFactored;
use crate::algebraic::{Factor, FactorFinder, ProcessedStatusApiResponse};
use crate::net::ResourceLimits;
use crate::shutdown::{Shutdown, handle_signals};
use async_backtrace::framed;
use channel::PushbackReceiver;
use compact_str::{CompactString};
use const_format::formatcp;
use cuckoofilter::CuckooFilter;
use gryf::algo::ShortestPaths;
use gryf::core::facts::complete_graph_edge_count;
use gryf::core::id::{DefaultId, VertexId};
use gryf::core::marker::{Directed, Direction, Incoming, Outgoing};
use gryf::core::{EdgeSet, GraphAdd, GraphMut, GraphRef, Neighbors, VertexSet};
use gryf::storage::AdjMatrix;
use itertools::Itertools;
use log::{debug, error, info, warn};
use net::ThrottlingHttpClient;
use primitive_types::U256;
use rand::seq::SliceRandom;
use rand::{Rng, rng};
use regex::Regex;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::backtrace::Backtrace;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display, Formatter};
use std::fs::File;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io::Write;
use std::num::{NonZeroU32, NonZeroU128};
use std::ops::Add;
use std::panic;
use std::process::exit;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::sync::atomic::{AtomicBool, AtomicUsize};
use arcstr::{literal, ArcStr};
use gryf::Graph;
use tokio::sync::mpsc::error::TrySendError::Full;
use tokio::sync::mpsc::{OwnedPermit, PermitIterator, Sender, channel};
use tokio::sync::{Mutex, OnceCell, oneshot};
use tokio::task::JoinHandle;
use tokio::time::{Duration, Instant, sleep, sleep_until, timeout};
use tokio::{select, task};

type DivisibilityGraph = Graph<Factor<ArcStr, CompactString>, bool, Directed, AdjMatrix<Factor<ArcStr, CompactString>, bool, Directed, DefaultId>>;

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

#[framed]
async fn composites_while_waiting(
    end: Instant,
    http: &ThrottlingHttpClient,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    c_filter: &mut CuckooFilter<DefaultHasher>,
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

#[framed]
async fn check_composite(
    http: &ThrottlingHttpClient,
    c_filter: &mut CuckooFilter<DefaultHasher>,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
    id: u128,
    digits_or_expr: CompactString,
    return_permit: OwnedPermit<CompositeCheckTask>,
) -> bool {
    if c_filter.contains(&id) {
        info!("{id}: Skipping duplicate C");
        return true;
    }
    let checks_triggered = if http
        .try_get_and_decode(format!("https://factordb.com/sequences.php?check={id}").into())
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
    } = factor_finder
        .known_factors_as_digits::<&str, &str>(http, Id(id), false, true)
        .await;
    if factors.is_empty() {
        if status == Some(FullyFactored) {
            warn!("{id}: Already fully factored");
            return true;
        } else {
            return_permit.send(CompositeCheckTask { id, digits_or_expr });
            info!("{id}: Requeued C");
            false
        }
    } else {
        let subfactors_may_have_algebraic = factors.len() > 1;
        let mut factors_submitted = false;
        let mut factors_to_dispatch = Vec::with_capacity(factors.len());
        for factor in factors {
            if let Some(factor_str) = factor.as_str_non_u128() {
                if find_and_submit_factors(
                    http,
                    id,
                    factor_str,
                    factor_finder,
                    id_and_expr_regex,
                    true,
                    !subfactors_may_have_algebraic,
                )
                .await
                {
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

#[derive(Ord, PartialOrd, Eq, PartialEq)]
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

#[framed]
async fn get_prp_remaining_bases(
    id: u128,
    http: &ThrottlingHttpClient,
    bases_regex: &Regex,
    nm1_regex: &Regex,
    np1_regex: &Regex,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    c_filter: &mut CuckooFilter<DefaultHasher>,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
) -> Result<U256, ()> {
    let mut bases_left = U256::MAX - 3;
    let bases_text = http
        .retrying_get_and_decode(
            format!("https://factordb.com/frame_prime.php?id={id}").into(),
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
        } = factor_finder
            .known_factors_as_digits::<&str, &str>(http, Id(nm1_id), false, false)
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
        } = factor_finder
            .known_factors_as_digits::<&str, &str>(http, Id(np1_id), false, false)
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
        match report_factor::<&str, &str>(http, nm1_id, &Numeric(2)).await {
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
        match report_factor::<&str, &str>(http, np1_id, &Numeric(2)).await {
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
        && !nm1_known_to_divide_3
        && !np1_known_to_divide_3
    {
        // N wouldn't be PRP if it was a multiple of 3, so N-1 xor N+1 must be a multiple of 3
        match report_factor::<&str, &str>(http, nm1_id, &Numeric(3)).await {
            AlreadyFullyFactored => {
                info!("{id}: N-1 (ID {nm1_id}) is fully factored!");
                prove_by_nm1(id, http).await;
                return Ok(U256::from(0));
            }
            Accepted => {}
            _ => match report_factor::<&str, &str>(http, np1_id, &Numeric(3)).await {
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
    let status_text = http
        .retrying_get_and_decode(
            format!("https://factordb.com/index.php?open=Prime&ct=Proof&id={id}").into(),
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

#[framed]
async fn prove_by_np1(id: u128, http: &ThrottlingHttpClient) {
    let _ = http
        .retrying_get_and_decode(
            format!("https://factordb.com/index.php?open=Prime&np1=Proof&id={id}").into(),
            RETRY_DELAY,
        )
        .await;
}

#[framed]
async fn prove_by_nm1(id: u128, http: &ThrottlingHttpClient) {
    let _ = http
        .retrying_get_and_decode(
            format!("https://factordb.com/index.php?open=Prime&nm1=Proof&id={id}").into(),
            RETRY_DELAY,
        )
        .await;
}

const MAX_BASES_BETWEEN_RESOURCE_CHECKS: usize = 127;

const MIN_BASES_BETWEEN_RESOURCE_CHECKS: usize = 16;

const MAX_CPU_BUDGET_TENTHS: usize = 6000;
const UNKNOWN_STATUS_CHECK_BACKOFF: Duration = Duration::from_mins(5);
static CPU_TENTHS_SPENT_LAST_CHECK: AtomicUsize = AtomicUsize::new(MAX_CPU_BUDGET_TENTHS);
static NO_RESERVE: AtomicBool = AtomicBool::new(false);

#[inline]
#[framed]
async fn do_checks(
    mut prp_receiver: PushbackReceiver<CheckTask>,
    mut u_receiver: PushbackReceiver<CheckTask>,
    mut c_receiver: PushbackReceiver<CompositeCheckTask>,
    mut c_filter: CuckooFilter<DefaultHasher>,
    http: ThrottlingHttpClient,
    factor_finder: FactorFinder,
    id_and_expr_regex: Regex,
    mut shutdown_receiver: Shutdown,
) {
    info!("do_checks task starting");
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
            _ = shutdown_receiver.recv() => {
                warn!("do_checks received shutdown signal; exiting");
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
                    for base in (0..=(u8::MAX as usize)).filter(|i| bases_left.bit(*i)) {
                        let url = ArcStr::from(format!("https://factordb.com/index.php?id={id}&open=prime&basetocheck={base}"));
                        let text = http.retrying_get_and_decode(url.clone(), RETRY_DELAY).await;
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
#[framed]
async fn try_handle_unknown(
    http: &ThrottlingHttpClient,
    u_status_regex: &Regex,
    many_digits_regex: &Regex,
    id: u128,
    next_attempt: &mut Instant,
) -> UnknownPrpCheckResult {
    let url = ArcStr::from(format!("https://factordb.com/index.php?id={id}&prp=Assign+to+worker"));
    let result = http.retrying_get_and_decode(url, RETRY_DELAY).await;
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

#[framed]
async fn throttle_if_necessary(
    http: &ThrottlingHttpClient,
    c_receiver: &mut PushbackReceiver<CompositeCheckTask>,
    bases_before_next_cpu_check: &mut usize,
    sleep_first: bool,
    c_filter: &mut CuckooFilter<DefaultHasher>,
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
        composites_while_waiting(
            resets_at,
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
#[framed]
async fn queue_composites(
    id_and_expr_regex: &Regex,
    http: &ThrottlingHttpClient,
    c_sender: &Sender<CompositeCheckTask>,
    digits: Option<NonZeroU128>,
) -> JoinHandle<()> {
    let mut c_sent = 0;
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
            format!("https://factordb.com/listtype.php?t=3&perpage={results_per_page}&start={start}&mindig={digits}").into()
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
    let mut c_tasks: Box<[_]> = id_and_expr_regex
        .captures_iter(&composites_page)
        .flat_map(|capture| {
            Some(CompositeCheckTask {
                id: capture[1].parse::<u128>().ok()?,
                digits_or_expr: capture[2].into(),
            })
        })
        .unique()
        .collect();
    c_tasks.shuffle(&mut rng());
    let mut c_buffered = Vec::with_capacity(c_tasks.len());
    for c_task in c_tasks {
        if let Err(Full(c_id)) = c_sender.try_send(c_task) {
            c_buffered.push(c_id);
        } else {
            c_sent += 1;
        }
    }
    if c_buffered.is_empty() {
        info!("Sent {c_sent} C's to channel");
        task::spawn(async {})
    } else {
        info!(
            "Sent {c_sent} C's to channel; buffering {} more",
            c_buffered.len()
        );
        let c_sender = c_sender.clone();
        task::spawn(async_backtrace::location!().frame(async move {
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
        }))
    }
}

// One worker thread for do_checks(), one for main(), one for c_buffer_task, one for handle_signals
#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
#[framed]
async fn main() -> anyhow::Result<()> {
    let (shutdown_sender, mut shutdown_receiver) = Shutdown::new();
    let (installed_sender, installed_receiver) = oneshot::channel();
    simple_log::console("debug").unwrap();
    task::spawn(
        async_backtrace::location!().frame(handle_signals(shutdown_sender, installed_sender)),
    );
    let default_panic_hook = panic::take_hook();
    panic::set_hook(Box::new(move |panic_info| {
        error!("\n{}\n", async_backtrace::taskdump_tree(true));
        default_panic_hook(panic_info); // Call the original panic hook
    }));
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
    let id_regex = Regex::new("index\\.php\\?id=([0-9]+)")?;
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
    let c_filter = CuckooFilter::with_capacity(2500);
    let id_and_expr_regex = Regex::new("index\\.php\\?id=([0-9]+)\"><font[^>]*>([^<]+)</font>")?;
    let factor_finder = FactorFinder::new();
    let http = ThrottlingHttpClient::new(
        rph_limit,
        max_concurrent_requests,
        shutdown_receiver.clone(),
    );
    let id_and_expr_regex_clone = id_and_expr_regex.clone();
    let http_clone = http.clone();
    let c_sender_clone = c_sender.clone();
    let mut c_buffer_task: JoinHandle<()> =
        task::spawn(async_backtrace::location!().frame(async move {
            queue_composites(
                &id_and_expr_regex_clone,
                &http_clone,
                &c_sender_clone,
                c_digits,
            )
            .await
            .await
            .unwrap();
        }));
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
        c_filter,
        http.clone(),
        factor_finder.clone(),
        id_and_expr_regex.clone(),
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
                info!("Ready to search for PRP's after {:?}", Instant::now() - select_start);
                let mut results_per_page = PRP_RESULTS_PER_PAGE;
                let mut results_text = None;
                while results_text.is_none() && results_per_page > 0 {
                    let prp_search_url = format!("https://factordb.com/listtype.php?t=1&mindig={MIN_DIGITS_IN_PRP}&perpage={results_per_page}&start={prp_start}").into();
                    let Some(text) = http.try_get_and_decode(prp_search_url).await else {
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
                let mut prp_permits = prp_permits?;
                for prp_id in id_regex
                    .captures_iter(&results_text)
                    .map(|result| result[1].parse::<u128>().ok())
                    .unique()
                {
                    let Some(prp_id) = prp_id else {
                        error!("Invalid PRP ID found");
                        continue;
                    };
                    if let Ok(false) = prp_filter.test_and_add(&prp_id) {
                        warn!("{prp_id}: Skipping duplicate PRP");
                        continue;
                    }
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
            u_permits = u_sender.reserve_many(U_RESULTS_PER_PAGE) => {
                info!("Ready to search for U's after {:?}", Instant::now() - select_start);
                queue_unknowns(&id_and_expr_regex, &http, u_digits, u_permits?, &mut u_filter, &factor_finder).await;
            }
        }
        if new_c_buffer_task {
            c_buffer_task = queue_composites(&id_and_expr_regex, &http, &c_sender, c_digits).await;
        }
    }
}

#[framed]
async fn queue_unknowns(
    id_and_expr_regex: &Regex,
    http: &ThrottlingHttpClient,
    u_digits: Option<NonZeroU128>,
    u_permits: PermitIterator<'_, CheckTask>,
    u_filter: &mut CuckooFilter<DefaultHasher>,
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

#[framed]
async fn try_queue_unknowns<'a>(
    id_and_expr_regex: &Regex,
    http: &ThrottlingHttpClient,
    u_digits: Option<NonZeroU128>,
    mut u_permits: PermitIterator<'a, CheckTask>,
    u_filter: &mut CuckooFilter<DefaultHasher>,
    factor_finder: &FactorFinder,
) -> Result<(), PermitIterator<'a, CheckTask>> {
    let mut rng = rng();
    let digits = u_digits.unwrap_or_else(|| {
        rng.random_range(U_MIN_DIGITS..=U_MAX_DIGITS)
            .try_into()
            .unwrap()
    });
    let u_start = rng.random_range(0..=MAX_START);
    let u_search_url = format!("{U_SEARCH_URL_BASE}{u_start}&mindig={}", digits.get()).into();
    let Some(results_text) = http.try_get_and_decode(u_search_url).await else {
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
        if u_filter.contains(&u_id_bytes) {
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
            let _ = u_filter.add(&u_id_bytes);
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

#[derive(Debug, Eq, PartialEq)]
enum ReportFactorResult {
    Accepted,
    DoesNotDivide,
    AlreadyFullyFactored,
    OtherError,
}

#[framed]
async fn try_report_factor<
    T: AsRef<str>,
    U: AsRef<str> + Display,
    V: AsRef<str>,
    W: AsRef<str> + Display,
>(
    http: &ThrottlingHttpClient,
    u_id: &NumberSpecifier<T, U>,
    factor: &Factor<V, W>,
) -> ReportFactorResult {
    if let Expression(Numeric(_)) = u_id {
        return AlreadyFullyFactored;
    }
    if let Id(n) = u_id
        && *n <= MAX_ID_EQUAL_TO_VALUE
    {
        return AlreadyFullyFactored;
    }
    let number = if let Expression(expr) = u_id {
        Some(expr.as_str())
    } else {
        None
    };
    let request_builder = match http
        .post(literal!("https://factordb.com/reportfactor.php"))
        .form(&FactorSubmission {
            id: if let Id(id) = u_id { Some(*id) } else { None },
            number,
            factor: factor.as_str()
        }) {
        Ok(builder) => builder,
        Err(e) => {
            error!("Error building request: {e}");
            return OtherError;
        }
    };
    match request_builder.send().await
    {
        Ok(text) => {
            info!("{u_id}: reported a factor of {factor}; response: {text}",);
            return if text.contains("Error") {
                OtherError
            } else if text.contains("submitted") {
                Accepted
            } else if text.contains("fully factored") || text.contains("Number too small") {
                AlreadyFullyFactored
            } else {
                DoesNotDivide
            };
        }
        Err(e) => {
            error!(
                "{u_id}: Failed to get response when submitting {factor}: {e}");
            sleep(RETRY_DELAY).await;
            OtherError
        }
    }
}

#[framed]
async fn report_factor<T: Display + AsRef<str>, U: Display + AsRef<str>>(
    http: &ThrottlingHttpClient,
    u_id: u128,
    factor: &Factor<T, U>,
) -> ReportFactorResult {
    for _ in 0..SUBMIT_FACTOR_MAX_ATTEMPTS {
        let result = try_report_factor::<&str, &str, T, U>(http, &Id(u_id), factor).await;
        if result != OtherError {
            return result;
        }
    }
    match FAILED_U_SUBMISSIONS_OUT
        .get()
        .unwrap()
        .lock()
        .await
        .write_fmt(format_args!("{u_id},{}\n", factor.as_str()))
    {
        Ok(_) => warn!("{u_id}: wrote {factor} to failed submissions file"),
        Err(e) => error!("{u_id}: failed to write {factor} to failed submissions file: {e}"),
    }
    OtherError // factor that we failed to submit may still have been valid
}

const MAX_ID_EQUAL_TO_VALUE: u128 = 999_999_999_999_999_999;

#[framed]
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
    let mut divisibility_graph = DivisibilityGraph::new_directed_in(AdjMatrix::new()).stabilize();
    let mut ids = BTreeMap::new();
    let mut checked_for_known_factors_since_last_submission = BTreeSet::new();
    let mut root_status = None;
    let (root_node, _) = if !skip_looking_up_known && !digits_or_expr.contains("...") {
        add_factor_node(
            &mut divisibility_graph,
            &digits_or_expr.into(),
        )
    } else {
        let ProcessedStatusApiResponse {
            factors: known_factors,
            status,
            ..
        } = factor_finder
            .known_factors_as_digits::<&str, &str>(http, Id(id), false, true)
            .await;
        if status == Some(FullyFactored) {
            warn!("{id}: Already fully factored");
            return true;
        }
        root_status = status;
        match known_factors.len() {
            0 => add_factor_node(
                &mut divisibility_graph,
                &digits_or_expr.into(),
            ),
            _ => {
                let (root_node, _) = add_factor_node(
                    &mut divisibility_graph,
                    &known_factors.iter().join("*").into(),
                );
                digits_or_expr_full.push(root_node);
                if known_factors.len() > 1 {
                    for known_factor in known_factors {
                        let (factor_vid, added) =
                            add_factor_node(&mut divisibility_graph, &known_factor);
                        if added {
                            add_edge_or_log(&mut divisibility_graph, &factor_vid, &root_node, true);
                            digits_or_expr_full.push(factor_vid);
                        } else {
                            warn!("{id}: Tried to add a duplicate node: {known_factor}");
                        }
                    }
                }
                (root_node, true)
            }
        }
    };
    if root_status.is_some() {
        checked_for_known_factors_since_last_submission.insert(root_node);
    }
    debug!("{id}: Root node for {digits_or_expr} is {}", divisibility_graph.vertex(&root_node).unwrap());
    ids.insert(root_node, id);
    let mut factor_found = false;
    let mut accepted_factors = 0;
    let mut already_fully_factored = BTreeSet::new();
    let mut already_checked_for_algebraic = BTreeSet::new();
    let multiple_starting_entries = digits_or_expr_full.len() > 1;
    for factor_vid in digits_or_expr_full.into_iter().rev() {
        let factor = divisibility_graph.vertex(&factor_vid).unwrap().clone();
        factor_found |= add_algebraic_factors_to_graph(
            http,
            if multiple_starting_entries {
                None
            } else {
                Some(id)
            },
            factor_finder,
            id_and_expr_regex,
            skip_looking_up_listed_algebraic,
            &mut divisibility_graph,
            &mut ids,
            &factor,
            &mut already_fully_factored,
            factor_vid,
            &mut checked_for_known_factors_since_last_submission,
        )
        .await;
        already_checked_for_algebraic.insert(factor_vid);
    }
    if !factor_found {
        info!("{id}: No factors to submit");
        return false;
    }
    // Simplest case: try submitting all factors as factors of the root
    let mut any_failed_retryably = false;
    let mut known_factors = divisibility_graph
        .vertices()
        .map(|vertex| (vertex.id, vertex.attr.clone()))
        .filter(|(factor_vid, _)| *factor_vid != root_node)
        .collect::<Box<[_]>>();
    known_factors.sort_by(|(_, factor1), (_, factor2)| factor1.cmp(factor2));
    for (factor_vid, factor) in known_factors
        .into_iter()
        .rev()
    {
        if factor.as_str_non_u128().is_some_and(|expr| expr.contains("..."))
            && !ids.contains_key(&factor_vid)
        {
            // Can't submit a factor that we can't fit into a URL, but can save it in case we find
            // out the ID later
            continue;
        }
        if get_edge(&divisibility_graph, &factor_vid, &root_node) == Some(true) {
            // This has been submitted directly to the root already, so it's probably already been
            // factored out of all other divisors.
            continue;
        }
        match try_report_factor::<&str, &str, _, _>(http, &Id(id), &factor).await {
            AlreadyFullyFactored => return true,
            Accepted => {
                checked_for_known_factors_since_last_submission.remove(&root_node);
                accepted_factors += 1;
                add_edge_or_log(&mut divisibility_graph, &factor_vid, &root_node, true);
            }
            DoesNotDivide => {
                // The root isn't divisible by this "factor", so try to split it up into smaller
                // factors and then we'll submit those instead.
                add_edge_or_log(&mut divisibility_graph, &factor_vid, &root_node, false);
                if already_checked_for_algebraic.insert(factor_vid) {
                    debug!("{id}: Searching for algebraic factors of {factor}");
                    any_failed_retryably |= add_algebraic_factors_to_graph(
                        http,
                        ids.get(&factor_vid).copied(),
                        factor_finder,
                        id_and_expr_regex,
                        skip_looking_up_listed_algebraic,
                        &mut divisibility_graph,
                        &mut ids,
                        &factor,
                        &mut already_fully_factored,
                        factor_vid,
                        &mut checked_for_known_factors_since_last_submission,
                    )
                    .await;
                }
            }
            _ => {
                any_failed_retryably = true;
            }
        }
    }
    if !any_failed_retryably {
        info!("{id}: {accepted_factors} factors accepted in a single pass");
        return accepted_factors > 0;
    }
    let mut iters_without_progress = 0;
    while iters_without_progress < SUBMIT_FACTOR_MAX_ATTEMPTS {
        iters_without_progress += 1;
        let node_count = divisibility_graph.vertex_count();
        let edge_count = divisibility_graph.edge_count();
        if edge_count == complete_graph_edge_count::<Directed>(node_count) {
            info!("{id}: {accepted_factors} factors accepted, none left to submit");
            // Graph is fully connected, meaning none are left to try
            return accepted_factors > 0;
        }
        info!(
            "{id}: Divisibility graph has {node_count} vertices and {edge_count} edges. \
        {accepted_factors} factors accepted so far."
        );
        let factors_to_submit = divisibility_graph
            .vertices()
            .filter(|factor| factor.id != root_node)
            .map(|vertex| (vertex.id, vertex.attr.clone()))
            .collect::<Box<[_]>>();
        if factors_to_submit.is_empty() {
            return accepted_factors > 0;
        }
        for (factor_vid, factor) in factors_to_submit {
            // root can't be a factor of any other number we'll encounter
            let _ = divisibility_graph.try_add_edge(&root_node, &factor_vid, false);

            // elided numbers and numbers over 65500 digits without an expression form can only
            // be submitted as factors, even if their IDs are known
            // however, this doesn't affect the divisibility graph because the ID may be found
            // later
            if factor.as_str_non_u128().is_some_and(|expr| expr.contains("...")) {
                continue;
            }

            let mut dest_factors = divisibility_graph
                .vertices()
                .filter(|dest|
                    // if factor == dest, the relation is trivial
                    factor_vid != dest.id
                        // Don't try to submit to a dest for which FactorDB already has a full factorization
                        && !already_fully_factored.contains(&dest.id)
                        // if this edge exists, FactorDB already knows whether factor is a factor of dest
                        && get_edge(&divisibility_graph, &factor_vid, &dest.id).is_none())
                .map(|vertex| (vertex.id, vertex.attr.clone()))
                .collect::<Box<[_]>>();
            if dest_factors.is_empty() {
                debug!("{id}: No destinations to submit {factor} to");
                continue;
            };
            let shortest_paths = ShortestPaths::on(&divisibility_graph)
                .edge_weight_fn(|edge| if *edge { 0usize } else { 1usize })
                .run(factor_vid)
                .unwrap();
            dest_factors.sort_by_key(|(_, factor)| factor.clone());
            for (dest_factor_vid, dest_factor) in dest_factors.into_iter().rev() {
                // Check if an edge has been added since dest_factors was built
                let edge_id = divisibility_graph.edge_id_any(&factor_vid, &dest_factor_vid);
                if edge_id.is_some() {
                    debug!(
                        "{id}: Skipping submission of {factor} to {dest_factor} because divisibility edge already exists"
                    );
                    continue;
                }

                if get_edge(&divisibility_graph, &dest_factor_vid, &factor_vid) == Some(true) {
                    // dest_factor can't be divisible by factor because factor is divisible by dest_factor
                    debug!(
                        "{id}: Skipping submission of {factor} to {dest_factor} because {dest_factor} is a factor of {factor}"
                    );
                    add_edge_or_log(
                        &mut divisibility_graph,
                        &factor_vid,
                        &dest_factor_vid,
                        false,
                    );
                    continue;
                }

                if shortest_paths.dist(dest_factor_vid) == Some(&0) {
                    // dest_factor is divisible by factor, and this is already known to factordb
                    // because it follows that relation transitively
                    debug!(
                        "{id}: Skipping submission of {factor} to {dest_factor} because it's already transitively known"
                    );
                    add_edge_or_log(&mut divisibility_graph, &factor_vid, &dest_factor_vid, true);

                    // This reverse edge may already exist, because we only checked for a *true* one
                    // above
                    let _ = divisibility_graph.try_add_edge(
                        &dest_factor_vid,
                        &factor_vid,
                        false,
                    );
                    continue;
                }

                if dest_factor.unambiguously_less_or_equal(&factor) {
                    debug!(
                        "Skipping submission of {factor} to {dest_factor} because {dest_factor} is smaller or equal"
                    );
                    add_edge_or_log(
                        &mut divisibility_graph,
                        &factor_vid,
                        &dest_factor_vid,
                        false,
                    );
                    continue;
                }

                // u128s are already fully factored
                if let Numeric(dest) = dest_factor {
                    debug!(
                        "{id}: Skipping submission of {factor} to {dest_factor} because the number is too small"
                    );
                    let divisible = if let Numeric(f) = factor {
                        dest.is_multiple_of(f)
                    } else {
                        false
                    };
                    add_edge_or_log(
                        &mut divisibility_graph,
                        &factor_vid,
                        &dest_factor_vid,
                        divisible,
                    );
                    if divisible {
                        add_edge_or_log(
                            &mut divisibility_graph,
                            &dest_factor_vid,
                            &factor_vid,
                            false,
                        );
                    }
                    continue;
                }

                let shortest_path_from_dest = ShortestPaths::on(&divisibility_graph)
                    .edge_weight_fn(|edge| if *edge { 0 } else { 1 })
                    .goal(factor_vid)
                    .run(dest_factor_vid)
                    .ok()
                    .and_then(|paths| paths.dist(factor_vid).copied());
                if shortest_path_from_dest == Some(0) {
                    debug!(
                        "{id}: Skipping submission of {factor} to {dest_factor} because {dest_factor} is transitively a factor of {factor}"
                    );
                    // dest_factor is transitively divisible by factor
                    add_edge_or_log(&mut divisibility_graph, &dest_factor_vid, &factor_vid, true);
                    add_edge_or_log(
                        &mut divisibility_graph,
                        &factor_vid,
                        &dest_factor_vid,
                        false,
                    );
                    continue;
                }
                // elided numbers and numbers over 65500 digits without an expression form can only
                // be used as dests if their IDs are known
                // however, this doesn't affect the divisibility graph because the ID may be found
                // later
                if dest_factor
                    .as_str_non_u128()
                    .is_some_and(|expr| expr.contains("..."))
                    && !ids.contains_key(&dest_factor_vid)
                {
                    debug!(
                        "{id}: Can't submit to {dest_factor} right now because we don't know its full specifier"
                    );
                    continue;
                }
                let dest_specifier = as_specifier(&ids, &dest_factor_vid, &dest_factor);
                match try_report_factor(http, &dest_specifier, &factor).await {
                    AlreadyFullyFactored => {
                        if dest_factor_vid == root_node {
                            warn!("{id}: Already fully factored");
                            return true;
                        }
                        already_fully_factored.insert(dest_factor_vid);
                        continue;
                    }
                    Accepted => {
                        checked_for_known_factors_since_last_submission.remove(&dest_factor_vid);
                        checked_for_known_factors_since_last_submission.remove(&root_node);
                        accepted_factors += 1;
                        iters_without_progress = 0;
                        add_edge_or_log(
                            &mut divisibility_graph,
                            &factor_vid,
                            &dest_factor_vid,
                            true,
                        );
                        let _ =
                            divisibility_graph.try_add_edge(&dest_factor_vid, &factor_vid, false);
                    }
                    DoesNotDivide => {
                        add_edge_or_log(
                            &mut divisibility_graph,
                            &factor_vid,
                            &dest_factor_vid,
                            false,
                        );
                        if already_checked_for_algebraic.insert(factor_vid) {
                            debug!("{id}: Searching for algebraic factors of {factor}");
                            add_algebraic_factors_to_graph(
                                http,
                                ids.get(&factor_vid).copied(),
                                factor_finder,
                                id_and_expr_regex,
                                false,
                                &mut divisibility_graph,
                                &mut ids,
                                &factor,
                                &mut already_fully_factored,
                                factor_vid,
                                &mut checked_for_known_factors_since_last_submission,
                            )
                            .await;
                        } else if !checked_for_known_factors_since_last_submission
                            .contains(&factor_vid)
                        {
                            debug!("{id}: Searching for algebraic factors of {factor}");
                            let factor_specifier = as_specifier(&ids, &factor_vid, &factor);
                            let result = add_known_factors_to_graph(
                                http,
                                factor_finder,
                                &mut divisibility_graph,
                                factor_vid,
                                factor_specifier,
                                false,
                                &factor,
                            )
                            .await;
                            if result.status.is_some() {
                                if result.status == Some(FullyFactored) {
                                    already_fully_factored.insert(factor_vid);
                                }
                                checked_for_known_factors_since_last_submission.insert(factor_vid);
                            }
                            if !result.factors.is_empty() {
                                iters_without_progress = 0;
                            }
                            if let Some(dest_entry_id) = result.id {
                                debug!("{id}: {dest_factor} has entry ID {dest_entry_id}");
                                if let Some(old_id) = ids.insert(dest_factor_vid, dest_entry_id)
                                        && old_id != dest_entry_id {
                                    error!("{id}: Detected that {dest_factor}'s entry ID is {dest_entry_id}, but it was stored as {old_id}");
                                };
                            }
                        }
                    }
                    OtherError => {
                        if !checked_for_known_factors_since_last_submission
                            .contains(&dest_factor_vid)
                        {
                            debug!("{id}: Searching for known factors of {dest_factor}");
                            // See if dest has some already-known factors we can submit to instead
                            let result = add_known_factors_to_graph(
                                http,
                                factor_finder,
                                &mut divisibility_graph,
                                dest_factor_vid,
                                dest_specifier,
                                false,
                                &dest_factor,
                            )
                            .await;
                            if let Some(status) = result.status {
                                checked_for_known_factors_since_last_submission
                                    .insert(dest_factor_vid);
                                if status == FullyFactored {
                                    already_fully_factored.insert(dest_factor_vid);
                                }
                            }
                            if !result.factors.is_empty() {
                                iters_without_progress = 0;
                            }
                            if let Some(dest_entry_id) = result.id {
                                debug!("{id}: {dest_factor} has entry ID {dest_entry_id}");
                                if let Some(old_id) = ids.insert(dest_factor_vid, dest_entry_id)
                                    && old_id != dest_entry_id {
                                    error!("{id}: Detected that {dest_factor}'s entry ID is {dest_entry_id}, but it was stored as {old_id}");
                                };
                            }
                        }
                    }
                }
            }
        }
    }
    for (factor_vid, factor) in divisibility_graph
        .vertices()
        .map(|vertex| (vertex.id, vertex.attr.clone()))
        .collect::<Box<[_]>>()
        .into_iter()
    {
        if factor_vid == root_node {
            continue;
        }
        if factor.as_str_non_u128().is_some_and(|expr| expr.contains("..."))
        {
            debug!(
                "{id}: Skipping writing {factor} to failed-submission file because we don't know its specifier"
            );
            continue;
        }
        let reverse_dist = ShortestPaths::on(&divisibility_graph)
            .edge_weight_fn(|edge| if *edge { 0usize } else { 1usize })
            .goal(root_node)
            .run(factor_vid)
            .ok()
            .and_then(|paths| paths.dist(root_node).copied());
        if reverse_dist == Some(0) {
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

fn as_specifier<'a>(
    ids: &BTreeMap<VertexId, u128>,
    factor_vid: &VertexId,
    factor: &'a Factor<ArcStr, CompactString>,
) -> NumberSpecifier<&'a str, &'a str> {
    if let Some(factor_entry_id) = ids.get(factor_vid) {
        Id(*factor_entry_id)
    } else if let Numeric(n) = factor
        && *n <= MAX_ID_EQUAL_TO_VALUE
    {
        Id(*n)
    } else {
        Expression(factor.as_ref())
    }
}

#[framed]
async fn add_known_factors_to_graph<T: AsRef<str>, U: AsRef<str>, V: AsRef<str>, W: AsRef<str> + std::fmt::Display>(
    http: &ThrottlingHttpClient,
    factor_finder: &FactorFinder,
    divisibility_graph: &mut DivisibilityGraph,
    root_vid: VertexId,
    root_specifier: NumberSpecifier<T, U>,
    include_ff: bool,
    root: &Factor<V, W>,
) -> ProcessedStatusApiResponse {
    let ProcessedStatusApiResponse {
        status,
        factors: dest_subfactors,
        id,
    } = factor_finder
        .known_factors_as_digits(http, root_specifier, include_ff, false)
        .await;
    debug!("Got entry ID of {id:?} for {root}");
    if status == Some(FullyFactored) {
        let mut dest_subfactors_set = BTreeSet::new();
        dest_subfactors_set.extend(dest_subfactors.iter().map(|factor| factor.as_ref()));
        let vertices = divisibility_graph
            .vertices()
            .map(|vertex| {
                (
                    vertex.id,
                    dest_subfactors_set.contains(&vertex.attr.as_ref()),
                )
            })
            .collect::<Box<[_]>>();
        for (vertex_id, divisible) in vertices {
            if vertex_id == root_vid {
                continue;
            }
            let _ = divisibility_graph.try_add_edge(&vertex_id, &root_vid, divisible);
            if divisible {
                let _ = divisibility_graph.try_add_edge(&root_vid, &vertex_id, false);
            }
        }
    }
    let len = dest_subfactors.len();
    let all_added = match len {
        0 => Box::new([]),
        1 => {
            let dest_subfactor = dest_subfactors.into_iter().next().unwrap();
            if dest_subfactor.as_str() == root.as_str() {
                Box::new([])
            } else {
                // These expressions are different but equivalent; merge their edges
                let (new_root_vid, added) = add_factor_node(divisibility_graph, &dest_subfactor);
                let old_out_neighbors =
                    neighbors_with_edge_weights(divisibility_graph, &root_vid, Outgoing);
                let old_in_neighbors =
                    neighbors_with_edge_weights(divisibility_graph, &root_vid, Incoming);
                let (new_out_neighbors, new_in_neighbors) = if added {
                    // new root is truly new, so there are no edges to copy *from* it
                    (Box::default(), Box::default())
                } else {
                    (
                        neighbors_with_edge_weights(divisibility_graph, &new_root_vid, Outgoing),
                        neighbors_with_edge_weights(divisibility_graph, &new_root_vid, Incoming),
                    )
                };
                upsert_edge(divisibility_graph, &root_vid, &new_root_vid, |_| true);
                upsert_edge(divisibility_graph, &new_root_vid, &root_vid, |_| true);
                copy_edges_true_overrides_false(
                    divisibility_graph,
                    &new_root_vid,
                    old_out_neighbors,
                    old_in_neighbors,
                );
                copy_edges_true_overrides_false(
                    divisibility_graph,
                    &root_vid,
                    new_out_neighbors,
                    new_in_neighbors,
                );
                if added { vec![dest_subfactor] } else { vec![] }.into_boxed_slice()
            }
        }
        _ => {
            let mut all_added = Vec::new();
            for dest_subfactor in dest_subfactors {
                let (subfactor_vid, added) = add_factor_node(divisibility_graph, &dest_subfactor);
                if added {
                    all_added.push(dest_subfactor);
                }
                let _ = divisibility_graph.try_add_edge(&subfactor_vid, &root_vid, true);
                let _ = divisibility_graph.try_add_edge(&root_vid, &subfactor_vid, false);
            }
            all_added.into_boxed_slice()
        }
    };
    ProcessedStatusApiResponse {
        status,
        factors: all_added,
        id,
    }
}

fn upsert_edge<F: FnOnce(Option<bool>) -> bool>(
    divisibility_graph: &mut DivisibilityGraph,
    from_vid: &VertexId,
    to_vid: &VertexId,
    new_value_fn: F,
) {
    match divisibility_graph.edge_id_any(from_vid, to_vid) {
        Some(old_edge_id) => {
            divisibility_graph.replace_edge(
                &old_edge_id,
                new_value_fn(Some(*divisibility_graph.edge(&old_edge_id).unwrap())),
            );
        }
        None => {
            add_edge_or_log(divisibility_graph, from_vid, to_vid, new_value_fn(None));
        }
    }
}

fn copy_edges_true_overrides_false(
    divisibility_graph: &mut DivisibilityGraph,
    new_vertex: &VertexId,
    out_edges: Box<[(VertexId, bool)]>,
    in_edges: Box<[(VertexId, bool)]>,
) {
    for (neighbor, divisible) in out_edges {
        upsert_edge(divisibility_graph, new_vertex, &neighbor, |old_edge| {
            if old_edge == Some(true) {
                true
            } else {
                divisible
            }
        });
    }
    for (neighbor, divisible) in in_edges {
        upsert_edge(divisibility_graph, &neighbor, new_vertex, |old_edge| {
            if old_edge == Some(true) {
                true
            } else {
                divisible
            }
        });
    }
}

fn neighbors_with_edge_weights(
    divisibility_graph: &mut DivisibilityGraph,
    root_vid: &VertexId,
    direction: Direction,
) -> Box<[(VertexId, bool)]> {
    divisibility_graph
        .neighbors_directed(root_vid, direction)
        .map(|neighbor_ref| {
            (
                neighbor_ref.id,
                *divisibility_graph.edge(&neighbor_ref.edge).unwrap(),
            )
        })
        .collect()
}

#[framed]
async fn add_algebraic_factors_to_graph<T: AsRef<str> + Display, U: AsRef<str> + Display>(
    http: &ThrottlingHttpClient,
    id: Option<u128>,
    factor_finder: &FactorFinder,
    id_and_expr_regex: &Regex,
    skip_looking_up_listed_algebraic: bool,
    divisibility_graph: &mut DivisibilityGraph,
    ids: &mut BTreeMap<VertexId, u128>,
    root: &Factor<T, U>,
    already_fully_factored: &mut BTreeSet<VertexId>,
    root_vid: VertexId,
    checked_for_known_factors_since_last_submission: &mut BTreeSet<VertexId>,
) -> bool {
    let mut any_added = false;
    let mut parseable_factors: BTreeSet<Factor<ArcStr, CompactString>> = BTreeSet::new();
    if !skip_looking_up_listed_algebraic && root.as_str_non_u128().is_some() {
        parseable_factors.insert(Factor::from(root));
        let id = match id {
            Some(id) => Some(id),
            None => {
                let result = add_known_factors_to_graph(
                    http,
                    factor_finder,
                    divisibility_graph,
                    root_vid,
                    Expression(root.as_ref()),
                    true,
                    root,
                )
                .await;
                if result.status.is_some() {
                    checked_for_known_factors_since_last_submission.insert(root_vid);
                }
                if result.status == Some(FullyFactored) {
                    already_fully_factored.insert(root_vid);
                    return true;
                }
                parseable_factors.extend(result.factors);
                result.id
            }
        };
        if let Some(id) = id {
            if id <= MAX_ID_EQUAL_TO_VALUE {
                error!("Tried to look up {root} using a smaller number's id {id}");
                error!("\n{}\n", async_backtrace::taskdump_tree(false));
                parseable_factors.insert(Factor::from(root));
            } else {
                info!("{id}: Checking for listed algebraic factors");
                // Links before the "Is factor of" header are algebraic factors; links after it aren't
                let url = format!("https://factordb.com/frame_moreinfo.php?id={id}").into();
                let result = http.retrying_get_and_decode(url, RETRY_DELAY).await;
                if let Some(listed_algebraic) = result.split("Is factor of").next() {
                    let algebraic_factors = id_and_expr_regex.captures_iter(listed_algebraic);
                    for factor_captures in algebraic_factors {
                        let factor_entry_id = &factor_captures[1];
                        let factor_digits_or_expr = &factor_captures[2];
                        let factor = factor_digits_or_expr.into();
                        let (factor_vid, added) = add_factor_node(divisibility_graph, &factor);
                        any_added |= added;
                        let mut should_add_factor = true;
                        if factor_digits_or_expr.contains("...") {
                            // Link text isn't an expression for the factor, so we need to look up its value
                            info!(
                                "{id}: Algebraic factor with ID {factor_entry_id} represented as digits with ellipsis: {factor_digits_or_expr}"
                            );
                            if !checked_for_known_factors_since_last_submission
                                .contains(&factor_vid)
                            {
                                let (factor_specifier, factor_entry_id) =
                                    if let Ok(factor_entry_id) = factor_entry_id.parse::<u128>() {
                                        (Id(factor_entry_id), Some(factor_entry_id))
                                    } else {
                                        let (factor_vid, _) =
                                            add_factor_node(divisibility_graph, &factor);
                                        (as_specifier(ids, &factor_vid, &factor), None)
                                    };
                                let result = add_known_factors_to_graph(
                                    http,
                                    factor_finder,
                                    divisibility_graph,
                                    factor_vid,
                                    factor_specifier,
                                    true,
                                    &factor,
                                )
                                .await;
                                if !result.factors.is_empty() {
                                    any_added = true;
                                }
                                if result.status.is_some() {
                                    if result.status == Some(FullyFactored) {
                                        already_fully_factored.insert(factor_vid);
                                    } else {
                                        parseable_factors.extend(result.factors);
                                    }
                                    checked_for_known_factors_since_last_submission
                                        .insert(factor_vid);
                                    should_add_factor = false;
                                }
                                if let Some(recvd_entry_id) = result.id{
                                    debug!("{id}: Entry ID of {factor} from add_known_factors_to_graph is {recvd_entry_id}");
                                };
                                if let Some(factor_entry_id) = factor_entry_id {
                                    debug!("{id}: Entry ID of {factor} from algebraic-factor scrape is {factor_entry_id}");
                                    if let Some(old_id) = ids.insert(factor_vid, factor_entry_id)
                                        && old_id != factor_entry_id {
                                        error!("{id}: Detected that {factor}'s entry ID is {factor_entry_id}, but it was stored as {old_id}");
                                    };
                                }
                            }
                        } else {
                            info!(
                                "{id}: Algebraic factor with ID {factor_entry_id:?} represented in full: {factor_digits_or_expr}"
                            );
                        }
                        if should_add_factor {
                            parseable_factors.insert(factor);
                            any_added |= added;
                        }
                    }
                }
            }
        }
    } else {
        parseable_factors.insert(Factor::from(root));
    }
    for parseable_factor in parseable_factors {
        for subfactor in factor_finder.find_unique_factors(&parseable_factor) {
            let (_, added) = add_factor_node(divisibility_graph, &subfactor);
            any_added |= added;
        }
    }
    any_added
}

fn get_edge<T>(
    graph: &DivisibilityGraph,
    source: &VertexId,
    dest: &VertexId,
) -> Option<bool> {
    Some(*graph.edge(&graph.edge_id_any(source, dest)?)?)
}

fn add_factor_node(
    divisibility_graph: &mut DivisibilityGraph,
    factor: &Factor<ArcStr, CompactString>,
) -> (VertexId, bool) {
    match divisibility_graph.find_vertex(factor) {
        Some(id) => (id, false),
        None => (divisibility_graph.add_vertex(factor.clone()), true),
    }
}

#[framed]
fn add_edge_or_log(
    graph: &mut DivisibilityGraph,
    from_vid: &VertexId,
    to_vid: &VertexId,
    value: bool,
) {
    if let Err(e) = graph.try_add_edge(from_vid, to_vid, value) {
        error!(
            "Error adding edge {}-({})->{} {e}\n{}\n{}\n",
            graph.vertex(from_vid).unwrap(),
            value,
            graph.vertex(to_vid).unwrap(),
            async_backtrace::taskdump_tree(false),
            Backtrace::force_capture()
        );
    }
}
