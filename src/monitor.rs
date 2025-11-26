// Adapted from: https://github.com/tokio-rs/mini-redis/blob/e186482ca00f8d884ddcbe20417f3654d03315a4/src/shutdown.rs

use log::{error, info, warn};
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering::{Acquire, Release};
use std::time::Duration;
use async_backtrace::{framed, taskdump_tree};
use tokio::signal::ctrl_c;
use tokio::sync::broadcast::{Receiver, Sender, channel};
use tokio::sync::oneshot;
use tokio::{select, signal};
use tokio::time::{sleep_until, Instant};

const STACK_TRACES_INTERVAL: Duration = Duration::from_mins(5);

/// A Monitor performs two tasks:
/// 1. Periodically prints the async backtraces of running tasks, so that any
///    deadlock can be diagnosed.
/// 2. Listens for the server shutdown signal.
///
/// Shutdown is signalled using a `broadcast::Receiver`. Only a single value is
/// ever sent. Once a value has been sent via the broadcast channel, the server
/// should shut down.
///
/// The `Shutdown` struct listens for the signal and tracks that the signal has
/// been received. Callers may query for whether the shutdown signal has been
/// received or not.
#[derive(Debug)]
pub(crate) struct Monitor {
    /// `true` if the shutdown signal has been received
    is_shutdown: Arc<AtomicBool>,

    /// The receiving half of the channel used to listen for shutdown.
    shutdown_notify: Receiver<()>,
}

impl Monitor {
    /// Create a new `Shutdown` and a sender for it.
    pub(crate) fn new() -> (Sender<()>, Monitor) {
        let (sender, notify) = channel(1);
        (
            sender,
            Monitor {
                is_shutdown: Arc::new(false.into()),
                shutdown_notify: notify,
            },
        )
    }

    /// Returns `true` if the shutdown signal has been received.
    pub(crate) fn check_for_shutdown(&mut self) -> bool {
        if self.is_shutdown.load(Acquire) {
            true
        } else if self.shutdown_notify.try_recv().is_ok() {
            self.is_shutdown.store(true, Release);
            true
        } else {
            false
        }
    }

    /// Receive the shutdown notice, waiting if necessary.
    #[framed]
    pub(crate) async fn recv(&mut self) {
        // If the shutdown signal has already been received, then return
        // immediately.
        if self.is_shutdown.load(Acquire) {
            return;
        }

        // Cannot receive a "lag error" as only one value is ever sent.
        let _ = self.shutdown_notify.recv().await;

        // Remember that the signal has been received.
        self.is_shutdown.store(true, Release);
    }
}

impl Clone for Monitor {
    /// All clones will receive the shutdown from the same sender.
    fn clone(&self) -> Self {
        Monitor {
            is_shutdown: self.is_shutdown.clone(),
            shutdown_notify: self.shutdown_notify.resubscribe(),
        }
    }
}

pub async fn monitor(shutdown_sender: Sender<()>, installed_sender: oneshot::Sender<()>) {
    let mut sigint = Box::pin(ctrl_c());
    info!("Signal handlers installed");
    installed_sender
        .send(())
        .expect("Error signaling main task that signal handlers are installed");
    let mut sigterm;
    #[cfg(unix)]
    {
        sigterm = signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("Failed to create SIGTERM signal stream");
    }
    #[cfg(not(unix))]
    {
        // Create a channel that will never receive a signal
        let (_sender, sigterm) = oneshot::channel();
    }
    let mut next_backtrace = Instant::now() + STACK_TRACES_INTERVAL;
    loop {
        select! {
            _ = sleep_until(next_backtrace) => {
                info!("Task backtraces:\n{}", taskdump_tree(false));
                info!("Task backtraces with all tasks idle:\n{}", taskdump_tree(true));
                next_backtrace = Instant::now() + STACK_TRACES_INTERVAL;
            }
            _ = sigterm.recv() => {
                warn!("Received SIGTERM; signaling tasks to exit");
                break;
            },
            _ = &mut sigint => {
                warn!("Received SIGINT; signaling tasks to exit");
                break;
            }
        }
    }
    if let Err(e) = shutdown_sender.send(()) {
        error!("Error sending shutdown signal: {e}");
    }
    loop {
        sleep_until(next_backtrace).await;
        info!("Task backtraces:\n{}", taskdump_tree(false));
        info!("Task backtraces with all tasks idle:\n{}", taskdump_tree(true));
        next_backtrace = Instant::now() + STACK_TRACES_INTERVAL;
    }
}
