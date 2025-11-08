// Adapted from: https://github.com/tokio-rs/mini-redis/blob/e186482ca00f8d884ddcbe20417f3654d03315a4/src/shutdown.rs

use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering::{Acquire, Release};
use tokio::sync::broadcast;
use tokio::sync::broadcast::{channel, Sender};

/// Listens for the server shutdown signal.
///
/// Shutdown is signalled using a `broadcast::Receiver`. Only a single value is
/// ever sent. Once a value has been sent via the broadcast channel, the server
/// should shut down.
///
/// The `Shutdown` struct listens for the signal and tracks that the signal has
/// been received. Callers may query for whether the shutdown signal has been
/// received or not.
#[derive(Debug)]
pub(crate) struct Shutdown {
    /// `true` if the shutdown signal has been received
    is_shutdown: Arc<AtomicBool>,

    /// The receive half of the channel used to listen for shutdown.
    notify: broadcast::Receiver<()>,
}

impl Shutdown {
    /// Create a new `Shutdown` and a sender for it.
    pub(crate) fn new() -> (Sender<()>, Shutdown) {
        let (sender, notify) = channel(1);
        (sender, Shutdown {
            is_shutdown: Arc::new(false.into()),
            notify,
        })
    }

    /// Returns `true` if the shutdown signal has been received.
    pub(crate) fn check_for_shutdown(&mut self) -> bool {
        if self.is_shutdown.load(Acquire) {
            true
        } else if self.notify.try_recv().is_ok() {
            self.is_shutdown.store(true, Release);
            true
        } else {
            false
        }
    }

    /// Receive the shutdown notice, waiting if necessary.
    pub(crate) async fn recv(&mut self) {
        // If the shutdown signal has already been received, then return
        // immediately.
        if self.is_shutdown.load(Acquire) {
            return;
        }

        // Cannot receive a "lag error" as only one value is ever sent.
        let _ = self.notify.recv().await;

        // Remember that the signal has been received.
        self.is_shutdown.store(true, Release);
    }
}

impl Clone for Shutdown {
    /// All clones will receive the shutdown from the same sender.
    fn clone(&self) -> Self {
        Shutdown {
            is_shutdown: self.is_shutdown.clone(),
            notify: self.notify.resubscribe()
        }
    }
}