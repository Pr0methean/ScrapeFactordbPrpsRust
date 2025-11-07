use log::info;
use std::fmt::Debug;
use tokio::select;
use tokio::sync::mpsc::{OwnedPermit, Receiver, Sender, channel};

pub struct PushbackReceiver<T: Debug> {
    receiver: Receiver<T>,
    sender: Sender<T>,
    return_sender: Sender<T>,
    return_receiver: Receiver<T>,
}

impl<T: Debug> PushbackReceiver<T> {
    pub fn new(receiver: Receiver<T>, sender: &Sender<T>) -> Self {
        let (return_sender, return_receiver) = channel((sender.max_capacity() >> 2).max(2));
        PushbackReceiver {
            receiver,
            sender: sender.clone(),
            return_sender,
            return_receiver,
        }
    }

    fn refeed_returned(&mut self) {
        while let Ok(permit) = self.sender.try_reserve() {
            if let Ok(item) = self.return_receiver.try_recv() {
                permit.send(item);
            }
        }
    }

    pub async fn recv(&mut self) -> (T, OwnedPermit<T>) {
        self.refeed_returned();
        let return_permit = self.return_sender.clone().reserve_owned().await.unwrap();
        select! {
            biased;
            result = self.receiver.recv() => {
                (result.unwrap(), return_permit)
            },
            result = self.return_receiver.recv() => {
                let result = result.unwrap();
                info!("Receiving returned item: {:?}", result);
                (result, return_permit)
            }
        }
    }

    pub fn try_recv(&mut self) -> Option<(T, OwnedPermit<T>)> {
        self.refeed_returned();
        match self.return_sender.clone().try_reserve_owned().ok() {
            Some(return_permit) => {
                if let Ok(received) = self.receiver.try_recv() {
                    Some((received, return_permit))
                } else if let Ok(received_return) = self.return_receiver.try_recv() {
                    info!(
                        "Receiving returned item because main channel is empty: {:?}",
                        received_return
                    );
                    Some((received_return, return_permit))
                } else {
                    None
                }
            }
            None => {
                let received = self.return_receiver.try_recv().expect(
                    "Failed to receive a returned item when no return permits are available",
                );
                let return_permit = self
                    .return_sender
                    .clone()
                    .try_reserve_owned()
                    .expect("Failed to obtain a return permit after receiving a returned item");
                info!(
                    "Receiving returned item because return channel is full: {:?}",
                    received
                );
                Some((received, return_permit))
            }
        }
    }
}
