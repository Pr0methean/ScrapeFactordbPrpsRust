use log::{info, warn};
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

    fn redrive_returned(&mut self) {
        let amount = self.sender.capacity().min(self.return_receiver.len());
        if amount == 0 {
            return;
        }
        let permits = self.sender.try_reserve_many(amount);
        if let Ok(permits) = permits {
            info!("redrive_returned obtained batch of {} permits (requested {})", permits.len(), amount);
            permits.for_each(|permit| {
                if let Ok(item) = self.return_receiver.try_recv() {
                    info!("Redriving returned item {:?} using a batched permit", item);
                    permit.send(item);
                }
            });
        } else {
            warn!("redrive_returned couldn't obtain batch of {} permits", amount);
        }
        while let Ok(permit) = self.sender.try_reserve()
            && let Ok(item) = self.return_receiver.try_recv()
        {
            info!("Redriving returned item {:?}", item);
            permit.send(item);
        }
    }

    pub async fn recv(&mut self) -> (T, OwnedPermit<T>) {
        self.redrive_returned();
        let return_sender = self.return_sender.clone();
        let return_permit = return_sender.try_reserve_owned();
        match return_permit {
            Ok(permit) => {
                let item = select! {
                    biased;
                    result = self.receiver.recv() => {
                        result.unwrap()
                    },
                    result = self.return_receiver.recv() => {
                        let result = result.unwrap();
                        info!("Receiving returned item: {:?}", result);
                        result
                    }
                };
                (item, permit)
            },
            Err(e) => {
                let item = select! {
                    biased;
                    // Polling return receiver first is more likely to get a permit sooner
                    result = self.return_receiver.recv() => {
                        let result = result.unwrap();
                        warn!("Couldn't get a return permit before receiving returned item {result:?}");
                        result
                    }
                    result = self.receiver.recv() => {
                        warn!("Couldn't get a return permit before receiving item {result:?}");
                        result.unwrap()
                    },
                };
                let return_permit = select! {
                    biased;
                    result = e.into_inner().reserve_owned() => result.unwrap(),
                    result = self.sender.clone().reserve_owned() => result.unwrap(),
                };
                (item, return_permit)
            }
        }
    }

    pub fn try_recv(&mut self) -> Option<(T, OwnedPermit<T>)> {
        self.redrive_returned();
        if let Ok(return_permit) = self.return_sender.clone().try_reserve_owned()
            .or_else(|_| self.sender.clone().try_reserve_owned()) {
            if let Ok(received) = self.receiver.try_recv() {
                return Some((received, return_permit));
            } else if let Ok(received_return) = self.return_receiver.try_recv() {
                info!(
                    "Receiving returned item because main channel is empty: {:?}",
                    received_return
                );
                return Some((received_return, return_permit));
            }
        }
        // Without a permit, we can't safely return anything; consuming the returned item first
        // would lead to a race condition where we might not be able to get the permit.
        None
    }
}
