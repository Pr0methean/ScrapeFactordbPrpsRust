use tokio::select;
use tokio::sync::mpsc::{OwnedPermit, Receiver, Sender, channel};

pub struct PushbackReceiver<T> {
    receiver: Receiver<T>,
    return_sender: Sender<T>,
    return_receiver: Receiver<T>,
}

impl<T> PushbackReceiver<T> {
    pub fn new(receiver: Receiver<T>, sender: &Sender<T>) -> Self {
        let (return_sender, return_receiver) = channel(sender.max_capacity());
        PushbackReceiver {
            receiver,
            return_sender,
            return_receiver,
        }
    }

    pub async fn recv(&mut self) -> (T, OwnedPermit<T>) {
        let return_permit = self.return_sender.clone().reserve_owned().await.unwrap();
        select! {
            biased;
            result = self.receiver.recv() => {
                (result.unwrap(), return_permit)
            },
            result = self.return_receiver.recv() => {
                (result.unwrap(), return_permit)
            }
        }
    }

    pub fn try_recv(&mut self) -> Option<(T, OwnedPermit<T>)> {
        match self.return_sender.clone().try_reserve_owned().ok() {
            Some(return_permit) => {
                if let Ok(received) = self.receiver.try_recv() {
                    Some((received, return_permit))
                } else if let Ok(received_return) = self.return_receiver.try_recv() {
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
                Some((received, return_permit))
            }
        }
    }
}
