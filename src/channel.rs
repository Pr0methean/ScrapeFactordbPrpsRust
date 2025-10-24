use tokio::sync::mpsc::{OwnedPermit, Receiver, Sender};

pub struct PushbackReceiver<T> {
    sender: Sender<T>,
    receiver: Receiver<T>,
    permit: Option<OwnedPermit<T>>,
}

impl<T> PushbackReceiver<T> {
    pub fn new(receiver: Receiver<T>, sender: &Sender<T>) -> Self {
        let sender = sender.clone();
        let permit = sender.clone().try_reserve_owned().ok();
        PushbackReceiver {
            receiver,
            sender,
            permit,
        }
    }

    pub async fn recv(&mut self) -> T {
        let result = self.receiver.recv().await.unwrap();
        if self.permit.is_none() {
            self.permit = self.sender.clone().try_reserve_owned().ok();
        }
        result
    }

    pub fn try_recv(&mut self) -> Option<T> {
        let result = self.receiver.try_recv().ok()?;
        if self.permit.is_none() {
            self.permit = self.sender.clone().try_reserve_owned().ok();
        }
        Some(result)
    }

    pub fn try_send(&mut self, value: T) -> bool {
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
