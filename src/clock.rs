use std::sync::{Arc, Mutex, Condvar};

#[derive(Clone)]
pub struct Pulse {
    pulse: Arc<(Mutex<bool>, Condvar)>,
}

impl Pulse {
    pub fn new() -> Self {
        let pulse = Arc::new((Mutex::new(false), Condvar::new()));
        Self { pulse }
    }

    fn set(&self, value: bool) {
        let (lock, cvar) = &*self.pulse;
        *lock.lock().unwrap() = value;
        cvar.notify_one();
    }

    fn set_start(&self) {
        self.set(true);
    }

    fn set_finish(&self) {
        self.set(false);
    }

    fn wait(&self, value: bool) {
        let (lock, cvar) = &*self.pulse;
        let mut guard = lock.lock().unwrap();
        while *guard != value {
            guard = cvar.wait(guard).unwrap();
        }
    }

    fn wait_start(&self) {
        self.wait(true);
    }

    fn wait_finish(&self) {
        self.wait(false);
    }

    pub fn on_pulse<F: FnOnce()>(&self, func: F) {
        self.wait_start();
        func();
        self.set_finish();
    }
}

pub struct Clock {
    taps: Vec<Pulse>,
}

impl Clock {
    pub fn new() -> Self {
        Self { taps: Vec::new() }
    }

    pub fn add_tap(&mut self) -> Pulse {
        let tap = Pulse::new();
        self.taps.push(tap.clone());
        tap
    }

    pub fn start_and_wait(&self) {
        self.taps.iter().for_each(Pulse::set_start);
        self.taps.iter().for_each(Pulse::wait_finish);
    }
}
