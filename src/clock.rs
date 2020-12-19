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

/*use std::thread::{self, JoinHandle};

mod clock;
use clock::{Pulse, Clock};

fn make_thread(pulse: Pulse, message: &'static str) -> JoinHandle<()> {
    thread::spawn(move || {
        loop {
            pulse.on_pulse(|| println!("{}", message));
        }
    })
}

fn main() {
    let mut tick = Clock::new();
    let mut tock = Clock::new();

    let mut tick_threads = Vec::new();
    tick_threads.push(make_thread(tick.add_tap(), "Tick 1"));
    tick_threads.push(make_thread(tick.add_tap(), "Tick 2"));
    tick_threads.push(make_thread(tick.add_tap(), "Tick 3"));
    
    let mut tock_threads = Vec::new();
    tock_threads.push(make_thread(tock.add_tap(), "Tock 1"));
    tock_threads.push(make_thread(tock.add_tap(), "Tock 2"));
    tock_threads.push(make_thread(tock.add_tap(), "Tock 3"));

    for _i in 0..2 {
        println!("Ticking...");
        tick.start_and_wait();
        println!("Tocking...");
        tock.start_and_wait();
    }
}*/
