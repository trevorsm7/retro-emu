use std::thread::{self, JoinHandle};

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
}
