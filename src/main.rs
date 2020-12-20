use std::sync::{Arc, RwLock};

mod bus;
mod memory;

use bus::{Port, Bus};
use memory::RAM;

fn main() {
}

#[test]
#[should_panic]
fn test_mem_overlap_same() {
    let ram = Arc::new(RwLock::new(RAM::<u16, u8>::new(10)));
    let mut bus = Bus::<u16, u8>::new();
    bus.add_port(0..10, ram.clone());
    bus.add_port(0..10, ram.clone());
}

#[test]
#[should_panic]
fn test_mem_overlap_after() {
    let ram = Arc::new(RwLock::new(RAM::<u16, u8>::new(10)));
    let mut bus = Bus::<u16, u8>::new();
    bus.add_port(0..10, ram.clone());
    bus.add_port(9..19, ram.clone());
}

#[test]
#[should_panic]
fn test_mem_overlap_before() {
    let ram = Arc::new(RwLock::new(RAM::<u16, u8>::new(10)));
    let mut bus = Bus::<u16, u8>::new();
    bus.add_port(10..20, ram.clone());
    bus.add_port(1..11, ram.clone());
}

#[test]
fn test_mem_rw() {
    let mut bus = Bus::<u16, u8>::new();

    let addr = 100;
    let size = 1;
    let ram = Arc::new(RwLock::new(RAM::<u16, u8>::new(size)));
    bus.add_port(addr..addr+size, ram.clone());

    let value = 5;
    bus.write(addr, value);
    assert_eq!(bus.read(addr).unwrap(), value);
    assert_eq!(ram.read().unwrap().read(0), value);
}
