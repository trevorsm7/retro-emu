use std::sync::{Arc, RwLock};

mod bus;
mod memory;

use bus::{Port, Bus};
use memory::RAM;

fn main() {
}

#[test]
fn test_mem_bus() {
    let mut bus = Bus::<u16, u8>::new();

    let addr = 100;
    let size = 1;
    let ram = Arc::new(RwLock::new(RAM::<u16, u8>::new(size)));
    bus.add_port((addr, addr+size), ram.clone());

    let value = 5;
    bus.write(addr, value);
    assert_eq!(bus.read(addr).unwrap(), value);
    assert_eq!(ram.read().unwrap().read(0), value);
}
