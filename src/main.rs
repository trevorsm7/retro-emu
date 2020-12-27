use std::sync::{Arc, RwLock};

mod cpu;
mod bus;
mod memory;

use cpu::CPU_6502;
use bus::{Port, Bus};
use memory::RAM;

fn main() {
    // CPU dictates address and data sizes
    let mut bus = Bus::new();

    // Simple program to write 5 to address 16 (start of RAM)
    let mut rom = RAM::new(16);
    rom.write(0, 0xA9); // LDA #5
    rom.write(1, 5);
    rom.write(2, 0x69); // ADC #3
    rom.write(3, 3);
    rom.write(4, 0x85); // STA 16
    rom.write(5, 16);
    bus.add_port(0..16, Arc::new(RwLock::new(rom)));

    let ram = Arc::new(RwLock::new(RAM::new(16)));
    bus.add_port(16..32, ram.clone());

    // Execute 3 instructions
    let mut cpu = CPU_6502::new(Arc::new(bus));
    for _i in 0..3 {
        cpu.tick();
    }

    let ram = ram.read().unwrap();
    println!("{}", ram.read(0));
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
