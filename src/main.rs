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

    let mut start_address = RAM::new(2);
    start_address.write(0, 0);
    start_address.write(1, 0);
    bus.add_port(cpu::RESET_VECTOR, Arc::new(RwLock::new(start_address)));

    // Simple program to write 5 to address 16 (start of RAM)
    let mut rom = RAM::new(16);
    rom.write(0, 0xA9); // LDA #5
    rom.write(1, 5);
    rom.write(2, 0x69); // ADC #3
    rom.write(3, 3);
    rom.write(4, 0x85); // STA 16
    rom.write(5, 16);
    bus.add_port(0, Arc::new(RwLock::new(rom)));

    let ram = Arc::new(RwLock::new(RAM::new(16)));
    bus.add_port(16, ram.clone());

    // Execute 3 instructions
    let mut cpu = CPU_6502::new(Arc::new(bus));
    for _i in 0..3 {
        cpu.tick();
    }

    let ram = ram.read().unwrap();
    println!("{}", ram.read(0));
}
