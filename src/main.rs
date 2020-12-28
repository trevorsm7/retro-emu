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
