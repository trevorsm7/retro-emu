use std::sync::{Arc, RwLock};

mod asm;
mod cpu;
mod bus;
mod memory;

use cpu::CPU_6502;
use bus::{Port, Bus};
use memory::RAM;

fn main() {
    let a = 5;
    let b = 3;
    let address = 16;
    let (_, code) = asm::assemble(format!("
        CODE $0000 ; start code segment at address 0
        LDA #{}
        ADC #{}
        STA @{} ; new @ prefix for explicit zero page
        BRK
        ENDCODE", a, b, address).as_ref(),
    ).drain(..).next().unwrap();

    println!("{:02x?}", code);

    // CPU dictates address and data sizes
    let mut bus = Bus::new();

    let jump_table = RAM::new(6); //< Default initialized to zeroes
    bus.add_port(cpu::NMI_VECTOR, Arc::new(RwLock::new(jump_table)));

    // Simple program to write 5 to address 16 (start of RAM)
    let mut ram = RAM::new(512);
    for (i, &byte) in code.iter().enumerate() {
        ram.write(i as u16, byte); //< TODO add RAM::from or ram.memcpy
    }
    bus.add_port(0, Arc::new(RwLock::new(ram)));

    // Execute 3 instructions
    let bus = Arc::new(bus);
    let mut cpu = CPU_6502::new(bus.clone());
    cpu.run_until_break();

    println!("{} + {} = {}", a, b, bus.read(address).unwrap());
}
