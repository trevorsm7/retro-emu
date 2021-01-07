use std::sync::{Arc, RwLock};

mod asm;
mod cpu;
mod bus;
mod memory;

use cpu::CPU_6502;
use bus::{Port, Bus};
use memory::RAM;

fn main() {
    let a = 0b00010101;
    let address = 0xFF;
    let program = asm::assemble(format!("
        CODE $0
        LDA #{}
        JSR leading_zeroes
        STA @{}
        BRK
        ENDCODE

        CODE $200
        leading_zeroes: LDX #-8
        loop: ROL A ; rotate left 8 times
        BCS end ; exit loop when we find the leading 1
        INX
        BNE loop
        end: TXA
        CLC ; don't forget to clear carry after ROL sets it...
        ADC #8 ; convert counter to number of leading zeros in A
        RTS
        ENDCODE", a, address).as_ref()
    );

    println!("{:02x?}", program);

    // CPU dictates address and data sizes
    let mut bus = Bus::new();

    let jump_table = RAM::new(6); //< Default initialized to zeroes
    bus.add_port(cpu::NMI_VECTOR, Arc::new(RwLock::new(jump_table)));

    // Simple program to write 5 to address 16 (start of RAM)
    let mut ram = RAM::new(0x300);
    for (offset, code) in program.iter() {
        for (i, &byte) in code.iter().enumerate() {
            ram.write(offset + i as u16, byte); //< TODO add RAM::from or ram.memcpy
        }
    }
    bus.add_port(0, Arc::new(RwLock::new(ram)));

    // Execute 3 instructions
    let bus = Arc::new(bus);
    let mut cpu = CPU_6502::new(bus.clone());
    cpu.run_until_break();

    println!("Leading zeroes in {:08b}: {}", a, bus.read(address).unwrap());
}
