use std::sync::Arc;

use super::bus::Bus;

type Address = u16;
type Data = u8;

pub struct CPU_6502 {
    a: Data,
    x: Data,
    y: Data,
    flags: Data,
    stack: Data,
    pc: Address,
    bus: Arc<Bus<Address, Data>>,
}

impl CPU_6502 {
    pub fn new(bus: Arc<Bus<Address, Data>>) -> Self {
        let a = 0;
        let x = 0;
        let y = 0;
        let flags = 0;
        let stack = 0xFF;
        let pc = 0; // TODO what should the initial PC/reset vector be?
        Self { a, x, y, flags, stack, pc, bus }
    }

    pub fn tick(&mut self) {
        let op = self.bus.read(self.pc).unwrap();
        match op & 0x03 {
            0b01 => {
                let addr = match (op >> 2) & 0x07 {
                    0b000 => { // Indirect, X
                        let base = self.bus.read(self.pc + 1).unwrap() as Address;
                        let addr_lo = self.bus.read((base + self.x as Address) & 0xFF).unwrap();
                        let addr_hi = self.bus.read((base + self.x as Address + 1) & 0xFF).unwrap();
                        let addr = addr_lo as Address | ((addr_hi as Address) << 8);
                        self.pc += 2;
                        addr
                    },
                    0b001 => { // Zero Page
                        let addr = self.bus.read(self.pc + 1).unwrap() as Address;
                        self.pc += 2;
                        addr
                    },
                    0b010 => { // Immediate
                        let addr = self.pc + 1;
                        self.pc += 2;
                        addr
                    },
                    0b011 => { // Absolute
                        let addr_lo = self.bus.read(self.pc + 1).unwrap();
                        let addr_hi = self.bus.read(self.pc + 2).unwrap();
                        let addr = addr_lo as Address | ((addr_hi as Address) << 8);
                        self.pc += 3;
                        addr
                    },
                    0b100 => { // Indirect, Y
                        let base = self.bus.read(self.pc + 1).unwrap() as Address;
                        let addr_lo = self.bus.read(base).unwrap();
                        let addr_hi = self.bus.read((base + 1) & 0xFF).unwrap();
                        let addr = (addr_lo as Address | ((addr_hi as Address) << 8)) + self.y as Address;
                        self.pc += 2;
                        // TODO add 1 cycle if page boundary crossed
                        addr
                    },
                    0b101 => { // Zero Page, X
                        let base = self.bus.read(self.pc + 1).unwrap() as Address;
                        let addr = self.bus.read((base + self.x as Address) & 0xFF).unwrap() as Address;
                        self.pc += 2;
                        addr
                    },
                    0b110 => { // Absolute, Y
                        let addr_lo = self.bus.read(self.pc + 1).unwrap() as Address;
                        let addr_hi = self.bus.read(self.pc + 2).unwrap() as Address;
                        let addr = (addr_lo as Address | ((addr_hi as Address) << 8)) + self.y as Address;
                        self.pc += 3;
                        // TODO add 1 cycle if page boundary crossed
                        addr
                    },
                    0b111 => { // Absolute, X
                        let addr_lo = self.bus.read(self.pc + 1).unwrap() as Address;
                        let addr_hi = self.bus.read(self.pc + 2).unwrap() as Address;
                        let addr = (addr_lo as Address | ((addr_hi as Address) << 8)) + self.x as Address;
                        self.pc += 3;
                        // TODO add 1 cycle if page boundary crossed
                        addr
                    },
                    _ => unreachable!(),
                };
                match (op >> 5) & 0x07 {
                    0b000 => { // ORA
                        self.a |= self.bus.read(addr).unwrap();
                    },
                    0b001 => { // AND
                        self.a &= self.bus.read(addr).unwrap();
                    },
                    0b010 => { // EOR
                        self.a ^= self.bus.read(addr).unwrap();
                    },
                    0b011 => { // ADC
                        self.a += self.bus.read(addr).unwrap();
                        // TODO deal with carry bit
                    },
                    0b100 => { // STA
                        // NOTE immediate mode STA is illegal and the opcode is used for something else on the 65C02/65C816
                        self.bus.write(addr, self.a).unwrap();
                    },
                    0b101 => { // LDA
                        self.a = self.bus.read(addr).unwrap();
                    },
                    0b110 => { // CMP
                        let _result = self.a - self.bus.read(addr).unwrap();
                        // TODO set flags as required
                    },
                    0b111 => { // SBC
                        self.a -= self.bus.read(addr).unwrap();
                        // TODO deal with carry bit
                    },
                    _ => unreachable!(),
                };
                // TODO set status bits
            },
            _ => panic!("unhandled op"),
        }
    }
}
