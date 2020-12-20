use std::sync::Arc;

use super::bus::Bus;

type Address = u16;
type Data = u8;

pub struct CPU {
    pc: Address,
    regs: [Data; 8],
    bus: Arc<Bus<Address, Data>>,
}

impl CPU {
    pub fn new(bus: Arc<Bus<Address, Data>>) -> Self {
        Self { pc: 0, regs: [0; 8], bus }
    }

    pub fn tick(&mut self) {
        let op = self.bus.read(self.pc).unwrap();
        match op & 0xF0 {
            0x00 => { // load
                let data = if op & 0x08 != 0 { // indirect
                    let addr_lo = self.bus.read(self.pc + 1).unwrap();
                    let addr_hi = self.bus.read(self.pc + 2).unwrap();
                    let addr = addr_lo as Address | ((addr_hi as Address) << 8);
                    self.pc += 3;
                    self.bus.read(addr).unwrap()
                } else { // immediate
                    let data = self.bus.read(self.pc + 1).unwrap();
                    self.pc += 2;
                    data
                };

                self.regs[(op & 0x07) as usize] = data;
            },
            0x10 => { // store
                let addr_lo = self.bus.read(self.pc + 1).unwrap();
                let addr_hi = self.bus.read(self.pc + 2).unwrap();
                let addr = addr_lo as Address | ((addr_hi as Address) << 8);
                self.pc += 3;

                let data = self.regs[(op & 0x07) as usize];
                self.bus.write(addr, data).unwrap();
            },
            _ => panic!("unhandled op"),
        }
    }
}
