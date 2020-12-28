use std::sync::Arc;

use super::bus::Bus;

type Address = u16;
type Data = u8;

const FLAG_N: Data = 0b1000_0000; // Negative (bit 7 of last operation)
const FLAG_V: Data = 0b0100_0000; // Signed overflow
const FLAG_B: Data = 0b0001_0000; // Break indicator
const FLAG_D: Data = 0b0000_1000; // Decimal mode
const FLAG_I: Data = 0b0000_0100; // Interrupt disable
const FLAG_Z: Data = 0b0000_0010; // Zero (set if zero!)
const FLAG_C: Data = 0b0000_0001; // Carry (unsigned overflow)

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

    fn set_flag(&mut self, condition: bool, flag: Data) {
        if condition {
            self.flags |= flag;
        } else {
            self.flags &= !flag;
        }
        // TODO bit twiddly version
        //self.flags ^= ((-(condition as i8) as u8) ^ self.flags) & flag;
    }

    fn test_flag(&self, flag: Data) -> bool {
        self.flags & flag != 0
    }

    fn update_flags_nz(&mut self, data: Data) {
        self.set_flag(data & 0x80 != 0, FLAG_N);
        self.set_flag(data == 0, FLAG_Z);
    }

    fn compare(&mut self, left: Data, right: Data) {
        self.set_flag(left < right, FLAG_N);
        self.set_flag(left == right, FLAG_Z);
        self.set_flag(left >= right, FLAG_C);
    }

    fn add_carry(&mut self, left: Data, right: Data) -> Data {
        // TODO handle decimal mode
        let result = left as u16 + right as u16 + (self.flags & FLAG_C) as u16;
        self.set_flag((left ^ right) & 0x80 == 0 && (result ^ result >> 1) & 0x80 != 0, FLAG_V);
        self.set_flag(result & 0x100 != 0, FLAG_C);
        let result = (result & 0xFF) as Data;
        self.update_flags_nz(result);
        result
    }

    fn sub_borrow(&mut self, left: Data, right: Data) -> Data {
        // TODO handle decimal mode
        // NOTE 1s complement of RHS plus carry is equivalent to 2s complement minus borrow
        self.add_carry(left, !right)
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
                        self.update_flags_nz(self.a);
                    },
                    0b001 => { // AND
                        self.a &= self.bus.read(addr).unwrap();
                        self.update_flags_nz(self.a);
                    },
                    0b010 => { // EOR
                        self.a ^= self.bus.read(addr).unwrap();
                        self.update_flags_nz(self.a);
                    },
                    0b011 => { // ADC
                        self.a = self.add_carry(self.a, self.bus.read(addr).unwrap());
                    },
                    0b100 => { // STA
                        // NOTE immediate mode STA is illegal and the opcode is used for something else on the 65C02/65C816
                        self.bus.write(addr, self.a).unwrap();
                    },
                    0b101 => { // LDA
                        self.a = self.bus.read(addr).unwrap();
                        self.update_flags_nz(self.a);
                    },
                    0b110 => { // CMP
                        self.compare(self.a, self.bus.read(addr).unwrap());
                    },
                    0b111 => { // SBC
                        self.a = self.sub_borrow(self.a, self.bus.read(addr).unwrap());
                    },
                    _ => unreachable!(),
                };
            },
            _ => panic!("unhandled op"),
        }
    }
}

#[test]
fn test_compare() {
    let bus = Bus::new();
    let mut cpu = CPU_6502::new(Arc::new(bus));

    cpu.compare(30, 40);
    assert_eq!(cpu.test_flag(FLAG_N), true);
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), false);

    cpu.compare(40, 40);
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_Z), true);
    assert_eq!(cpu.test_flag(FLAG_C), true);

    cpu.compare(50, 40);
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), true);
}

#[test]
fn test_add_carry() {
    let bus = Bus::new();
    let mut cpu = CPU_6502::new(Arc::new(bus));

    // Unsigned overflow (carry out)
    cpu.set_flag(false, FLAG_C);
    assert_eq!(cpu.add_carry(0xFF, 1), 0);
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), false);
    assert_eq!(cpu.test_flag(FLAG_Z), true);
    assert_eq!(cpu.test_flag(FLAG_C), true); // unsigned overflow

    // Unsigned overflow from carry
    cpu.set_flag(true, FLAG_C);
    assert_eq!(cpu.add_carry(0xFF, 0), 0);
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), false);
    assert_eq!(cpu.test_flag(FLAG_Z), true);
    assert_eq!(cpu.test_flag(FLAG_C), true); // unsigned overflow

    // Signed overflow (positive + positive -> negative)
    cpu.set_flag(false, FLAG_C);
    assert_eq!(cpu.add_carry(0x40, 0x40), 0x80);
    assert_eq!(cpu.test_flag(FLAG_N), true);
    assert_eq!(cpu.test_flag(FLAG_V), true); // signed overflow
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), false);

    // Signed overflow (negative + negative -> positive)
    cpu.set_flag(false, FLAG_C);
    assert_eq!(cpu.add_carry(0x80, 0x80), 0); // -128 + -128
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), true); // signed overflow
    assert_eq!(cpu.test_flag(FLAG_Z), true);
    assert_eq!(cpu.test_flag(FLAG_C), true);
}

#[test]
fn test_sub_borrow() {
    let bus = Bus::new();
    let mut cpu = CPU_6502::new(Arc::new(bus));

    // Subtract self
    cpu.set_flag(true, FLAG_C); // clear borrow (set carry)
    assert_eq!(cpu.sub_borrow(0xFF, 0xFF), 0);
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), false);
    assert_eq!(cpu.test_flag(FLAG_Z), true);
    assert_eq!(cpu.test_flag(FLAG_C), true); // borrow clear (carry set)

    // Signed underflow from borrow
    cpu.set_flag(false, FLAG_C); // set borrow (clear carry)
    assert_eq!(cpu.sub_borrow(0, 0), 0xFF);
    assert_eq!(cpu.test_flag(FLAG_N), true);
    assert_eq!(cpu.test_flag(FLAG_V), false);
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), false); // borrow set (carry clear)

    // Signed overflow (negative - positive -> positive)
    cpu.set_flag(true, FLAG_C); // clear borrow (set carry)
    assert_eq!(cpu.sub_borrow(0x80, 0x01), 0x7F); // -128 - 1 = 127
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), true); // signed overflow
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), true); // borrow clear (carry set)

    // Signed overflow (negative - positive -> positive)
    cpu.set_flag(true, FLAG_C); // clear borrow (set carry)
    assert_eq!(cpu.sub_borrow(0x7F, 0xFF), 0x80); // 127 - (-1) = -128
    assert_eq!(cpu.test_flag(FLAG_N), true);
    assert_eq!(cpu.test_flag(FLAG_V), true); // signed overflow
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), false); // borrow set (carry clear)
}

#[test]
fn test_program() {
    use super::memory::RAM;
    use super::bus::Port;
    use std::sync::RwLock;

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

    // Add RAM starting at address 16
    bus.add_port(16..32, Arc::new(RwLock::new(RAM::new(16))));

    // Execute 3 instructions
    let bus = Arc::new(bus);
    let mut cpu = CPU_6502::new(bus.clone());
    for _i in 0..3 {
        cpu.tick();
    }

    assert_eq!(bus.read(16).unwrap(), 8); // 5 + 3 = 8
}
