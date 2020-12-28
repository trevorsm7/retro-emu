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
        self.set_flag(result > 0xFF, FLAG_C);
        let result = (result & 0xFF) as Data;
        self.set_flag((left ^ result) & (right ^ result) & 0x80 != 0, FLAG_V);
        self.update_flags_nz(result);
        result
    }

    fn sub_borrow(&mut self, left: Data, right: Data) -> Data {
        // TODO handle decimal mode
        // NOTE 1s complement of RHS plus carry is equivalent to 2s complement minus borrow
        self.add_carry(left, !right)
    }

    fn read_immediate_data(&mut self) -> Data {
        let data = self.bus.read(self.pc + 1).unwrap();
        self.pc += 2;
        data
    }

    fn read_zero_page_address(&mut self) -> Address {
        let addr = self.bus.read(self.pc + 1).unwrap() as Address;
        self.pc += 2;
        addr
    }

    fn read_zero_page_data(&mut self) -> Data {
        let addr = self.read_zero_page_address();
        self.bus.read(addr).unwrap()
    }

    fn read_zero_page_x_address(&mut self) -> Address {
        // Add X to zero page address, wrapping to zero page
        let base = self.bus.read(self.pc + 1).unwrap() as Address;
        let addr = (base + self.x as Address) & 0xFF;
        self.pc += 2;
        addr
    }

    fn read_zero_page_x_data(&mut self) -> Data {
        let addr = self.read_zero_page_x_address();
        self.bus.read(addr).unwrap()
    }

    fn read_indirect_x_address(&mut self) -> Address {
        // Add X to zero page address, then read 2-byte address
        let base = self.bus.read(self.pc + 1).unwrap() as Address;
        let addr_lo = self.bus.read((base + self.x as Address) & 0xFF).unwrap();
        let addr_hi = self.bus.read((base + self.x as Address + 1) & 0xFF).unwrap();
        let addr = addr_lo as Address | ((addr_hi as Address) << 8);
        self.pc += 2;
        addr
    }

    fn read_indirect_x_data(&mut self) -> Data {
        let addr = self.read_indirect_x_address();
        self.bus.read(addr).unwrap()
    }

    fn read_indirect_y_address(&mut self) -> Address {
        // Read 2-byte address from zero page, then add Y
        let base = self.bus.read(self.pc + 1).unwrap() as Address;
        let addr_lo = self.bus.read(base).unwrap();
        let addr_hi = self.bus.read((base + 1) & 0xFF).unwrap();
        let addr = (addr_lo as Address | ((addr_hi as Address) << 8)) + self.y as Address;
        self.pc += 2;
        // TODO add 1 cycle if page boundary crossed
        addr
    }

    fn read_indirect_y_data(&mut self) -> Data {
        let addr = self.read_indirect_y_address();
        self.bus.read(addr).unwrap()
    }

    fn read_absolute_address(&mut self) -> Address {
        // Read 2-byte absolute address
        let addr_lo = self.bus.read(self.pc + 1).unwrap();
        let addr_hi = self.bus.read(self.pc + 2).unwrap();
        let addr = addr_lo as Address | ((addr_hi as Address) << 8);
        self.pc += 3;
        addr
    }

    fn read_absolute_data(&mut self) -> Data {
        let addr = self.read_absolute_address();
        self.bus.read(addr).unwrap()
    }

    fn read_absolute_x_address(&mut self) -> Address {
        // Add X to absolute address
        let addr_lo = self.bus.read(self.pc + 1).unwrap();
        let addr_hi = self.bus.read(self.pc + 2).unwrap();
        let addr = (addr_lo as Address | ((addr_hi as Address) << 8)) + self.x as Address;
        self.pc += 3;
        // TODO add 1 cycle if page boundary crossed
        addr
    }

    fn read_absolute_x_data(&mut self) -> Data {
        let addr = self.read_absolute_x_address();
        self.bus.read(addr).unwrap()
    }

    fn read_absolute_y_address(&mut self) -> Address {
        // Add Y to absolute address
        let addr_lo = self.bus.read(self.pc + 1).unwrap();
        let addr_hi = self.bus.read(self.pc + 2).unwrap();
        let addr = (addr_lo as Address | ((addr_hi as Address) << 8)) + self.y as Address;
        self.pc += 3;
        // TODO add 1 cycle if page boundary crossed
        addr
    }

    fn read_absolute_y_data(&mut self) -> Data {
        let addr = self.read_absolute_y_address();
        self.bus.read(addr).unwrap()
    }

    pub fn tick(&mut self) {
        let op = self.bus.read(self.pc).unwrap();
        match op {
            0x69 => { // ADC #Imm
                let data = self.read_immediate_data();
                self.a = self.add_carry(self.a, data);
            },
            0x65 => { // ADC ZP
                let data = self.read_zero_page_data();
                self.a = self.add_carry(self.a, data);
            },
            0x75 => { // ADC ZP, X
                let data = self.read_zero_page_x_data();
                self.a = self.add_carry(self.a, data);
            },
            0x6D => { // ADC Abs
                let data = self.read_absolute_data();
                self.a = self.add_carry(self.a, data);
            },
            0x7D => { // ADC Abs, X
                let data = self.read_absolute_x_data();
                self.a = self.add_carry(self.a, data);
            },
            0x79 => { // ADC Abs, Y
                let data = self.read_absolute_y_data();
                self.a = self.add_carry(self.a, data);
            },
            0x61 => { // ADC (ZP, X)
                let data = self.read_indirect_x_data();
                self.a = self.add_carry(self.a, data);
            },
            0x71 => { // ADC (ZP), Y
                let data = self.read_indirect_y_data();
                self.a = self.add_carry(self.a, data);
            },
            0x29 => { // AND #Imm
                self.a &= self.read_immediate_data();
                self.update_flags_nz(self.a);
            },
            0x25 => { // AND ZP
                self.a &= self.read_zero_page_data();
                self.update_flags_nz(self.a);
            },
            0x35 => { // AND ZP, X
                self.a &= self.read_zero_page_x_data();
                self.update_flags_nz(self.a);
            },
            0x2D => { // AND Abs
                self.a &= self.read_absolute_data();
                self.update_flags_nz(self.a);
            },
            0x3D => { // AND Abs, X
                self.a &= self.read_absolute_x_data();
                self.update_flags_nz(self.a);
            },
            0x39 => { // AND Abs, Y
                self.a &= self.read_absolute_y_data();
                self.update_flags_nz(self.a);
            },
            0x21 => { // AND (ZP, X)
                self.a &= self.read_indirect_x_data();
                self.update_flags_nz(self.a);
            },
            0x31 => { // AND (ZP), Y
                self.a &= self.read_indirect_y_data();
                self.update_flags_nz(self.a);
            },
            // ASL
            // BCC
            // BCS
            // BEQ
            // BIT
            // BMI
            // BNE
            // BPL
            // BRK
            // BVC
            // BVS
            // CLC
            // CLD
            // CLI
            // CLV
            0xC9 => { // CMP #Imm
                let data = self.read_immediate_data();
                self.compare(self.a, data);
            },
            0xC5 => { // CMP ZP
                let data = self.read_zero_page_data();
                self.compare(self.a, data);
            },
            0xD5 => { // CMP ZP, X
                let data = self.read_zero_page_x_data();
                self.compare(self.a, data);
            },
            0xCD => { // CMP Abs
                let data = self.read_absolute_data();
                self.compare(self.a, data);
            },
            0xDD => { // CMP Abs, X
                let data = self.read_absolute_x_data();
                self.compare(self.a, data);
            },
            0xD9 => { // CMP Abs, Y
                let data = self.read_absolute_y_data();
                self.compare(self.a, data);
            },
            0xC1 => { // CMP (ZP, X)
                let data = self.read_indirect_x_data();
                self.compare(self.a, data);
            },
            0xD1 => { // CMP (ZP), Y
                let data = self.read_indirect_y_data();
                self.compare(self.a, data);
            },
            // CPX
            // CPY
            // DEC
            // DEX
            // DEY
            0x49 => { // EOR #Imm
                self.a ^= self.read_immediate_data();
                self.update_flags_nz(self.a);
            },
            0x45 => { // EOR ZP
                self.a ^= self.read_zero_page_data();
                self.update_flags_nz(self.a);
            },
            0x55 => { // EOR ZP, X
                self.a ^= self.read_zero_page_x_data();
                self.update_flags_nz(self.a);
            },
            0x4D => { // EOR Abs
                self.a ^= self.read_absolute_data();
                self.update_flags_nz(self.a);
            },
            0x5D => { // EOR Abs, X
                self.a ^= self.read_absolute_x_data();
                self.update_flags_nz(self.a);
            },
            0x59 => { // EOR Abs, Y
                self.a ^= self.read_absolute_y_data();
                self.update_flags_nz(self.a);
            },
            0x41 => { // EOR (ZP, X)
                self.a ^= self.read_indirect_x_data();
                self.update_flags_nz(self.a);
            },
            0x51 => { // EOR (ZP), Y
                self.a ^= self.read_indirect_y_data();
                self.update_flags_nz(self.a);
            },
            // INC
            // INX
            // INY
            // JMP
            // JSR
            0xA9 => { // LDA #Imm
                self.a = self.read_immediate_data();
                self.update_flags_nz(self.a);
            },
            0xA5 => { // LDA ZP
                self.a = self.read_zero_page_data();
                self.update_flags_nz(self.a);
            },
            0xB5 => { // LDA ZP, X
                self.a = self.read_zero_page_x_data();
                self.update_flags_nz(self.a);
            },
            0xAD => { // LDA Abs
                self.a = self.read_absolute_data();
                self.update_flags_nz(self.a);
            },
            0xBD => { // LDA Abs, X
                self.a = self.read_absolute_x_data();
                self.update_flags_nz(self.a);
            },
            0xB9 => { // LDA Abs, Y
                self.a = self.read_absolute_y_data();
                self.update_flags_nz(self.a);
            },
            0xA1 => { // LDA (ZP, X)
                self.a = self.read_indirect_x_data();
                self.update_flags_nz(self.a);
            },
            0xB1 => { // LDA (ZP), Y
                self.a = self.read_indirect_y_data();
                self.update_flags_nz(self.a);
            },
            // LDX
            // LDY
            // LSR
            0xEA => { // NOP
                self.pc += 1;
            },
            0x09 => { // ORA #Imm
                self.a |= self.read_immediate_data();
                self.update_flags_nz(self.a);
            },
            0x05 => { // ORA ZP
                self.a |= self.read_zero_page_data();
                self.update_flags_nz(self.a);
            },
            0x15 => { // ORA ZP, X
                self.a |= self.read_zero_page_x_data();
                self.update_flags_nz(self.a);
            },
            0x0D => { // ORA Abs
                self.a |= self.read_absolute_data();
                self.update_flags_nz(self.a);
            },
            0x1D => { // ORA Abs, X
                self.a |= self.read_absolute_x_data();
                self.update_flags_nz(self.a);
            },
            0x19 => { // ORA Abs, Y
                self.a |= self.read_absolute_y_data();
                self.update_flags_nz(self.a);
            },
            0x01 => { // ORA (ZP, X)
                self.a |= self.read_indirect_x_data();
                self.update_flags_nz(self.a);
            },
            0x11 => { // ORA (ZP), Y
                self.a |= self.read_indirect_y_data();
                self.update_flags_nz(self.a);
            },
            // PHA
            // PHP
            // PLA
            // PLP
            // ROL
            // ROR
            // RTI
            // RTS
            0xE9 => { // SBC #Imm
                let data = self.read_immediate_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xE5 => { // SBC ZP
                let data = self.read_zero_page_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xF5 => { // SBC ZP, X
                let data = self.read_zero_page_x_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xED => { // SBC Abs
                let data = self.read_absolute_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xFD => { // SBC Abs, X
                let data = self.read_absolute_x_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xF9 => { // SBC Abs, Y
                let data = self.read_absolute_y_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xE1 => { // SBC (ZP, X)
                let data = self.read_indirect_x_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xF1 => { // SBC (ZP), Y
                let data = self.read_indirect_y_data();
                self.a = self.sub_borrow(self.a, data);
            },
            // SEC
            // SED
            // SEI
            0x85 => { // STA ZP
                let addr = self.read_zero_page_address();
                self.bus.write(addr, self.a).unwrap();
            },
            0x95 => { // STA ZP, X
                let addr = self.read_zero_page_x_address();
                self.bus.write(addr, self.a).unwrap();
            },
            0x8D => { // STA Abs
                let addr = self.read_absolute_address();
                self.bus.write(addr, self.a).unwrap();
            },
            0x9D => { // STA Abs, X
                let addr = self.read_absolute_x_address();
                self.bus.write(addr, self.a).unwrap();
            },
            0x99 => { // STA Abs, Y
                let addr = self.read_absolute_y_address();
                self.bus.write(addr, self.a).unwrap();
            },
            0x81 => { // STA (ZP, X)
                let addr = self.read_indirect_x_address();
                self.bus.write(addr, self.a).unwrap();
            },
            0x91 => { // STA (ZP), Y
                let addr = self.read_indirect_y_address();
                self.bus.write(addr, self.a).unwrap();
            },
            // STX
            // STY
            // TAX
            // TAY
            // TSX
            // TXA
            // TXS
            // TYA
            _ => panic!(format!("Illegal opcode {} at address {}", op, self.pc))
        };
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
