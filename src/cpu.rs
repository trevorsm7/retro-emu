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
    sp: Data,
    pc: Address,
    bus: Arc<Bus<Address, Data>>,
}

impl CPU_6502 {
    pub fn new(bus: Arc<Bus<Address, Data>>) -> Self {
        let a = 0;
        let x = 0;
        let y = 0;
        let flags = 0;
        let sp = 0xFF;
        let pc = 0; // TODO what should the initial PC/reset vector be?
        Self { a, x, y, flags, sp, pc, bus }
    }

    // Stack functions

    fn push_data(&mut self, data: Data) {
        let stack_page = 0x100;
        self.bus.write(stack_page | self.sp as Address, data).unwrap();
        self.sp -= 1;
    }

    fn pop_data(&mut self) -> Data {
        self.sp += 1;
        let stack_page = 0x100;
        self.bus.read(stack_page | self.sp as Address).unwrap()
    }

    fn push_status(&mut self, interrupt: bool) {
        // Set bit 5 and conditionally set bit 4 if not an interrupt
        let mask = 0b1100_1111;
        let set = 0x20 | ((!interrupt) as u8) << 4;
        self.push_data((self.flags & mask) | set);
    }

    fn pop_status(&mut self) {
        // Clear bits 4 and 5
        let mask = 0b1100_1111;
        self.flags = self.pop_data() & mask;
    }

    fn push_address(&mut self, addr: Address) {
        if cfg!(target_endian = "little") {
            let bytes = addr.to_le_bytes();
            self.push_data(bytes[1]); //< push high byte
            self.push_data(bytes[0]); //< push low byte
        } else if cfg!(target_endian = "big") {
            let bytes = addr.to_be_bytes();
            self.push_data(bytes[0]); //< push high byte
            self.push_data(bytes[1]); //< push low byte
        } else {
            unreachable!();
        }
    }

    fn pop_address(&mut self) -> Address {
        if cfg!(target_endian = "little") {
            let mut bytes = [0; 2];
            bytes[0] = self.pop_data(); //< pop low byte
            bytes[1] = self.pop_data(); //< pop high byte
            u16::from_le_bytes(bytes)
        } else if cfg!(target_endian = "big") {
            let mut bytes = [0; 2];
            bytes[1] = self.pop_data(); //< pop low byte
            bytes[0] = self.pop_data(); //< pop high byte
            u16::from_be_bytes(bytes)
        } else {
            unreachable!();
        }
    }

    // Status functions

    fn set_flag(&mut self, flag: Data, condition: bool) {
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
        self.set_flag(FLAG_N, data & 0x80 != 0);
        self.set_flag(FLAG_Z, data == 0);
    }

    fn compare(&mut self, left: Data, right: Data) {
        self.set_flag(FLAG_N, left < right);
        self.set_flag(FLAG_Z, left == right);
        self.set_flag(FLAG_C, left >= right);
    }

    fn compare_bits(&mut self, left: Data, right: Data) {
        // Set the N and V flags from bits 7 and 6 of the tested address
        self.flags = (self.flags & 0b0011_1111) | (right & 0b1100_0000);
        self.set_flag(FLAG_Z, left & right == 0);
    }

    fn branch(&mut self, flag: Data, condition: bool) {
        let rel = self.read_immediate_data() as i8;
        if self.test_flag(flag) == condition {
            // TODO verify this is correct when bit 15 of PC is set
            self.pc = (self.pc as i16 + rel as i16) as Address;
        }
    }

    // Arithmetic functions

    fn add_carry(&mut self, left: Data, right: Data) -> Data {
        let sum = if self.test_flag(FLAG_D) {
            unimplemented!("TODO Decimal mode unimplemented");
        } else {
            let sum = left as u16 + right as u16 + (self.flags & FLAG_C) as u16;

            // Set carry flag from bit 9 and wrap to 8 bits
            self.set_flag(FLAG_C, sum > 0xFF);
            (sum & 0xFF) as Data
        };

        // TODO it seems that the N and V flags are set incorrectly in BCD mode due to HW bug

        // Compute overflow (carry in xor carry out of bit 7)
        let overflow = (left ^ sum) & (right ^ sum) & 0x80 != 0;
        self.set_flag(FLAG_V, overflow);

        self.update_flags_nz(sum);
        sum
    }

    fn sub_borrow(&mut self, left: Data, right: Data) -> Data {
        // TODO handle decimal mode
        assert_eq!(self.test_flag(FLAG_D), false);
        // NOTE 1s complement of RHS plus carry is equivalent to 2s complement minus borrow
        self.add_carry(left, !right)
    }

    fn increment(&mut self, data: Data) -> Data {
        let result = data.wrapping_add(1);
        self.update_flags_nz(result);
        result
    }

    fn increment_mem(&mut self, addr: Address) {
        let input = self.bus.read(addr).unwrap();
        let result = self.increment(input);
        self.bus.write(addr, result);
    }

    fn decrement(&mut self, data: Data) -> Data {
        let result = data.wrapping_sub(1);
        self.update_flags_nz(result);
        result
    }

    fn decrement_mem(&mut self, addr: Address) {
        let input = self.bus.read(addr).unwrap();
        let result = self.decrement(input);
        self.bus.write(addr, result);
    }

    fn rotate_left(&mut self, input: Data, carry_in: bool) -> Data {
        self.set_flag(FLAG_C, input > 0x7F);
        let result = (input << 1) | (carry_in as u8);
        self.update_flags_nz(result);
        result
    }

    fn rotate_left_mem(&mut self, addr: Address, carry_in: bool) {
        let input = self.bus.read(addr).unwrap();
        let result = self.rotate_left(input, carry_in);
        self.bus.write(addr, result);
    }

    fn rotate_right(&mut self, input: Data, carry_in: bool) -> Data {
        self.set_flag(FLAG_C, input & 0x01 != 0);
        let result = (input >> 1) | ((carry_in as u8) << 7);
        self.update_flags_nz(result);
        result
    }

    fn rotate_right_mem(&mut self, addr: Address, carry_in: bool) {
        let input = self.bus.read(addr).unwrap();
        let result = self.rotate_right(input, carry_in);
        self.bus.write(addr, result);
    }

    // Addressing functions

    fn read_immediate_data(&mut self) -> Data {
        let data = self.bus.read(self.pc).unwrap();
        self.pc += 1;
        data
    }

    fn read_zero_page_address(&mut self) -> Address {
        let addr = self.bus.read(self.pc).unwrap() as Address;
        self.pc += 1;
        addr
    }

    fn read_zero_page_data(&mut self) -> Data {
        let addr = self.read_zero_page_address();
        self.bus.read(addr).unwrap()
    }

    fn read_indexed_zero_page_address(&mut self, index: Data) -> Address {
        // Add index to zero page address, wrapping to zero page
        let base = self.read_zero_page_address();
        (base + index as Address) & 0xFF
    }

    fn read_indexed_zero_page_data(&mut self, index: Data) -> Data {
        let addr = self.read_indexed_zero_page_address(index);
        self.bus.read(addr).unwrap()
    }

    // OP (ZP, X)
    fn read_indexed_indirect_address(&mut self, index: Data) -> Address {
        // Index zero page address, then follow indirect address
        let base = self.read_indexed_zero_page_address(index);
        let addr_lo = self.bus.read(base).unwrap();
        let addr_hi = self.bus.read((base + 1) & 0xFF).unwrap();
        addr_lo as Address | ((addr_hi as Address) << 8)
    }

    fn read_indexed_indirect_data(&mut self, index: Data) -> Data {
        let addr = self.read_indexed_indirect_address(index);
        self.bus.read(addr).unwrap()
    }

    // OP (ZP), Y
    fn read_indirect_indexed_address(&mut self, index: Data) -> Address {
        // Follow zero page address, then index indirect address
        let base = self.read_zero_page_address();
        let addr_lo = self.bus.read(base).unwrap();
        let addr_hi = self.bus.read((base + 1) & 0xFF).unwrap();
        (addr_lo as Address | ((addr_hi as Address) << 8)) + index as Address
    }

    fn read_indirect_indexed_data(&mut self, index: Data) -> Data {
        let addr = self.read_indirect_indexed_address(index);
        self.bus.read(addr).unwrap()
    }

    fn read_absolute_address(&mut self) -> Address {
        // Read 2-byte absolute address
        let addr_lo = self.bus.read(self.pc).unwrap();
        let addr_hi = self.bus.read(self.pc + 1).unwrap();
        self.pc += 2;
        addr_lo as Address | ((addr_hi as Address) << 8)
    }

    fn read_absolute_data(&mut self) -> Data {
        let addr = self.read_absolute_address();
        self.bus.read(addr).unwrap()
    }

    fn read_absolute_indirect_address(&mut self) -> Address {
        let base = self.read_absolute_address();
        let addr_lo = self.bus.read(base).unwrap();
        let addr_hi = self.bus.read(base + 1).unwrap();
        addr_lo as Address | ((addr_hi as Address) << 8)
    }

    fn read_indexed_absolute_address(&mut self, index: Data) -> Address {
        self.read_absolute_address() + index as Address
    }

    fn read_indexed_absolute_data(&mut self, index: Data) -> Data {
        let addr = self.read_indexed_absolute_address(index);
        self.bus.read(addr).unwrap()
    }

    // Instruction decoding

    pub fn tick(&mut self) {
        let op = self.bus.read(self.pc).unwrap();
        self.pc += 1;
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
                let data = self.read_indexed_zero_page_data(self.x);
                self.a = self.add_carry(self.a, data);
            },
            0x6D => { // ADC Abs
                let data = self.read_absolute_data();
                self.a = self.add_carry(self.a, data);
            },
            0x7D => { // ADC Abs, X
                let data = self.read_indexed_absolute_data(self.x);
                self.a = self.add_carry(self.a, data);
            },
            0x79 => { // ADC Abs, Y
                let data = self.read_indexed_absolute_data(self.y);
                self.a = self.add_carry(self.a, data);
            },
            0x61 => { // ADC (ZP, X)
                let data = self.read_indexed_indirect_data(self.x);
                self.a = self.add_carry(self.a, data);
            },
            0x71 => { // ADC (ZP), Y
                let data = self.read_indirect_indexed_data(self.y);
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
                self.a &= self.read_indexed_zero_page_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x2D => { // AND Abs
                self.a &= self.read_absolute_data();
                self.update_flags_nz(self.a);
            },
            0x3D => { // AND Abs, X
                self.a &= self.read_indexed_absolute_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x39 => { // AND Abs, Y
                self.a &= self.read_indexed_absolute_data(self.y);
                self.update_flags_nz(self.a);
            },
            0x21 => { // AND (ZP, X)
                self.a &= self.read_indexed_indirect_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x31 => { // AND (ZP), Y
                self.a &= self.read_indirect_indexed_data(self.y);
                self.update_flags_nz(self.a);
            },
            0x0A => { // ASL A
                self.a = self.rotate_left(self.a, false);
            },
            0x06 => { // ASL ZP
                let addr = self.read_zero_page_address();
                self.rotate_left_mem(addr, false);
            },
            0x16 => { // ASL ZP, X
                let addr = self.read_indexed_zero_page_address(self.x);
                self.rotate_left_mem(addr, false);
            },
            0x0E => { // ASL Abs
                let addr = self.read_absolute_address();
                self.rotate_left_mem(addr, false);
            },
            0x1E => { // ASL Abs, X
                let addr = self.read_indexed_absolute_address(self.x);
                self.rotate_left_mem(addr, false);
            },
            0x90 => { // BCC Rel
                self.branch(FLAG_C, false);
            },
            0xB0 => { // BCS Rel
                self.branch(FLAG_C, true);
            },
            0xF0 => { // BEQ Rel
                self.branch(FLAG_Z, true);
            },
            0x24 => { // BIT ZP
                let mask = self.read_zero_page_data();
                self.compare_bits(self.a, mask);
            },
            0x2C => { // BIT Abs
                let mask = self.read_absolute_data();
                self.compare_bits(self.a, mask);
            },
            0x30 => { // BMI Rel
                self.branch(FLAG_N, true);
            },
            0xD0 => { // BNE Rel
                self.branch(FLAG_Z, false);
            },
            0x10 => { // BPL Rel
                self.branch(FLAG_N, false);
            },
            0x00 => { // BRK
                // NOTE return address skips a byte after BRK
                self.push_address(self.pc + 1);
                self.push_status(false);
                self.set_flag(FLAG_I, true);

                // Jump to interrupt vector 0xFFFE
                //let addr_lo = self.bus.read(0xFFFE).unwrap();
                //let addr_hi = self.bus.read(0xFFFF).unwrap();
                //self.pc = addr_lo as Address | ((addr_hi as Address) << 8);

                // TODO until bus ranges are fixed, just jump to 0 and set break flag to stop loop
                self.set_flag(FLAG_B, true);
                self.pc = 0;
            },
            0x50 => { // BVC Rel
                self.branch(FLAG_V, false);
            },
            0x70 => { // BVS Rel
                self.branch(FLAG_V, true);
            },
            0x18 => { // CLC
                self.set_flag(FLAG_C, false);
            },
            0xD8 => { // CLD
                self.set_flag(FLAG_D, false);
            },
            0x58 => { // CLI
                self.set_flag(FLAG_I, false);
            },
            0xB8 => { // CLV
                self.set_flag(FLAG_V, false);
            },
            0xC9 => { // CMP #Imm
                let data = self.read_immediate_data();
                self.compare(self.a, data);
            },
            0xC5 => { // CMP ZP
                let data = self.read_zero_page_data();
                self.compare(self.a, data);
            },
            0xD5 => { // CMP ZP, X
                let data = self.read_indexed_zero_page_data(self.x);
                self.compare(self.a, data);
            },
            0xCD => { // CMP Abs
                let data = self.read_absolute_data();
                self.compare(self.a, data);
            },
            0xDD => { // CMP Abs, X
                let data = self.read_indexed_absolute_data(self.x);
                self.compare(self.a, data);
            },
            0xD9 => { // CMP Abs, Y
                let data = self.read_indexed_absolute_data(self.y);
                self.compare(self.a, data);
            },
            0xC1 => { // CMP (ZP, X)
                let data = self.read_indexed_indirect_data(self.x);
                self.compare(self.a, data);
            },
            0xD1 => { // CMP (ZP), Y
                let data = self.read_indirect_indexed_data(self.y);
                self.compare(self.a, data);
            },
            0xE0 => { // CPX #Imm
                let data = self.read_immediate_data();
                self.compare(self.x, data);
            },
            0xE4 => { // CPX ZP
                let data = self.read_zero_page_data();
                self.compare(self.x, data);
            },
            0xEC => { // CPX Abs
                let data = self.read_absolute_data();
                self.compare(self.x, data);
            },
            0xC0 => { // CPY #Imm
                let data = self.read_immediate_data();
                self.compare(self.y, data);
            },
            0xC4 => { // CPY ZP
                let data = self.read_zero_page_data();
                self.compare(self.y, data);
            },
            0xCC => { // CPY Abs
                let data = self.read_absolute_data();
                self.compare(self.y, data);
            },
            0xC6 => { // DEC ZP
                let addr = self.read_zero_page_address();
                self.decrement_mem(addr);
            },
            0xD6 => { // DEC ZP, X
                let addr = self.read_indexed_zero_page_address(self.x);
                self.decrement_mem(addr);
            },
            0xCE => { // DEC Abs
                let addr = self.read_absolute_address();
                self.decrement_mem(addr);
            },
            0xDE => { // DEC Abs, X
                let addr = self.read_indexed_absolute_address(self.x);
                self.decrement_mem(addr);
            },
            0xCA => { // DEX
                self.x = self.decrement(self.x);
            },
            0x88 => { // DEY
                self.y = self.decrement(self.y);
            },
            0x49 => { // EOR #Imm
                self.a ^= self.read_immediate_data();
                self.update_flags_nz(self.a);
            },
            0x45 => { // EOR ZP
                self.a ^= self.read_zero_page_data();
                self.update_flags_nz(self.a);
            },
            0x55 => { // EOR ZP, X
                self.a ^= self.read_indexed_zero_page_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x4D => { // EOR Abs
                self.a ^= self.read_absolute_data();
                self.update_flags_nz(self.a);
            },
            0x5D => { // EOR Abs, X
                self.a ^= self.read_indexed_absolute_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x59 => { // EOR Abs, Y
                self.a ^= self.read_indexed_absolute_data(self.y);
                self.update_flags_nz(self.a);
            },
            0x41 => { // EOR (ZP, X)
                self.a ^= self.read_indexed_indirect_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x51 => { // EOR (ZP), Y
                self.a ^= self.read_indirect_indexed_data(self.y);
                self.update_flags_nz(self.a);
            },
            0xE6 => { // INC ZP
                let addr = self.read_zero_page_address();
                self.increment_mem(addr);
            },
            0xF6 => { // INC ZP, X
                let addr = self.read_indexed_zero_page_address(self.x);
                self.increment_mem(addr);
            },
            0xEE => { // INC Abs
                let addr = self.read_absolute_address();
                self.increment_mem(addr);
            },
            0xFE => { // INC Abs, X
                let addr = self.read_indexed_absolute_address(self.x);
                self.increment_mem(addr);
            },
            0xE8 => { // INX
                self.x = self.increment(self.x);
            },
            0xC8 => { // INY
                self.y = self.increment(self.y);
            },
            0x4C => { // JMP Abs
                self.pc = self.read_absolute_address();
            },
            0x6C => { // JMP (Abs)
                self.pc = self.read_absolute_indirect_address();
            },
            0x20 => { // JSR Abs
                let addr = self.read_absolute_address();
                // NOTE for some reason JSR pushes PC - 1 rather than PC
                self.push_address(self.pc - 1);
                self.pc = addr;
            },
            0xA9 => { // LDA #Imm
                self.a = self.read_immediate_data();
                self.update_flags_nz(self.a);
            },
            0xA5 => { // LDA ZP
                self.a = self.read_zero_page_data();
                self.update_flags_nz(self.a);
            },
            0xB5 => { // LDA ZP, X
                self.a = self.read_indexed_zero_page_data(self.x);
                self.update_flags_nz(self.a);
            },
            0xAD => { // LDA Abs
                self.a = self.read_absolute_data();
                self.update_flags_nz(self.a);
            },
            0xBD => { // LDA Abs, X
                self.a = self.read_indexed_absolute_data(self.x);
                self.update_flags_nz(self.a);
            },
            0xB9 => { // LDA Abs, Y
                self.a = self.read_indexed_absolute_data(self.y);
                self.update_flags_nz(self.a);
            },
            0xA1 => { // LDA (ZP, X)
                self.a = self.read_indexed_indirect_data(self.x);
                self.update_flags_nz(self.a);
            },
            0xB1 => { // LDA (ZP), Y
                self.a = self.read_indirect_indexed_data(self.y);
                self.update_flags_nz(self.a);
            },
            0xA2 => { // LDX #Imm
                self.x = self.read_immediate_data();
                self.update_flags_nz(self.x);
            },
            0xA6 => { // LDX ZP
                self.x = self.read_zero_page_data();
                self.update_flags_nz(self.x);
            },
            0xB6 => { // LDX ZP, Y
                self.x = self.read_indexed_zero_page_data(self.y);
                self.update_flags_nz(self.x);
            },
            0xAE => { // LDX Abs
                self.x = self.read_absolute_data();
                self.update_flags_nz(self.x);
            },
            0xBE => { // LDX Abs, Y
                self.x = self.read_indexed_absolute_data(self.y);
                self.update_flags_nz(self.x);
            },
            0xA0 => { // LDY #Imm
                self.y = self.read_immediate_data();
                self.update_flags_nz(self.y);
            },
            0xA4 => { // LDY ZP
                self.y = self.read_zero_page_data();
                self.update_flags_nz(self.y);
            },
            0xB4 => { // LDY ZP, X
                self.y = self.read_indexed_zero_page_data(self.x);
                self.update_flags_nz(self.y);
            },
            0xAC => { // LDY Abs
                self.y = self.read_absolute_data();
                self.update_flags_nz(self.y);
            },
            0xBC => { // LDY Abs, X
                self.y = self.read_indexed_absolute_data(self.x);
                self.update_flags_nz(self.y);
            },
            0x4A => { // LSR A
                self.a = self.rotate_right(self.a, false);
            },
            0x46 => { // LSR ZP
                let addr = self.read_zero_page_address();
                self.rotate_right_mem(addr, false);
            },
            0x56 => { // LSR ZP, X
                let addr = self.read_indexed_zero_page_address(self.x);
                self.rotate_right_mem(addr, false);
            },
            0x4E => { // LSR Abs
                let addr = self.read_absolute_address();
                self.rotate_right_mem(addr, false);
            },
            0x5E => { // LSR Abs, X
                let addr = self.read_indexed_absolute_address(self.x);
                self.rotate_right_mem(addr, false);
            },
            0xEA => { // NOP
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
                self.a |= self.read_indexed_zero_page_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x0D => { // ORA Abs
                self.a |= self.read_absolute_data();
                self.update_flags_nz(self.a);
            },
            0x1D => { // ORA Abs, X
                self.a |= self.read_indexed_absolute_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x19 => { // ORA Abs, Y
                self.a |= self.read_indexed_absolute_data(self.y);
                self.update_flags_nz(self.a);
            },
            0x01 => { // ORA (ZP, X)
                self.a |= self.read_indexed_indirect_data(self.x);
                self.update_flags_nz(self.a);
            },
            0x11 => { // ORA (ZP), Y
                self.a |= self.read_indirect_indexed_data(self.y);
                self.update_flags_nz(self.a);
            },
            0x48 => { // PHA
                self.push_data(self.a);
            },
            0x08 => { // PHP
                self.push_status(false);
            },
            0x68 => { // PLA
                self.a = self.pop_data();
                self.update_flags_nz(self.a);
            },
            0x28 => { // PLP
                self.pop_status();
            },
            0x2A => { // ROL A
                let carry_in = self.test_flag(FLAG_C);
                self.a = self.rotate_left(self.a, carry_in);
            },
            0x26 => { // ROL ZP
                let addr = self.read_zero_page_address();
                let carry_in = self.test_flag(FLAG_C);
                self.rotate_left_mem(addr, carry_in);
            },
            0x36 => { // ROL ZP, X
                let addr = self.read_indexed_zero_page_address(self.x);
                let carry_in = self.test_flag(FLAG_C);
                self.rotate_left_mem(addr, carry_in);
            },
            0x2E => { // ROL Abs
                let addr = self.read_absolute_address();
                let carry_in = self.test_flag(FLAG_C);
                self.rotate_left_mem(addr, carry_in);
            },
            0x3E => { // ROL Abs, X
                let addr = self.read_indexed_absolute_address(self.x);
                let carry_in = self.test_flag(FLAG_C);
                self.rotate_left_mem(addr, carry_in);
            },
            0x6A => { // ROR A
                let carry_in = self.test_flag(FLAG_C);
                self.a = self.rotate_right(self.a, carry_in);
            },
            0x66 => { // ROR ZP
                let addr = self.read_zero_page_address();
                let carry_in = self.test_flag(FLAG_C);
                self.rotate_right_mem(addr, carry_in);
            },
            0x76 => { // ROR ZP, X
                let addr = self.read_indexed_zero_page_address(self.x);
                let carry_in = self.test_flag(FLAG_C);
                self.rotate_right_mem(addr, carry_in);
            },
            0x6E => { // ROR Abs
                let addr = self.read_absolute_address();
                let carry_in = self.test_flag(FLAG_C);
                self.rotate_right_mem(addr, carry_in);
            },
            0x7E => { // ROR Abs, X
                let addr = self.read_indexed_absolute_address(self.x);
                let carry_in = self.test_flag(FLAG_C);
                self.rotate_right_mem(addr, carry_in);
            },
            0x40 => { // RTI
                self.pop_status();
                self.pc = self.pop_address();
            },
            0x60 => { // RTS
                // NOTE JSR pushes PC - 1, so need to add 1
                self.pc = self.pop_address() + 1;
            },
            0xE9 => { // SBC #Imm
                let data = self.read_immediate_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xE5 => { // SBC ZP
                let data = self.read_zero_page_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xF5 => { // SBC ZP, X
                let data = self.read_indexed_zero_page_data(self.x);
                self.a = self.sub_borrow(self.a, data);
            },
            0xED => { // SBC Abs
                let data = self.read_absolute_data();
                self.a = self.sub_borrow(self.a, data);
            },
            0xFD => { // SBC Abs, X
                let data = self.read_indexed_absolute_data(self.x);
                self.a = self.sub_borrow(self.a, data);
            },
            0xF9 => { // SBC Abs, Y
                let data = self.read_indexed_absolute_data(self.y);
                self.a = self.sub_borrow(self.a, data);
            },
            0xE1 => { // SBC (ZP, X)
                let data = self.read_indexed_indirect_data(self.x);
                self.a = self.sub_borrow(self.a, data);
            },
            0xF1 => { // SBC (ZP), Y
                let data = self.read_indirect_indexed_data(self.y);
                self.a = self.sub_borrow(self.a, data);
            },
            0x38 => { // SEC
                self.set_flag(FLAG_C, true);
            },
            0xF8 => { // SED
                self.set_flag(FLAG_D, true);
            },
            0x78 => { // SEI
                self.set_flag(FLAG_I, true);
            },
            0x85 => { // STA ZP
                let addr = self.read_zero_page_address();
                self.bus.write(addr, self.a).unwrap();
            },
            0x95 => { // STA ZP, X
                let addr = self.read_indexed_zero_page_address(self.x);
                self.bus.write(addr, self.a).unwrap();
            },
            0x8D => { // STA Abs
                let addr = self.read_absolute_address();
                self.bus.write(addr, self.a).unwrap();
            },
            0x9D => { // STA Abs, X
                let addr = self.read_indexed_absolute_address(self.x);
                self.bus.write(addr, self.a).unwrap();
            },
            0x99 => { // STA Abs, Y
                let addr = self.read_indexed_absolute_address(self.y);
                self.bus.write(addr, self.a).unwrap();
            },
            0x81 => { // STA (ZP, X)
                let addr = self.read_indexed_indirect_address(self.x);
                self.bus.write(addr, self.a).unwrap();
            },
            0x91 => { // STA (ZP), Y
                let addr = self.read_indirect_indexed_address(self.y);
                self.bus.write(addr, self.a).unwrap();
            },
            0x86 => { // STX ZP
                let addr = self.read_zero_page_address();
                self.bus.write(addr, self.x);
            },
            0x96 => { // STX ZP, Y
                let addr = self.read_indexed_zero_page_address(self.y);
                self.bus.write(addr, self.x);
            },
            0x8E => { // STX Abs
                let addr = self.read_absolute_address();
                self.bus.write(addr, self.x);
            },
            0x84 => { // STY ZP
                let addr = self.read_zero_page_address();
                self.bus.write(addr, self.y);
            },
            0x94 => { // STY ZP, X
                let addr = self.read_indexed_zero_page_address(self.x);
                self.bus.write(addr, self.y);
            },
            0x8C => { // STY Abs
                let addr = self.read_absolute_address();
                self.bus.write(addr, self.y);
            },
            0xAA => { // TAX
                self.x = self.a;
                self.update_flags_nz(self.x);
            },
            0xA8 => { // TAY
                self.y = self.a;
                self.update_flags_nz(self.y);
            },
            0xBA => { // TSX
                self.x = self.sp;
                self.update_flags_nz(self.x);
            },
            0x8A => { // TXA
                self.a = self.x;
                self.update_flags_nz(self.a);
            },
            0x9A => { // TXS
                self.sp = self.x;
                // NOTE does NOT update N and Z flags
            },
            0x98 => { // TYA
                self.a = self.y;
                self.update_flags_nz(self.a);
            },
            _ => panic!(format!("Illegal opcode {} at address {}", op, self.pc))
        };
    }

    pub fn run_until_break(&mut self) {
        while !self.test_flag(FLAG_B) {
            self.tick();
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
    cpu.set_flag(FLAG_C, false);
    assert_eq!(cpu.add_carry(0xFF, 1), 0);
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), false);
    assert_eq!(cpu.test_flag(FLAG_Z), true);
    assert_eq!(cpu.test_flag(FLAG_C), true); // unsigned overflow

    // Unsigned overflow from carry
    cpu.set_flag(FLAG_C, true);
    assert_eq!(cpu.add_carry(0xFF, 0), 0);
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), false);
    assert_eq!(cpu.test_flag(FLAG_Z), true);
    assert_eq!(cpu.test_flag(FLAG_C), true); // unsigned overflow

    // Signed overflow (positive + positive -> negative)
    cpu.set_flag(FLAG_C, false);
    assert_eq!(cpu.add_carry(0x40, 0x40), 0x80);
    assert_eq!(cpu.test_flag(FLAG_N), true);
    assert_eq!(cpu.test_flag(FLAG_V), true); // signed overflow
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), false);

    // Signed overflow (negative + negative -> positive)
    cpu.set_flag(FLAG_C, false);
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
    cpu.set_flag(FLAG_C, true); // clear borrow (set carry)
    assert_eq!(cpu.sub_borrow(0xFF, 0xFF), 0);
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), false);
    assert_eq!(cpu.test_flag(FLAG_Z), true);
    assert_eq!(cpu.test_flag(FLAG_C), true); // borrow clear (carry set)

    // Signed underflow from borrow
    cpu.set_flag(FLAG_C, false); // set borrow (clear carry)
    assert_eq!(cpu.sub_borrow(0, 0), 0xFF);
    assert_eq!(cpu.test_flag(FLAG_N), true);
    assert_eq!(cpu.test_flag(FLAG_V), false);
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), false); // borrow set (carry clear)

    // Signed overflow (negative - positive -> positive)
    cpu.set_flag(FLAG_C, true); // clear borrow (set carry)
    assert_eq!(cpu.sub_borrow(0x80, 0x01), 0x7F); // -128 - 1 = 127
    assert_eq!(cpu.test_flag(FLAG_N), false);
    assert_eq!(cpu.test_flag(FLAG_V), true); // signed overflow
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), true); // borrow clear (carry set)

    // Signed overflow (negative - positive -> positive)
    cpu.set_flag(FLAG_C, true); // clear borrow (set carry)
    assert_eq!(cpu.sub_borrow(0x7F, 0xFF), 0x80); // 127 - (-1) = -128
    assert_eq!(cpu.test_flag(FLAG_N), true);
    assert_eq!(cpu.test_flag(FLAG_V), true); // signed overflow
    assert_eq!(cpu.test_flag(FLAG_Z), false);
    assert_eq!(cpu.test_flag(FLAG_C), false); // borrow set (carry clear)
}

#[test]
fn test_lda_adc_sta() {
    use super::memory::RAM;
    use super::bus::Port;
    use std::sync::RwLock;

    // CPU dictates address and data sizes
    let mut bus = Bus::new();

    let lhs = 5;
    let rhs = 3;
    let result_addr = 16;

    // Add two immediate values and store result to address 16
    let mut rom = RAM::new(512);
    rom.write(0, 0xA9); // LDA #5
    rom.write(1, lhs);
    rom.write(2, 0x69); // ADC #3
    rom.write(3, rhs);
    rom.write(4, 0x85); // STA 16
    rom.write(5, result_addr as u8);
    rom.write(6, 0x00); // BRK
    bus.add_port(0, Arc::new(RwLock::new(rom)));

    // Execute 3 instructions
    let bus = Arc::new(bus);
    let mut cpu = CPU_6502::new(bus.clone());
    cpu.run_until_break();

    assert_eq!(bus.read(result_addr).unwrap(), lhs + rhs);
}

#[test]
fn test_multiplication() {
    use super::memory::RAM;
    use super::bus::Port;
    use std::sync::RwLock;

    // CPU dictates address and data sizes
    let mut bus = Bus::new();

    // Multiplication routine from "Programming the 6502"
    let multiplier = 15;
    let multiplicand = 43;

    let result_addr_lo = 64;
    let multiplier_addr = 65;
    let multiplicand_addr = 66;

    let ram_size = 512;
    let mut ram = RAM::new(ram_size);
    ram.write(0, 0xA9); // LDA #multiplier
    ram.write(1, multiplier); // imm
    ram.write(2, 0x85); // STA multiplier
    ram.write(3, multiplier_addr); // zp
    ram.write(4, 0xA9); // LDA #multiplicand
    ram.write(5, multiplicand); // imm
    ram.write(6, 0x85); // STA multiplicand
    ram.write(7, multiplicand_addr); // zp
    ram.write(8, 0x20); // JSR MULT
    ram.write(9, 12); // abs lo
    ram.write(10, 0); // abs hi
    ram.write(11, 0x00); // BRK
    // MULT:
    ram.write(12, 0xA9); // LDA #0
    ram.write(13, 0); // imm
    ram.write(14, 0x85); // STA result_lo
    ram.write(15, result_addr_lo); // zp
    ram.write(16, 0xA2); // LDX #8
    ram.write(17, 8); // imm
    // LOOP:
    ram.write(18, 0x46); // LSR multiplier
    ram.write(19, multiplier_addr); // zp
    ram.write(20, 0x90); // BCC NOADD
    ram.write(21, (25i8 - 22i8) as u8); // rel
    ram.write(22, 0x18); // CLC
    ram.write(23, 0x65); // ADC multiplicand
    ram.write(24, multiplicand_addr); // zp
    // NOADD:
    ram.write(25, 0x6A); // ROR A (result_hi)
    ram.write(26, 0x66); // ROR result_lo
    ram.write(27, result_addr_lo); // zp
    ram.write(28, 0xCA); // DEX
    ram.write(29, 0xD0); // BNE LOOP
    ram.write(30, (18i8 - 31i8) as u8); // rel
    ram.write(31, 0x60); // RTS
    bus.add_port(0, Arc::new(RwLock::new(ram)));

    // Execute until break
    let bus = Arc::new(bus);
    let mut cpu = CPU_6502::new(bus.clone());
    cpu.run_until_break();

    // Evaluate result
    let result = multiplicand as u16 * multiplier as u16;
    let result_lo = (result & 0xFF) as u8;
    let result_hi = (result >> 8) as u8;
    assert_eq!(bus.read(result_addr_lo as Address).unwrap(), result_lo);
    assert_eq!(cpu.a, result_hi);
}

#[test]
fn test_wrapping() {
    use super::memory::RAM;
    use super::bus::Port;
    use std::sync::RwLock;

    let result1 = 200;
    let result2 = 201;
    let result3 = 202;

    let ram_size = 512;
    let mut ram = RAM::new(ram_size);
    // Test increment/decrement wrapping
    ram.write(0, 0xA2); // LDX #$FF
    ram.write(1, 0xFF); // imm
    ram.write(2, 0xE8); // INX (wrap from 255 to 0)
    ram.write(3, 0x86); // STX result1
    ram.write(4, result1); // zp
    ram.write(5, 0xCA); // DEX (wrap from 0 to 255)
    ram.write(6, 0x86); // STX result2
    ram.write(7, result2); // zp
    // Test zero page indexed wrapping
    ram.write(8, 0xA9); // LDA #1
    ram.write(9, 1); // imm
    ram.write(10, 0xA2); // LDX #result3+1
    ram.write(11, result3 + 1); // imm
    ram.write(12, 0x95); // STA -1, X
    ram.write(13, 255); // zp
    ram.write(14, 0x00); // BRK

    let mut bus = Bus::new();
    bus.add_port(0, Arc::new(RwLock::new(ram)));

    // Execute until break
    let bus = Arc::new(bus);
    let mut cpu = CPU_6502::new(bus.clone());
    cpu.run_until_break();

    assert_eq!(bus.read(result1 as Address).unwrap(), 0);
    assert_eq!(bus.read(result2 as Address).unwrap(), 255);
    assert_eq!(bus.read(result3 as Address).unwrap(), 1);
}
