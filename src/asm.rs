use std::collections::HashMap;

use num_traits::{Num, FromPrimitive};

type Data = u8;
type Address = u16;
type LabelMap = HashMap<String, Address>;

pub fn assemble(source: &str) -> (Vec<(Address, Vec<Data>)>, LabelMap) {
    let mut assembler = Assembler::new();

    // First pass: parse instructions and record labels
    for line in source.lines() {
        assembler.parse_line(line);
    }

    // Second pass: substitute labels skipped during the first pass
    assembler.assemble()
}

#[test]
fn test_assemble() {
    use std::iter::FromIterator;

    let (program, labels) = assemble("");
    assert_eq!(program, vec![]);
    assert_eq!(labels, LabelMap::new());

    let (program, labels) = assemble("
        CODE 0
        ENDCODE");
    assert_eq!(program, vec![(0, vec![])]);
    assert_eq!(labels, LabelMap::new());

    let (program, labels) = assemble("
        CODE $300
            LDX #8
        loop: ASL A ; shift A left 8 times
            DEX
            BNE loop
            BRK
        ENDCODE");
    assert_eq!(program, vec![(0x300, vec![0xA2, 8, 0x0A, 0xCA, 0xD0, (-4i8) as u8, 0x00])]);
    assert_eq!(labels, LabelMap::from_iter(vec![
        ("loop".to_string(), 0x302)]));

    let (program, labels) = assemble("
        CODE $0
            LDA #%00101010
            JSR leading_zeroes
            STA @$FF
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
        ENDCODE");
    assert_eq!(program, vec![
        (0, vec![0xA9, 0b00101010, 0x20, 0x00, 0x02, 0x85, 0xff, 0x00]),
        (0x200, vec![0xA2, (-8i8) as u8, 0x2A, 0xB0, 3, 0xE8, 0xD0, (-6i8) as u8, 0x8A, 0x18, 0x69, 8, 0x60])]);
    assert_eq!(labels, LabelMap::from_iter(vec![
        ("leading_zeroes".to_string(), 0x200),
        ("loop".to_string(), 0x202),
        ("end".to_string(), 0x208)]));
}

#[derive(Clone, Debug, PartialEq)]
enum State {
    Default,
    Code,
}

#[derive(Clone, Debug, PartialEq)]
struct Assembler {
    labels: LabelMap,
    code_segments: Vec<CodeSegment>,
    state: State,
}

impl Assembler {
    fn new() -> Self {
        let labels = LabelMap::new();
        let code_segments = vec![];
        let state = State::Default;
        Assembler {labels, code_segments, state}
    }

    fn assemble(self) -> (Vec<(Address, Vec<Data>)>, LabelMap) {
        let Assembler {labels, mut code_segments, state:_} = self;
        let program = code_segments.drain(..).map(|p| p.assemble(&labels)).collect();
        (program, labels)
    }

    fn parse_line(&mut self, line: &str) {
        // Ignore any comments following first occurence of ';'
        let line = line.split(';').next().unwrap();

        self.state = match &self.state {
            State::Default => {
                // Parse blank line, directive, or instruction
                if line.is_empty() {
                    State::Default
                } else if let Some(directive) = parse_directive(line) {
                    match directive {
                        Directive::Code(address) => {
                            self.code_segments.push(CodeSegment::new(address));
                            State::Code
                        },
                        _ => panic!(format!("Unsupported directive {:?}", directive)),
                    }
                } else {
                    panic!(format!("Unhandled command {}", line));
                }
            },
            State::Code => self.code_segments.last_mut().unwrap().parse_line(line, &mut self.labels),
        };
    }
}

#[derive(Clone, Debug, PartialEq)]
struct CodeSegment {
    offset: Address,
    code: Vec<Data>,
    undefined: Vec<(LabelKind, Address)>,
}

fn compute_relative_address(to: Address, from: Address) -> Data {
    let rel = to as i32 - from as i32;
    assert!(rel >= -128 && rel < 128); //< TODO return result instead of panic
    rel as Data //< TODO make sure that negative labels convert correctly
}

impl CodeSegment {
    fn new(offset: Address) -> Self {
        let code = vec![];
        let undefined = vec![];
        Self {offset, code, undefined}
    }

    fn push_instruction(&mut self, (code, operand): (u8, Operand), labels: &LabelMap) {
        self.code.push(code);
        match operand.get_value(labels) {
            Ok(ValueKind::None) => (),
            Ok(ValueKind::Single(value)) => self.code.push(value),
            Ok(ValueKind::Double(value)) => {
                // Push value as little endian
                self.code.push((value & 0xFF) as Data);
                self.code.push((value >> 8) as Data);
            },
            Ok(ValueKind::Relative(address)) => {
                let from = self.offset + (self.code.len() + 1) as Address;
                self.code.push(compute_relative_address(address, from));
            },
            Err(label) => {
                let size = label.size();
                self.undefined.push((label, self.code.len() as Address));
                self.code.resize(self.code.len() + size, 0);
            },
        };
    }

    fn assemble(self, labels: &LabelMap) -> (Address, Vec<Data>) {
        let CodeSegment {offset, mut code, undefined} = self;

        for (label, position) in undefined {
            // TODO propagate still undefined labels as error
            let &address = labels.get(label.get_label()).unwrap();
            match label {
                LabelKind::ZeroPage(_) => {
                    assert!(address < 256);
                    code[position as usize] = address as Data;
                },
                LabelKind::Absolute(_) => {
                    code[position as usize] = (address & 0xFF) as Data;
                    code[position as usize + 1] = (address >> 8) as Data;
                },
                LabelKind::Relative(_) => {
                    let from = self.offset + position + 1;
                    code[position as usize] = compute_relative_address(address, from);
                },
            };
        }

        (offset, code)
    }

    fn parse_line(&mut self, line: &str, labels: &mut LabelMap) -> State {
        // Split at ':' and set aside rightmost token as a command
        let mut tokens = line.rsplit(':');
        let command = tokens.next().unwrap().trim();

        // Parse remaining tokens as labels (permits multiple labels per line)
        for label in tokens {
            if let Some(label) = parse_label(label.trim()) {
                let address = self.offset + self.code.len() as Address;
                if labels.insert(label.to_string(), address).is_some() {
                    panic!(format!("Label \"{}\" already exists", label));
                }
            } else {
                panic!(format!("Invalid label \"{}\"", label));
            }
        }

        // Parse blank line, directive, or instruction
        if command.is_empty() {
            State::Code
        } else if let Some(directive) = parse_directive(command) {
            match directive {
                Directive::EndCode => State::Default, //< return to parent state
                _ => panic!(format!("Unsupported directive {:?}", directive)),
            }
        } else if let Some(instruction) = parse_instruction(command) {
            self.push_instruction(instruction, labels);
            State::Code
        } else {
            panic!(format!("Invalid command \"{}\"", command));
        }
    }
}

fn parse_number<T: Num>(token: &str) -> Result<T, T::FromStrRadixErr> {
    if let Some(hex) = token.strip_prefix('$') {
        T::from_str_radix(hex, 16)
    } else if let Some(bin) = token.strip_prefix('%') {
        T::from_str_radix(bin, 2)
    } else {
        T::from_str_radix(token, 10)
    }
}

#[test]
fn test_parse_number() {
    assert_eq!(parse_number("$FF"), Ok(0xFF));
    assert_eq!(parse_number("%1010"), Ok(0b1010));
    assert_eq!(parse_number("1234"), Ok(1234));
    assert_eq!(parse_number("-123"), Ok(-123));
    assert_eq!(parse_number::<i16>("-1").map(|i| i as u8), Ok(255));
    assert!(parse_number::<u16>("twenty").is_err());
}

fn parse_label(token: &str) -> Option<&str> {
    // First char must be alphabetic and remainder must be alphanumeric
    let valid = |c| !(char::is_alphanumeric(c) || c == '_');
    if token.starts_with(char::is_alphabetic) && token.find(valid).is_none() {
        Some(token)
    } else {
        None
    }
}

#[test]
fn test_parse_label() {
    assert_eq!(parse_label("foo"), Some("foo"));
    assert_eq!(parse_label("bar1"), Some("bar1"));
    assert_eq!(parse_label("1baz"), None);
    assert_eq!(parse_label("bad space"), None);
    assert_eq!(parse_label("ok_underscore"), Some("ok_underscore"));
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Symbol<'a, T> {
    Value(T),
    Label(&'a str),
}

impl<'a, T> Symbol<'a, T> {
    fn size(&self) -> usize {
        std::mem::size_of::<T>()
    }

    fn get_value(&self, labels: &LabelMap) -> Result<T, &str> where T: Copy + FromPrimitive {
        match *self {
            Self::Value(value) => Ok(value),
            Self::Label(label) => match labels.get(label) {
                Some(&value) => Ok(T::from_u16(value).unwrap()), //< TODO may need to handle this unwrap
                None => Err(label),
            }
        }
    }
}

fn parse_symbol<T: Num>(token: &str) -> Result<Symbol<T>, T::FromStrRadixErr> {
    if let Some(label) = parse_label(token) {
        Ok(Symbol::Label(label))
    } else {
        parse_number(token).map(Symbol::Value)
    }
}

#[test]
fn test_parse_symbol() {
    assert_eq!(parse_symbol("$FF"), Ok(Symbol::Value(0xFF)));
    assert_eq!(parse_symbol("%1010"), Ok(Symbol::Value(0b1010)));
    assert_eq!(parse_symbol("1234"), Ok(Symbol::Value(1234)));
    assert_eq!(parse_symbol::<Data>("twenty"), Ok(Symbol::Label("twenty")));
    assert!(parse_symbol::<Data>("***").is_err());
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum ValueKind {
    None,
    Single(Data),
    Double(Address),
    Relative(Address),
}

#[derive(Clone, Debug, PartialEq)]
enum LabelKind {
    ZeroPage(String),
    Absolute(String),
    Relative(String),
}

impl LabelKind {
    fn size(&self) -> usize {
        match self {
            Self::ZeroPage(_) => 1,
            Self::Absolute(_) => 2,
            Self::Relative(_) => 1,
        }
    }

    fn get_label(&self) -> &str {
        match self {
            Self::ZeroPage(label) => label,
            Self::Absolute(label) => label,
            Self::Relative(label) => label,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Operand<'a> {
    Implied,
    Accumulator,
    Immediate(Data),
    Relative(Symbol<'a, Address>), //< NOTE the full address is converted to 1 byte relative address when assembled
    ZeroPage(Symbol<'a, Data>),
    ZeroPageX(Symbol<'a, Data>),
    ZeroPageY(Symbol<'a, Data>),
    Absolute(Symbol<'a, Address>),
    AbsoluteX(Symbol<'a, Address>),
    AbsoluteY(Symbol<'a, Address>),
    Indirect(Symbol<'a, Address>), //< absolute
    IndexedIndirectX(Symbol<'a, Data>), //< zero page
    IndirectIndexedY(Symbol<'a, Data>), //< zero page
    // TODO
}

impl<'a> Operand<'a> {
    fn size(&self) -> usize {
        match self {
            Self::Implied => 0,
            Self::Accumulator => 0,
            Self::Immediate(data) => std::mem::size_of_val(data),
            Self::Relative(_) => 1, // NOTE assembler must store full (2 byte) address until assembly
            Self::ZeroPage(sym) => sym.size(),
            Self::ZeroPageX(sym) => sym.size(),
            Self::ZeroPageY(sym) => sym.size(),
            Self::Absolute(sym) => sym.size(),
            Self::AbsoluteX(sym) => sym.size(),
            Self::AbsoluteY(sym) => sym.size(),
            Self::Indirect(sym) => sym.size(),
            Self::IndexedIndirectX(sym) => sym.size(),
            Self::IndirectIndexedY(sym) => sym.size(),
        }
    }

    fn get_value(&self, labels: &LabelMap) -> Result<ValueKind, LabelKind> {
        match *self {
            Self::Implied => Ok(ValueKind::None),
            Self::Accumulator => Ok(ValueKind::None),
            Self::Immediate(data) => Ok(ValueKind::Single(data)),
            Self::Relative(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Relative(value)),
                Err(label) => Err(LabelKind::Relative(label.to_string())),
            },
            Self::ZeroPage(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Single(value)),
                Err(label) => Err(LabelKind::ZeroPage(label.to_string())),
            },
            Self::ZeroPageX(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Single(value)),
                Err(label) => Err(LabelKind::ZeroPage(label.to_string())),
            },
            Self::ZeroPageY(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Single(value)),
                Err(label) => Err(LabelKind::ZeroPage(label.to_string())),
            },
            Self::Absolute(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Double(value)),
                Err(label) => Err(LabelKind::Absolute(label.to_string())),
            },
            Self::AbsoluteX(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Double(value)),
                Err(label) => Err(LabelKind::Absolute(label.to_string())),
            },
            Self::AbsoluteY(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Double(value)),
                Err(label) => Err(LabelKind::Absolute(label.to_string())),
            },
            Self::Indirect(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Double(value)),
                Err(label) => Err(LabelKind::Absolute(label.to_string())),
            },
            Self::IndexedIndirectX(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Single(value)),
                Err(label) => Err(LabelKind::ZeroPage(label.to_string())),
            },
            Self::IndirectIndexedY(symbol) => match symbol.get_value(labels) {
                Ok(value) => Ok(ValueKind::Single(value)),
                Err(label) => Err(LabelKind::ZeroPage(label.to_string())),
            },
        }
    }
}

fn parse_operand(token: &str) -> Option<Operand> {
    if token.is_empty() {
        Some(Operand::Implied)
    } else if token == "A" || token == "a" {
        Some(Operand::Accumulator)
    } else if let Some(immediate) = token.strip_prefix('#') {
        // NOTE parsing as i16 and converting to u8 to allow parsing negative values
        // TODO do this more explicitly and validate value in range [-128, 255]
        parse_number::<i16>(immediate).ok().map(|i| Operand::Immediate(i as Data))
    } else if let Some(indirect) = token.strip_prefix('(') {
        let mut tokens = indirect.splitn(2, ')');
        let inner = tokens.next().unwrap().trim();
        let outer = tokens.next().unwrap().trim(); //< TODO return error if closing ) not present
        if outer.is_empty() {
            let mut tokens = inner.splitn(2, ',');
            let symbol = tokens.next().unwrap().trim();
            if let Some(index) = tokens.next().map(str::trim) {
                if index == "X" || index == "x" {
                    parse_symbol(symbol).ok().map(Operand::IndexedIndirectX)
                } else {
                    None
                }
            } else {
                parse_symbol(inner).ok().map(Operand::Indirect)
            }
        } else if let Some(index) = outer.strip_prefix(',').map(str::trim) {
            if index == "Y" || index == "y" {
                parse_symbol(inner).ok().map(Operand::IndirectIndexedY)
            } else {
                None
            }
        } else {
            None
        }
    } else if let Some(token) = token.strip_prefix('@') {
        // TODO refactor zero page and absolute processing together
        let mut tokens = token.splitn(2, ',');
        let symbol = parse_symbol(tokens.next().unwrap().trim()).ok()?;
        if let Some(index) = tokens.next().map(str::trim) {
            if index == "X" || index == "x" {
                Some(Operand::ZeroPageX(symbol))
            } else if index == "Y" || index == "y" {
                Some(Operand::ZeroPageY(symbol))
            } else {
                None
            }
        } else {
            Some(Operand::ZeroPage(symbol))
        }
    } else {
        let mut tokens = token.splitn(2, ',');
        let symbol = parse_symbol(tokens.next().unwrap().trim()).ok()?;
        if let Some(index) = tokens.next().map(str::trim) {
            if index == "X" || index == "x" {
                Some(Operand::AbsoluteX(symbol))
            } else if index == "Y" || index == "y" {
                Some(Operand::AbsoluteY(symbol))
            } else {
                None
            }
        } else {
            Some(Operand::Absolute(symbol))
        }
    }
}

#[test]
fn test_parse_operand() {
    assert_eq!(parse_operand(""), Some(Operand::Implied));
    assert_eq!(parse_operand("#$FF"), Some(Operand::Immediate(0xFF)));
    assert_eq!(parse_operand("#-10"), Some(Operand::Immediate((-10i8) as u8)));
    assert_eq!(parse_operand("@%1010"), Some(Operand::ZeroPage(Symbol::Value(0b1010))));
    assert_eq!(parse_operand("@123,X"), Some(Operand::ZeroPageX(Symbol::Value(123))));
    assert_eq!(parse_operand("@$10,Y"), Some(Operand::ZeroPageY(Symbol::Value(0x10))));
    assert_eq!(parse_operand("1024"), Some(Operand::Absolute(Symbol::Value(1024))));
    assert_eq!(parse_operand("$FFFF, X"), Some(Operand::AbsoluteX(Symbol::Value(0xFFFF))));
    assert_eq!(parse_operand("%0, y"), Some(Operand::AbsoluteY(Symbol::Value(0))));
    assert_eq!(parse_operand("(label)"), Some(Operand::Indirect(Symbol::Label("label"))));
    assert_eq!(parse_operand("(label, x)"), Some(Operand::IndexedIndirectX(Symbol::Label("label"))));
    assert_eq!(parse_operand("(label), y"), Some(Operand::IndirectIndexedY(Symbol::Label("label"))));
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Mnemonic {
    ADC, AND, ASL, BCC, BCS, BEQ, BIT, BMI, BNE, BPL, BRK, BVC, BVS, CLC, CLD, CLI, CLV, CMP, CPX,
    CPY, DEC, DEX, DEY, EOR, INC, INX, INY, JMP, JSR, LDA, LDX, LDY, LSR, NOP, ORA, PHA, PHP, PLA,
    PLP, ROL, ROR, RTI, RTS, SBC, SEC, SED, SEI, STA, STX, STY, TAX, TAY, TSX, TXA, TXS, TYA,
}

// TODO consider using a macro to generate this
fn parse_mnemonic(mnemonic: &str) -> Option<Mnemonic> {
    match mnemonic.to_ascii_uppercase().as_ref() {
        "ADC" => Some(Mnemonic::ADC),
        "AND" => Some(Mnemonic::AND),
        "ASL" => Some(Mnemonic::ASL),
        "BCC" => Some(Mnemonic::BCC),
        "BCS" => Some(Mnemonic::BCS),
        "BEQ" => Some(Mnemonic::BEQ),
        "BIT" => Some(Mnemonic::BIT),
        "BMI" => Some(Mnemonic::BMI),
        "BNE" => Some(Mnemonic::BNE),
        "BPL" => Some(Mnemonic::BPL),
        "BRK" => Some(Mnemonic::BRK),
        "BVC" => Some(Mnemonic::BVC),
        "BVS" => Some(Mnemonic::BVS),
        "CLC" => Some(Mnemonic::CLC),
        "CLD" => Some(Mnemonic::CLD),
        "CLI" => Some(Mnemonic::CLI),
        "CLV" => Some(Mnemonic::CLV),
        "CMP" => Some(Mnemonic::CMP),
        "CPX" => Some(Mnemonic::CPX),
        "CPY" => Some(Mnemonic::CPY),
        "DEC" => Some(Mnemonic::DEC),
        "DEX" => Some(Mnemonic::DEX),
        "DEY" => Some(Mnemonic::DEY),
        "EOR" => Some(Mnemonic::EOR),
        "INC" => Some(Mnemonic::INC),
        "INX" => Some(Mnemonic::INX),
        "INY" => Some(Mnemonic::INY),
        "JMP" => Some(Mnemonic::JMP),
        "JSR" => Some(Mnemonic::JSR),
        "LDA" => Some(Mnemonic::LDA),
        "LDX" => Some(Mnemonic::LDX),
        "LDY" => Some(Mnemonic::LDY),
        "LSR" => Some(Mnemonic::LSR),
        "NOP" => Some(Mnemonic::NOP),
        "ORA" => Some(Mnemonic::ORA),
        "PHA" => Some(Mnemonic::PHA),
        "PHP" => Some(Mnemonic::PHP),
        "PLA" => Some(Mnemonic::PLA),
        "PLP" => Some(Mnemonic::PLP),
        "ROL" => Some(Mnemonic::ROL),
        "ROR" => Some(Mnemonic::ROR),
        "RTI" => Some(Mnemonic::RTI),
        "RTS" => Some(Mnemonic::RTS),
        "SBC" => Some(Mnemonic::SBC),
        "SEC" => Some(Mnemonic::SEC),
        "SED" => Some(Mnemonic::SED),
        "SEI" => Some(Mnemonic::SEI),
        "STA" => Some(Mnemonic::STA),
        "STX" => Some(Mnemonic::STX),
        "STY" => Some(Mnemonic::STY),
        "TAX" => Some(Mnemonic::TAX),
        "TAY" => Some(Mnemonic::TAY),
        "TSX" => Some(Mnemonic::TSX),
        "TXA" => Some(Mnemonic::TXA),
        "TXS" => Some(Mnemonic::TXS),
        "TYA" => Some(Mnemonic::TYA),
        _ => None,
    }
}

fn parse_instruction(instruction: &str) -> Option<(u8, Operand)> {
    // Parse mnemonic and optional operand separated by whitespace
    let mut tokens = instruction.splitn(2, char::is_whitespace);

    // If mnemnonic is unrecognized, return None to continue parsing
    let mnemonic = parse_mnemonic(tokens.next().unwrap())?;

    // TODO If mnemonic is valid but operand is not, return an error
    let operand = parse_operand(tokens.next().unwrap_or("").trim()).unwrap();

    match (mnemonic, operand) {
        (Mnemonic::ADC, Operand::Immediate(_)) => Some((0x69, operand)),
        (Mnemonic::ADC, Operand::ZeroPage(_)) => Some((0x65, operand)),
        (Mnemonic::ADC, Operand::ZeroPageX(_)) => Some((0x75, operand)),
        (Mnemonic::ADC, Operand::Absolute(_)) => Some((0x6D, operand)),
        (Mnemonic::ADC, Operand::AbsoluteX(_)) => Some((0x7D, operand)),
        (Mnemonic::ADC, Operand::AbsoluteY(_)) => Some((0x79, operand)),
        (Mnemonic::ADC, Operand::IndexedIndirectX(_)) => Some((0x61, operand)),
        (Mnemonic::ADC, Operand::IndirectIndexedY(_)) => Some((0x71, operand)),
        (Mnemonic::AND, Operand::Immediate(_)) => Some((0x29, operand)),
        (Mnemonic::AND, Operand::ZeroPage(_)) => Some((0x25, operand)),
        (Mnemonic::AND, Operand::ZeroPageX(_)) => Some((0x35, operand)),
        (Mnemonic::AND, Operand::Absolute(_)) => Some((0x2D, operand)),
        (Mnemonic::AND, Operand::AbsoluteX(_)) => Some((0x3D, operand)),
        (Mnemonic::AND, Operand::AbsoluteY(_)) => Some((0x39, operand)),
        (Mnemonic::AND, Operand::IndexedIndirectX(_)) => Some((0x21, operand)),
        (Mnemonic::AND, Operand::IndirectIndexedY(_)) => Some((0x31, operand)),
        (Mnemonic::ASL, Operand::Accumulator) => Some((0x0A, operand)),
        (Mnemonic::ASL, Operand::ZeroPage(_)) => Some((0x06, operand)),
        (Mnemonic::ASL, Operand::ZeroPageX(_)) => Some((0x16, operand)),
        (Mnemonic::ASL, Operand::Absolute(_)) => Some((0x0E, operand)),
        (Mnemonic::ASL, Operand::AbsoluteX(_)) => Some((0x1E, operand)),
        (Mnemonic::BCC, Operand::Absolute(symbol)) => Some((0x90, Operand::Relative(symbol))),
        (Mnemonic::BCS, Operand::Absolute(symbol)) => Some((0xB0, Operand::Relative(symbol))),
        (Mnemonic::BEQ, Operand::Absolute(symbol)) => Some((0xF0, Operand::Relative(symbol))),
        (Mnemonic::BIT, Operand::ZeroPage(_)) => Some((0x24, operand)),
        (Mnemonic::BIT, Operand::Absolute(_)) => Some((0x2C, operand)),
        (Mnemonic::BMI, Operand::Absolute(symbol)) => Some((0x30, Operand::Relative(symbol))),
        (Mnemonic::BNE, Operand::Absolute(symbol)) => Some((0xD0, Operand::Relative(symbol))),
        (Mnemonic::BPL, Operand::Absolute(symbol)) => Some((0x10, Operand::Relative(symbol))),
        (Mnemonic::BRK, Operand::Implied) => Some((0x00, operand)), //< TODO assemble as 2 bytes? maybe warn if not followed by NOP?
        (Mnemonic::BVC, Operand::Absolute(symbol)) => Some((0x50, Operand::Relative(symbol))),
        (Mnemonic::BVS, Operand::Absolute(symbol)) => Some((0x70, Operand::Relative(symbol))),
        (Mnemonic::CLC, Operand::Implied) => Some((0x18, operand)),
        (Mnemonic::CLD, Operand::Implied) => Some((0xD8, operand)),
        (Mnemonic::CLI, Operand::Implied) => Some((0x58, operand)),
        (Mnemonic::CLV, Operand::Implied) => Some((0xB8, operand)),
        (Mnemonic::CMP, Operand::Immediate(_)) => Some((0xC9, operand)),
        (Mnemonic::CMP, Operand::ZeroPage(_)) => Some((0xC5, operand)),
        (Mnemonic::CMP, Operand::ZeroPageX(_)) => Some((0xD5, operand)),
        (Mnemonic::CMP, Operand::Absolute(_)) => Some((0xCD, operand)),
        (Mnemonic::CMP, Operand::AbsoluteX(_)) => Some((0xDD, operand)),
        (Mnemonic::CMP, Operand::AbsoluteY(_)) => Some((0xD9, operand)),
        (Mnemonic::CMP, Operand::IndexedIndirectX(_)) => Some((0xC1, operand)),
        (Mnemonic::CMP, Operand::IndirectIndexedY(_)) => Some((0xD1, operand)),
        (Mnemonic::CPX, Operand::Immediate(_)) => Some((0xE0, operand)),
        (Mnemonic::CPX, Operand::ZeroPage(_)) => Some((0xE4, operand)),
        (Mnemonic::CPX, Operand::Absolute(_)) => Some((0xEC, operand)),
        (Mnemonic::CPY, Operand::Immediate(_)) => Some((0xC0, operand)),
        (Mnemonic::CPY, Operand::ZeroPage(_)) => Some((0xC4, operand)),
        (Mnemonic::CPY, Operand::Absolute(_)) => Some((0xCC, operand)),
        (Mnemonic::DEC, Operand::ZeroPage(_)) => Some((0xC6, operand)),
        (Mnemonic::DEC, Operand::ZeroPageX(_)) => Some((0xD6, operand)),
        (Mnemonic::DEC, Operand::Absolute(_)) => Some((0xCE, operand)),
        (Mnemonic::DEC, Operand::AbsoluteX(_)) => Some((0xDE, operand)),
        (Mnemonic::DEX, Operand::Implied) => Some((0xCA, operand)),
        (Mnemonic::DEY, Operand::Implied) => Some((0x88, operand)),
        (Mnemonic::EOR, Operand::Immediate(_)) => Some((0x49, operand)),
        (Mnemonic::EOR, Operand::ZeroPage(_)) => Some((0x45, operand)),
        (Mnemonic::EOR, Operand::ZeroPageX(_)) => Some((0x55, operand)),
        (Mnemonic::EOR, Operand::Absolute(_)) => Some((0x4D, operand)),
        (Mnemonic::EOR, Operand::AbsoluteX(_)) => Some((0x5D, operand)),
        (Mnemonic::EOR, Operand::AbsoluteY(_)) => Some((0x59, operand)),
        (Mnemonic::EOR, Operand::IndexedIndirectX(_)) => Some((0x41, operand)),
        (Mnemonic::EOR, Operand::IndirectIndexedY(_)) => Some((0x51, operand)),
        (Mnemonic::INC, Operand::ZeroPage(_)) => Some((0xE6, operand)),
        (Mnemonic::INC, Operand::ZeroPageX(_)) => Some((0xF6, operand)),
        (Mnemonic::INC, Operand::Absolute(_)) => Some((0xEE, operand)),
        (Mnemonic::INC, Operand::AbsoluteX(_)) => Some((0xFE, operand)),
        (Mnemonic::INX, Operand::Implied) => Some((0xE8, operand)),
        (Mnemonic::INY, Operand::Implied) => Some((0xC8, operand)),
        (Mnemonic::JMP, Operand::Absolute(_)) => Some((0x4C, operand)),
        (Mnemonic::JMP, Operand::Indirect(_)) => Some((0x6C, operand)),
        (Mnemonic::JSR, Operand::Absolute(_)) => Some((0x20, operand)),
        (Mnemonic::LDA, Operand::Immediate(_)) => Some((0xA9, operand)),
        (Mnemonic::LDA, Operand::ZeroPage(_)) => Some((0xA5, operand)),
        (Mnemonic::LDA, Operand::ZeroPageX(_)) => Some((0xB5, operand)),
        (Mnemonic::LDA, Operand::Absolute(_)) => Some((0xAD, operand)),
        (Mnemonic::LDA, Operand::AbsoluteX(_)) => Some((0xBD, operand)),
        (Mnemonic::LDA, Operand::AbsoluteY(_)) => Some((0xB9, operand)),
        (Mnemonic::LDA, Operand::IndexedIndirectX(_)) => Some((0xA1, operand)),
        (Mnemonic::LDA, Operand::IndirectIndexedY(_)) => Some((0xB1, operand)),
        (Mnemonic::LDX, Operand::Immediate(_)) => Some((0xA2, operand)),
        (Mnemonic::LDX, Operand::ZeroPage(_)) => Some((0xA6, operand)),
        (Mnemonic::LDX, Operand::ZeroPageY(_)) => Some((0xB6, operand)),
        (Mnemonic::LDX, Operand::Absolute(_)) => Some((0xAE, operand)),
        (Mnemonic::LDX, Operand::AbsoluteY(_)) => Some((0xBE, operand)),
        (Mnemonic::LDY, Operand::Immediate(_)) => Some((0xA0, operand)),
        (Mnemonic::LDY, Operand::ZeroPage(_)) => Some((0xA4, operand)),
        (Mnemonic::LDY, Operand::ZeroPageX(_)) => Some((0xB4, operand)),
        (Mnemonic::LDY, Operand::Absolute(_)) => Some((0xAC, operand)),
        (Mnemonic::LDY, Operand::AbsoluteX(_)) => Some((0xBC, operand)),
        (Mnemonic::LSR, Operand::Accumulator) => Some((0x4A, operand)),
        (Mnemonic::LSR, Operand::ZeroPage(_)) => Some((0x46, operand)),
        (Mnemonic::LSR, Operand::ZeroPageX(_)) => Some((0x56, operand)),
        (Mnemonic::LSR, Operand::Absolute(_)) => Some((0x4E, operand)),
        (Mnemonic::LSR, Operand::AbsoluteX(_)) => Some((0x5E, operand)),
        (Mnemonic::NOP, Operand::Implied) => Some((0xEA, operand)),
        (Mnemonic::ORA, Operand::Immediate(_)) => Some((0x09, operand)),
        (Mnemonic::ORA, Operand::ZeroPage(_)) => Some((0x05, operand)),
        (Mnemonic::ORA, Operand::ZeroPageX(_)) => Some((0x15, operand)),
        (Mnemonic::ORA, Operand::Absolute(_)) => Some((0x0D, operand)),
        (Mnemonic::ORA, Operand::AbsoluteX(_)) => Some((0x1D, operand)),
        (Mnemonic::ORA, Operand::AbsoluteY(_)) => Some((0x19, operand)),
        (Mnemonic::ORA, Operand::IndexedIndirectX(_)) => Some((0x01, operand)),
        (Mnemonic::ORA, Operand::IndirectIndexedY(_)) => Some((0x11, operand)),
        (Mnemonic::PHA, Operand::Implied) => Some((0x48, operand)),
        (Mnemonic::PHP, Operand::Implied) => Some((0x08, operand)),
        (Mnemonic::PLA, Operand::Implied) => Some((0x68, operand)),
        (Mnemonic::PLP, Operand::Implied) => Some((0x28, operand)),
        (Mnemonic::ROL, Operand::Accumulator) => Some((0x2A, operand)),
        (Mnemonic::ROL, Operand::ZeroPage(_)) => Some((0x26, operand)),
        (Mnemonic::ROL, Operand::ZeroPageX(_)) => Some((0x36, operand)),
        (Mnemonic::ROL, Operand::Absolute(_)) => Some((0x2E, operand)),
        (Mnemonic::ROL, Operand::AbsoluteX(_)) => Some((0x3E, operand)),
        (Mnemonic::ROR, Operand::Accumulator) => Some((0x6A, operand)),
        (Mnemonic::ROR, Operand::ZeroPage(_)) => Some((0x66, operand)),
        (Mnemonic::ROR, Operand::ZeroPageX(_)) => Some((0x76, operand)),
        (Mnemonic::ROR, Operand::Absolute(_)) => Some((0x6E, operand)),
        (Mnemonic::ROR, Operand::AbsoluteX(_)) => Some((0x7E, operand)),
        (Mnemonic::RTI, Operand::Implied) => Some((0x40, operand)),
        (Mnemonic::RTS, Operand::Implied) => Some((0x60, operand)),
        (Mnemonic::SBC, Operand::Immediate(_)) => Some((0xE9, operand)),
        (Mnemonic::SBC, Operand::ZeroPage(_)) => Some((0xE5, operand)),
        (Mnemonic::SBC, Operand::ZeroPageX(_)) => Some((0xF5, operand)),
        (Mnemonic::SBC, Operand::Absolute(_)) => Some((0xED, operand)),
        (Mnemonic::SBC, Operand::AbsoluteX(_)) => Some((0xFD, operand)),
        (Mnemonic::SBC, Operand::AbsoluteY(_)) => Some((0xF9, operand)),
        (Mnemonic::SBC, Operand::IndexedIndirectX(_)) => Some((0xE1, operand)),
        (Mnemonic::SBC, Operand::IndirectIndexedY(_)) => Some((0xF1, operand)),
        (Mnemonic::SEC, Operand::Implied) => Some((0x38, operand)),
        (Mnemonic::SED, Operand::Implied) => Some((0xF8, operand)),
        (Mnemonic::SEI, Operand::Implied) => Some((0x78, operand)),
        (Mnemonic::STA, Operand::ZeroPage(_)) => Some((0x85, operand)),
        (Mnemonic::STA, Operand::ZeroPageX(_)) => Some((0x95, operand)),
        (Mnemonic::STA, Operand::Absolute(_)) => Some((0x8D, operand)),
        (Mnemonic::STA, Operand::AbsoluteX(_)) => Some((0x9D, operand)),
        (Mnemonic::STA, Operand::AbsoluteY(_)) => Some((0x99, operand)),
        (Mnemonic::STA, Operand::IndexedIndirectX(_)) => Some((0x81, operand)),
        (Mnemonic::STA, Operand::IndirectIndexedY(_)) => Some((0x91, operand)),
        (Mnemonic::STX, Operand::ZeroPage(_)) => Some((0x86, operand)),
        (Mnemonic::STX, Operand::ZeroPageY(_)) => Some((0x96, operand)),
        (Mnemonic::STX, Operand::Absolute(_)) => Some((0x8E, operand)),
        (Mnemonic::STY, Operand::ZeroPage(_)) => Some((0x84, operand)),
        (Mnemonic::STY, Operand::ZeroPageX(_)) => Some((0x94, operand)),
        (Mnemonic::STY, Operand::Absolute(_)) => Some((0x8C, operand)),
        (Mnemonic::TAX, Operand::Implied) => Some((0xAA, operand)),
        (Mnemonic::TAY, Operand::Implied) => Some((0xA8, operand)),
        (Mnemonic::TSX, Operand::Implied) => Some((0xBA, operand)),
        (Mnemonic::TXA, Operand::Implied) => Some((0x8A, operand)),
        (Mnemonic::TXS, Operand::Implied) => Some((0x9A, operand)),
        (Mnemonic::TYA, Operand::Implied) => Some((0x98, operand)),
        _ => panic!("Unsupported addressing mode"), //< TODO return error
    }
}

#[test]
fn test_parse_instruction() {
    assert_eq!(parse_instruction("ADC #$FF"), Some((0x69, Operand::Immediate(0xFF))));
    assert_eq!(parse_instruction("ADC @$20"), Some((0x65, Operand::ZeroPage(Symbol::Value(0x20)))));
    assert_eq!(parse_instruction("JMP (label)"), Some((0x6C, Operand::Indirect(Symbol::Label("label")))));
    assert_eq!(parse_instruction("BNE rel"), Some((0xD0, Operand::Relative(Symbol::Label("rel")))));
    assert_eq!(parse_instruction("BRK"), Some((0x00, Operand::Implied)));
    assert_eq!(parse_instruction("WOT que?"), None);
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Directive {
    Code(Address),
    EndCode,
}

fn parse_directive(directive: &str) -> Option<Directive> {
    let mut tokens = directive.split_whitespace();
    match tokens.next().unwrap().to_ascii_uppercase().as_str() {
        "CODE" => {
            let address = parse_number(tokens.next().unwrap()).unwrap();
            Some(Directive::Code(address))
        },
        "ENDCODE" => {
            Some(Directive::EndCode)
        },
        _ => None,
    }
}
