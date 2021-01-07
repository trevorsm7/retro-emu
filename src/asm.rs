use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use num_traits::{Num, FromPrimitive};

type Data = u8;
type Address = u16;
type LabelMap<'a> = HashMap<&'a str, Address>;

// TODO maybe add a Hold option instead of wrapping in Option
enum Transition {
    Push(Rc<RefCell<dyn LineParser>>),
    Pop,
}

trait LineParser {
    // TODO return Result<..., AsmError>
    fn parse_line<'a>(&mut self, line: &'a str, labels: &mut LabelMap<'a>) -> Option<Transition>;
}

pub fn assemble(source: &str) -> Vec<(Address, Vec<Data>)> {
    let mut labels = LabelMap::new();

    let default = Rc::new(RefCell::new(DefaultParser::new()));

    // TODO maybe downgrade these into Weak instead
    let mut stack: Vec<Rc<RefCell<dyn LineParser>>> = vec![default.clone()];

    // First pass: parse instructions and record labels
    for line in source.lines() {
        // Ignore any comments following first occurence of ';'
        let line = line.split(';').next().unwrap();

        // Prase line with current state and handle state transition
        let parser = stack.last().unwrap().clone();
        match parser.borrow_mut().parse_line(line, &mut labels) {
            Some(Transition::Push(next)) => stack.push(next),
            Some(Transition::Pop) => {stack.pop();},
            None => (),
        };
    }

    // TODO there must not be any remaining references to code segments before proceeding
    assert_eq!(stack.len(), 1);
    drop(stack); //< Need to clear stack before unwrapping Rcs (reason to use Weak instead?)

    // Second pass: substitute any previously undefined labels
    Rc::try_unwrap(default).unwrap().into_inner().assemble(&labels)
}

#[derive(Clone, Debug, PartialEq)]
struct DefaultParser {
    code_segments: Vec<Rc<RefCell<CodeParser>>>,
}

impl DefaultParser {
    fn new() -> Self {
        let code_segments = vec![];
        Self {code_segments}
    }

    fn assemble(&mut self, labels: &LabelMap) -> Vec<(Address, Vec<Data>)> {
        // This got really ugly after wrapping the segments in Rc<RefCell>
        self.code_segments.drain(..).filter_map(|p| Rc::try_unwrap(p).unwrap().into_inner().assemble(&labels)).collect()
    }
}

impl LineParser for DefaultParser {
    fn parse_line<'a>(&mut self, line: &'a str, labels: &mut LabelMap<'a>) -> Option<Transition> {
        // Parse blank line, directive, or instruction
        if line.is_empty() {
            None
        } else if let Some(directive) = parse_directive(line) {
            match directive {
                Directive::Code(address) => {
                    self.code_segments.push(Rc::new(RefCell::new(CodeParser::new(address))));
                    Some(Transition::Push(self.code_segments.last().unwrap().clone()))
                },
                _ => panic!(format!("Unsupported directive {:?}", directive)),
            }
        } else {
            panic!(format!("Unhandled command {}", line));
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct CodeParser {
    offset: Address,
    code: Vec<Data>,
    undefined: Vec<(LabelKind, Address)>,
}

impl CodeParser {
    fn new(offset: Address) -> Self {
        let code = vec![];
        let undefined = vec![];
        Self {offset, code, undefined}
    }

    fn assemble(mut self, labels: &LabelMap) -> Option<(Address, Vec<Data>)> {
        // Substitute labels that were undefined in the first pass
        for (label, position) in self.undefined {
            // TODO propagate still undefined labels as error
            let &address = labels.get(label.get_label()).unwrap();
            match label {
                LabelKind::ZeroPage(_) => {
                    assert!(address < 256);
                    self.code[position as usize] = address as Data;
                },
                LabelKind::Absolute(_) => {
                    self.code[position as usize] = (address & 0xFF) as Data;
                    self.code[position as usize + 1] = (address >> 8) as Data;
                },
                LabelKind::Relative(_) => {
                    let rel = address as i32 - (self.offset + position + 1) as i32;
                    assert!(rel >= -128 && rel < 128);
                    self.code[position as usize] = rel as Data; //< TODO make sure that negative labels convert correctly
                },
            };
        }

        Some((self.offset, self.code))
    }
}

impl LineParser for CodeParser {
    fn parse_line<'a>(&mut self, line: &'a str, labels: &mut LabelMap<'a>) -> Option<Transition> {
        // Split at ':' and set aside rightmost token as a command
        let mut tokens = line.rsplit(':');
        let command = tokens.next().unwrap().trim();

        // Parse remaining tokens as labels (permits multiple labels per line)
        for label in tokens {
            if let Some(label) = parse_label(label.trim()) {
                let address = self.offset + self.code.len() as Address;
                if labels.insert(label, address).is_some() {
                    panic!(format!("Label \"{}\" already exists", label));
                }
            } else {
                panic!(format!("Invalid label \"{}\"", label));
            }
        }

        // Parse blank line, directive, or instruction
        if command.is_empty() {
            None
        } else if let Some(directive) = parse_directive(command) {
            match directive {
                Directive::EndCode => Some(Transition::Pop),
                _ => panic!(format!("Unsupported directive {:?}", directive)),
            }
        } else if let Some((code, operand)) = parse_instruction(command) {
            self.code.push(code);
            match operand.get_value(labels) {
                Ok(ValueKind::None) => (),
                Ok(ValueKind::Single(value)) => self.code.push(value),
                Ok(ValueKind::Double(value)) => {
                    // Push value as little endian
                    self.code.push((value & 0xFF) as Data);
                    self.code.push((value >> 8) as Data);
                },
                Err(label) => {
                    let size = label.size();
                    self.undefined.push((label, self.code.len() as Address));
                    self.code.resize(self.code.len() + size, 0);
                },
            };
            None
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
    assert!(parse_number::<u16>("twenty").is_err());
}

fn parse_label(token: &str) -> Option<&str> {
    // First char must be alphabetic and remainder must be alphanumeric
    if token.starts_with(char::is_alphabetic) && token.find(|c| !char::is_alphanumeric(c)).is_none() {
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
    Relative(Symbol<'a, Data>), //< TODO! this will be parsed as Absolute and must be converted when matching with branch instructions!!
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
            Self::Relative(sym) => sym.size(),
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
                Ok(value) => Ok(ValueKind::Single(value)),
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
        parse_number(immediate).ok().map(Operand::Immediate)
    } else if let Some(indirect) = token.strip_prefix('(') {
        // TODO handle labels and indexing
        let mut tokens = indirect.split(')');
        parse_symbol(tokens.next().unwrap()).ok().map(Operand::Indirect)
    } else {
        // TODO handle labels and indexing
        if let Some(token) = token.strip_prefix('@') {
            parse_symbol(token).ok().map(Operand::ZeroPage)
        } else {
            parse_symbol(token).ok().map(Operand::Absolute)
        }
    }
}

#[test]
fn test_parse_operand() {
    assert_eq!(parse_operand(""), Some(Operand::Implied));
    assert_eq!(parse_operand("#$FF"), Some(Operand::Immediate(0xFF)));
    assert_eq!(parse_operand("@%1010"), Some(Operand::ZeroPage(Symbol::Value(0b1010))));
    assert_eq!(parse_operand("1024"), Some(Operand::Absolute(Symbol::Value(1024))));
    assert_eq!(parse_operand("(label)"), Some(Operand::Indirect(Symbol::Label("label"))));
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
        (Mnemonic::ADC, Operand::Immediate(_)) => Some(0x69),
        (Mnemonic::ADC, Operand::ZeroPage(_)) => Some(0x65),
        (Mnemonic::ADC, Operand::ZeroPageX(_)) => Some(0x75),
        (Mnemonic::ADC, Operand::Absolute(_)) => Some(0x6D),
        (Mnemonic::ADC, Operand::AbsoluteX(_)) => Some(0x7D),
        (Mnemonic::ADC, Operand::AbsoluteY(_)) => Some(0x79),
        (Mnemonic::ADC, Operand::IndexedIndirectX(_)) => Some(0x61),
        (Mnemonic::ADC, Operand::IndirectIndexedY(_)) => Some(0x71),
        (Mnemonic::AND, Operand::Immediate(_)) => Some(0x29),
        (Mnemonic::AND, Operand::ZeroPage(_)) => Some(0x25),
        (Mnemonic::AND, Operand::ZeroPageX(_)) => Some(0x35),
        (Mnemonic::AND, Operand::Absolute(_)) => Some(0x2D),
        (Mnemonic::AND, Operand::AbsoluteX(_)) => Some(0x3D),
        (Mnemonic::AND, Operand::AbsoluteY(_)) => Some(0x39),
        (Mnemonic::AND, Operand::IndexedIndirectX(_)) => Some(0x21),
        (Mnemonic::AND, Operand::IndirectIndexedY(_)) => Some(0x31),
        (Mnemonic::ASL, Operand::Accumulator) => Some(0x0A),
        (Mnemonic::ASL, Operand::ZeroPage(_)) => Some(0x06),
        (Mnemonic::ASL, Operand::ZeroPageX(_)) => Some(0x16),
        (Mnemonic::ASL, Operand::Absolute(_)) => Some(0x0E),
        (Mnemonic::ASL, Operand::AbsoluteX(_)) => Some(0x1E),
        (Mnemonic::BCC, Operand::Relative(_)) => Some(0x90),
        (Mnemonic::BCS, Operand::Relative(_)) => Some(0xB0),
        (Mnemonic::BEQ, Operand::Relative(_)) => Some(0xF0),
        (Mnemonic::BIT, Operand::ZeroPage(_)) => Some(0x24),
        (Mnemonic::BIT, Operand::Absolute(_)) => Some(0x2C),
        (Mnemonic::BMI, Operand::Relative(_)) => Some(0x30),
        (Mnemonic::BNE, Operand::Relative(_)) => Some(0xD0),
        (Mnemonic::BPL, Operand::Relative(_)) => Some(0x10),
        (Mnemonic::BRK, Operand::Implied) => Some(0x00), //< TODO assemble as 2 bytes? maybe warn if not followed by NOP?
        (Mnemonic::BVC, Operand::Relative(_)) => Some(0x50),
        (Mnemonic::BVS, Operand::Relative(_)) => Some(0x70),
        (Mnemonic::CLC, Operand::Implied) => Some(0x18),
        (Mnemonic::CLD, Operand::Implied) => Some(0xD8),
        (Mnemonic::CLI, Operand::Implied) => Some(0x58),
        (Mnemonic::CLV, Operand::Implied) => Some(0xB8),
        (Mnemonic::CMP, Operand::Immediate(_)) => Some(0xC9),
        (Mnemonic::CMP, Operand::ZeroPage(_)) => Some(0xC5),
        (Mnemonic::CMP, Operand::ZeroPageX(_)) => Some(0xD5),
        (Mnemonic::CMP, Operand::Absolute(_)) => Some(0xCD),
        (Mnemonic::CMP, Operand::AbsoluteX(_)) => Some(0xDD),
        (Mnemonic::CMP, Operand::AbsoluteY(_)) => Some(0xD9),
        (Mnemonic::CMP, Operand::IndexedIndirectX(_)) => Some(0xC1),
        (Mnemonic::CMP, Operand::IndirectIndexedY(_)) => Some(0xD1),
        (Mnemonic::CPX, Operand::Immediate(_)) => Some(0xE0),
        (Mnemonic::CPX, Operand::ZeroPage(_)) => Some(0xE4),
        (Mnemonic::CPX, Operand::Absolute(_)) => Some(0xEC),
        (Mnemonic::CPY, Operand::Immediate(_)) => Some(0xC0),
        (Mnemonic::CPY, Operand::ZeroPage(_)) => Some(0xC4),
        (Mnemonic::CPY, Operand::Absolute(_)) => Some(0xCC),
        (Mnemonic::DEC, Operand::ZeroPage(_)) => Some(0xC6),
        (Mnemonic::DEC, Operand::ZeroPageX(_)) => Some(0xD6),
        (Mnemonic::DEC, Operand::Absolute(_)) => Some(0xCE),
        (Mnemonic::DEC, Operand::AbsoluteX(_)) => Some(0xDE),
        (Mnemonic::DEX, Operand::Implied) => Some(0xCA),
        (Mnemonic::DEY, Operand::Implied) => Some(0x88),
        (Mnemonic::EOR, Operand::Immediate(_)) => Some(0x49),
        (Mnemonic::EOR, Operand::ZeroPage(_)) => Some(0x45),
        (Mnemonic::EOR, Operand::ZeroPageX(_)) => Some(0x55),
        (Mnemonic::EOR, Operand::Absolute(_)) => Some(0x4D),
        (Mnemonic::EOR, Operand::AbsoluteX(_)) => Some(0x5D),
        (Mnemonic::EOR, Operand::AbsoluteY(_)) => Some(0x59),
        (Mnemonic::EOR, Operand::IndexedIndirectX(_)) => Some(0x41),
        (Mnemonic::EOR, Operand::IndirectIndexedY(_)) => Some(0x51),
        (Mnemonic::INC, Operand::ZeroPage(_)) => Some(0xE6),
        (Mnemonic::INC, Operand::ZeroPageX(_)) => Some(0xF6),
        (Mnemonic::INC, Operand::Absolute(_)) => Some(0xEE),
        (Mnemonic::INC, Operand::AbsoluteX(_)) => Some(0xFE),
        (Mnemonic::INX, Operand::Implied) => Some(0xE8),
        (Mnemonic::INY, Operand::Implied) => Some(0xC8),
        (Mnemonic::JMP, Operand::Absolute(_)) => Some(0x4C),
        (Mnemonic::JMP, Operand::Indirect(_)) => Some(0x6C),
        (Mnemonic::JSR, Operand::Absolute(_)) => Some(0x20),
        (Mnemonic::LDA, Operand::Immediate(_)) => Some(0xA9),
        (Mnemonic::LDA, Operand::ZeroPage(_)) => Some(0xA5),
        (Mnemonic::LDA, Operand::ZeroPageX(_)) => Some(0xB5),
        (Mnemonic::LDA, Operand::Absolute(_)) => Some(0xAD),
        (Mnemonic::LDA, Operand::AbsoluteX(_)) => Some(0xBD),
        (Mnemonic::LDA, Operand::AbsoluteY(_)) => Some(0xB9),
        (Mnemonic::LDA, Operand::IndexedIndirectX(_)) => Some(0xA1),
        (Mnemonic::LDA, Operand::IndirectIndexedY(_)) => Some(0xB1),
        (Mnemonic::LDX, Operand::Immediate(_)) => Some(0xA2),
        (Mnemonic::LDX, Operand::ZeroPage(_)) => Some(0xA6),
        (Mnemonic::LDX, Operand::ZeroPageY(_)) => Some(0xB6),
        (Mnemonic::LDX, Operand::Absolute(_)) => Some(0xAE),
        (Mnemonic::LDX, Operand::AbsoluteY(_)) => Some(0xBE),
        (Mnemonic::LDY, Operand::Immediate(_)) => Some(0xA0),
        (Mnemonic::LDY, Operand::ZeroPage(_)) => Some(0xA4),
        (Mnemonic::LDY, Operand::ZeroPageX(_)) => Some(0xB4),
        (Mnemonic::LDY, Operand::Absolute(_)) => Some(0xAC),
        (Mnemonic::LDY, Operand::AbsoluteX(_)) => Some(0xBC),
        (Mnemonic::LSR, Operand::Accumulator) => Some(0x4A),
        (Mnemonic::LSR, Operand::ZeroPage(_)) => Some(0x46),
        (Mnemonic::LSR, Operand::ZeroPageX(_)) => Some(0x56),
        (Mnemonic::LSR, Operand::Absolute(_)) => Some(0x4E),
        (Mnemonic::LSR, Operand::AbsoluteX(_)) => Some(0x5E),
        (Mnemonic::NOP, Operand::Implied) => Some(0xEA),
        (Mnemonic::ORA, Operand::Immediate(_)) => Some(0x09),
        (Mnemonic::ORA, Operand::ZeroPage(_)) => Some(0x05),
        (Mnemonic::ORA, Operand::ZeroPageX(_)) => Some(0x15),
        (Mnemonic::ORA, Operand::Absolute(_)) => Some(0x0D),
        (Mnemonic::ORA, Operand::AbsoluteX(_)) => Some(0x1D),
        (Mnemonic::ORA, Operand::AbsoluteY(_)) => Some(0x19),
        (Mnemonic::ORA, Operand::IndexedIndirectX(_)) => Some(0x01),
        (Mnemonic::ORA, Operand::IndirectIndexedY(_)) => Some(0x11),
        (Mnemonic::PHA, Operand::Implied) => Some(0x48),
        (Mnemonic::PHP, Operand::Implied) => Some(0x08),
        (Mnemonic::PLA, Operand::Implied) => Some(0x68),
        (Mnemonic::PLP, Operand::Implied) => Some(0x28),
        (Mnemonic::ROL, Operand::Accumulator) => Some(0x2A),
        (Mnemonic::ROL, Operand::ZeroPage(_)) => Some(0x26),
        (Mnemonic::ROL, Operand::ZeroPageX(_)) => Some(0x36),
        (Mnemonic::ROL, Operand::Absolute(_)) => Some(0x2E),
        (Mnemonic::ROL, Operand::AbsoluteX(_)) => Some(0x3E),
        (Mnemonic::ROR, Operand::Accumulator) => Some(0x6A),
        (Mnemonic::ROR, Operand::ZeroPage(_)) => Some(0x66),
        (Mnemonic::ROR, Operand::ZeroPageX(_)) => Some(0x76),
        (Mnemonic::ROR, Operand::Absolute(_)) => Some(0x6E),
        (Mnemonic::ROR, Operand::AbsoluteX(_)) => Some(0x7E),
        (Mnemonic::RTI, Operand::Implied) => Some(0x40),
        (Mnemonic::RTS, Operand::Implied) => Some(0x60),
        (Mnemonic::SBC, Operand::Immediate(_)) => Some(0xE9),
        (Mnemonic::SBC, Operand::ZeroPage(_)) => Some(0xE5),
        (Mnemonic::SBC, Operand::ZeroPageX(_)) => Some(0xF5),
        (Mnemonic::SBC, Operand::Absolute(_)) => Some(0xED),
        (Mnemonic::SBC, Operand::AbsoluteX(_)) => Some(0xFD),
        (Mnemonic::SBC, Operand::AbsoluteY(_)) => Some(0xF9),
        (Mnemonic::SBC, Operand::IndexedIndirectX(_)) => Some(0xE1),
        (Mnemonic::SBC, Operand::IndirectIndexedY(_)) => Some(0xF1),
        (Mnemonic::SEC, Operand::Implied) => Some(0x38),
        (Mnemonic::SED, Operand::Implied) => Some(0xF8),
        (Mnemonic::SEI, Operand::Implied) => Some(0x78),
        (Mnemonic::STA, Operand::ZeroPage(_)) => Some(0x85),
        (Mnemonic::STA, Operand::ZeroPageX(_)) => Some(0x95),
        (Mnemonic::STA, Operand::Absolute(_)) => Some(0x8D),
        (Mnemonic::STA, Operand::AbsoluteX(_)) => Some(0x9D),
        (Mnemonic::STA, Operand::AbsoluteY(_)) => Some(0x99),
        (Mnemonic::STA, Operand::IndexedIndirectX(_)) => Some(0x81),
        (Mnemonic::STA, Operand::IndirectIndexedY(_)) => Some(0x91),
        (Mnemonic::STX, Operand::ZeroPage(_)) => Some(0x86),
        (Mnemonic::STX, Operand::ZeroPageY(_)) => Some(0x96),
        (Mnemonic::STX, Operand::Absolute(_)) => Some(0x8E),
        (Mnemonic::STY, Operand::ZeroPage(_)) => Some(0x84),
        (Mnemonic::STY, Operand::ZeroPageX(_)) => Some(0x94),
        (Mnemonic::STY, Operand::Absolute(_)) => Some(0x8C),
        (Mnemonic::TAX, Operand::Implied) => Some(0xAA),
        (Mnemonic::TAY, Operand::Implied) => Some(0xA8),
        (Mnemonic::TSX, Operand::Implied) => Some(0xBA),
        (Mnemonic::TXA, Operand::Implied) => Some(0x8A),
        (Mnemonic::TXS, Operand::Implied) => Some(0x9A),
        (Mnemonic::TYA, Operand::Implied) => Some(0x98),
        _ => panic!("Unsupported addressing mode"), //< TODO return error
    }.map(|code| (code, operand))
}

#[test]
fn test_parse_instruction() {
    assert_eq!(parse_instruction("ADC #$FF"), Some((0x69, Operand::Immediate(0xFF))));
    assert_eq!(parse_instruction("ADC @$20"), Some((0x65, Operand::ZeroPage(Symbol::Value(0x20)))));
    assert_eq!(parse_instruction("JMP (label)"), Some((0x6C, Operand::Indirect(Symbol::Label("label")))));
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
