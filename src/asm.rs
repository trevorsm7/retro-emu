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
    Immediate(Data),
    Relative(Symbol<'a, Data>),
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

fn parse_instruction(instruction: &str) -> Option<(u8, Operand)> {
    // Parse mnemonic and optional operand separated by whitespace
    let mut tokens = instruction.splitn(2, char::is_whitespace);
    let mnemonic = tokens.next().unwrap();
    // TODO maybe match with mnemonic before returning to more precisely identify syntax errors
    let operand = parse_operand(tokens.next().unwrap_or("").trim())?;

    match (mnemonic.to_ascii_uppercase().as_ref(), operand) {
        ("ADC", Operand::Immediate(_)) => Some(0x69),
        ("ADC", Operand::ZeroPage(_)) => Some(0x65),
        ("ADC", Operand::ZeroPageX(_)) => Some(0x75),
        ("ADC", Operand::Absolute(_)) => Some(0x6D),
        ("ADC", Operand::AbsoluteX(_)) => Some(0x7D),
        ("ADC", Operand::AbsoluteY(_)) => Some(0x79),
        ("ADC", Operand::IndexedIndirectX(_)) => Some(0x61),
        ("ADC", Operand::IndirectIndexedY(_)) => Some(0x71),
        ("ADC", _) => panic!(format!("Unsupported addressing mode {:?}", operand)), //< TODO return as Result
        /*"AND" => Some(Mnemonic::AND),
        "ASL" => Some(Mnemonic::ASL),
        "BCC" => Some(Mnemonic::BCC),
        "BCS" => Some(Mnemonic::BCS),
        "BEQ" => Some(Mnemonic::BEQ),
        "BIT" => Some(Mnemonic::BIT),
        "BMI" => Some(Mnemonic::BMI),
        "BNE" => Some(Mnemonic::BNE),
        "BPL" => Some(Mnemonic::BPL),*/
        ("BRK", Operand::Implied) => Some(0x00), //< TODO assemble as 2 bytes? maybe warn if not followed by NOP?
        /*"BVC" => Some(Mnemonic::BVC),
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
        "INY" => Some(Mnemonic::INY),*/
        ("JMP", Operand::Absolute(_)) => Some(0x4C),
        ("JMP", Operand::Indirect(_)) => Some(0x6C),
        //"JSR" => Some(Mnemonic::JSR),
        ("LDA", Operand::Immediate(_)) => Some(0xA9),
        ("LDA", Operand::ZeroPage(_)) => Some(0xA5),
        ("LDA", Operand::ZeroPageX(_)) => Some(0xB5),
        ("LDA", Operand::Absolute(_)) => Some(0xAD),
        ("LDA", Operand::AbsoluteX(_)) => Some(0xBD),
        ("LDA", Operand::AbsoluteY(_)) => Some(0xB9),
        ("LDA", Operand::IndexedIndirectX(_)) => Some(0xA1),
        ("LDA", Operand::IndirectIndexedY(_)) => Some(0xB1),
        /*"LDX" => Some(Mnemonic::LDX),
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
        "SEI" => Some(Mnemonic::SEI),*/
        ("STA", Operand::ZeroPage(_)) => Some(0x85),
        ("STA", Operand::ZeroPageX(_)) => Some(0x95),
        ("STA", Operand::Absolute(_)) => Some(0x8D),
        ("STA", Operand::AbsoluteX(_)) => Some(0x9D),
        ("STA", Operand::AbsoluteY(_)) => Some(0x99),
        ("STA", Operand::IndexedIndirectX(_)) => Some(0x81),
        ("STA", Operand::IndirectIndexedY(_)) => Some(0x91),
        /*"STX" => Some(Mnemonic::STX),
        "STY" => Some(Mnemonic::STY),
        "TAX" => Some(Mnemonic::TAX),
        "TAY" => Some(Mnemonic::TAY),
        "TSX" => Some(Mnemonic::TSX),
        "TXA" => Some(Mnemonic::TXA),
        "TXS" => Some(Mnemonic::TXS),
        "TYA" => Some(Mnemonic::TYA),*/
        _ => None,
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
