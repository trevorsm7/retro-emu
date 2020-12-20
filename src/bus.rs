use std::sync::{Arc, RwLock};

use num_traits::PrimInt;

pub trait Port<Address, Data> {
    fn read(&self, address: Address) -> Data;
    fn write(&mut self, address: Address, data: Data);
}

struct PortMap<Address, Data> {
    range: (Address, Address),
    port: Arc<RwLock<dyn Port<Address, Data>>>,
}

pub struct Bus<Address, Data> {
    ports: Vec<PortMap<Address, Data>>,
}

impl<Address: PrimInt, Data: Copy> Bus<Address, Data> {
    pub fn new() -> Self {
        Self { ports: vec![] }
    }

    pub fn add_port(&mut self, range: (Address, Address), port: Arc<RwLock<dyn Port<Address, Data>>>) {
        // TODO sort by start and check for overlapping ranges
        self.ports.push(PortMap { range, port });
    }

    pub fn write(&self, address: Address, data: Data) {
        // NOTE this can write to multiple ports that claim the same address
        for port in self.ports.iter() {
            if address >= port.range.0 && address < port.range.1 {
                let address = address - port.range.0;
                port.port.write().unwrap().write(address, data);
            }
        }
    }

    pub fn read(&self, address: Address) -> Option<Data> {
        // NOTE this only reads from the first port that claims it; maybe make this an error since it doesn't match write?
        for port in self.ports.iter() {
            if address >= port.range.0 && address < port.range.1 {
                let address = address - port.range.0;
                return Some(port.port.read().unwrap().read(address));
            }
        }
        None
    }
}
