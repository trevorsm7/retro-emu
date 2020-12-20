use std::sync::{Arc, RwLock};
use std::ops::Range;

use num_traits::PrimInt;

pub trait Port<Address, Data> {
    fn read(&self, address: Address) -> Data;
    fn write(&mut self, address: Address, data: Data);
}

type PortPtr<Address, Data> = Arc<RwLock<dyn Port<Address, Data>>>;

struct PortMap<Address, Data> {
    range: Range<Address>,
    port: PortPtr<Address, Data>,
}

pub struct Bus<Address, Data> {
    ports: Vec<PortMap<Address, Data>>,
}

impl<Address: PrimInt + std::fmt::Debug, Data: Copy> Bus<Address, Data> {
    pub fn new() -> Self {
        Self { ports: vec![] }
    }

    // TODO return an error instead of panicking
    pub fn add_port(&mut self, range: Range<Address>, port: PortPtr<Address, Data>) {
        match self.ports.binary_search_by_key(&range.start, |port| port.range.start) {
            Err(index) => {
                if index > 0 && self.ports[index - 1].range.end > range.start {
                    panic!(format!("address range {:?} overlaps with {:?}", range, self.ports[index - 1].range));
                }
                if index < self.ports.len() && self.ports[index].range.start < range.end {
                    panic!(format!("address range {:?} overlaps with {:?}", range, self.ports[index].range));
                }
                self.ports.insert(index, PortMap { range, port });
            },
            Ok(index) => panic!(format!("address range {:?} overlaps with {:?}", range, self.ports[index].range)),
        }
    }

    fn map_address(&self, address: Address) -> Option<(&PortPtr<Address, Data>, Address)> {
        match self.ports.binary_search_by_key(&address, |port| port.range.start) {
            Ok(index) => Some((&self.ports[index].port, Address::zero())),
            Err(index) => {
                if index > 0 {
                    let prev = &self.ports[index - 1];
                    if prev.range.contains(&address) {
                        return Some((&prev.port, address - prev.range.start));
                    }
                }
                None
            },
        }
    }

    pub fn write(&self, address: Address, data: Data) -> Option<()> {
        self.map_address(address).map(|(port, address)|
            port.write().unwrap().write(address, data))
    }

    pub fn read(&self, address: Address) -> Option<Data> {
        self.map_address(address).map(|(port, address)|
            port.read().unwrap().read(address))
    }
}
