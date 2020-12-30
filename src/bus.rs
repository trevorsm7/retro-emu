use std::sync::{Arc, RwLock};

use num_traits::PrimInt;

pub trait Port<Address, Data> {
    fn read(&self, address: Address) -> Data;
    fn write(&mut self, address: Address, data: Data);
}

type PortPtr<Address, Data> = Arc<RwLock<dyn Port<Address, Data>>>;

struct PortMap<Address, Data> {
    address: Address,
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
    pub fn add_port(&mut self, address: Address, port: PortPtr<Address, Data>) {
        match self.ports.binary_search_by_key(&address, |port| port.address) {
            Err(index) => self.ports.insert(index, PortMap { address, port }),
            Ok(_) => panic!(format!("address {:?} already assigned", address)),
        }
    }

    fn map_address(&self, address: Address) -> Option<(&PortPtr<Address, Data>, Address)> {
        match self.ports.binary_search_by_key(&address, |port| port.address) {
            Ok(index) => Some((&self.ports[index].port, Address::zero())),
            Err(0) => None,
            Err(index) => {
                let prev = &self.ports[index - 1];
                Some((&prev.port, address - prev.address))
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

#[test]
#[should_panic]
fn test_mem_overlap_same() {
    use super::memory::RAM;
    let ram = Arc::new(RwLock::new(RAM::<u16, u8>::new(10)));
    let mut bus = Bus::<u16, u8>::new();
    bus.add_port(0, ram.clone());
    bus.add_port(0, ram.clone());
}
