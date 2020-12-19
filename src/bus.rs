struct Port<Address, Data> {
    map: Box<dyn Fn(Address) -> Option<Address>>,
    read: Box<dyn Fn(Address) -> Data>,
    write: Box<dyn Fn(Address, Data)>,
}

pub struct Bus<Address, Data> {
    ports: Vec<Port<Address, Data>>,
}

impl<Address: Copy, Data: Copy> Bus<Address, Data> {
    pub fn new() -> Self {
        Self { ports: vec![] }
    }

    pub fn add_port<M, R, W>(&mut self, map: M, read: R, write: W)
    where M: 'static + Fn(Address) -> Option<Address>, R: 'static + Fn(Address) -> Data, W: 'static + Fn(Address, Data) {
        let map = Box::new(map);
        let read = Box::new(read);
        let write = Box::new(write);
        self.ports.push(Port { map, read, write });
    }

    pub fn write(&self, address: Address, data: Data) {
        // NOTE this can write to multiple ports that claim the same address
        for port in self.ports.iter() {
            if let Some(address) = (port.map)(address) {
                (port.write)(address, data);
            }
        }
    }

    pub fn read(&self, address: Address) -> Option<Data> {
        // NOTE this only reads from the first port that claims it; maybe make this an error since it doesn't match write?
        for port in self.ports.iter() {
            if let Some(address) = (port.map)(address) {
                return Some((port.read)(address));
            }
        }
        None
    }
}
