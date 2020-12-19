use std::sync::{Arc, RwLock};

use num_traits::{PrimInt, cast::AsPrimitive};

pub struct RAM<Address, Data> {
    size: Address, // Redundant with len() of boxed slice, but easier to access AND provides constraint for Address
    ram: Arc<RwLock<Box<[Data]>>>,
}

impl<Address: PrimInt + AsPrimitive<usize>, Data: PrimInt> RAM<Address, Data> {
    pub fn new(size: Address) -> Self {
        let ram = Arc::new(RwLock::new(vec![Data::zero(); size.as_()].into_boxed_slice()));
        Self { size, ram }
    }

    pub fn read(&self, address: Address) -> Data {
        self.ram.read().unwrap()[address.as_()]
    }

    pub fn write(&self, address: Address, data: Data) {
        self.ram.write().unwrap()[address.as_()] = data;
    }

    pub fn map_cb(&self, start: Address) -> impl Fn(Address) -> Option<Address> {
        let size = self.size;
        move |address| {
            if address >= start {
                let address = address - start;
                if address < size {
                    return Some(address);
                }
            }
            None
        }
    }

    pub fn read_cb(&self) -> impl Fn(Address) -> Data {
        let ram = self.ram.clone();
        move |address| ram.read().unwrap()[address.as_()]
    }

    pub fn write_cb(&self) -> impl Fn(Address, Data) {
        let ram = self.ram.clone();
        move |address, data| ram.write().unwrap()[address.as_()] = data
    }
}
