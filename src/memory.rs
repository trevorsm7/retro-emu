use std::marker::PhantomData;

use num_traits::{PrimInt, cast::AsPrimitive};

use super::bus::Port;

pub struct RAM<Address, Data> {
    ram: Box<[Data]>,
    _junk: PhantomData<Address>,
}

impl<Address: PrimInt + AsPrimitive<usize>, Data: PrimInt> RAM<Address, Data> {
    pub fn new(size: Address) -> Self {
        let ram = vec![Data::zero(); size.as_()].into_boxed_slice();
        Self { ram, _junk: PhantomData }
    }
}

impl<Address: AsPrimitive<usize>, Data: PrimInt> Port<Address, Data> for RAM<Address, Data> {
    fn read(&self, address: Address) -> Data {
        self.ram[address.as_()]
    }

    fn write(&mut self, address: Address, data: Data) {
        self.ram[address.as_()] = data;
    }
}
