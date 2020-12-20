mod bus;
mod memory;

use bus::Bus;
use memory::RAM;

fn main() {
}

#[test]
fn test_mem_bus() {
    let mut bus = Bus::<u16, u8>::new();

    let addr = 100;
    let ram = RAM::<u16, u8>::new(1);
    bus.add_port(ram.map_cb(addr), ram.read_cb(), ram.write_cb());

    let value = 5;
    bus.write(addr, value);
    assert_eq!(bus.read(addr).unwrap(), value);
    assert_eq!(ram.read(0), value);
}
