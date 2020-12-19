mod bus;
mod memory;

use bus::Bus;
use memory::RAM;

fn main() {
    let mut bus = Bus::<u16, u8>::new();

    let ram = RAM::<u16, u8>::new(1);
    bus.add_port(ram.map_cb(100), ram.read_cb(), ram.write_cb());

    bus.write(100, 5);
    println!("{}", bus.read(100).unwrap());
    println!("{}", ram.read(0));
}
