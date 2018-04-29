extern crate subset_map;

use subset_map::*;

fn main() {
    SubsetMap::new(&[1u32, 2, 3], |x| println!("{:?}", x));
}
