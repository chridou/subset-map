extern crate subset_map;

use subset_map::*;

fn main() {
    let mut n = 0;
    SubsetMap::fill(&[1u32, 2, 3, 4, 5], |x| {
        n += 1;
        println!("{} -> {:?}", n, x)
    });
}
