extern crate subset_map;

use subset_map::*;

fn main() {
    let elements: Vec<_> = (0..5).collect();

    let mut n = 0;
    let map = SubsetMap::fill(&elements, |_x| {
        n += 1;
        n
    });

    map.walk(|elements, payload| println!("{:?} -> {:?}", elements, payload))
}
