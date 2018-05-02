extern crate subset_map;

use subset_map::*;
use std::time::Instant;

fn main() {
    let elements: Vec<_> = (0..17).collect();
    let start = Instant::now();

    let mut n = 0;
    let map = SubsetMap::fill(&elements, |_x| {
        n += 1;
        n
    });

    println!(
        "[CREATE_SIMPLE]: Combinations: {}(Size: {}) -> Time: {:?}",
        n,
        map.size(),
        start.elapsed()
    );

    drop(map);

    let start = Instant::now();

    let mut n = 0usize;
    let mut combinations = Vec::new();
    let map = SubsetMap::fill(&elements, |x| {
        combinations.push(x.to_vec());
        n += 1;
        n
    });

    println!(
        "[CREATE_FOR_QUERY]: Combinations: {}(Size: {}) -> Time: {:?}",
        n,
        map.size(),
        start.elapsed()
    );

    let start = Instant::now();

    let mut n = 0usize;
    for combination in combinations {
        if let Some(_p) = map.get(&combination) {
            n += 1;
        }
    }

    println!(
        "[GET]: Combinations: {} -> Time: {:?} {}",
        map.size(),
        start.elapsed(),
        n
    );

    drop(map);

    let mut n = 0usize;
    let mut combinations = Vec::new();
    let map = SubsetMap::fill(&elements, |x| {
        combinations.push(x.to_vec());
        n += 1;
        n
    });

    let start = Instant::now();

    let mut n = 0usize;
    for combination in combinations {
        if let LookupResult::Perfect(Some(_p)) = map.lookup(&combination) {
            n += 1;
        }
    }

    println!(
        "[LOOKUP]: Combinations: {} -> Time: {:?} {}",
        map.size(),
        start.elapsed(),
        n
    );

    drop(map);

    let mut n = 0usize;
    let mut combinations = Vec::new();
    let map = SubsetMap::fill(&elements, |x| {
        combinations.push(x.to_vec());
        n += 1;
        n
    });

    let start = Instant::now();

    let mut n = 0usize;
    for combination in combinations {
        if let FindResult::Perfect(_) = map.find(&combination) {
            n += 1;
        }
    }

    println!(
        "[FIND]: Combinations: {} -> Time: {:?} {}",
        map.size(),
        start.elapsed(),
        n
    );
}
