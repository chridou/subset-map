# subset-map

## Summary

`subset-map` is a map like data structure where the keys are combinations
of elements the `SubsetMap` has been initialized with.

The order of the elements is defined by the position of an element
within the elements the `SubsetMap` has been initialized with.

`SubsetMap` clones the elements into the subsets. So you should
consider to only use element types where you would feel good to assign
them the `Copy` trait.

Lookup is done linearly. Therefore `SubsetMap` should only be used
with not too big sets of elements.

### Example

```rust
use subset_map::*;
// Initialize the map where the payloads are basically the keys
let subset_map = SubsetMap::fill(&[1, 2, 3], |x| x.iter().cloned().collect::<Vec<_>>());

assert_eq!(subset_map.lookup(&[1]), Some(&vec![1]));
assert_eq!(subset_map.lookup(&[2]), Some(&vec![2]));
assert_eq!(subset_map.lookup(&[3]), Some(&vec![3]));
assert_eq!(subset_map.lookup(&[1, 2]), Some(&vec![1, 2]));
assert_eq!(subset_map.lookup(&[2, 3]), Some(&vec![2, 3]));
assert_eq!(subset_map.lookup(&[1, 3]), Some(&vec![1, 3]));
assert_eq!(subset_map.lookup(&[1, 2, 3]), Some(&vec![1, 2, 3]));

// No internal ordering is performed:
// The position in the original set is crucial:
assert_eq!(subset_map.lookup(&[2,1]), None);
```

## Features

The `serde` feature allows serialization and deserialization with `serde`.

## License

`subset-map` is distributed under the terms of both the MIT license and the Apache License (Version
2.0).

Copyright(2018) Christian Douven

See LICENSE-APACHE and LICENSE-MIT for details.

License: Apache-2.0/MIT
