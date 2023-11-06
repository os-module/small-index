# Small-index

A simple lowest index allocator.
This crate provides a simple lowest index allocator. It is useful for allocating indexes for arrays.

## Example
```rust
use small_index::{IndexAllocator};
let mut allocator = IndexAllocator::<128>::new(); // Specify the maximum index value as a generic parameter.
assert_eq!(allocator.allocate(),Ok(0));
assert_eq!(allocator.allocate(),Ok(1));
```

 