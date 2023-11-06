use small_index::{IndexAllocator};

fn main() {
    let mut allocator = IndexAllocator::<128>::new(); // Specify the maximum index value as a generic parameter.

    let index1 = allocator.allocate();
    let index2 = allocator.allocate();
    println!("Allocated indexes: {:?}, {:?}", index1, index2);

    if let Ok(index1) = index1 {
        allocator.deallocate(index1).unwrap();
    }

    let index3 = allocator.allocate();
    println!("Allocated index after deallocation: {:?}", index3);
}
