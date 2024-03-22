//! A simple lowest index allocator.
//!
//! This crate provides a simple lowest index allocator. It is useful for allocating indexes for arrays.
//! # Example
//! ```
//! use small_index::{IndexAllocator};
//! let mut allocator = IndexAllocator::<128>::new(); // Specify the maximum index value as a generic parameter.
//! assert_eq!(allocator.allocate(),Ok(0));
//! assert_eq!(allocator.allocate(),Ok(1));
//! ```
//!

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]
#![feature(error_in_core)]
#![cfg_attr(not(test), no_std)]

use core::error::Error;
use core::fmt::{Debug, Display, Formatter};
use core::ops::Range;

#[derive(Debug, Eq, PartialEq)]
pub enum IndexAllocationError {
    NoFreeIndex,
    InvalidIndex,
    Truncated,
    NotAllocated,
}

impl Display for IndexAllocationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            IndexAllocationError::NoFreeIndex => "No free index",
            IndexAllocationError::InvalidIndex => "Invalid index",
            IndexAllocationError::Truncated => "Index Truncated",
            IndexAllocationError::NotAllocated => "Index Not Allocated",
        })
    }
}

impl Error for IndexAllocationError {}

type Result<T> = core::result::Result<T, IndexAllocationError>;

#[derive(Debug,Clone)]
pub struct IndexAllocator<const MAX_INDEX: usize>
where
    [(); (MAX_INDEX + 64) / 64]:,
{
    map: [u64; (MAX_INDEX + 64) / 64],
    current_allocation: usize,
    max_index: usize,
}

impl<const T: usize> Display for IndexAllocator<T>
where
    [(); (T + 64) / 64]:,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!(
            "current_allocation:{}, max_index:{}\n",
            self.current_allocation, self.max_index
        ))?;
        for v in self.map.iter() {
            f.write_fmt(format_args!("{:>064b}\n", v))?;
        }
        Ok(())
    }
}

impl<const MAX_INDEX: usize> Default for IndexAllocator<MAX_INDEX>
where
    [(); (MAX_INDEX + 64) / 64]:,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const MAX_INDEX: usize> IndexAllocator<MAX_INDEX>
where
    [(); (MAX_INDEX + 64) / 64]:,
{
    pub const fn new() -> Self {
        IndexAllocator {
            map: [0; (MAX_INDEX + 64) / 64],
            current_allocation: 0,
            max_index: MAX_INDEX,
        }
    }

    /// Set the maximum index value. This will clear the bits in the map that are above the new max index
    ///
    /// The new max index must be less than or equal to the generic parameter `MAX_INDEX`.
    pub fn set_max_index(&mut self, max_index: usize) -> Result<()> {
        if max_index > MAX_INDEX {
            return Err(IndexAllocationError::InvalidIndex);
        }
        if max_index < self.max_index {
            // clear the bits in the map that are above the new max index
            let word_idx = max_index / 64;
            let bit = max_index % 64;
            let mask = (1u64 << bit) - 1;
            self.map
                .iter_mut()
                .skip(word_idx + 1)
                .for_each(|word| *word = 0);
            self.map[word_idx] &= mask;
        }
        self.max_index = max_index;
        Ok(())
    }

    fn allocate_inner(&mut self, r: Range<usize>) -> Result<usize> {
        let start = r.start;
        let tmp_map = &mut self.map[r];
        for (word_idx, word) in tmp_map.iter_mut().enumerate() {
            if *word != u64::MAX {
                let free_bits = !*word;
                if free_bits != 0 {
                    // get the index of the first free bit
                    let bit = free_bits.trailing_zeros() as usize;
                    let index = (word_idx + start) * 64 + bit;
                    return if index < self.max_index {
                        self.current_allocation = index + 1;
                        *word |= 1u64 << bit;
                        Ok(index)
                    } else {
                        Err(IndexAllocationError::InvalidIndex)
                    };
                }
            }
        }
        Err(IndexAllocationError::NoFreeIndex)
    }

    /// Allocate an index.
    pub fn allocate(&mut self) -> Result<usize> {
        let r = self.current_allocation / 64..(self.max_index + 64) / 64;
        let res = self.allocate_inner(r);
        match res {
            Ok(index) => Ok(index),
            Err(IndexAllocationError::InvalidIndex) => {
                let r = 0..self.current_allocation / 64;
                self.allocate_inner(r)
            }
            Err(e) => Err(e),
        }
    }

    /// Deallocate an index.
    pub fn deallocate(&mut self, index: usize) -> Result<()> {
        if index < self.max_index {
            let word_idx = index / 64;
            let bit = index % 64;
            let mask = 1u64 << bit;
            if (self.map[word_idx] & mask) == 0 {
                return Err(IndexAllocationError::NotAllocated);
            } // index is not allocated
            self.map[word_idx] &= !mask;
            Ok(())
        } else if index < MAX_INDEX {
            Err(IndexAllocationError::Truncated)
        } else {
            Err(IndexAllocationError::InvalidIndex)
        }
    }

    /// Test if an index is allocated.
    pub fn test_bit(&self, index: usize) -> Result<bool> {
        if index < self.max_index {
            let word_idx = index / 64;
            let bit = index % 64;
            let mask = 1u64 << bit;
            Ok((self.map[word_idx] & mask) != 0)
        } else if index < MAX_INDEX {
            Err(IndexAllocationError::Truncated)
        } else {
            Err(IndexAllocationError::InvalidIndex)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::IndexAllocator;

    fn test_alloc_success_max<const MAX: usize>()
    where
        [(); (MAX + 64) / 64]:,
    {
        let mut allocator = IndexAllocator::<MAX>::new(); // Specify the maximum index value as a generic parameter.
        for i in 0..MAX {
            let index = allocator.allocate();
            assert_eq!(index, Ok(i));
        }
        for i in 0..MAX {
            let index = allocator.deallocate(i);
            assert_eq!(index, Ok(()));
        }
        for i in 0..MAX {
            let index = allocator.allocate();
            assert_eq!(index, Ok(i));
        }
    }
    #[test]
    fn test_alloc_success() {
        test_alloc_success_max::<128>();
        test_alloc_success_max::<256>();
        test_alloc_success_max::<0>();
        test_alloc_success_max::<5>();
    }

    #[test]
    #[should_panic]
    fn test_alloc_fail() {
        let mut allocator = IndexAllocator::<0>::new(); // Specify the maximum index value as a generic parameter.
        allocator.allocate().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_alloc_fail2() {
        let mut allocator = IndexAllocator::<10>::new();
        for i in 0..10 {
            let index = allocator.allocate();
            assert_eq!(index, Ok(i));
        }
        allocator.allocate().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_dealloc_fail() {
        let mut allocator = IndexAllocator::<10>::new();
        for i in 0..10 {
            let index = allocator.allocate();
            assert_eq!(index, Ok(i));
        }
        for i in 0..10 {
            let index = allocator.deallocate(i);
            assert_eq!(index, Ok(()));
        }
        allocator.deallocate(0).unwrap();
    }
    #[test]
    #[should_panic]
    fn test_dealloc_fail2() {
        let mut allocator = IndexAllocator::<10>::new();
        allocator.deallocate(1).unwrap();
    }

    #[test]
    fn test_reset_max() {
        let mut allocator = IndexAllocator::<10>::new();
        for i in 0..10 {
            let index = allocator.allocate();
            assert_eq!(index, Ok(i));
        }
        let r = allocator.set_max_index(5);
        assert_eq!(r, Ok(()));
        let r = allocator.allocate();
        assert_eq!(r, Err(crate::IndexAllocationError::NoFreeIndex));
        assert_eq!(allocator.set_max_index(10), Ok(()));
        for i in 0..5 {
            let index = allocator.allocate();
            assert_eq!(index, Ok(i + 5));
        }
        assert_eq!(
            allocator.allocate(),
            Err(crate::IndexAllocationError::NoFreeIndex)
        );

        allocator.set_max_index(5).unwrap();
        for i in 0..5 {
            let index = allocator.deallocate(i);
            assert_eq!(index, Ok(()));
        }
        for i in 5..10 {
            let index = allocator.deallocate(i);
            assert_eq!(index, Err(crate::IndexAllocationError::Truncated));
        }
        assert_eq!(
            allocator.deallocate(1),
            Err(crate::IndexAllocationError::NotAllocated)
        );
        allocator.set_max_index(10).unwrap();
        assert_eq!(
            allocator.deallocate(6),
            Err(crate::IndexAllocationError::NotAllocated)
        );
    }

    #[test]
    fn test_alloc() {
        let mut allocator = IndexAllocator::<10>::new();
        for i in 0..10 {
            let index = allocator.allocate();
            assert_eq!(index, Ok(i));
        }
        allocator.deallocate(0).unwrap();
        allocator.deallocate(5).unwrap();
        assert_eq!(allocator.allocate(), Ok(0));
        assert_eq!(allocator.allocate(), Ok(5));
    }
}
