mod buddy_bitmap;

pub use self::BlockSize::*;
use crate::buddy_bitmap::BuddyBitmap;
use bit_field::BitField;

const FRAME_SIZE: usize = 4096;

/// A Buddy allocator used to manage allocation and deallocation of physical memory frames.
pub struct BuddyBitmapAllocator {
    bitmaps: [BuddyBitmap; 8],
    mem_size: usize,
}

impl BuddyBitmapAllocator {
    /// Create a [`BuddyBitmapAllocator`]. The constructor needs a `*mut ptr` to a physical memory
    /// address, where it can lay out it's internal structures in a safe way (see Safety). It also
    /// needs the system's total memory size.
    ///
    /// # Safety
    /// The [`BuddyBitmapAllocator`] operates on an unsafe mutable pointer in a C-like fashion,
    /// so the caller must guarantee, that the pointer points to a valid memory area. The size of this
    /// must be at least the size returned by the
    /// [`BuddyFrameAllocator::allocator_bitmaps_size(mem_size: usize)`] func. The caller must
    /// guarantee, that this memory area cannot be manipulated in any other way than by the
    /// [`BuddyBitmapAllocator`] itself.
    pub unsafe fn new(start_ptr: *mut u64, mem_size: usize) -> Self {
        // number of pages is ram_size / page_size
        let pages_n = mem_size / FRAME_SIZE;
        // number of u64 for all the pages is pages_n / 64, as an u64 represents 64 pages
        let int_n = pages_n / u64::BIT_LENGTH;

        // calculate start pointers for every bitmap
        let start_ptr1 = start_ptr.add(int_n);
        let start_ptr2 = start_ptr1.add(int_n >> 1);
        let start_ptr3 = start_ptr2.add(int_n >> 2);
        let start_ptr4 = start_ptr3.add(int_n >> 3);
        let start_ptr5 = start_ptr4.add(int_n >> 4);
        let start_ptr6 = start_ptr5.add(int_n >> 5);
        let start_ptr7 = start_ptr6.add(int_n >> 6);

        let mut bitmaps = [
            BuddyBitmap::new(start_ptr, int_n),
            BuddyBitmap::new(start_ptr1, int_n >> 1),
            BuddyBitmap::new(start_ptr2, int_n >> 2),
            BuddyBitmap::new(start_ptr3, int_n >> 3),
            BuddyBitmap::new(start_ptr4, int_n >> 4),
            BuddyBitmap::new(start_ptr5, int_n >> 5),
            BuddyBitmap::new(start_ptr6, int_n >> 6),
            BuddyBitmap::new(start_ptr7, int_n >> 7),
        ];

        for bitmap in &mut bitmaps {
            // initialize every bitmap to zero
            bitmap.set_all_false();
        }

        Self { bitmaps, mem_size }
    }

    // fixme: shall this return a physical frame? which could then be mapped effectively inside a loop which wants to allocate a larger chunk of memory
    /// Allocate a memory block of given [`BlockSize`]. Returns `None` if out of memory, else returns
    /// the physical address of the allocated block.
    pub fn allocate_block(&mut self, block_size: BlockSize) -> Option<usize> {
        let bitmap = &mut self.bitmaps[block_size as usize];
        match bitmap.lowest_bit_unset() {
            Some(idx) => {
                let bit_idx_allocated = self._allocate_block_by_idx(idx, block_size);
                Some(bit_idx_allocated * BlockSize4KiB.in_bytes())
            }
            None => None,
        }
    }

    /// Deallocate a Block of a specific [`BlockSize`] at the specified memory address.
    pub fn deallocate_block(&mut self, addr_to_deallocate: usize, block_size: BlockSize) {
        // assert addr is aligned
        debug_assert_eq!(
            (addr_to_deallocate % block_size.in_bytes()),
            0,
            "address to deallocate not aligned to block_size"
        );
        self._deallocate_block_by_idx(addr_to_deallocate / block_size.in_bytes(), block_size);
    }

    /// Get the number of bytes which are currently allocated.
    pub fn used_bytes(&self) -> usize {
        self.bitmaps[0].get_bits_set_n() * FRAME_SIZE
    }

    /// Get the system's total memory size.
    pub fn available_bytes(&self) -> usize {
        self.mem_size
    }

    /// Get the number of free bytes.
    pub fn unused_bytes(&self) -> usize {
        self.mem_size - self.used_bytes()
    }

    /// Get the number of free blocks per [`BlockSize`]
    pub fn unused_blocks(&self, block_size: BlockSize) -> usize {
        let bitmap = &self.bitmaps[block_size as usize];
        bitmap.get_bits_n() - bitmap.get_bits_set_n()
    }

    /// Calculates the size of memory needed for the ```[```[`BuddyBitmap`]```;8] ``` array,
    /// depending on the available `mem_size` that this array represents.
    pub fn allocator_bitmaps_size(mem_size: usize) -> usize {
        // number of pages is ram_size / page_size
        let pages_n = mem_size / FRAME_SIZE;
        // number of u64 for all the pages is pages_n / 64, as an u64 represents 64 pages
        let int_n = pages_n / u64::BIT_LENGTH;
        // size of the 4KiB bitmap
        let mut total_bitmaps_size = int_n * 8;
        let mut bitmap_size = int_n * 8;
        for _ in 0..7 {
            bitmap_size >>= 1;
            total_bitmaps_size += bitmap_size
        }
        total_bitmaps_size
    }

    fn _get_free_blocks_n(&self, size: usize) -> [usize; 8] {
        let mut free_blocks_n: [usize; 8] = [0; 8];
        let mut tmp_size = size;

        for i in (0usize..8).rev() {
            let block_size = BlockSize::from_u8(i as u8);
            let block_n = tmp_size / block_size.in_bytes();
            let free_block_n = self.unused_blocks(block_size);
            if free_block_n < block_n {
                free_blocks_n[i] = free_block_n
            } else {
                free_blocks_n[i] = block_n
            }
            tmp_size -= free_blocks_n[i] * block_size.in_bytes();
        }
        free_blocks_n
    }

    fn _allocate_block_by_idx(&mut self, bit_idx: usize, block_size: BlockSize) -> usize {
        self._set_bits_true_propagate_up(bit_idx, block_size);
        // returns the start index of the bit range which was set at the 4KiB Bitmap,
        // as this represents the actual physical address of the allocated block
        self._set_bits_propagate_down(bit_idx, 1, block_size, true)
    }

    fn _deallocate_block_by_idx(&mut self, bit_idx: usize, block_size: BlockSize) {
        self._set_bits_propagate_down(bit_idx, 1, block_size, false);
        self._set_bits_false_propagate_up(bit_idx, block_size);
    }

    fn _set_bits_propagate_down(
        &mut self,
        bit_idx: usize,
        bit_n: usize,
        block_size: BlockSize,
        value: bool,
    ) -> usize {
        match block_size {
            // recursion endpoint: when we reach the smallest block size, just set all the bits
            BlockSize4KiB => {
                self.bitmaps[0].set_bit_range(bit_idx, bit_n, value);
                // return bit_idx as this represents the actual physical address of the allocated block
                // println!("{:#?}", bit_idx);
                bit_idx
            }
            b_size => {
                // set bits for the current block size
                self.bitmaps[b_size as usize].set_bit_range(bit_idx, bit_n, value);
                // bitmap with the next smaller block size
                let next_bitmap = BlockSize::from_u8((b_size as u8) - 1);
                // recurse to the next bitmap with index * 2 and the number of bits to be set * 2
                self._set_bits_propagate_down(bit_idx << 1, bit_n << 1, next_bitmap, value)
            }
        }
    }

    fn _set_bits_true_propagate_up(&mut self, bit_idx: usize, block_size: BlockSize) {
        match block_size {
            // recursion endpoint: when we reach the largest block size, just set the bit to true
            BlockSize512KiB => self.bitmaps[7].set_bit(bit_idx, true),
            b_size => {
                // set bit to true for the current block size
                self.bitmaps[b_size as usize].set_bit(bit_idx, true);
                // bitmap with the next larger block size

                // IF BUDDY BLOCK IS TRUE, I CAN STOP THE RECURSION BC PARENT BIT IS ALSO TRUE
                if self.bitmaps[b_size as usize].is_buddy_bit_true(bit_idx) {
                    return;
                }
                let next_bitmap = BlockSize::from_u8((b_size as u8) + 1);
                // recurse to the next bitmap with index // 2 and number of bits to be set / 2
                self._set_bits_true_propagate_up(bit_idx >> 1, next_bitmap)
            }
        }
    }

    fn _set_bits_false_propagate_up(&mut self, bit_idx: usize, block_size: BlockSize) {
        match block_size {
            // recursion endpoint: when we reach the largest block size, just set the bit to false
            BlockSize512KiB => self.bitmaps[7].set_bit(bit_idx, false),
            b_size => {
                // set bit to false for the current block size
                self.bitmaps[b_size as usize].set_bit(bit_idx, false);
                // if buddy_bitmap_allocator bit is also false, set the parent bit on the next larger block size to false
                if !self.bitmaps[b_size as usize].is_buddy_bit_true(bit_idx) {
                    // bitmap with the next larger block size
                    let next_bitmap = BlockSize::from_u8((b_size as u8) + 1);
                    // recurse to the next bitmap with index // 2
                    self._set_bits_false_propagate_up(bit_idx >> 1, next_bitmap)
                }
            }
        }
    }
}

/// An enum which represents the different sizes of memory blocks that the [`BuddyBitmapAllocator`]
/// manages.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum BlockSize {
    BlockSize4KiB,
    BlockSize8KiB,
    BlockSize16KiB,
    BlockSize32KiB,
    BlockSize64KiB,
    BlockSize128KiB,
    BlockSize256KiB,
    BlockSize512KiB,
}

impl BlockSize {
    /// Creates a [`BlockSize`] variant from its u8 representation.
    pub fn from_u8(value: u8) -> BlockSize {
        match value {
            0 => BlockSize4KiB,
            1 => BlockSize8KiB,
            2 => BlockSize16KiB,
            3 => BlockSize32KiB,
            4 => BlockSize64KiB,
            5 => BlockSize128KiB,
            6 => BlockSize256KiB,
            7 => BlockSize512KiB,
            _ => panic!("Unknown value: {}", value),
        }
    }

    /// Returns the [`BlockSize`] in bytes.
    pub const fn in_bytes(&self) -> usize {
        match self {
            BlockSize4KiB => 4 * 1024,
            BlockSize8KiB => 8 * 1024,
            BlockSize16KiB => 16 * 1024,
            BlockSize32KiB => 32 * 1024,
            BlockSize64KiB => 64 * 1024,
            BlockSize128KiB => 128 * 1024,
            BlockSize256KiB => 256 * 1024,
            BlockSize512KiB => 512 * 1024,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const RAM: usize = 128usize * 1024 * 1024;

    #[test]
    fn set_bits_propagate_down_works() {
        let mut data = Box::new([0u64; 1020]);
        let mut buddy = unsafe { BuddyBitmapAllocator::new(data.as_mut_ptr(), RAM) };

        assert_eq!(buddy.bitmaps[7].get_bits_set_n(), 0);
        let bit_idx = buddy._set_bits_propagate_down(1, 1, BlockSize512KiB, true);
        assert_eq!(bit_idx, 128);

        assert_eq!(buddy.bitmaps[0].get_bits_set_n(), 128);
        assert_eq!(buddy.bitmaps[1].get_bits_set_n(), 64);
        assert_eq!(buddy.bitmaps[2].get_bits_set_n(), 32);
        assert_eq!(buddy.bitmaps[3].get_bits_set_n(), 16);
        assert_eq!(buddy.bitmaps[4].get_bits_set_n(), 8);
        assert_eq!(buddy.bitmaps[5].get_bits_set_n(), 4);
        assert_eq!(buddy.bitmaps[6].get_bits_set_n(), 2);
        assert_eq!(buddy.bitmaps[7].get_bits_set_n(), 1);
    }

    #[test]
    fn set_bits_propagate_up_true_works() {
        let mut data = Box::new([0u64; 1020]);
        let mut buddy = unsafe { BuddyBitmapAllocator::new(data.as_mut_ptr(), RAM) };

        buddy._set_bits_true_propagate_up(394, BlockSize4KiB);
        assert_eq!(buddy.bitmaps[0].get_bits_set_n(), 1);
        assert_eq!(buddy.bitmaps[1].get_bits_set_n(), 1);
        assert_eq!(buddy.bitmaps[2].get_bits_set_n(), 1);
        assert_eq!(buddy.bitmaps[3].get_bits_set_n(), 1);
        assert_eq!(buddy.bitmaps[4].get_bits_set_n(), 1);
        assert_eq!(buddy.bitmaps[5].get_bits_set_n(), 1);
        assert_eq!(buddy.bitmaps[6].get_bits_set_n(), 1);
        assert_eq!(buddy.bitmaps[7].get_bits_set_n(), 1);
    }

    #[test]
    fn set_bits_propagate_up_false_works() {
        let mut data = Box::new([0u64; 1020]);
        let mut buddy = unsafe { BuddyBitmapAllocator::new(data.as_mut_ptr(), RAM) };

        buddy._set_bits_propagate_down(0, 1, BlockSize32KiB, true);
        assert_eq!(buddy.bitmaps[0].get_bits_set_n(), 8);
        assert_eq!(buddy.bitmaps[1].get_bits_set_n(), 4);
        assert_eq!(buddy.bitmaps[2].get_bits_set_n(), 2);
        assert_eq!(buddy.bitmaps[3].get_bits_set_n(), 1);

        buddy._set_bits_false_propagate_up(7, BlockSize4KiB);
        buddy._set_bits_false_propagate_up(6, BlockSize4KiB);
        assert_eq!(buddy.bitmaps[0].get_bits_set_n(), 6);
        assert_eq!(buddy.bitmaps[1].get_bits_set_n(), 3);

        buddy._set_bits_false_propagate_up(4, BlockSize4KiB);
        buddy._set_bits_false_propagate_up(5, BlockSize4KiB);

        assert_eq!(buddy.bitmaps[0].get_bits_set_n(), 4);
        assert_eq!(buddy.bitmaps[1].get_bits_set_n(), 2);
        assert_eq!(buddy.bitmaps[2].get_bits_set_n(), 1);
        assert_eq!(buddy.bitmaps[3].get_bits_set_n(), 1);
    }

    #[test]
    fn _allocate_and_deallocate_block_by_idx_works() {
        for i in 0..8u8 {
            let mut data = Box::new([0u64; 1020]);
            let mut buddy = unsafe { BuddyBitmapAllocator::new(data.as_mut_ptr(), RAM) };

            let block_size = BlockSize::from_u8(i);

            // allocate
            for j in 0..(buddy.mem_size / block_size.in_bytes()) {
                let addr = buddy._allocate_block_by_idx(j, block_size);
                assert_eq!(addr, j << (block_size as usize));
            }

            // check if every bit in every bitmap is set
            for j in 0..8 {
                assert_eq!(
                    buddy.bitmaps[j].get_bits_set_n(),
                    buddy.bitmaps[j].get_bits_n()
                );
            }

            // deallocate
            for j in 0..(buddy.mem_size / block_size.in_bytes()) {
                buddy._deallocate_block_by_idx(j, block_size);
            }

            // check if every bit in every bitmap is unset
            for j in 0..8 {
                assert_eq!(buddy.bitmaps[j].get_bits_set_n(), 0);
            }
        }
    }

    #[test]
    fn allocate_all_blocks_works() {
        for i in 0..8u8 {
            let mut data = Box::new([0u64; 1020]);
            let mut buddy = unsafe { BuddyBitmapAllocator::new(data.as_mut_ptr(), RAM) };

            let block_size = BlockSize::from_u8(i);

            for j in 0..(buddy.mem_size / block_size.in_bytes()) {
                let addr = buddy.allocate_block(block_size);
                assert_eq!(
                    addr.unwrap(),
                    ((j << (block_size as usize)) * BlockSize4KiB.in_bytes())
                )
            }

            // allocating another block of arbitrary size must return none, as the bitmap is already filled
            let addr = buddy.allocate_block(block_size);
            assert_eq!(addr, None);

            // check if every bit in every bitmap is set
            assert_eq!(buddy.bitmaps[0].lowest_bit_unset(), None);
            assert_eq!(buddy.bitmaps[1].lowest_bit_unset(), None);
            assert_eq!(buddy.bitmaps[2].lowest_bit_unset(), None);
            assert_eq!(buddy.bitmaps[3].lowest_bit_unset(), None);
            assert_eq!(buddy.bitmaps[4].lowest_bit_unset(), None);
            assert_eq!(buddy.bitmaps[5].lowest_bit_unset(), None);
            assert_eq!(buddy.bitmaps[6].lowest_bit_unset(), None);
            assert_eq!(buddy.bitmaps[7].lowest_bit_unset(), None);
        }
    }

    #[test]
    fn deallocate_block_works() {
        use rand::prelude::*;
        let mut rng = thread_rng();
        let mut data = Box::new([0u64; 1020]);
        let mut buddy = unsafe { BuddyBitmapAllocator::new(data.as_mut_ptr(), RAM) };

        let mut addresses = Vec::new();
        for _ in 0..(buddy.mem_size / BlockSize4KiB.in_bytes()) {
            addresses.push(buddy.allocate_block(BlockSize4KiB).unwrap());
        }

        addresses.shuffle(&mut rng);

        for address in addresses {
            buddy.deallocate_block(address, BlockSize4KiB);
        }

        // check if every bit in every bitmap is unset
        assert_eq!(buddy.bitmaps[0].get_bits_set_n(), 0);
        assert_eq!(buddy.bitmaps[1].get_bits_set_n(), 0);
        assert_eq!(buddy.bitmaps[2].get_bits_set_n(), 0);
        assert_eq!(buddy.bitmaps[3].get_bits_set_n(), 0);
        assert_eq!(buddy.bitmaps[4].get_bits_set_n(), 0);
        assert_eq!(buddy.bitmaps[5].get_bits_set_n(), 0);
        assert_eq!(buddy.bitmaps[6].get_bits_set_n(), 0);
        assert_eq!(buddy.bitmaps[7].get_bits_set_n(), 0);
    }

    #[test]
    fn get_allocation_block_map_works() {
        let mut data = Box::new([0u64; 1020]);
        let mut buddy = unsafe { BuddyBitmapAllocator::new(data.as_mut_ptr(), RAM) };

        // allocate to the max

        while Option::is_some(&buddy.allocate_block(BlockSize512KiB)) {}

        assert_eq!(buddy.unused_blocks(BlockSize512KiB), 0);
        assert_eq!(buddy.unused_blocks(BlockSize256KiB), 0);
        assert_eq!(buddy.unused_blocks(BlockSize128KiB), 0);
        assert_eq!(buddy.unused_blocks(BlockSize64KiB), 0);
        assert_eq!(buddy.unused_blocks(BlockSize32KiB), 0);
        assert_eq!(buddy.unused_blocks(BlockSize16KiB), 0);
        assert_eq!(buddy.unused_blocks(BlockSize8KiB), 0);
        assert_eq!(buddy.unused_blocks(BlockSize4KiB), 0);

        // free every second 4KiB block
        for i in (0..buddy.bitmaps[0].get_bits_n()).step_by(2) {
            buddy.deallocate_block(i * FRAME_SIZE, BlockSize4KiB)
        }

        assert_eq!(buddy.used_bytes(), buddy.unused_bytes());
        assert_eq!(buddy.unused_blocks(BlockSize512KiB), 0);

        let block_map = buddy._get_free_blocks_n(buddy.unused_bytes());

        //
        let expected_map = [16384usize, 0, 0, 0, 0, 0, 0, 0];

        assert_eq!(block_map, expected_map)
    }

    #[test]
    fn allocation_and_deallocation_of_large_amounts_of_memory_works_in_a_reasonable_time() {
        use rand::prelude::*;
        let mut rng = thread_rng();
        let ram = 2usize * 1024 * 1024 * 1024; // 2 GiB

        let mut data = Box::new([0u64; 0x1fe00]);
        let mut buddy = unsafe { BuddyBitmapAllocator::new(data.as_mut_ptr(), ram) };
        assert_eq!(buddy.available_bytes(), ram);

        let blocks512k_n = ram / (BlockSize512KiB.in_bytes());
        for _ in 0..blocks512k_n {
            buddy.allocate_block(BlockSize512KiB);
        }
        assert_eq!(buddy.unused_bytes(), 0);

        for i in (0..(ram / FRAME_SIZE)).step_by(2) {
            buddy.deallocate_block(i * 4096, BlockSize4KiB);
        }
        assert_eq!(buddy.unused_bytes(), buddy.used_bytes());

        // worst case scenario:

        for _ in (0..(ram / (FRAME_SIZE))).step_by(2) {
            buddy.allocate_block(BlockSize4KiB);
        }
        assert_eq!(buddy.unused_bytes(), 0);

        let mut i_vec: Vec<usize> = (0..buddy.mem_size)
            .step_by(BlockSize512KiB.in_bytes())
            .collect();
        i_vec.shuffle(&mut rng);

        for i in i_vec {
            buddy.deallocate_block(i, BlockSize512KiB);
        }
        assert_eq!(buddy.unused_bytes(), ram);
    }
}
