use bit_field::BitField;

/// A Bitmap used by the [`BuddyFrameAllocator`]
pub struct BuddyBitmap {
    /// A `mut` pointer to the physical memory address of the [`BuddyBitmap`].
    ptr: *mut u64,
    /// Number of `u64` integers, which represent the [`BuddyBitmap`].
    /// This equals to `bit_n` / [`u64::BIT_LENGTH`].
    int_n: usize,
    /// Number of bits managed by the [`BuddyBitmap`].
    /// This equals to `int_n` * [`u64::BIT_LENGTH`].
    bit_n: usize,
    int_last_touched: usize,
}

impl BuddyBitmap {
    /// Create a new [`BuddyBitmap`] with following args:
    /// * `ptr`: a `mut` pointer to the (physical) memory address of the
    /// [`BuddyBitmap`]
    /// * `int_n`: the number of `u64` integers representing the bits of the [`BuddyBitmap`].

    /// # Safety
    ///
    /// The [`BuddyBitmap`] operates on an unsafe mutable pointer in a `C`-like fashion,
    /// so the caller *must* guarantee, that the bitmap is located in a valid memory area
    /// and that this memory area cannot be manipulated in any other way.
    pub unsafe fn new(ptr: *mut u64, int_n: usize) -> Self {
        Self {
            ptr,
            int_n,
            bit_n: int_n * u64::BIT_LENGTH,
            int_last_touched: 0,
        }
    }

    /// Set a single bit at the `bit_idx` to the given `value`.
    pub fn set_bit(&mut self, bit_idx: usize, value: bool) {
        // prevent overflow
        debug_assert!(bit_idx < self.bit_n);

        let int_offset: usize = bit_idx / u64::BIT_LENGTH;
        let bit_offset: usize = bit_idx % u64::BIT_LENGTH;
        self.int_last_touched = int_offset;
        unsafe {
            let ptr = self.ptr.add(int_offset);
            (*ptr).set_bit(bit_offset, value);
        };
    }

    /// Set a number of `bit_n` bits to the given `value`, starting from `bit_idx`.
    pub fn set_bit_range(&mut self, bit_idx: usize, bit_n: usize, value: bool) {
        // assert number of bits to set is a power of two
        debug_assert!(bit_n.is_power_of_two());
        // assert index is aligned
        debug_assert_eq!((bit_idx % bit_n), 0, "index not aligned");
        // prevent overflow
        debug_assert!(bit_idx < self.bit_n, "index out of range");
        debug_assert!(bit_idx + bit_n - 1 < self.bit_n, "index out of range");

        match bit_n {
            0..=63 => {
                let int_offset = bit_idx / u64::BIT_LENGTH;
                let bit_offset = bit_idx % u64::BIT_LENGTH;
                self.int_last_touched = int_offset;

                unsafe {
                    let ptr = self.ptr.add(int_offset);
                    let value = if value { bitmask_from_bit_n(bit_n) } else { 0 };
                    (*ptr).set_bits(bit_offset..bit_offset + bit_n, value);
                }
            }
            64.. => {
                let int_offset = bit_idx / u64::BIT_LENGTH;
                let num_int = bit_n / u64::BIT_LENGTH;
                let value = if value { u64::MAX } else { 0 };

                self.int_last_touched = int_offset + num_int - 1;
                for i in int_offset..int_offset + num_int {
                    unsafe {
                        let ptr = self.ptr.add(i);
                        *ptr = value;
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn set_all_false(&mut self) {
        self.set_bit_range(0, self.bit_n, false);
        self.int_last_touched = 0;
        debug_assert_eq!(self.get_bits_set_n(), 0)
    }

    /// Get the index of the lowest bit unset in the [`BuddyBitmap`]. If every bit in the
    /// [`BuddyBitmap`] is set to `true`, this will return `None`.
    pub fn lowest_bit_unset(&mut self) -> Option<usize> {
        for i in 0..self.int_n {
            let int_idx = (i + self.int_last_touched) % self.int_n;
            unsafe {
                let ptr = self.ptr.add(int_idx);
                if *ptr == u64::MAX {
                    continue;
                }
                self.int_last_touched = int_idx;
                let bit_mask = (!(*ptr)) & ((*ptr) + 1); // !val & val + 1
                let bit_idx_within_int = (bit_mask - 1).count_ones() as usize;
                let bit_idx = bit_idx_within_int + int_idx * u64::BIT_LENGTH;
                return Some(bit_idx);
            }
        }
        None
    }

    /// Returns the value of the given bit's "buddy_bitmap_allocator bit", where the "buddy_bitmap_allocator bit" is
    /// `bit_idx + 1` if the `bit_idx` is even and `bit_idx - 1` if it is uneven.
    pub fn is_buddy_bit_true(&self, bit_idx: usize) -> bool {
        // prevent overflow
        debug_assert!(bit_idx < self.bit_n, "index out of range");

        let buddy_bit_idx = if bit_idx % 2 == 0 {
            bit_idx + 1
        } else {
            bit_idx - 1
        };
        let int_offset = bit_idx / u64::BIT_LENGTH;
        let buddy_bit_offset = buddy_bit_idx % u64::BIT_LENGTH;
        unsafe {
            let ptr = self.ptr.add(int_offset);
            (*ptr).get_bit(buddy_bit_offset)
        }
    }

    /// Gets the number of true bits in this [`BuddyBitmap`].
    pub fn get_bits_set_n(&self) -> usize {
        let mut set_bits: usize = 0;
        for i in 0..self.int_n {
            unsafe {
                set_bits += (*self.ptr.add(i)).count_ones() as usize;
            }
        }
        set_bits
    }

    /// Get the number of bits in this [`BuddyBitmap`].
    pub fn get_bits_n(&self) -> usize {
        self.bit_n
    }

    #[cfg(test)]
    fn get_int_value(&self, int_idx: usize) -> u64 {
        unsafe { *self.ptr.add(int_idx) }
    }
}

const fn bitmask_from_bit_n(bit_n: usize) -> u64 {
    2u64.pow(bit_n as u32) - 1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_bit_works() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };

        bitmap.set_bit(7, true);
        bitmap.set_bit(63, true);
        assert_eq!(bitmap.get_int_value(0), 0x8000_0000_0000_0080);

        bitmap.set_bit(7, false);
        assert_eq!(bitmap.get_int_value(0), 0x8000_0000_0000_0000);

        bitmap.set_bit(67, true);
        assert_eq!(bitmap.get_int_value(1), 0x8);
    }

    #[test]
    fn set_bit_range_works() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };

        bitmap.set_bit_range(0, 32, true);
        assert_eq!(bitmap.get_int_value(0), u32::MAX as u64);

        bitmap.set_bit_range(512, 512, true);
        assert_eq!(bitmap.get_int_value(8), u64::MAX);
        assert_eq!(bitmap.get_int_value(9), u64::MAX);
        assert_eq!(bitmap.get_int_value(10), u64::MAX);
        assert_eq!(bitmap.get_int_value(11), u64::MAX);
        assert_eq!(bitmap.get_int_value(12), u64::MAX);
        assert_eq!(bitmap.get_int_value(13), u64::MAX);
        assert_eq!(bitmap.get_int_value(14), u64::MAX);
        assert_eq!(bitmap.get_int_value(15), u64::MAX);

        bitmap.set_bit_range(704, 64, false);
        assert_eq!(bitmap.get_int_value(11), 0);
    }

    #[test]
    fn get_bits_set_n_works() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };

        bitmap.set_bit_range(512, 512, true);
        bitmap.set_bit_range(0, 32, true);
        bitmap.set_bit_range(2048, 4, true);

        assert_eq!(bitmap.get_bits_set_n(), 548)
    }

    #[test]
    fn lowest_bit_unset_works() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };

        for i in 0..bitmap.bit_n {
            assert_eq!(bitmap.lowest_bit_unset(), Some(i));
            bitmap.set_bit(i, true)
        }

        assert_eq!(bitmap.int_last_touched, 511)
    }

    #[test]
    #[should_panic]
    fn set_bit_fails_with_overflow() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };
        bitmap.set_bit(512 * 64, true);
    }

    #[test]
    #[should_panic]
    fn set_bit_range_fails_with_overflow() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };
        bitmap.set_bit_range(512 * 64, 2, true);
    }

    #[test]
    #[should_panic]
    fn set_bit_range_fails_with_overflow2() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };
        bitmap.set_bit_range(0, 512 * 64 + 1, true);
    }

    #[test]
    #[should_panic]
    fn set_bit_range_fails_with_bad_alignment() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };
        bitmap.set_bit_range(0, 3, true);
    }

    #[test]
    #[should_panic]
    fn set_bit_range_fails_when_not_pow_2() {
        let mut data = Box::new([0u64; 512]);
        let mut bitmap = unsafe { BuddyBitmap::new(data.as_mut_ptr(), 512) };
        bitmap.set_bit_range(0, 6, true);
    }
}
