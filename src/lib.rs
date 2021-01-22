/*!

***Reading bits until the bitter end***

Bitter takes a slice of byte data and reads bits in a desired endian format platform agonistically.

## Features

 - ✔ support for little endian, big endian, and native endian formats
 - ✔ request an arbitrary amount of bits (up to 32 bits)
 - ✔ ergonomic requests for common data types (including `u64` / `i64`)
 - ✔ > 5 GB/s throughput when reading large number of bits
 - ✔ > 1 GB/s throughput when reading single digit sized chunks of bits
 - ✔ two APIs: one for safety and one for speed
 - ✔ zero dependencies
 - ✔ zer  o allocations
 - ✔ `no_std` compatible

## Example

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
assert_eq!(bitter.read_bit(), Some(true));
assert_eq!(bitter.read_u8(), Some(0x7f));
assert_eq!(bitter.read_u32_bits(7), Some(0x02));
```

There are two main APIs available: checked and unchecked functions. The above example uses the checked API as return types are options to designate that there wasn't sufficient data to complete the read. Unchecked APIs will exhibit
undefined behavior if there is not enough data left, but can be significantly faster.

Tips:

- Prefer checked functions for all but the most performance critical code
- Group all unchecked functions in a single block guarded by a `has_bits_remaining` call

Below is a demonstration of the unchecked APIs with a guard to ensure safety:

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
if bitter.has_bits_remaining(16) {
    assert_eq!(bitter.read_bit_unchecked(), true);
    assert_eq!(bitter.read_u8_unchecked(), 0x7f);
    assert_eq!(bitter.read_u32_bits_unchecked(7), 0x02);
}
```

Another guard usage:

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
if bitter.has_bits_remaining(16) {
    for _ in 0..8 {
        assert_eq!(bitter.read_bit_unchecked(), true);
    }
    assert_eq!(bitter.read_u8_unchecked(), 0x04);
}
```

### `no_std` crates

This crate has a feature, `std`, that is enabled by default. To use this crate
in a `no_std` context, add the following to your `Cargo.toml`:

```toml
[dependencies]
bitter = { version = "x", default-features = false }
```

*/

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]
#![warn(missing_docs)]

/// Read bits in a given endian order
pub trait BitReader {
    /// Consume a bit and return if the bit was enabled
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bits = BigEndianReader::new(&[0b1001_0011]);
    /// assert_eq!(bits.read_bit(), Some(true));
    /// assert_eq!(bits.read_bit(), Some(false));
    /// ```
    fn read_bit(&mut self) -> Option<bool>;

    /// Consume 8 bits and return the deserialized byte
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bits = BigEndianReader::new(&[0b1001_0011]);
    /// assert_eq!(bits.read_u8(), Some(0b1001_0011));
    /// ```
    fn read_u8(&mut self) -> Option<u8>;

    /// Consume 8 bits and return the deserialized byte
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bits = BigEndianReader::new(&[0b1001_0011]);
    /// assert_eq!(bits.read_i8(), Some(-109));
    /// ```
    fn read_i8(&mut self) -> Option<i8>;

    /// Consume 16 bits and return the deserialized short
    ///
    /// ```rust
    /// use bitter::{BitReader, LittleEndianReader};
    /// let mut bits = LittleEndianReader::new(&[0b1001_0011, 0b1111_1111]);
    /// assert_eq!(bits.read_u16(), Some(0xff93));
    /// ```
    fn read_u16(&mut self) -> Option<u16>;

    /// Consume 16 bits and return the deserialized short
    ///
    /// ```rust
    /// use bitter::{BitReader, LittleEndianReader};
    /// let data = (-500i16).to_le_bytes();
    /// let mut bits = LittleEndianReader::new(&data);
    /// assert_eq!(bits.read_i16(), Some(-500));
    /// ```
    fn read_i16(&mut self) -> Option<i16>;

    /// Consume 32 bits and return the deserialized int
    ///
    /// ```rust
    /// use bitter::{BitReader, LittleEndianReader};
    /// let data = (22000u32).to_le_bytes();
    /// let mut bits = LittleEndianReader::new(&data);
    /// assert_eq!(bits.read_u32(), Some(22000u32));
    /// ```
    fn read_u32(&mut self) -> Option<u32>;

    /// Consume 32 bits and return the deserialized int
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = (-22000i32).to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_i32(), Some(-22000i32));
    /// ```
    fn read_i32(&mut self) -> Option<i32>;

    /// Consume 64 bits and return the deserialized long
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = (22000u64).to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_u64(), Some(22000u64));
    /// ```
    fn read_u64(&mut self) -> Option<u64>;

    /// Consume 64 bits and return the deserialized long
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = (-22000i64).to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_i64(), Some(-22000i64));
    /// ```
    fn read_i64(&mut self) -> Option<i64>;

    /// Consume 32 bits and return the deserialized floating point
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = 12.5f32.to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_f32(), Some(12.5f32));
    /// ```
    fn read_f32(&mut self) -> Option<f32>;

    /// Reads an arbitrary number of bits from 1 to 32 (inclusive)
    /// and returns the unsigned result
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bitter = BigEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
    /// assert_eq!(bitter.read_u32_bits(32), Some(0xff00abcd));
    /// ```
    fn read_u32_bits(&mut self, bits: i32) -> Option<u32>;

    /// Reads an arbitrary number of bits from 1 to 32 (inclusive)
    /// and returns the signed result.
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bitter = BigEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
    /// let result = i32::from_be_bytes([0xff, 0x00, 0xab, 0xcd]);
    /// assert_eq!(bitter.read_i32_bits(32), Some(result));
    /// ```
    fn read_i32_bits(&mut self, bits: i32) -> Option<i32>;

    /// If the next bit is available and on, decode the next chunk of data (which can return None).
    /// The return value can be one of the following:
    ///
    /// - None: Not enough data was available
    /// - Some(None): Bit was off so data not decoded
    /// - Some(x): Bit was on and data was decoded
    ///
    /// ```rust
    /// use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
    /// assert_eq!(bitter.if_get(BitReader::read_u8), Some(Some(0x7f)));
    /// assert_eq!(bitter.if_get(BitReader::read_u8), Some(None));
    /// assert_eq!(bitter.if_get(BitReader::read_u8), None);
    /// ```
    fn if_get<T, F>(&mut self, f: F) -> Option<Option<T>>
    where
        F: FnMut(&mut Self) -> Option<T>;

    /// Reads a value from the stream that consumes the same or fewer number of bits of a given
    /// max. The value read will always be less than the given max.
    ///
    /// For example if one wants to read a value that is less than 20, bitter will read at least
    /// 4 bits from the stream. If the 5th bit would cause the accumulator to exceed the max, the
    /// 5th bit is not consumed. Else the 5th bit is consumed and added to accumulator. If the
    /// necessary number of bits are not available, `None` is returned.
    ///
    /// ```rust
    /// use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0b1111_1000]);
    /// assert_eq!(bitter.read_bits_max(20), Some(8));
    /// assert_eq!(bitter.read_bits_max(20), Some(15));
    /// ```
    fn read_bits_max(&mut self, max: u32) -> Option<u32>;

    /// Same as `read_bits_max` except that this function accepts the already computed number of
    /// bits to at least read. For instance, if 20 is the max, then 4 bits are at least needed.
    ///
    /// In general, prefer `read_bits_max` for ease of use, as passing an incorrectly
    /// computed max can lead to undefined behavior
    ///
    /// ```rust
    /// use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0b1111_1000]);
    /// assert_eq!(bitter.read_bits_max_computed(4, 20), Some(8));
    /// assert_eq!(bitter.read_bits_max_computed(4, 20), Some(15));
    /// ```
    fn read_bits_max_computed(&mut self, bits: i32, max: u32) -> Option<u32>;

    /// *Assumes* there is at least one bit left in the stream.
    ///
    /// ```rust
    /// use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
    /// assert_eq!(bitter.read_bit_unchecked(), false);
    /// ```
    fn read_bit_unchecked(&mut self) -> bool;

    /// *Assumes* there is at least 8 bits left in the stream.
    ///
    /// ```rust
    /// use bitter::{BigEndianReader, BitReader};
    /// let mut bitter = BigEndianReader::new(&[0b1010_1010, 0b0101_0101]);
    /// assert_eq!(bitter.read_u8_unchecked(), 0b1010_1010);
    /// ```
    fn read_u8_unchecked(&mut self) -> u8;

    /// *Assumes* there is at least 8 bits left in the stream.
    ///
    /// ```rust
    /// use bitter::{BigEndianReader, BitReader};
    /// let mut bitter = BigEndianReader::new(&[0b1010_1010, 0b0101_0101]);
    /// assert_eq!(bitter.read_i8_unchecked(), i8::from_be_bytes([0b1010_1010]));
    /// ```
    fn read_i8_unchecked(&mut self) -> i8;

    /// Consume 16 bits and return the deserialized short
    ///
    /// ```rust
    /// use bitter::{BitReader, LittleEndianReader};
    /// let mut bits = LittleEndianReader::new(&[0b1001_0011, 0b1111_1111]);
    /// assert_eq!(bits.read_u16_unchecked(), 0xff93);
    /// ```
    fn read_u16_unchecked(&mut self) -> u16;

    /// Consume 16 bits and return the deserialized short
    ///
    /// ```rust
    /// use bitter::{BitReader, LittleEndianReader};
    /// let data = (-500i16).to_le_bytes();
    /// let mut bits = LittleEndianReader::new(&data);
    /// assert_eq!(bits.read_i16_unchecked(), -500);
    /// ```
    fn read_i16_unchecked(&mut self) -> i16;

    /// Consume 32 bits and return the deserialized int
    ///
    /// ```rust
    /// use bitter::{BitReader, LittleEndianReader};
    /// let data = (22000u32).to_le_bytes();
    /// let mut bits = LittleEndianReader::new(&data);
    /// assert_eq!(bits.read_u32_unchecked(), 22000u32);
    /// ```
    fn read_u32_unchecked(&mut self) -> u32;

    /// Consume 32 bits and return the deserialized int
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = (-22000i32).to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_i32_unchecked(), -22000i32);
    /// ```
    fn read_i32_unchecked(&mut self) -> i32;

    /// Consume 64 bits and return the deserialized long
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = (22000u64).to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_u64_unchecked(), 22000u64);
    /// ```
    fn read_u64_unchecked(&mut self) -> u64;

    /// Consume 64 bits and return the deserialized long
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = (-22000i64).to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_i64_unchecked(), -22000i64);
    /// ```
    fn read_i64_unchecked(&mut self) -> i64;

    /// Consume 32 bits and return the deserialized floating point
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = 12.5f32.to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_f32_unchecked(), 12.5f32);
    /// ```
    fn read_f32_unchecked(&mut self) -> f32;

    /// Reads an arbitrary number of bits from 1 to 32 (inclusive)
    /// and returns the unsigned result
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bitter = BigEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
    /// assert_eq!(bitter.read_u32_bits_unchecked(32), 0xff00abcd);
    /// ```
    fn read_u32_bits_unchecked(&mut self, bits: i32) -> u32;

    /// Reads an arbitrary number of bits from 1 to 32 (inclusive)
    /// and returns the signed result.
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bitter = BigEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
    /// let result = i32::from_be_bytes([0xff, 0x00, 0xab, 0xcd]);
    /// assert_eq!(bitter.read_i32_bits_unchecked(32), result);
    /// ```
    fn read_i32_bits_unchecked(&mut self, bits: i32) -> i32;

    /// If the next bit is available and on, decode the next chunk of data.  The return value can
    /// be one of the following:
    ///
    /// - Some(None): Bit was off so data not decoded
    /// - Some(x): Bit was on and data was decoded
    ///
    /// ```rust
    /// use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
    /// assert_eq!(bitter.if_get_unchecked(LittleEndianReader::read_u8_unchecked), Some(0x7f));
    /// assert_eq!(bitter.if_get_unchecked(LittleEndianReader::read_u8_unchecked), None);
    /// ```
    fn if_get_unchecked<T, F>(&mut self, f: F) -> Option<T>
    where
        F: FnMut(&mut Self) -> T;

    /// Reads a value from the stream that consumes the same or fewer number of bits of a given
    /// max. The value read will always be less than the given max.
    ///
    /// For example if one wants to read a value that is less than 20, bitter will read at least
    /// 4 bits from the stream. If the 5th bit would cause the accumulator to exceed the max, the
    /// 5th bit is not consumed. Else the 5th bit is consumed and added to accumulator. If the
    /// necessary number of bits are not available, `None` is returned.
    ///
    /// ```rust
    /// use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0b1111_1000]);
    /// assert_eq!(bitter.read_bits_max_unchecked(20), 8);
    /// assert_eq!(bitter.read_bits_max_unchecked(20), 15);
    /// ```
    fn read_bits_max_unchecked(&mut self, max: u32) -> u32;

    /// Same as `read_bits_max_unchecked` except that this function accepts the already computed number of
    /// bits to at least read. For instance, if 20 is the max, then 4 bits are at least needed.
    ///
    /// In general, prefer `read_bits_max_unchecked` for ease of use, as passing an incorrectly
    /// computed max can lead to undefined behavior
    ///
    /// ```rust
    /// use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0b1111_1000]);
    /// assert_eq!(bitter.read_bits_max_computed_unchecked(4, 20), 8);
    /// assert_eq!(bitter.read_bits_max_computed_unchecked(4, 20), 15);
    /// ```
    fn read_bits_max_computed_unchecked(&mut self, bits: i32, max: u32) -> u32;

    /// Return approximately how many bytes are left in the bitstream. This
    /// can overestimate by one when the reader is at a position that is not
    /// byte aligned. Thus it is recommended to always compare with a greater
    /// than sign to avoid undefined behavior with unchecked reads
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0xff]);
    /// assert_eq!(bitter.approx_bytes_remaining(), 1);
    /// assert!(bitter.read_bit().is_some());
    /// assert_eq!(bitter.approx_bytes_remaining(), 1);
    /// assert!(bitter.read_u32_bits(7).is_some());
    /// assert_eq!(bitter.approx_bytes_remaining(), 0);
    /// ```
    fn approx_bytes_remaining(&self) -> usize;

    /// Returns the exact number of bits remaining in the bitstream if the number of bits can fit
    /// within a `usize`. For large byte slices, the calculating the number of bits can cause an
    /// overflow, hence an `Option` is returned. See `has_bits_remaining` for a more performant and
    /// ergonomic alternative.
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0xff]);
    /// assert_eq!(bitter.bits_remaining(), Some(8));
    /// assert!(bitter.read_bit().is_some());
    /// assert_eq!(bitter.bits_remaining(), Some(7));
    /// assert!(bitter.read_u32_bits(7).is_some());
    /// assert_eq!(bitter.bits_remaining(), Some(0));
    /// ```
    fn bits_remaining(&self) -> Option<usize>;

    /// Returns true if at least `bits` number of bits are left in the stream. A more performant
    /// and ergonomic way than `bits_remaining`.
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0xff]);
    /// assert!(bitter.has_bits_remaining(7));
    /// assert!(bitter.has_bits_remaining(8));
    /// assert!(!bitter.has_bits_remaining(9));
    ///
    /// assert!(bitter.read_bit().is_some());
    /// assert!(bitter.has_bits_remaining(7));
    /// assert!(!bitter.has_bits_remaining(8));
    ///
    /// assert!(bitter.read_u32_bits(7).is_some());
    /// assert!(!bitter.has_bits_remaining(7));
    /// assert!(bitter.has_bits_remaining(0));
    /// ```
    fn has_bits_remaining(&self, bits: usize) -> bool;

    /// Read the number of bytes needed to fill the provided buffer. Returns whether
    /// the read was successful and the buffer has been filled.
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
    /// let mut buf = [0; 1];
    /// assert_eq!(bitter.read_bit_unchecked(), false);
    /// assert!(bitter.read_bytes(&mut buf));
    /// assert_eq!(&buf, &[0b1101_0101]);
    /// assert!(!bitter.read_bytes(&mut buf));
    /// ```
    fn read_bytes(&mut self, buf: &mut [u8]) -> bool;

    /// Returns if the bitstream has no bits left
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
    /// assert_eq!(bitter.is_empty(), false);
    /// assert_eq!(bitter.read_u16_unchecked(), 0b0101_0101_1010_1010);
    /// assert_eq!(bitter.is_empty(), true);
    /// ```    
    fn is_empty(&self) -> bool;
}

/// Calculates the width of the input in bits
///
/// ```rust
/// assert_eq!(bitter::bit_width(20), 5);
/// assert_eq!(bitter::bit_width(0), 0);
/// assert_eq!(bitter::bit_width(u32::max_value()), 32);
/// ```
pub const fn bit_width(input: u32) -> u32 {
    (core::mem::size_of::<u32>() as u32) * 8 - input.leading_zeros()
}

/// Generates the bitmask for 32-bit integers (yes, even though the return type is u64)
#[inline]
const fn bit_mask(bits: usize) -> u64 {
    (1 << bits) - 1
}

/// Returns value shifted left by the given bits. If the
/// the number of bits exceeds 63 then 0 is returned
#[inline]
fn shl_mask(val: u64, shift: usize) -> u64 {
    if shift == 64 {
        0
    } else {
        val << shift
    }
}

/// Returns value shifted right by the given bits. If the
/// the number of bits exceeds 63 then 0 is returned
#[inline]
fn shr_mask(val: u64, shift: usize) -> u64 {
    if shift == 64 {
        0
    } else {
        val >> shift
    }
}

const BYTE_WIDTH: usize = core::mem::size_of::<u64>();
const BIT_WIDTH: usize = BYTE_WIDTH * 8;

macro_rules! gen_read {
    ($name:ident, $t:ty) => {
        #[inline]
        fn $name(&mut self) -> Option<$t> {
            let bits = (core::mem::size_of::<$t>() * 8) as i32;
            self.read_u32_bits(bits).map(|x| x as $t)
        }
    };
}

macro_rules! gen_read_unchecked {
    ($name:ident, $t:ty) => {
        #[inline]
        fn $name(&mut self) -> $t {
            let bits = (core::mem::size_of::<$t>() * 8) as i32;
            self.read_u32_bits_unchecked(bits) as $t
        }
    };
}

macro_rules! generate_bitter_end {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        pub struct $name<'a> {
            /// The bit position in `current` that we are at
            pos: usize,

            /// Byte stream of data we are parsing
            data: &'a [u8],

            /// The eight bytes that current is pointing at
            current_val: u64,

            end_pos: usize,
        }

        impl<'a> $name<'a> {
            /// Creates the endian specific reader that is tied to a given slice of bytes
            pub fn new(data: &'a [u8]) -> Self {
                let mut res = $name {
                    pos: 0,
                    current_val: 0,
                    data,
                    end_pos: BIT_WIDTH,
                };

                res.current_val = res.read();
                res
            }

            /// Determines if our bit position is not byte aligned
            #[inline]
            fn is_mid_byte(&self) -> bool {
                // 0x38 = 32 | 24 | 16 | 8
                self.pos & !0x38 != 0
            }
        }

        impl<'a> BitReader for $name<'a> {
            gen_read!(read_u8, u8);
            gen_read!(read_i8, i8);
            gen_read!(read_u16, u16);
            gen_read!(read_i16, i16);
            gen_read!(read_u32, u32);
            gen_read!(read_i32, i32);

            gen_read_unchecked!(read_u8_unchecked, u8);
            gen_read_unchecked!(read_i8_unchecked, i8);
            gen_read_unchecked!(read_u16_unchecked, u16);
            gen_read_unchecked!(read_i16_unchecked, i16);
            gen_read_unchecked!(read_u32_unchecked, u32);
            gen_read_unchecked!(read_i32_unchecked, i32);

            #[inline]
            fn read_u64_unchecked(&mut self) -> u64 {
                $name::read_u64_unchecked(self)
            }

            #[inline]
            fn read_u64(&mut self) -> Option<u64> {
                $name::read_u64(self)
            }

            #[inline]
            fn read_i64(&mut self) -> Option<i64> {
                self.read_u64().map(|x| x as i64)
            }

            #[inline]
            fn read_i64_unchecked(&mut self) -> i64 {
                self.read_u64_unchecked() as i64
            }

            #[inline]
            fn read_u32_bits_unchecked(&mut self, bits: i32) -> u32 {
                self.read_bits_unchecked(bits)
            }

            #[inline]
            fn read_u32_bits(&mut self, bits: i32) -> Option<u32> {
                self.read_bits(bits)
            }

            #[inline]
            fn read_i32_bits_unchecked(&mut self, bits: i32) -> i32 {
                self.read_u32_bits_unchecked(bits) as i32
            }

            #[inline]
            fn read_i32_bits(&mut self, bits: i32) -> Option<i32> {
                self.read_u32_bits(bits).map(|x| x as i32)
            }

            #[inline]
            fn approx_bytes_remaining(&self) -> usize {
                self.data.len() - (self.pos >> 3)
            }

            #[inline]
            fn bits_remaining(&self) -> Option<usize> {
                self.approx_bytes_remaining()
                    .checked_mul(8)
                    .map(|x| x - (self.pos & 0x7) as usize)
            }

            #[inline]
            fn has_bits_remaining(&self, bits: usize) -> bool {
                let bytes_requested = bits >> 3;
                if self.data.len() > bytes_requested + BYTE_WIDTH {
                    true
                } else {
                    let pos_bytes = self.pos >> 3;
                    let diff = self.data.len();
                    if !self.is_mid_byte() {
                        let bytes_left = diff - pos_bytes;
                        if bytes_left == bytes_requested {
                            bits & 0x7 == 0
                        } else {
                            bytes_left > bytes_requested
                        }
                    } else {
                        let whole_bytes_left = diff - pos_bytes;
                        if whole_bytes_left == bytes_requested + 1 {
                            (self.pos & 0x7) <= (8 - (bits & 0x7))
                        } else {
                            whole_bytes_left > bytes_requested + 1
                        }
                    }
                }
            }

            fn is_empty(&self) -> bool {
                self.approx_bytes_remaining() == 0
            }

            #[inline]
            fn read_bit(&mut self) -> Option<bool> {
                self.read_u32_bits(1).map(|x| x != 0)
            }

            #[inline]
            fn read_bit_unchecked(&mut self) -> bool {
                self.read_u32_bits_unchecked(1) & 1 != 0
            }

            #[inline]
            fn read_f32(&mut self) -> Option<f32> {
                self.read_u32().map(f32::from_bits)
            }

            #[inline]
            fn read_f32_unchecked(&mut self) -> f32 {
                f32::from_bits(self.read_u32_unchecked())
            }

            #[cfg_attr(feature = "cargo-clippy", allow(clippy::option_option))]
            fn if_get<T, F>(&mut self, mut f: F) -> Option<Option<T>>
            where
                F: FnMut(&mut Self) -> Option<T>,
            {
                self.read_bit()
                    .and_then(|bit| if bit { f(self).map(Some) } else { Some(None) })
            }

            fn if_get_unchecked<T, F>(&mut self, mut f: F) -> Option<T>
            where
                F: FnMut(&mut Self) -> T,
            {
                if self.read_bit_unchecked() {
                    Some(f(self))
                } else {
                    None
                }
            }

            fn read_bytes(&mut self, buf: &mut [u8]) -> bool {
                let pos_bytes = self.pos >> 3;
                let bytes_left = self.data.len() - pos_bytes;
                if !self.is_mid_byte() && bytes_left >= buf.len() {
                    let end = pos_bytes + buf.len();
                    buf.copy_from_slice(&self.data[pos_bytes..end]);
                    self.data = &self.data[end..];
                    self.current_val = self.read();
                    self.pos = 0;
                    true
                } else if bytes_left > buf.len() {
                    for b in buf.iter_mut() {
                        *b = self.read_u8_unchecked();
                    }

                    true
                } else {
                    false
                }
            }

            fn read_bits_max(&mut self, max: u32) -> Option<u32> {
                let bits = bit_width(max) as i32 - 1;
                self.read_bits_max_computed(core::cmp::max(bits, 0), max)
            }

            #[inline]
            fn read_bits_max_computed(&mut self, bits: i32, max: u32) -> Option<u32> {
                debug_assert!(core::cmp::max(bit_width(max) as i32, 1) == bits + 1);
                self.read_u32_bits(bits).and_then(|data| {
                    let up = data + (1 << bits);
                    if up >= max {
                        Some(data)
                    } else {
                        // Check the next bit
                        self.read_bit().map(|x| if x { up } else { data })
                    }
                })
            }

            #[inline]
            fn read_bits_max_unchecked(&mut self, max: u32) -> u32 {
                let bits = bit_width(max) as i32 - 1;
                self.read_bits_max_computed_unchecked(core::cmp::max(bits, 0), max)
            }

            #[inline]
            fn read_bits_max_computed_unchecked(&mut self, bits: i32, max: u32) -> u32 {
                debug_assert!(core::cmp::max(bit_width(max) as i32, 1) == bits + 1);
                let data = self.read_u32_bits_unchecked(bits);

                // If the next bit is on, what would our value be
                let up = data + (1 << bits);

                // If we have the potential to equal or exceed max don't read the next bit, else read the
                // next bit
                if up >= max || !self.read_bit_unchecked() {
                    data
                } else {
                    up
                }
            }
        }
    };
}

generate_bitter_end!(
    /// Reads bits in the little-endian format
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut lebits = BigEndianReader::new(&[0b1000_0000]);
    /// assert_eq!(lebits.read_bit(), Some(true));
    /// ```
    LittleEndianReader
);
generate_bitter_end!(
    /// Reads bits in the big-endian format
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bebits = BigEndianReader::new(&[0b1000_0000]);
    /// assert_eq!(bebits.read_bit(), Some(true));
    /// ```
    BigEndianReader
);

/// Read bits in system native-endian format
#[cfg(target_endian = "little")]
pub type NativeEndianReader<'a> = LittleEndianReader<'a>;

/// Read bits in system native-endian format
#[cfg(target_endian = "big")]
pub type NativeEndianReader<'a> = BigEndianReader<'a>;

impl<'a> LittleEndianReader<'a> {
    /// Assuming that `self.data` is pointing to data not yet seen. slurp up 8 bytes or the
    /// rest of the data (whatever is smaller)
    ///
    /// Clippy lint can be unsuppressed once Clippy recognizes this pattern as correct.
    /// https://github.com/rust-lang/rust-clippy/issues/2881
    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    fn read(&mut self) -> u64 {
        unsafe {
            if self.data.len() >= BYTE_WIDTH {
                core::ptr::read_unaligned(self.data.as_ptr() as *const u8 as *const u64).to_le()
            } else {
                let mut result: u64 = 0;
                let len = self.data.len();
                self.end_pos = len * 8;
                core::ptr::copy_nonoverlapping(
                    self.data.as_ptr(),
                    &mut result as *mut u64 as *mut u8,
                    len,
                );
                result.to_le()
            }
        }
    }

    #[inline]
    fn read_bits(&mut self, bits: i32) -> Option<u32> {
        let bts = bits as usize;
        let new_pos = self.pos + bts;
        if new_pos <= self.end_pos {
            let res = (self.current_val >> self.pos) & bit_mask(bts);
            self.pos = new_pos;
            Some(res as u32)
        } else if self.end_pos == BIT_WIDTH {
            let new_data = &self.data[BYTE_WIDTH..];
            let left = new_pos - BIT_WIDTH;
            if new_data.len() < BYTE_WIDTH && left > new_data.len() * 8 {
                None
            } else {
                let little = shr_mask(self.current_val, self.pos);
                self.data = new_data;
                self.current_val = self.read();
                let big = (self.current_val & bit_mask(left)) << (bts - left);
                self.pos = left;
                Some((little + big) as u32)
            }
        } else {
            None
        }
    }

    #[inline]
    fn read_u64(&mut self) -> Option<u64> {
        // While reading 64bit we can take advantage of an optimization trick not available to
        // other reads as 64bits is the same as our cache size
        if self.end_pos - self.pos == BIT_WIDTH {
            let ret = self.current_val;
            self.data = &self.data[BYTE_WIDTH..];
            self.current_val = self.read();
            Some(ret)
        } else if self.end_pos == BIT_WIDTH {
            let bts = core::mem::size_of::<u64>() * 8;
            let new_data = &self.data[BYTE_WIDTH..];
            if new_data.len() < BYTE_WIDTH && self.pos > new_data.len() * 8 {
                None
            } else {
                let little = shr_mask(self.current_val, self.pos);
                self.data = new_data;
                self.current_val = self.read();
                let big = self.current_val << (bts - self.pos);
                Some(little + big)
            }
        } else {
            None
        }
    }

    #[inline]
    fn read_u64_unchecked(&mut self) -> u64 {
        // While reading 64bit we can take advantage of an optimization trick not available to
        // other reads as 64bits is the same as our cache size
        let bts = core::mem::size_of::<u64>() * 8;
        let little = shr_mask(self.current_val, self.pos);
        self.data = &self.data[BYTE_WIDTH..];
        self.current_val = self.read();
        let big = shl_mask(self.current_val, bts - self.pos);
        little + big
    }

    #[inline]
    fn read_bits_unchecked(&mut self, bits: i32) -> u32 {
        let bts = bits as usize;
        let new_pos = self.pos + bts;
        if new_pos <= BIT_WIDTH {
            let res = (self.current_val >> self.pos) & bit_mask(bts);
            self.pos = new_pos;
            res as u32
        } else {
            let little = shr_mask(self.current_val, self.pos);
            self.data = &self.data[BYTE_WIDTH..];
            self.current_val = self.read();
            let left = new_pos - BIT_WIDTH;
            let big = (self.current_val & bit_mask(left)) << (bts - left);
            self.pos = left;
            (little + big) as u32
        }
    }
}

impl<'a> BigEndianReader<'a> {
    /// Assuming that `self.data` is pointing to data not yet seen. slurp up 8 bytes or the
    /// rest of the data (whatever is smaller)
    ///
    /// Clippy lint can be unsuppressed once Clippy recognizes this pattern as correct.
    /// https://github.com/rust-lang/rust-clippy/issues/2881
    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    fn read(&mut self) -> u64 {
        unsafe {
            if self.data.len() >= BYTE_WIDTH {
                core::ptr::read_unaligned(self.data.as_ptr() as *const u8 as *const u64).to_be()
            } else {
                let mut result: u64 = 0;
                let len = self.data.len();
                self.end_pos = len * 8;
                core::ptr::copy_nonoverlapping(
                    self.data.as_ptr(),
                    &mut result as *mut u64 as *mut u8,
                    len,
                );
                result.to_be()
            }
        }
    }

    #[inline]
    fn read_u64(&mut self) -> Option<u64> {
        // While reading 64bit we can take advantage of an optimization trick not available to
        // other reads as 64bits is the same as our cache size
        if self.end_pos - self.pos == BIT_WIDTH {
            let ret = self.current_val;
            self.data = &self.data[BYTE_WIDTH..];
            self.current_val = self.read();
            Some(ret)
        } else if self.end_pos == BIT_WIDTH {
            let bts = core::mem::size_of::<u64>() * 8;
            let new_data = &self.data[BYTE_WIDTH..];
            if new_data.len() < BYTE_WIDTH && self.pos > new_data.len() * 8 {
                None
            } else {
                let big = shl_mask(self.current_val, self.pos);
                self.data = new_data;
                self.current_val = self.read();
                let little = self.current_val >> (bts - self.pos);
                Some(little + big)
            }
        } else {
            None
        }
    }

    #[inline]
    fn read_u64_unchecked(&mut self) -> u64 {
        // While reading 64bit we can take advantage of an optimization trick not available to
        // other reads as 64bits is the same as our cache size
        let big = shl_mask(self.current_val, self.pos);
        self.data = &self.data[BYTE_WIDTH..];
        self.current_val = self.read();
        let bts = core::mem::size_of::<u64>() * 8;
        let little = shr_mask(self.current_val, bts - self.pos);
        little + big
    }

    #[inline]
    fn read_bits(&mut self, bits: i32) -> Option<u32> {
        let bts = bits as usize;
        let new_pos = self.pos + bts;
        if new_pos <= self.end_pos {
            let res = (self.current_val >> (BIT_WIDTH - new_pos)) & bit_mask(bts);
            self.pos = new_pos;
            Some(res as u32)
        } else if self.end_pos == BIT_WIDTH {
            let new_data = &self.data[BYTE_WIDTH..];
            let left = new_pos - BIT_WIDTH;
            if new_data.len() < BYTE_WIDTH && left > new_data.len() * 8 {
                None
            } else {
                let mask = bit_mask(BIT_WIDTH - self.pos);
                let big = (self.current_val & mask) << left;
                self.data = new_data;
                self.current_val = self.read();
                let little = self.current_val >> (BIT_WIDTH - left);
                self.pos = left;
                Some((little + big) as u32)
            }
        } else {
            None
        }
    }

    #[inline]
    fn read_bits_unchecked(&mut self, bits: i32) -> u32 {
        let bts = bits as usize;
        let new_pos = self.pos + bts;
        if new_pos <= BIT_WIDTH {
            let res = (self.current_val >> (BIT_WIDTH - new_pos)) & bit_mask(bts);
            self.pos = new_pos;
            res as u32
        } else {
            let mask = bit_mask(BIT_WIDTH - self.pos);
            let left = new_pos - BIT_WIDTH;
            let big = (self.current_val & mask) << left;
            self.data = &self.data[BYTE_WIDTH..];
            self.current_val = self.read();
            let little = self.current_val >> (BIT_WIDTH - left);
            self.pos = left;
            (little + big) as u32
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{bit_width, BitReader, LittleEndianReader};

    #[test]
    fn test_bit_reads() {
        let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert_eq!(bitter.bits_remaining(), Some(16));
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.bits_remaining(), Some(15));
        assert_eq!(bitter.read_bit().unwrap(), true);
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.read_bit().unwrap(), true);
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.read_bit().unwrap(), true);
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.read_bit().unwrap(), true);

        assert_eq!(bitter.read_bit().unwrap(), true);
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.read_bit().unwrap(), true);
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.read_bit().unwrap(), true);
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.read_bit().unwrap(), true);
        assert_eq!(bitter.read_bit().unwrap(), false);

        assert_eq!(bitter.read_bit(), None);
    }

    #[test]
    fn test_bit_unchecked_reads() {
        let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert_eq!(bitter.read_bit_unchecked(), false);
        assert_eq!(bitter.read_bit_unchecked(), true);
        assert_eq!(bitter.read_bit_unchecked(), false);
        assert_eq!(bitter.read_bit_unchecked(), true);
        assert_eq!(bitter.read_bit_unchecked(), false);
        assert_eq!(bitter.read_bit_unchecked(), true);
        assert_eq!(bitter.read_bit_unchecked(), false);
        assert_eq!(bitter.read_bit_unchecked(), true);

        assert_eq!(bitter.read_bit_unchecked(), true);
        assert_eq!(bitter.read_bit_unchecked(), false);
        assert_eq!(bitter.read_bit_unchecked(), true);
        assert_eq!(bitter.read_bit_unchecked(), false);
        assert_eq!(bitter.read_bit_unchecked(), true);
        assert_eq!(bitter.read_bit_unchecked(), false);
        assert_eq!(bitter.read_bit_unchecked(), true);
        assert_eq!(bitter.read_bit_unchecked(), false);

        assert_eq!(bitter.read_bit(), None);
    }

    #[test]
    fn test_bit_unchecked_bits_reads() {
        let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);

        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);

        assert_eq!(bitter.read_bit(), None);
    }

    #[test]
    fn test_has_remaining_bits() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0xff]);
        assert!(bitter.has_bits_remaining(7));
        assert!(bitter.has_bits_remaining(8));
        assert!(bitter.has_bits_remaining(9));

        assert!(bitter.read_u32_bits(9).is_some());
        assert!(bitter.has_bits_remaining(7));
        assert!(!bitter.has_bits_remaining(8));
        assert!(!bitter.has_bits_remaining(9));

        assert!(bitter.read_u32_bits(7).is_some());
        assert!(!bitter.has_bits_remaining(7));
        assert!(bitter.has_bits_remaining(0));
    }

    #[test]
    fn test_has_remaining_bits2() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0xff, 0xff, 0xff]);
        assert!(bitter.read_u32_bits(31).is_some());
        assert!(!bitter.has_bits_remaining(2));
        assert!(bitter.has_bits_remaining(1));
    }

    #[test]
    fn test_has_remaining_bits_bit_by_bit() {
        let mut bitter = LittleEndianReader::new(&[0, 0, 0, 0, 0, 0, 0, 0]);
        for _ in 0..200 {
            assert!(bitter.has_bits_remaining(1), bitter.read_bit().is_some());
        }
    }

    #[test]
    fn test_16_bits_reads() {
        let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert_eq!(bitter.read_u32_bits(16), Some(0b0101_0101_1010_1010));
    }

    #[test]
    fn test_bit_bits_reads() {
        let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));

        assert_eq!(bitter.read_u32_bits(1), None);
    }

    #[test]
    fn test_read_bytes() {
        let mut buf = [0u8; 2];
        let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert!(bitter.read_bytes(&mut buf));
        assert_eq!(&buf, &[0b1010_1010, 0b0101_0101]);

        let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert_eq!(bitter.read_bit_unchecked(), false);
        assert!(!bitter.read_bytes(&mut buf));
        assert!(bitter.read_bytes(&mut buf[0..1]));
        assert_eq!(&buf[0..1], &[0b1101_0101]);
    }

    #[test]
    fn test_read_bytes2() {
        let mut bitter = LittleEndianReader::new(&[]);
        assert!(bitter.read_bytes(&mut []));
    }

    #[test]
    fn test_read_bytes3() {
        let mut bitter = LittleEndianReader::new(&[0, 0]);
        let mut buf = [0u8; 1];
        assert!(bitter.read_bytes(&mut buf));
        assert_eq!(&buf, &[0]);
    }

    #[test]
    fn test_read_bytes4() {
        let mut bitter = LittleEndianReader::new(&[0, 120]);
        let mut buf = [0u8; 1];
        assert!(bitter.read_bytes(&mut buf));
        assert_eq!(&buf, &[0]);
        assert_eq!(bitter.read_u8_unchecked(), 120);
    }

    #[test]
    fn test_read_bytes5() {
        let mut bitter = LittleEndianReader::new(&[119, 0, 120]);
        assert_eq!(bitter.read_u32_bits_unchecked(8), 119);
        let mut buf = [0u8; 1];
        assert!(bitter.read_bytes(&mut buf));
        assert_eq!(&buf, &[0]);
        assert_eq!(bitter.read_u32_bits_unchecked(8), 120);
    }

    #[test]
    fn test_u8_reads() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2]);
        assert_eq!(bitter.read_u8(), Some(0xff));
        assert_eq!(bitter.read_u8(), Some(0xfe));
        assert_eq!(bitter.read_u8(), Some(0xfa));
        assert_eq!(bitter.read_u8(), Some(0xf7));
        assert_eq!(bitter.read_u8(), Some(0xf5));
        assert_eq!(bitter.read_u8(), Some(0xf0));
        assert_eq!(bitter.read_u8(), Some(0xb1));
        assert_eq!(bitter.read_u8(), Some(0xb2));
        assert_eq!(bitter.read_u8(), None);
    }

    #[test]
    fn test_u8_unchecked_reads() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2]);
        assert_eq!(bitter.read_u8_unchecked(), 0xff);
        assert_eq!(bitter.read_u8_unchecked(), 0xfe);
        assert_eq!(bitter.read_u8_unchecked(), 0xfa);
        assert_eq!(bitter.read_u8_unchecked(), 0xf7);
        assert_eq!(bitter.read_u8_unchecked(), 0xf5);
        assert_eq!(bitter.read_u8_unchecked(), 0xf0);
        assert_eq!(bitter.read_u8_unchecked(), 0xb1);
        assert_eq!(bitter.read_u8_unchecked(), 0xb2);
        assert_eq!(bitter.read_u8(), None);
    }

    #[test]
    fn test_u64_reads() {
        let mut bitter = LittleEndianReader::new(&[
            0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2, 0x01, 0xff, 0xfe, 0xfa, 0xf7, 0xf5,
            0xf0, 0xb1, 0xb3,
        ]);
        assert_eq!(bitter.read_u64(), Some(0xb2b1_f0f5_f7fa_feff));
        assert_eq!(bitter.read_u8(), Some(0x01));
        assert_eq!(bitter.read_u64(), Some(0xb3b1_f0f5_f7fa_feff));
    }

    #[test]
    fn test_u64_unchecked_reads() {
        let mut bitter = LittleEndianReader::new(&[
            0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2, 0x01, 0xff, 0xfe, 0xfa, 0xf7, 0xf5,
            0xf0, 0xb1, 0xb3,
        ]);
        assert_eq!(bitter.read_u64_unchecked(), 0xb2b1_f0f5_f7fa_feff);
        assert_eq!(bitter.read_u8_unchecked(), 0x01);
        assert_eq!(bitter.read_u64_unchecked(), 0xb3b1_f0f5_f7fa_feff);
    }

    #[test]
    fn test_i64_unchecked_reads() {
        let mut bitter = LittleEndianReader::new(&[
            0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2, 0x01, 0xff, 0xfe, 0xfa, 0xf7, 0xf5,
            0xf0, 0xb1, 0xb3,
        ]);

        unsafe {
            assert_eq!(
                bitter.read_i64_unchecked(),
                core::mem::transmute::<u64, i64>(0xb2b1_f0f5_f7fa_feff)
            );
            assert_eq!(bitter.read_u8_unchecked(), 0x01);
            assert_eq!(
                bitter.read_i64_unchecked(),
                core::mem::transmute::<u64, i64>(0xb3b1_f0f5_f7fa_feff)
            );
        }
    }

    #[test]
    fn test_u32_bit_read() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
        assert_eq!(bitter.read_u32_bits(32), Some(0xcdab00ff));
    }

    #[test]
    fn test_u32_reads() {
        let mut bitter = LittleEndianReader::new(&[
            0xff,
            0x00,
            0xab,
            0xcd,
            0b1111_1110,
            0b0000_0001,
            0b0101_0110,
            0b1001_1011,
            0b0101_0101,
        ]);
        assert_eq!(bitter.read_u32(), Some(0xcdab00ff));
        assert_eq!(bitter.read_bit(), Some(false));
        assert_eq!(bitter.read_u32(), Some(0xcdab00ff));
        assert_eq!(bitter.read_bit(), Some(false));
        assert_eq!(bitter.read_u32(), None);
    }

    #[test]
    fn test_f32_reads() {
        let mut bitter = LittleEndianReader::new(&[
            0b0111_1011,
            0b0001_0100,
            0b1010_1110,
            0b0011_1101,
            0b1111_0110,
            0b0010_1000,
            0b0101_1100,
            0b0111_1011,
            0b0000_0010,
        ]);
        assert_eq!(bitter.read_f32(), Some(0.085));
        assert_eq!(bitter.read_bit(), Some(false));
        assert_eq!(bitter.read_f32(), Some(0.085));
    }

    #[test]
    fn test_f32_unchecked_reads() {
        let mut bitter = LittleEndianReader::new(&[
            0b0111_1011,
            0b0001_0100,
            0b1010_1110,
            0b0011_1101,
            0b1111_0110,
            0b0010_1000,
            0b0101_1100,
            0b0111_1011,
            0b0000_0010,
        ]);
        assert_eq!(bitter.read_f32_unchecked(), 0.085);
        assert_eq!(bitter.read_bit(), Some(false));
        assert_eq!(bitter.read_f32_unchecked(), 0.085);
    }

    #[test]
    fn test_u32_bits() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee]);
        assert_eq!(bitter.read_u32_bits(10), Some(0x1ff));
        assert_eq!(bitter.read_u32_bits(10), Some(0x3b7));
        assert_eq!(bitter.read_u32_bits(10), Some(0x3fe));
        assert_eq!(bitter.read_u32_bits(10), Some(0x377));
        assert_eq!(bitter.read_u32_bits(10), None);
    }

    #[test]
    fn test_u32_unchecked() {
        let mut bitter = LittleEndianReader::new(&[
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        ]);
        assert_eq!(bitter.read_u32_unchecked(), 0xffff_ffff);
        assert_eq!(bitter.read_u32_bits_unchecked(30), 0x3fff_ffff);
        assert_eq!(bitter.read_u32_unchecked(), 0xffff_ffff);
    }

    #[test]
    fn test_u32_bits_unchecked() {
        let mut bitter =
            LittleEndianReader::new(&[0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd]);
        assert_eq!(bitter.read_u32_bits_unchecked(10), 0x1ff);
        assert_eq!(bitter.read_u32_bits_unchecked(10), 0x3b7);
        assert_eq!(bitter.read_u32_bits_unchecked(10), 0x3fe);
        assert_eq!(bitter.read_u32_bits_unchecked(10), 0x377);
        assert_eq!(bitter.read_u32_bits_unchecked(8), 0xee);
        assert_eq!(bitter.read_u32_bits_unchecked(8), 0xaa);
        assert_eq!(bitter.read_u32_bits_unchecked(8), 0xbb);
        assert_eq!(bitter.read_u32_bits_unchecked(8), 0xcc);
        assert_eq!(bitter.read_u32_bits_unchecked(8), 0xdd);
        assert_eq!(bitter.read_bit(), None);
    }

    #[test]
    fn test_u32_bits_unchecked2() {
        let mut bitter = LittleEndianReader::new(&[
            0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
            0xe7,
        ]);
        for _ in 0..10 {
            assert_eq!(bitter.read_u32_bits_unchecked(5), 28);
        }
    }

    #[test]
    fn test_i32_bits_unchecked() {
        let mut bitter =
            LittleEndianReader::new(&[0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd]);
        assert_eq!(bitter.read_i32_bits_unchecked(10), 0x1ff);
        assert_eq!(bitter.read_i32_bits_unchecked(10), 0x3b7);
        assert_eq!(bitter.read_i32_bits_unchecked(10), 0x3fe);
        assert_eq!(bitter.read_i32_bits_unchecked(10), 0x377);
        assert_eq!(bitter.read_i32_bits_unchecked(8), 0xee);
        assert_eq!(bitter.read_i32_bits_unchecked(8), 0xaa);
        assert_eq!(bitter.read_i32_bits_unchecked(8), 0xbb);
        assert_eq!(bitter.read_i32_bits_unchecked(8), 0xcc);
        assert_eq!(bitter.read_i32_bits_unchecked(8), 0xdd);
        assert_eq!(bitter.read_bit(), None);
    }

    #[test]
    fn test_u32_bits2() {
        let mut bitter = LittleEndianReader::new(&[
            0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
            0xe7,
        ]);
        for _ in 0..10 {
            assert_eq!(bitter.read_u32_bits(5), Some(28));
        }
    }

    #[test]
    fn test_i32_bits2() {
        let mut bitter = LittleEndianReader::new(&[
            0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
            0xe7,
        ]);
        for _ in 0..10 {
            assert_eq!(bitter.read_i32_bits(5), Some(28));
        }
    }

    #[test]
    fn test_bit_width() {
        assert_eq!(0, bit_width(0));
        assert_eq!(1, bit_width(1));
        assert_eq!(2, bit_width(2));
        assert_eq!(2, bit_width(3));
        assert_eq!(3, bit_width(4));
        assert_eq!(5, bit_width(16));
        assert_eq!(5, bit_width(20));
        assert_eq!(32, bit_width(u32::max_value()));
    }

    #[test]
    fn test_max_read() {
        let mut bitter = LittleEndianReader::new(&[0b1111_1000]);
        assert_eq!(bitter.read_bits_max(20), Some(8));
        assert_eq!(bitter.read_bits_max(20), Some(15));
        assert_eq!(bitter.read_bits_max(20), None);

        let mut bitter = LittleEndianReader::new(&[0b1111_0000]);
        assert_eq!(bitter.read_bits_max(20), Some(16));
        assert_eq!(bitter.read_bits_max(20), None);

        let mut bitter = LittleEndianReader::new(&[0b1110_0010]);
        assert_eq!(bitter.read_bits_max(20), Some(2));

        let mut bitter = LittleEndianReader::new(&[0b0001_0100]);
        assert_eq!(bitter.read_bits_max(20), Some(4));

        let mut bitter = LittleEndianReader::new(&[0b0001_0011]);
        assert_eq!(bitter.read_bits_max(20), Some(19));

        let mut bitter = LittleEndianReader::new(&[0b0001_0011]);
        assert_eq!(bitter.read_bits_max(0), Some(0));

        let mut bitter = LittleEndianReader::new(&[0xff, 0xff, 0xff, 0xff]);
        assert_eq!(bitter.read_bits_max(u32::max_value()), Some(0x7fff_ffff));
    }

    #[test]
    fn test_max_read_computed() {
        let mut bitter = LittleEndianReader::new(&[0b1111_1000]);
        assert_eq!(bitter.read_bits_max_computed(4, 20), Some(8));
        assert_eq!(bitter.read_bits_max_computed(4, 20), Some(15));
        assert_eq!(bitter.read_bits_max_computed(4, 20), None);

        let mut bitter = LittleEndianReader::new(&[0b1111_0000]);
        assert_eq!(bitter.read_bits_max_computed(4, 20), Some(16));
        assert_eq!(bitter.read_bits_max_computed(4, 20), None);

        let mut bitter = LittleEndianReader::new(&[0b1110_0010]);
        assert_eq!(bitter.read_bits_max_computed(4, 20), Some(2));

        let mut bitter = LittleEndianReader::new(&[0b0001_0100]);
        assert_eq!(bitter.read_bits_max_computed(4, 20), Some(4));

        let mut bitter = LittleEndianReader::new(&[0b0001_0011]);
        assert_eq!(bitter.read_bits_max_computed(4, 20), Some(19));

        let mut bitter = LittleEndianReader::new(&[0b0001_0011]);
        assert_eq!(bitter.read_bits_max_computed(0, 00), Some(0));

        let mut bitter = LittleEndianReader::new(&[0xff, 0xff, 0xff, 0xff]);
        assert_eq!(
            bitter.read_bits_max_computed(31, u32::max_value()),
            Some(0x7fff_ffff)
        );
    }

    #[test]
    fn test_max_read_unchecked() {
        let mut bitter = LittleEndianReader::new(&[0b1111_1000]);
        assert_eq!(bitter.read_bits_max_unchecked(20), 8);
        assert_eq!(bitter.read_bits_max_unchecked(20), 15);

        let mut bitter = LittleEndianReader::new(&[0b1111_0000]);
        assert_eq!(bitter.read_bits_max_unchecked(20), 16);

        let mut bitter = LittleEndianReader::new(&[0b1110_0010]);
        assert_eq!(bitter.read_bits_max_unchecked(20), 2);

        let mut bitter = LittleEndianReader::new(&[0b0001_0100]);
        assert_eq!(bitter.read_bits_max_unchecked(20), 4);

        let mut bitter = LittleEndianReader::new(&[0b0001_0011]);
        assert_eq!(bitter.read_bits_max_unchecked(20), 19);

        let mut bitter = LittleEndianReader::new(&[0b0001_0011]);
        assert_eq!(bitter.read_bits_max_unchecked(0), 0);

        let mut bitter = LittleEndianReader::new(&[0xff, 0xff, 0xff, 0xff]);
        assert_eq!(
            bitter.read_bits_max_unchecked(u32::max_value()),
            0x7fff_ffff
        );
    }

    #[test]
    fn test_max_read_unchecked_computed() {
        let mut bitter = LittleEndianReader::new(&[0b1111_1000]);
        assert_eq!(bitter.read_bits_max_computed_unchecked(4, 20), 8);
        assert_eq!(bitter.read_bits_max_computed_unchecked(4, 20), 15);

        let mut bitter = LittleEndianReader::new(&[0b1111_0000]);
        assert_eq!(bitter.read_bits_max_computed_unchecked(4, 20), 16);

        let mut bitter = LittleEndianReader::new(&[0b1110_0010]);
        assert_eq!(bitter.read_bits_max_computed_unchecked(4, 20), 2);

        let mut bitter = LittleEndianReader::new(&[0b0001_0100]);
        assert_eq!(bitter.read_bits_max_computed_unchecked(4, 20), 4);

        let mut bitter = LittleEndianReader::new(&[0b0001_0011]);
        assert_eq!(bitter.read_bits_max_computed_unchecked(4, 20), 19);

        let mut bitter = LittleEndianReader::new(&[0b0001_0011]);
        assert_eq!(bitter.read_bits_max_computed_unchecked(0, 0), 0);

        let mut bitter = LittleEndianReader::new(&[0xff, 0xff, 0xff, 0xff]);
        assert_eq!(
            bitter.read_bits_max_computed_unchecked(31, u32::max_value()),
            0x7fff_ffff
        );
    }

    #[test]
    fn test_if_get() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
        assert_eq!(bitter.if_get(LittleEndianReader::read_u8), Some(Some(0x7f)));
        assert_eq!(bitter.if_get(LittleEndianReader::read_u8), Some(None));
        assert_eq!(bitter.if_get(LittleEndianReader::read_u8), None);
    }

    #[test]
    fn test_if_get_unchecked() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
        assert_eq!(
            bitter.if_get_unchecked(LittleEndianReader::read_u8_unchecked),
            Some(0x7f)
        );
        assert_eq!(
            bitter.if_get_unchecked(LittleEndianReader::read_u8_unchecked),
            None
        );
    }

    #[test]
    fn test_approx_bytes_and_empty() {
        let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
        assert!(!bitter.is_empty());
        assert_eq!(bitter.approx_bytes_remaining(), 2);
        assert!(bitter.read_bit().is_some());
        assert!(!bitter.is_empty());
        assert_eq!(bitter.approx_bytes_remaining(), 2);
        assert!(bitter.read_u32_bits(6).is_some());
        assert!(!bitter.is_empty());
        assert_eq!(bitter.approx_bytes_remaining(), 2);
        assert!(bitter.read_bit().is_some());
        assert!(!bitter.is_empty());
        assert_eq!(bitter.approx_bytes_remaining(), 1);
        assert!(bitter.read_bit().is_some());
        assert!(!bitter.is_empty());
        assert_eq!(bitter.approx_bytes_remaining(), 1);
        assert!(bitter.read_u32_bits(7).is_some());
        assert!(bitter.is_empty());
        assert_eq!(bitter.approx_bytes_remaining(), 0);
    }

    #[test]
    fn has_bits_remaining_max() {
        let data = vec![];
        let bits = LittleEndianReader::new(data.as_slice());
        assert_eq!(false, bits.has_bits_remaining(usize::max_value()));
    }

    #[test]
    fn i16_test() {
        let data = [0b1111_1111, 0b1111_1111];
        let mut bits = LittleEndianReader::new(&data[..]);

        assert_eq!(bits.read_i16(), Some(i16::from_le_bytes(data)));
    }

    #[test]
    fn i16_min_test() {
        let data = [0b0000_0000, 0b1000_0000];
        let mut bits = LittleEndianReader::new(&data[..]);

        assert_eq!(bits.read_i16(), Some(core::i16::MIN));
    }

    #[test]
    fn i16_max_test() {
        let data = [0b1111_1111, 0b0111_1111];
        let mut bits = LittleEndianReader::new(&data[..]);

        assert_eq!(bits.read_i16(), Some(core::i16::MAX));
    }

    #[test]
    fn back_to_back_le_u64() {
        let mut data = Vec::new();
        data.extend_from_slice(&(1u64.to_le_bytes()));
        data.extend_from_slice(&(0u64.to_le_bytes()));
        let mut bits = LittleEndianReader::new(data.as_slice());
        assert_eq!(bits.read_u64(), Some(1));
        assert_eq!(bits.read_u64(), Some(0));
    }

    #[test]
    fn pushed_le_u64() {
        let mut data = Vec::new();
        data.extend_from_slice(&(0u64.to_le_bytes()));
        data.extend_from_slice(&(1u64.to_le_bytes()));
        let mut bits = LittleEndianReader::new(data.as_slice());
        for _ in 0..8 {
            assert_eq!(bits.read_u8(), Some(0));
        }
        assert_eq!(bits.read_u64(), Some(1));
    }

    #[test]
    fn pushed_le_unchecked_u64() {
        let mut data = Vec::new();
        data.extend_from_slice(&(0u64.to_le_bytes()));
        data.extend_from_slice(&(1u64.to_le_bytes()));
        let mut bits = LittleEndianReader::new(data.as_slice());
        for _ in 0..8 {
            assert_eq!(bits.read_u8_unchecked(), 0);
        }
        assert_eq!(bits.read_u64_unchecked(), 1);
    }

    #[test]
    fn regression1() {
        let data = vec![0b0000_0010, 0b0011_1111, 0b1011_1100];
        let mut bits = LittleEndianReader::new(data.as_slice());

        assert_eq!(bits.read_u32_bits(3), Some(2));
        assert_eq!(bits.read_u8(), Some(224));
        assert_eq!(bits.read_bit(), Some(true));
        assert_eq!(bits.read_u32_bits(13), None);
    }

    #[test]
    fn regression2() {
        let data = vec![2, 63, 63, 2, 63, 2, 0, 0, 0];
        let mut bits = LittleEndianReader::new(data.as_slice());

        assert_eq!(bits.read_u32_bits(3), Some(2));
        assert_eq!(bits.read_u8(), Some(224));
        assert_eq!(bits.read_u64(), None);
    }
}

#[cfg(test)]
mod be_tests {
    use super::{BigEndianReader, BitReader};

    #[test]
    fn test_be_bit_bits_reads() {
        let mut bitter = BigEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert!(bitter.has_bits_remaining(16));
        assert_eq!(bitter.bits_remaining(), Some(16));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert!(!bitter.has_bits_remaining(16));
        assert_eq!(bitter.bits_remaining(), Some(15));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));
        assert_eq!(bitter.read_u32_bits(1), Some(0));
        assert_eq!(bitter.read_u32_bits(1), Some(1));

        assert_eq!(bitter.read_u32_bits(1), None);
    }

    #[test]
    fn test_whole_bytes() {
        let mut bitter = BigEndianReader::new(&[
            0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd, 0xff, 0xdd, 0xee, 0xff,
            0xdd,
        ]);
        assert_eq!(bitter.read_u8(), Some(0xff));
        assert_eq!(bitter.read_u16(), Some(u16::from_be_bytes([0xdd, 0xee])));
        assert_eq!(
            bitter.read_u64(),
            Some(u64::from_be_bytes([
                0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd, 0xff
            ]))
        );
        assert_eq!(
            bitter.read_u32(),
            Some(u32::from_be_bytes([0xdd, 0xee, 0xff, 0xdd]))
        );
    }

    #[test]
    fn test_u32_bits() {
        let mut bitter =
            BigEndianReader::new(&[0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd]);
        assert_eq!(bitter.read_u32_bits(10), Some(0b11_1111_1111));
        assert_eq!(bitter.read_u32_bits(10), Some(0b01_1101_1110));
        assert_eq!(bitter.read_u32_bits(10), Some(0b11_1011_1111));
        assert_eq!(bitter.read_u32_bits(10), Some(0b11_1101_1101));
        assert_eq!(bitter.read_u32_bits(8), Some(0xee));
        assert_eq!(bitter.read_u32_bits(8), Some(0xaa));
        assert_eq!(bitter.read_u32_bits(8), Some(0xbb));
        assert_eq!(bitter.read_u32_bits(8), Some(0xcc));
        assert_eq!(bitter.read_u32_bits(8), Some(0xdd));
        assert_eq!(bitter.read_bit(), None);
    }

    #[test]
    fn test_u32_bits2() {
        let mut bitter = BigEndianReader::new(&[
            0b1110_0111,
            0b0011_1001,
            0b1100_1110,
            0b0111_0011,
            0b1001_1100,
            0b1110_0111,
            0b0011_1001,
            0b1100_1110,
            0b0111_0011,
            0b1001_1100,
        ]);
        for _ in 0..16 {
            assert_eq!(bitter.read_u32_bits(5), Some(28));
        }
    }

    #[test]
    fn test_bit_unchecked_bits_reads() {
        let mut bitter = BigEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 0);
        assert_eq!(bitter.read_u32_bits_unchecked(1), 1);

        assert_eq!(bitter.read_bit(), None);
    }

    #[test]
    fn test_u64_unchecked_reads() {
        let mut bitter = BigEndianReader::new(&[
            0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2, 0x01, 0xff, 0xfe, 0xfa, 0xf7, 0xf5,
            0xf0, 0xb1, 0xb3,
        ]);
        assert_eq!(
            bitter.read_u64_unchecked(),
            u64::from_be_bytes([0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2])
        );
        assert_eq!(bitter.read_u8_unchecked(), 0x01);
        assert_eq!(
            bitter.read_u64_unchecked(),
            u64::from_be_bytes([0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb3])
        );
    }

    #[test]
    fn test_u32_bit_read() {
        let mut bitter = BigEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
        assert_eq!(bitter.read_u32_bits(32), Some(0xff00abcd));
    }

    #[test]
    fn back_to_back_be_u64() {
        let mut data = Vec::new();
        data.extend_from_slice(&(0u64.to_be_bytes()));
        data.extend_from_slice(&(1u64.to_be_bytes()));
        let mut bits = BigEndianReader::new(data.as_slice());
        assert_eq!(bits.read_u64(), Some(0));
        assert_eq!(bits.read_u64(), Some(1));
    }

    #[test]
    fn back_to_back_be_u64_2() {
        let mut data = Vec::new();
        data.extend_from_slice(&(1u64.to_be_bytes()));
        data.extend_from_slice(&(0u64.to_be_bytes()));
        let mut bits = BigEndianReader::new(data.as_slice());
        assert_eq!(bits.read_u64(), Some(1));
        assert_eq!(bits.read_u64(), Some(0));
    }

    #[test]
    fn pushed_be_u64() {
        let mut data = Vec::new();
        data.extend_from_slice(&(0u64.to_be_bytes()));
        data.extend_from_slice(&(1u64.to_be_bytes()));
        let mut bits = BigEndianReader::new(data.as_slice());
        for _ in 0..8 {
            assert_eq!(bits.read_u8(), Some(0));
        }
        assert_eq!(bits.read_u64(), Some(1));
    }

    #[test]
    fn back_to_back_be_unchecked_u64() {
        let mut data = Vec::new();
        data.extend_from_slice(&(0u64.to_be_bytes()));
        data.extend_from_slice(&(1u64.to_be_bytes()));
        let mut bits = BigEndianReader::new(data.as_slice());
        assert_eq!(bits.read_u64_unchecked(), 0);
        assert_eq!(bits.read_u64_unchecked(), 1);
    }

    #[test]
    fn back_to_back_be_unchecked_u64_2() {
        let mut data = Vec::new();
        data.extend_from_slice(&(1u64.to_be_bytes()));
        data.extend_from_slice(&(0u64.to_be_bytes()));
        let mut bits = BigEndianReader::new(data.as_slice());
        assert_eq!(bits.read_u64_unchecked(), 1);
        assert_eq!(bits.read_u64_unchecked(), 0);
    }
}
