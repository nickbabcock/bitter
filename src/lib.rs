/*!

***Reading bits until the bitter end***

Bitter reads bits in a desired endian format platform agnostically. Performance is the distinguishing feature compared to other bit readers. See [benchmarks](https://github.com/nickbabcock/bitter#comparison-to-other-libraries) for more information.

## Features

 - ✔ support for little endian, big endian, and native endian formats
 - ✔ request an arbitrary amount of bits (up to 56 bits)
 - ✔ ergonomic requests for common data types (eg: `u8` ... `u32`, `f32`, etc)
 - ✔ throughput exceeds 2 GiB/s for small reads (< 10 bits) and 10 GiB/s for larger reads
 - ✔ zero allocations
 - ✔ zero dependencies
 - ✔ `no_std` compatible

## Example

The example below gives a good demonstration of the main API surface area to decode a 16 bit data model. It strikes a good balance between ergonomics and speed.

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bits = LittleEndianReader::new(&[0xff, 0x04]);
assert_eq!(bits.bytes_remaining(), 2);
assert_eq!(bits.read_bit(), Some(true));
assert_eq!(bits.bytes_remaining(), 1);
assert_eq!(bits.read_u8(), Some(0x7f));
assert!(bits.has_bits_remaining(7));
assert_eq!(bits.read_bits(7), Some(0x02));
```

However, one can unlock additional performance by amortizing internal state logic management when exploiting patterns in the encoded data. Colloquially known as Manual Mode, our example from before can be rewritten to take advantage of our domain knowledge that we'll be decoding 16 bits.

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bits = LittleEndianReader::new(&[0xff, 0x04]);

// Always start manual management with a refill, which
// will return the number of bits buffered
let len = bits.refill_lookahead();

// We need at least 16 bits buffered
assert!(len >= 16);

// We use a combination of peek and consume instead of read_*
assert_eq!(bits.peek(1), 1);
bits.consume(1);

// Notice how the return type is not an `Option`
assert_eq!(bits.peek(8), 0x7f);
bits.consume(8);

// We can switch back to auto mode any time
assert!(bits.has_bits_remaining(7));
assert_eq!(bits.read_bits(7), Some(0x02));
```

The refill, peek, and consume combination are the building blocks for Manual Mode, and allows fine grain management for hot loops. The surface area of Manual Mode APIs is purposely compact to keep things simple. The "Auto Mode" API (the functions with `read_` prefix) is larger as that API should be the one reaches for first

Manual mode can be intimidating, but it's one of if not the fastest way to decode a bit stream, as it's based on variant 4 from [Fabian Giesen's excellent series on reading bits](https://fgiesen.wordpress.com/2018/02/20/reading-bits-in-far-too-many-ways-part-2/). Others have employed this underlying technique to [significantly speed up DEFLATE](https://dougallj.wordpress.com/2022/08/20/faster-zlib-deflate-decompression-on-the-apple-m1-and-x86/).

Still, the limitation of a bit reading library only able to read up to 56 bits seems arbitrary and limiting. This can be mitigated through a couple measures. The first is to use a static assertion so we know refilling the lookahead buffer can yield sufficient data if available.

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bits = LittleEndianReader::new(&[0xff, 0x04]);

const _: () = assert!(
    bitter::MAX_READ_BITS >= 16,
    "lookahead bit buffer not large enough for our data"
);

let len = bits.refill_lookahead();
if len < 16 {
    panic!("Early EOF");
}

// ... peek & consume ...
```

The read size limitation can be eliminated by emulating larger reads. For instance, decoding a 128 bit number:

```rust
use bitter::{BitReader, LittleEndianReader};

let value: i128 = 0x12345678901234567890123456789012;
let data = value.to_le_bytes();
let mut bits = LittleEndianReader::new(&data);
let mut out = [0u8; core::mem::size_of::<i128>()];
assert!(bits.read_bytes(&mut out));
assert_eq!(i128::from_le_bytes(out), value);
```

Or one can break it down into manageable chunks:

```rust
use bitter::{BitReader, LittleEndianReader};

let data: [u8; 8] = [0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89];
let bits_to_read = 60u32;
let value: u64 = 0x123456789;
let mut bits = LittleEndianReader::new(&data);
assert!(bits.has_bits_remaining(bits_to_read as usize));
assert!(bits.refill_lookahead() >= bitter::MAX_READ_BITS);

let lo = bits.peek(bitter::MAX_READ_BITS);
bits.consume(bitter::MAX_READ_BITS);

let hi_bits = bits_to_read - bitter::MAX_READ_BITS;
assert!(bits.refill_lookahead() >= hi_bits);

let hi = bits.peek(hi_bits);
bits.consume(hi_bits);

let mut expected = [0u8; 8];
expected.copy_from_slice(&data);
expected[7] = 0x09;

assert_eq!((hi << bitter::MAX_READ_BITS) + lo, u64::from_le_bytes(expected));
```

There's one final trick that bitter exposes that dials performance to 11 at the cost of safety and increased assumptions. Welcome to the unchecked refill API (referred to as "unchecked"), which can only be called when there are at least 8 bytes left in the buffer. Anything less than that can cause invalid memory access. The upside is that this API unlocks the holy grail of branchless bit reading.

Always consider guarding unchecked access at a higher level:

```rust
use bitter::{BitReader, LittleEndianReader};

let mut bits = LittleEndianReader::new(&[0u8; 100]);
let objects_to_read = 10;
let object_bits = 56;
let bitter_padding = 64;

// make sure we have enough data to read all our objects and there is enough
// data leftover so bitter can unalign read 8 bytes without fear of reading past
// the end of the buffer.
if bits.has_bits_remaining(objects_to_read * object_bits + bitter_padding) {
    for _ in 0..objects_to_read {
        unsafe { bits.refill_lookahead_unchecked() };
        let _field1 = bits.peek(2);
        bits.consume(2);

        let _field2 = bits.peek(18);
        bits.consume(18);

        let _field3 = bits.peek(18);
        bits.consume(18);

        let _field4 = bits.peek(18);
        bits.consume(18);
    }
}
```

All three modes: auto, manual, and unchecked can be mixed and matched as desired.

### `no_std` crates

This crate has a feature, `std`, that is enabled by default. To use this crate
in a `no_std` context, add the following to your `Cargo.toml`:

```toml
[dependencies]
bits = { version = "x", default-features = false }
```

*/

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]

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

    /// Consume 32 bits and return the deserialized floating point
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = 12.5f32.to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_f32(), Some(12.5f32));
    /// ```
    fn read_f32(&mut self) -> Option<f32>;

    /// Reads an arbitrary number of bits from 1 to 56 (inclusive)
    /// and returns the unsigned result
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bits = BigEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
    /// assert_eq!(bits.read_bits(32), Some(0xff00abcd));
    /// ```
    fn read_bits(&mut self, bits: u32) -> Option<u64>;

    /// Reads an arbitrary number of bits from 1 to 56 (inclusive)
    /// and returns the signed result. If the most significant bit
    /// is enabled, the result will be negative. This can be somewhat
    /// counterintuitive so see the examples
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bits = BigEndianReader::new(&[0xfa, 0x93]);
    /// assert_eq!(bits.read_signed_bits(4), Some(-1));
    /// assert_eq!(bits.read_signed_bits(4), Some(-6));
    /// assert_eq!(bits.read_signed_bits(4), Some(-7));
    /// assert_eq!(bits.read_signed_bits(4), Some(3));
    /// ```
    ///
    /// To think of it another way, reading the number of bits equivalent
    /// to a builtin type (i8, i16, etc), will always equal its associated
    /// ergonomic equivalent when casted.
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bits = BigEndianReader::new(&[0xff]);
    /// let mut bitter2 = BigEndianReader::new(&[0xff]);
    /// assert_eq!(
    ///     bits.read_signed_bits(8).map(|x| x as i8),
    ///     bitter2.read_i8()
    /// );
    /// ```
    fn read_signed_bits(&mut self, bits: u32) -> Option<i64>;

    /// Returns how many complete bytes are left in the bitstream.
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bits = LittleEndianReader::new(&[0xff]);
    /// assert_eq!(bits.bytes_remaining(), 1);
    /// assert!(bits.read_bit().is_some());
    /// assert_eq!(bits.bytes_remaining(), 0);
    /// assert!(bits.read_bits(7).is_some());
    /// assert_eq!(bits.bytes_remaining(), 0);
    /// ```
    fn bytes_remaining(&self) -> usize;

    /// Returns the exact number of bits remaining in the bitstream if the
    /// number of bits can fit within a `usize`. For large byte slices,
    /// calculating the number of bits can cause an overflow, hence an `Option`
    /// is returned. See [`has_bits_remaining`](BitReader::has_bits_remaining)
    /// for a more robust, performant, and ergonomic alternative.
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bits = LittleEndianReader::new(&[0xff]);
    /// assert_eq!(bits.bits_remaining(), Some(8));
    /// assert!(bits.read_bit().is_some());
    /// assert_eq!(bits.bits_remaining(), Some(7));
    /// assert!(bits.read_bits(7).is_some());
    /// assert_eq!(bits.bits_remaining(), Some(0));
    /// ```
    fn bits_remaining(&self) -> Option<usize>;

    /// Returns true if at least `bits` number of bits are left in the stream. A
    /// more robust, performant, and ergonomic way than
    /// [`bits_remaining`](BitReader::bits_remaining).
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bits = LittleEndianReader::new(&[0xff]);
    /// assert!(bits.has_bits_remaining(7));
    /// assert!(bits.has_bits_remaining(8));
    /// assert!(!bits.has_bits_remaining(9));
    ///
    /// assert!(bits.read_bit().is_some());
    /// assert!(bits.has_bits_remaining(7));
    /// assert!(!bits.has_bits_remaining(8));
    ///
    /// assert!(bits.read_bits(7).is_some());
    /// assert!(!bits.has_bits_remaining(7));
    /// assert!(bits.has_bits_remaining(0));
    /// ```
    fn has_bits_remaining(&self, bits: usize) -> bool;

    /// Read the number of bytes needed to fill the provided buffer. Returns whether
    /// the read was successful and the buffer has been filled. If there aren't enough
    /// bytes remaining, then the bit stream and buffer remains unchanged
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bits = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
    /// let mut buf = [0; 1];
    /// assert_eq!(bits.read_bit(), Some(false));
    /// assert!(bits.read_bytes(&mut buf));
    /// assert_eq!(&buf, &[0b1101_0101]);
    /// assert!(!bits.read_bytes(&mut buf));
    /// assert_eq!(bits.read_bits(1), Some(0));
    /// ```
    fn read_bytes(&mut self, buf: &mut [u8]) -> bool;

    /// Returns if the bitstream has no bits left
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bits = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
    /// assert_eq!(bits.is_empty(), false);
    /// assert_eq!(bits.read_u16(), Some(0b0101_0101_1010_1010));
    /// assert_eq!(bits.is_empty(), true);
    /// ```    
    fn is_empty(&self) -> bool;

    /// Peeks at the given number of bits in the lookahead buffer
    ///
    /// It is invalid to peek at more than what was returned in the
    /// last [refill](BitReader::refill_lookahead)
    ///
    /// A core tenent of Manual Mode: refill / peek / consume
    fn peek(&self, count: u32) -> u64;

    /// Consumes the number of bits from the lookahead buffer
    ///
    /// A core tenent of Manual Mode: refill / peek / consume
    ///
    /// # Safety
    ///
    /// This operation itself is always safe, but consuming more than what is
    /// available will cause a debug assertion to be tripped and undefined
    /// behavior in release mode.
    fn consume(&mut self, count: u32);

    /// Refills the lookahead buffer and returns the number of bits available to
    /// consume.
    ///
    /// The return value will be less than [`MAX_READ_BITS`](crate::MAX_READ_BITS)
    ///
    /// A core tenent of Manual Mode: refill / peek / consume
    fn refill_lookahead(&mut self) -> u32;

    /// Refills the buffer without bounds checking
    ///
    /// Guard any usage with
    /// [`has_bits_remaining`](BitReader::has_bits_remaining)
    ///
    /// There is no return value as it would always be
    /// [`MAX_READ_BITS`](crate::MAX_READ_BITS)
    ///
    /// # Safety
    ///
    /// This function assumes that there are at least 8 bytes left in the data
    /// for an unaligned read. If there are less than that, there is a risk of
    unsafe fn refill_lookahead_unchecked(&mut self);

    /// Returns true if the reader is not partway through a byte
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bits = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
    /// let mut buf = [0; 1];
    /// assert!(bits.byte_aligned());
    /// assert_eq!(bits.read_bit(), Some(false));
    /// assert!(!bits.byte_aligned());
    /// ```
    fn byte_aligned(&self) -> bool;
}

#[inline]
fn bit_mask(bits: usize) -> u64 {
    let mask = u64::MAX;
    let size = core::mem::size_of::<u64>() * 8;
    mask >> (size - bits)
}

const BYTE_WIDTH: usize = core::mem::size_of::<u64>();
const BIT_WIDTH: usize = BYTE_WIDTH * 8;

/// The maximum number of bits available to buffer
///
/// [BitReader::refill_lookahead](BitReader::refill_lookahead) returns a maximum equal to this constant.
///
/// Use static assertions to ensure that your data model fits within expected number of refills
///
/// ```rust
/// const _: () = assert!(
///     bitter::MAX_READ_BITS >= 56,
///     "unexpected lookahead buffer size"
/// );
/// ```
///
/// If your data model doesn't fit, use multiple refills to emulate support.
pub const MAX_READ_BITS: u32 = 56;

macro_rules! gen_read {
    ($name:ident, $t:ty) => {
        #[inline]
        fn $name(&mut self) -> Option<$t> {
            let bits = (core::mem::size_of::<$t>() * 8);
            self.read_bits(bits as u32).map(|x| x as $t)
        }
    };
}

macro_rules! base_reader {
    ($which:ident) => {
        #[inline]
        unsafe fn read(&mut self) -> u64 {
            core::ptr::read_unaligned(self.bit_ptr as *const u64).$which()
        }

        #[inline]
        fn unbuffered_bytes(&self) -> usize {
            (self.end_ptr as usize) - (self.bit_ptr as usize)
        }
    };
}

macro_rules! base_bit_reader {
    ($name:ident) => {
        gen_read!(read_u8, u8);
        gen_read!(read_i8, i8);
        gen_read!(read_u16, u16);
        gen_read!(read_i16, i16);
        gen_read!(read_u32, u32);
        gen_read!(read_i32, i32);

        #[inline]
        unsafe fn refill_lookahead_unchecked(&mut self) {
            self.refill();
        }

        #[inline]
        fn read_bit(&mut self) -> Option<bool> {
            self.read_bits(1).map(|x| x == 1)
        }

        #[inline]
        fn read_signed_bits(&mut self, bits: u32) -> Option<i64> {
            let bts = bits as usize;
            self.read_bits(bits).map(|x| {
                if x.leading_zeros() == (BIT_WIDTH - bts) as u32 {
                    (x as i64) - (bit_mask(bts) + 1) as i64
                } else {
                    x as i64
                }
            })
        }

        #[inline]
        fn read_f32(&mut self) -> Option<f32> {
            self.read_u32().map(f32::from_bits)
        }

        #[inline]
        fn read_bytes(&mut self, buf: &mut [u8]) -> bool {
            let lookahead_bytes = (self.bit_count >> 3) as usize;
            let unbuffed = self.unbuffered_bytes();
            if unbuffed + lookahead_bytes < buf.len() {
                return false;
            }

            if self.byte_aligned() {
                let lookahead_consumption = lookahead_bytes.min(buf.len());
                let (head, tail) = buf.split_at_mut(lookahead_consumption);
                for dst in head.iter_mut() {
                    *dst = self.peek(8) as u8;
                    self.consume(8);
                }

                // One isn't supposed to consume all of `bit_count`, that's
                // why we limit the max reads to 56 bits, but since we may
                // have just consumed the entire lookahead, we reset some
                // internal state.
                if lookahead_consumption == lookahead_bytes {
                    self.bit_buf = 0;
                }

                let data = unsafe { core::slice::from_raw_parts(self.bit_ptr, unbuffed) };
                let (data_head, data_tail) = data.split_at(tail.len());
                tail.copy_from_slice(data_head);
                self.bit_ptr = data_tail.as_ptr();
                self.refill_lookahead();
            } else {
                let mut len = self.refill_lookahead();
                for dst in buf.iter_mut() {
                    if len == 0 {
                        len = self.refill_lookahead();
                        debug_assert!(len != 0, "we should have checked we had enough data");
                    }

                    *dst = self.peek(8) as u8;
                    self.consume(8);
                    len -= 8;
                }
            }

            true
        }

        #[inline]
        fn peek(&self, count: u32) -> u64 {
            debug_assert!(count > 0, "peeked zero bits");
            debug_assert!(
                count <= MAX_READ_BITS && count <= self.bit_count,
                "peeking too much data"
            );
            $name::peek_(self, count)
        }

        #[inline]
        fn consume(&mut self, count: u32) {
            debug_assert!(
                count <= MAX_READ_BITS && count <= self.bit_count,
                "consumed too much data"
            );
            $name::consume_(self, count);
            self.bit_count -= count;
        }

        #[inline]
        fn bytes_remaining(&self) -> usize {
            self.unbuffered_bytes() + (self.bit_count >> 3) as usize
        }

        #[inline]
        fn bits_remaining(&self) -> Option<usize> {
            self.unbuffered_bytes()
                .checked_mul(8)
                .map(|x| x + self.bit_count as usize)
        }

        #[inline]
        fn has_bits_remaining(&self, bits: usize) -> bool {
            let bytes = self.unbuffered_bytes();
            bytes >= bits || (bytes * 8 + (self.bit_count) as usize) >= bits
        }

        #[inline]
        fn is_empty(&self) -> bool {
            !self.has_bits_remaining(1)
        }

        #[inline]
        fn byte_aligned(&self) -> bool {
            self.bit_count % 8 == 0
        }
    };
}

macro_rules! generate_bitter_end {
    ($(#[$meta:meta])* $name:ident, $which:ident, $shift:tt) => {
        $(#[$meta])*
        pub struct $name<'a> {
            /// Current lookahead buffer contents
            bit_buf: u64,

            /// Pointer of next byte for lookahead
            bit_ptr: *const u8,

            /// One past the last element of the given data
            end_ptr: *const u8,

            /// Pointer to the element that marks it as no longer safe for blind
            /// unaligned reads
            input_marker: *const u8,

            /// Number of bits in buffer
            bit_count: u32,

            phantom: ::core::marker::PhantomData<&'a [u8]>,
        }

        impl<'a> $name<'a> {
            #[inline]
            pub fn new(data: &'a [u8]) -> Self {
                let input_marker = data.len().saturating_sub(7);
                let rng = data.as_ptr_range();

                Self {
                    bit_ptr: rng.start,
                    end_ptr: rng.end,
                    input_marker: data[input_marker..].as_ptr(),
                    bit_buf: 0,
                    bit_count: 0,
                    phantom: ::core::marker::PhantomData,
                }
            }

            base_reader!($which);

            #[inline]
            unsafe fn refill(&mut self) {
                self.bit_buf |= self.read() $shift self.bit_count;

                // Splitting up the bit_ptr adjustment yields a 10% throughput
                // improvement. Adapted from zlib-dougallj:
                // https://github.com/dougallj/zlib-dougallj/blob/315b6636bfca5797f7e7d037e29c5edd2c605e70/inffast_chunk.c#L156
                self.bit_ptr = self.bit_ptr.add(7);
                self.bit_ptr = self.bit_ptr.sub((self.bit_count as usize >> 3) & 7);

                self.bit_count |= MAX_READ_BITS;
            }

            #[inline]
            fn refill_eof(&mut self) {
                self.bit_buf |= unsafe { self.read_eof() } $shift self.bit_count;

                let left = self.unbuffered_bytes();
                let consumed = ((63 - (self.bit_count) as usize) >> 3).min(left);
                self.bit_ptr = unsafe { self.bit_ptr.add(consumed) };

                if self.unbuffered_bytes() > 0 {
                    self.bit_count |= MAX_READ_BITS;
                } else {
                    self.bit_count += (consumed * 8) as u32;
                }
            }

            #[inline]
            unsafe fn read_eof(&mut self) -> u64 {
                let mut result: u64 = 0;
                let len = self.unbuffered_bytes();
                core::ptr::copy_nonoverlapping(self.bit_ptr, &mut result as *mut u64 as *mut u8, len);
                result.$which()
            }

            // End of buffer checking is a fascinating topic, see:
            // https://fgiesen.wordpress.com/2016/01/02/end-of-buffer-checks-in-decompressors/
            //
            // We use the so declared "boring" method of using a marker to know when
            // we can't blindly unalign read 64 bits, and duplicate some behavior.
            #[inline]
            fn has_data_for_unaligned_loads(&self) -> bool {
                self.bit_ptr < self.input_marker
            }

            #[inline]
            fn refill_bits_eof(&mut self) -> u32 {
                self.refill_eof();
                self.bit_count.min(MAX_READ_BITS)
            }

            #[inline]
            fn read_bits_eof(&mut self, count: u32) -> Option<u64> {
                if !self.has_bits_remaining(count as usize) {
                    return None;
                }

                if count > self.bit_count {
                    self.refill_eof();
                }

                let result = self.peek(count);
                self.consume(count);
                Some(result)
            }
        }

        impl<'a> BitReader for $name<'a> {
            base_bit_reader!($name);

            #[inline]
            fn read_bits(&mut self, count: u32) -> Option<u64> {
                if self.has_data_for_unaligned_loads() {
                    // This branch to check if a refill is necessary is a little
                    // controversial, as this branch doesn't exist on variant 4
                    // (and Fabien stresses branchless lookahead several times),
                    // but I've found that including this branch on the real
                    // world benchmarks yields 30-50% throughput increase. This
                    // is could be hardware dependent, but if a use case is was
                    // negatively affected by this decision, it is probably
                    // better off using the manual method anyways.
                    if count > self.bit_count {
                        unsafe { self.refill(); }
                    }

                    let result = self.peek(count);
                    self.consume(count);
                    Some(result)
                } else {
                    self.read_bits_eof(count)
                }
            }

            /// Refills the lookahead buffer and returns the number of bits available to
            /// consume.
            #[inline]
            fn refill_lookahead(&mut self) -> u32 {
                if self.has_data_for_unaligned_loads() {
                    unsafe { self.refill() }
                    MAX_READ_BITS
                } else {
                    self.refill_bits_eof()
                }
            }
        }
    }
}

generate_bitter_end!(
    /// Reads bits in the little-endian format
    ///
    /// ```rust
    /// use bitter::{BitReader, LittleEndianReader};
    /// let mut lebits = LittleEndianReader::new(&[0b0000_0001]);
    /// assert_eq!(lebits.read_bit(), Some(true));
    /// ```
    LittleEndianReader,
    to_le,
    <<
);

impl<'a> LittleEndianReader<'a> {
    #[inline]
    fn peek_(&self, count: u32) -> u64 {
        self.bit_buf & ((1 << count) - 1)
    }

    #[inline]
    fn consume_(&mut self, count: u32) {
        self.bit_buf >>= count;
    }
}

generate_bitter_end!(
    /// Reads bits in the big-endian format
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bebits = BigEndianReader::new(&[0b1000_0000]);
    /// assert_eq!(bebits.read_bit(), Some(true));
    /// ```
    BigEndianReader,
    to_be,
    >>
);

impl<'a> BigEndianReader<'a> {
    #[inline]
    fn peek_(&self, count: u32) -> u64 {
        self.bit_buf >> (BIT_WIDTH - count as usize)
    }

    #[inline]
    fn consume_(&mut self, count: u32) {
        self.bit_buf <<= count;
    }
}

/// Read bits in system native-endian format
#[cfg(target_endian = "little")]
pub type NativeEndianReader<'a> = LittleEndianReader<'a>;

/// Read bits in system native-endian format
#[cfg(target_endian = "big")]
pub type NativeEndianReader<'a> = BigEndianReader<'a>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u64_reads_le() {
        let mut bits = LittleEndianReader::new(&[
            0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2, 0x01, 0xff, 0xfe, 0xfa, 0xf7, 0xf5,
            0xf0, 0xb1, 0xb3,
        ]);

        let mut out = [0u8; 8];
        assert!(bits.read_bytes(&mut out));
        assert_eq!(u64::from_le_bytes(out), 0xb2b1_f0f5_f7fa_feff);
        assert_eq!(bits.read_bits(8), Some(0x01));
        assert!(bits.read_bytes(&mut out));
        assert_eq!(u64::from_le_bytes(out), 0xb3b1_f0f5_f7fa_feff);
    }

    #[test]
    fn test_has_remaining_bits() {
        let mut bits = LittleEndianReader::new(&[0xff, 0xff]);
        assert!(bits.has_bits_remaining(7));
        assert!(bits.has_bits_remaining(8));
        assert!(bits.has_bits_remaining(9));

        assert!(bits.read_bits(9).is_some());
        assert!(bits.has_bits_remaining(7));
        assert!(!bits.has_bits_remaining(8));
        assert!(!bits.has_bits_remaining(9));

        assert!(bits.read_bits(7).is_some());
        assert!(!bits.has_bits_remaining(7));
        assert!(bits.has_bits_remaining(0));
    }

    #[test]
    fn test_whole_bytes() {
        let mut bits = LittleEndianReader::new(&[
            0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd, 0xff, 0xdd, 0xee, 0xff,
            0xdd,
        ]);
        assert_eq!(bits.read_u8(), Some(0xff));
        assert_eq!(bits.read_u16(), Some(u16::from_le_bytes([0xdd, 0xee])));
        let mut out = [0u8; 8];
        assert!(bits.read_bytes(&mut out));
        assert_eq!(
            u64::from_le_bytes(out),
            u64::from_le_bytes([0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd, 0xff])
        );
        assert_eq!(
            bits.read_u32(),
            Some(u32::from_le_bytes([0xdd, 0xee, 0xff, 0xdd]))
        );
    }

    #[test]
    fn test_has_remaining_bits2() {
        let mut bits = LittleEndianReader::new(&[0xff, 0xff, 0xff, 0xff]);
        assert!(bits.read_bits(31).is_some());
        assert!(!bits.has_bits_remaining(2));
        assert!(bits.has_bits_remaining(1));
    }

    #[test]
    fn test_signed_bits_fast() {
        let mut bits = LittleEndianReader::new(&[
            0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
            0xe7,
        ]);

        for _ in 0..10 {
            assert_eq!(bits.read_signed_bits(5), Some(-4));
        }
    }

    #[test]
    fn test_signed_bits2_fast() {
        let mut bits =
            LittleEndianReader::new(&[0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd]);
        assert_eq!(bits.read_signed_bits(10), Some(0x1ff));
        assert_eq!(bits.read_signed_bits(10), Some(-73));
        assert_eq!(bits.read_signed_bits(10), Some(-2));
        assert_eq!(bits.read_signed_bits(10), Some(-137));
        assert_eq!(bits.read_signed_bits(8), Some(-18));
        assert_eq!(bits.read_signed_bits(8), Some(-86));
        assert_eq!(bits.read_signed_bits(8), Some(-69));
        assert_eq!(bits.read_signed_bits(8), Some(-52));
        assert_eq!(bits.read_signed_bits(8), Some(-35));
        assert_eq!(bits.read_bits(1), None);
    }

    #[test]
    fn test_u8_reads() {
        let mut bits = LittleEndianReader::new(&[0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2]);
        assert_eq!(bits.read_u8(), Some(0xff));
        assert_eq!(bits.read_u8(), Some(0xfe));
        assert_eq!(bits.read_u8(), Some(0xfa));
        assert_eq!(bits.read_u8(), Some(0xf7));
        assert_eq!(bits.read_u8(), Some(0xf5));
        assert_eq!(bits.read_u8(), Some(0xf0));
        assert_eq!(bits.read_u8(), Some(0xb1));
        assert_eq!(bits.read_u8(), Some(0xb2));
        assert_eq!(bits.read_u8(), None);
    }

    #[test]
    fn test_u32_bit_read() {
        let mut bits = LittleEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
        assert_eq!(bits.read_bits(32), Some(0xcdab00ff));
    }

    #[test]
    fn test_u32_reads() {
        let mut bits = LittleEndianReader::new(&[
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
        assert_eq!(bits.read_u32(), Some(0xcdab00ff));
        assert_eq!(bits.read_bit(), Some(false));
        assert_eq!(bits.read_u32(), Some(0xcdab00ff));
        assert_eq!(bits.read_bit(), Some(false));
        assert_eq!(bits.read_u32(), None);
    }

    #[test]
    fn test_f32_reads() {
        let mut bits = LittleEndianReader::new(&[
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
        assert_eq!(bits.read_f32(), Some(0.085));
        assert_eq!(bits.read_bit(), Some(false));
        assert_eq!(bits.read_f32(), Some(0.085));
    }

    #[test]
    fn test_u32_bits() {
        let mut bits = LittleEndianReader::new(&[0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee]);
        assert_eq!(bits.read_bits(10), Some(0x1ff));
        assert_eq!(bits.read_bits(10), Some(0x3b7));
        assert_eq!(bits.read_bits(10), Some(0x3fe));
        assert_eq!(bits.read_bits(10), Some(0x377));
        assert_eq!(bits.read_bits(10), None);
    }

    #[test]
    fn test_u32_bits2() {
        let mut bits = LittleEndianReader::new(&[
            0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
            0xe7,
        ]);
        for _ in 0..10 {
            assert_eq!(bits.read_bits(5), Some(28));
        }
    }

    #[test]
    fn test_signed_bits2() {
        let mut bits = LittleEndianReader::new(&[
            0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
            0xe7,
        ]);

        for _ in 0..10 {
            assert_eq!(bits.read_signed_bits(5), Some(-4));
        }
    }

    #[test]
    fn test_approx_bytes_and_empty() {
        let mut bits = LittleEndianReader::new(&[0xff, 0x04]);
        assert!(!bits.is_empty());
        assert_eq!(bits.bytes_remaining(), 2);
        assert!(bits.read_bit().is_some());
        assert!(!bits.is_empty());
        assert_eq!(bits.bytes_remaining(), 1);
        assert!(bits.read_bits(6).is_some());
        assert!(!bits.is_empty());
        assert_eq!(bits.bytes_remaining(), 1);
        assert!(bits.read_bit().is_some());
        assert!(!bits.is_empty());
        assert_eq!(bits.bytes_remaining(), 1);
        assert!(bits.read_bit().is_some());
        assert!(!bits.is_empty());
        assert_eq!(bits.bytes_remaining(), 0);
        assert!(bits.read_bits(7).is_some());
        assert!(bits.is_empty());
        assert_eq!(bits.bytes_remaining(), 0);
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
    fn read_bits_52() {
        let data = [0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88];
        let mut bits = LittleEndianReader::new(&data);
        assert_eq!(bits.read_bits(4), Some(0xf));
        assert_eq!(bits.read_bits(52), Some(0x99aabbccddeef));
    }

    #[test]
    fn read_bits_56() {
        let data: [u8; 8] = [0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89];
        let mut bits = LittleEndianReader::new(&data);
        assert_eq!(bits.read_bits(56), Some(0x67452301efcdab));
        assert_eq!(bits.read_bits(4), Some(0x09));
    }

    #[test]
    fn regression1() {
        let data = vec![0b0000_0010, 0b0011_1111, 0b1011_1100];
        let mut bits = LittleEndianReader::new(data.as_slice());

        assert_eq!(bits.read_bits(3), Some(2));
        assert_eq!(bits.read_u8(), Some(224));
        assert_eq!(bits.read_bit(), Some(true));
        assert_eq!(bits.read_bits(13), None);
    }
}

#[cfg(test)]
mod be_tests {
    use super::{BigEndianReader, BitReader};

    #[test]
    fn test_be_bit_bits_reads() {
        let mut bits = BigEndianReader::new(&[0b1010_1010, 0b0101_0101]);
        assert!(bits.has_bits_remaining(16));
        assert_eq!(bits.bits_remaining(), Some(16));
        assert_eq!(bits.read_bits(1), Some(1));
        assert!(!bits.has_bits_remaining(16));
        assert_eq!(bits.bits_remaining(), Some(15));
        assert_eq!(bits.read_bits(1), Some(0));
        assert_eq!(bits.read_bits(1), Some(1));
        assert_eq!(bits.read_bits(1), Some(0));
        assert_eq!(bits.read_bits(1), Some(1));
        assert_eq!(bits.read_bits(1), Some(0));
        assert_eq!(bits.read_bits(1), Some(1));
        assert_eq!(bits.read_bits(1), Some(0));
        assert_eq!(bits.read_bits(1), Some(0));
        assert_eq!(bits.read_bits(1), Some(1));
        assert_eq!(bits.read_bits(1), Some(0));
        assert_eq!(bits.read_bits(1), Some(1));
        assert_eq!(bits.read_bits(1), Some(0));
        assert_eq!(bits.read_bits(1), Some(1));
        assert_eq!(bits.read_bits(1), Some(0));
        assert_eq!(bits.read_bits(1), Some(1));

        assert_eq!(bits.read_bits(1), None);
    }

    #[test]
    fn test_whole_bytes() {
        let mut bits = BigEndianReader::new(&[
            0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd, 0xff, 0xdd, 0xee, 0xff,
            0xdd,
        ]);
        assert_eq!(bits.read_u8(), Some(0xff));
        assert_eq!(bits.read_u16(), Some(u16::from_be_bytes([0xdd, 0xee])));
        let mut out = [0u8; 8];
        assert!(bits.read_bytes(&mut out));
        assert_eq!(
            u64::from_be_bytes(out),
            u64::from_be_bytes([0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd, 0xff])
        );
        assert_eq!(
            bits.read_u32(),
            Some(u32::from_be_bytes([0xdd, 0xee, 0xff, 0xdd]))
        );
    }

    #[test]
    fn test_u32_bits() {
        let mut bits =
            BigEndianReader::new(&[0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee, 0xaa, 0xbb, 0xcc, 0xdd]);
        assert_eq!(bits.read_bits(10), Some(0b11_1111_1111));
        assert_eq!(bits.read_bits(10), Some(0b01_1101_1110));
        assert_eq!(bits.read_bits(10), Some(0b11_1011_1111));
        assert_eq!(bits.read_bits(10), Some(0b11_1101_1101));
        assert_eq!(bits.read_bits(8), Some(0xee));
        assert_eq!(bits.read_bits(8), Some(0xaa));
        assert_eq!(bits.read_bits(8), Some(0xbb));
        assert_eq!(bits.read_bits(8), Some(0xcc));
        assert_eq!(bits.read_bits(8), Some(0xdd));
        assert_eq!(bits.read_bit(), None);
    }

    #[test]
    fn test_u32_bits2() {
        let mut bits = BigEndianReader::new(&[
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
            assert_eq!(bits.read_bits(5), Some(28));
        }
    }

    #[test]
    fn test_u32_bit_read() {
        let mut bits = BigEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
        assert_eq!(bits.read_bits(32), Some(0xff00abcd));
    }

    #[test]
    fn read_bits_52() {
        let data = [0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88];
        let mut bits = BigEndianReader::new(&data);
        assert_eq!(bits.read_bits(4), Some(0xf));
        assert_eq!(bits.read_bits(52), Some(0xfeeddccbbaa99));
    }

    #[test]
    fn test_signed_bits() {
        let mut bits = BigEndianReader::new(&[0xe7, 0x39, 0xce, 0x73, 0x9C, 0xE7, 0x39, 0xC0]);

        for _ in 0..12 {
            assert_eq!(bits.read_signed_bits(5), Some(-4));
        }
    }
}
