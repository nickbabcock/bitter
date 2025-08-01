/*!

***Reading bits until the bitter end***

Bitter reads bits in a desired endian format platform agnostically. Performance is the distinguishing feature compared to other bit readers. See [benchmarks](https://github.com/nickbabcock/bitter#comparison-to-other-libraries) for more information.

## Features

 - ✔ support for little endian, big endian, and native endian formats
 - ✔ request an arbitrary amount of bits (up to 64 bits) and bytes
 - ✔ ergonomic requests for common data types (eg: `u8` ... `u64`, `f64`, etc)
 - ✔ fastest bit reader at multi-GiB/s throughput
 - ✔ no allocations, no dependencies, and [no panics](https://github.com/dtolnay/no-panic)
 - ✔ `no_std` compatible

## Quick start with Auto mode

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

The `read_` prefixed functions are colloquially known as "Auto mode", as one does not need to manage the underlying bits in the lookahead buffer.

## Manual mode

One can unlock additional performance by amortizing internal state logic management when exploiting patterns in the encoded data. Our example from before can be rewritten to take advantage of our domain knowledge that we'll be decoding 16 bits.

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bits = LittleEndianReader::new(&[0xff, 0x04]);

// ... snip code that may have read some bits

// We first check that there's enough total bits
if !bits.has_bits_remaining(16) {
  panic!("not enough bits remaining");
}

// Despite there being enough data, the lookahead buffer may not be sufficient
if bits.lookahead_bits() < 16 {
  bits.refill_lookahead();
  assert!(bits.lookahead_bits() >= 16)
}

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

The refill, peek, and consume combination are the building blocks for Manual Mode, and allows fine grain management for hot loops. The surface area of Manual Mode APIs is purposely compact to keep things simple. The Auto mode API is larger as that API should be the first choice.

A major difference between Manual mode and Auto mode is that one can't peek at more than what's in the lookahead buffer. Since the lookahead buffer will vary between `MAX_READ_BITS` and 63 bits, one will need to write logic to stitch together peeks above `MAX_READ_BITS` in the endian of their choice.

Manual mode can be intimidating, but it's one of if not the fastest way to decode a bit stream, as it's based on variant 4 from [Fabian Giesen's excellent series on reading bits](https://fgiesen.wordpress.com/2018/02/20/reading-bits-in-far-too-many-ways-part-2/). Others have employed this underlying technique to [significantly speed up DEFLATE](https://dougallj.wordpress.com/2022/08/20/faster-zlib-deflate-decompression-on-the-apple-m1-and-x86/).

An example of how one can write a Manual mode solution for reading 60 bits:

```rust
use bitter::{BitReader, LittleEndianReader};

let data: [u8; 8] = [0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89];
let mut bits = LittleEndianReader::new(&data);

// ... snip ... maybe some bits are read here.

let expected = 0x0967_4523_01EF_CDAB;
let bits_to_read = 60u32;

bits.refill_lookahead();
let lo_len = bits.lookahead_bits();
let lo = bits.peek(lo_len);
bits.consume(lo_len);

let left = bits_to_read - lo_len;
bits.refill_lookahead();
let hi_len = bits.lookahead_bits().min(left);
let hi = bits.peek(hi_len);
bits.consume(hi_len);

assert_eq!(expected, (hi << lo_len) + lo);
```

The above is not an endorsement of the best way to simulate larger reads in Manual mode. For instance, it may be better to drain the lookahead first, or use `MAX_READ_BITS` to calculate `lo` instead of querying `lookahead_bits`. Always profile for your environment.

## Unchecked mode

There's one final trick that bitter exposes that dials performance to 11 at the cost of safety and increased assumptions. Welcome to the unchecked refill API (referred to as "unchecked"), which can only be called when there are at least 8 bytes left in the buffer. Anything less than that can cause invalid memory access. The upside is that this API unlocks the holy grail of branchless bit reading.

Always guard unchecked access at a higher level:

```rust
use bitter::{BitReader, LittleEndianReader, MAX_READ_BITS};

let mut bits = LittleEndianReader::new(&[0u8; 100]);
let objects_to_read = 10;
let object_bits = 56;
let desired_bits = objects_to_read * object_bits;
let bytes_needed = (desired_bits as f64 / 8.0).ceil();

if bits.unbuffered_bytes_remaining() >= bytes_needed as usize {
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
} else if bits.has_bits_remaining(desired_bits) {
  // So have enough bits to read all the objects just not
  // enough bits to call the unchecked lookahead API everytime.
  assert!(false);
} else {
  // Not enough data.
  assert!(false);
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

#![warn(missing_docs)]
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

    /// Consume 64 bits and return the deserialized int
    ///
    /// ```rust
    /// use bitter::{BitReader, LittleEndianReader};
    /// let data = (22000u64).to_le_bytes();
    /// let mut bits = LittleEndianReader::new(&data);
    /// assert_eq!(bits.read_u64(), Some(22000u64));
    /// ```
    fn read_u64(&mut self) -> Option<u64>;

    /// Consume 64 bits and return the deserialized int
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = (-22000i64).to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_i64(), Some(-22000i64));
    /// ```
    fn read_i64(&mut self) -> Option<i64>;

    /// Consume 64 bits and return the deserialized floating point
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let data = 12.5f64.to_be_bytes();
    /// let mut bits = BigEndianReader::new(&data);
    /// assert_eq!(bits.read_f64(), Some(12.5f64));
    /// ```
    fn read_f64(&mut self) -> Option<f64>;

    /// Reads an arbitrary number of bits in the range of [0, 64] and returns
    /// the unsigned result
    ///
    /// ```rust
    /// use bitter::{BitReader, BigEndianReader};
    /// let mut bits = BigEndianReader::new(&[0xff, 0x00, 0xab, 0xcd]);
    /// assert_eq!(bits.read_bits(32), Some(0xff00abcd));
    /// ```
    fn read_bits(&mut self, bits: u32) -> Option<u64>;

    /// Reads an arbitrary number of bits in the range of [0, 64] and returns
    /// the signed result.
    ///
    /// If the most significant bit is enabled, the result will be negative.
    /// This can be somewhat counterintuitive so see the examples
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
    /// To think of it another way, reading the number of bits equivalent to a
    /// builtin type (i8, i16, etc), will always equal its associated ergonomic
    /// equivalent when casted.
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

    /// Returns how many bytes are still left in the passed in buffer.
    ///
    /// How many bytes remain in the original buffer is typically an
    /// implementation detail, and one should prefer
    /// [`BitReader::bytes_remaining`], which includes bytes in the lookahead
    /// buffer.
    ///
    /// However, the bitter unchecked API,
    /// [`BitReader::refill_lookahead_unchecked`], requires this same
    /// calculation to avoid undefined behavior.
    ///
    /// **Anecdotally** the use of this function can assist the compiler in
    /// eliminating branches that would appear in
    /// [`BitReader::refill_lookahead`] without needing to introduce unsafe
    /// blocks. Your mileage may vary.
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bits = LittleEndianReader::new(&[0u8; 100]);
    /// if bits.unbuffered_bytes_remaining() >= 16 {
    ///   // The compiler can eliminate the end of buffer checks
    ///   // in both of these refills without needing to drop to unsafe
    ///   bits.refill_lookahead();
    ///   // ... do some reading ...
    ///   bits.refill_lookahead();
    /// }
    /// ```
    fn unbuffered_bytes_remaining(&self) -> usize;

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
    fn consume(&mut self, count: u32);

    /// Refills the lookahead buffer.
    ///
    /// A core tenent of Manual Mode: refill / peek / consume
    ///
    /// Refills the lookahead buffer anywhere between [[`MAX_READ_BITS`], 64] as
    /// long as the end of the stream has not been reached. See how many bits
    /// are in the buffer with [`BitReader::lookahead_bits`].
    ///
    /// If [`BitReader::lookahead_bits`] is already in the specified range,
    /// additional refills will have no effect.
    fn refill_lookahead(&mut self);

    /// Returns the number of bits in the lookahead buffer
    ///
    /// These are the number of bits available to be consumed before a refill is
    /// necessary.
    ///
    /// Guaranteed to be between [[`MAX_READ_BITS`], 64] when at least 8 bytes
    /// of data remains unread.
    fn lookahead_bits(&self) -> u32;

    /// Refills the lookahead buffer without bounds checking
    ///
    /// After calling, the lookahead buffer is guaranteed to have between
    /// [[`MAX_READ_BITS`], 64] bits available to read.
    ///
    /// # Safety
    ///
    /// This function assumes that there are at least 8 bytes left unbuffered
    /// for an unaligned read. It is undefined behavior if there is less than 8
    /// bytes remaining
    ///
    /// Guard all usages with [`BitReader::unbuffered_bytes_remaining`]
    ///
    /// ```rust
    /// # use bitter::{LittleEndianReader, BitReader};
    /// let mut bits = LittleEndianReader::new(&[0u8; 100]);
    /// let objects_to_read = 7;
    /// let object_bits = 39;
    /// let desired_bits = objects_to_read * object_bits;
    /// let bytes_needed = (desired_bits as f64 / 8.0).ceil();
    /// if bits.unbuffered_bytes_remaining() >= bytes_needed as usize {
    ///   for _ in 0..objects_to_read {
    ///     unsafe { bits.refill_lookahead_unchecked() };
    ///     let _field1 = bits.peek(10);
    ///     bits.consume(10);
    ///
    ///     let _field2 = bits.peek(29);
    ///     bits.consume(29);
    ///   }
    /// }
    /// ```
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

const BYTE_WIDTH: usize = core::mem::size_of::<u64>();
const BIT_WIDTH: usize = BYTE_WIDTH * 8;

/// The minimum number of bits available after a lookahead refill.
///
/// This minimum is only guaranteed when the end of data has not been reached.
/// It provides the lower bound to the maximum number of bits that can be
/// consumed without a refill.
///
/// The actual number of bits available in the lookahead can be found at
/// [`BitReader::lookahead_bits`].
///
/// Use static assertions to ensure that your data model fits within expected
/// number of refills
///
/// ```rust
/// const _: () = assert!(
///     bitter::MAX_READ_BITS >= 56,
///     "unexpected lookahead buffer size"
/// );
/// ```
///
/// If your data model doesn't fit, either use [`BitReader::lookahead_bits`] to
/// dynamically adjust to what's available for a given refill or refill at given
/// intervals regardless of what's available.
pub const MAX_READ_BITS: u32 = 56;

#[derive(Debug, Clone, Copy)]
struct BitterState<'a, const LE: bool> {
    /// Pointer of next byte for lookahead
    data: &'a [u8],

    /// Current lookahead buffer contents
    bit_buf: u64,

    /// Number of bits in buffer
    bit_count: u32,
}

impl<'a, const LE: bool> BitterState<'a, LE> {
    #[inline]
    #[must_use]
    pub fn new(data: &'a [u8]) -> Self {
        Self {
            data,
            bit_buf: 0,
            bit_count: 0,
        }
    }

    #[inline]
    fn which(input: u64) -> u64 {
        if LE {
            input.to_le()
        } else {
            input.to_be()
        }
    }

    #[inline]
    fn read(&self) -> u64 {
        debug_assert!(self.unbuffered_bytes() >= 8);
        let mut result = [0u8; 8];
        result.copy_from_slice(&self.data[..8]);
        Self::which(u64::from_ne_bytes(result))
    }

    #[inline]
    fn read_eof(&self) -> u64 {
        debug_assert!(self.unbuffered_bytes() < 8);
        let mut result = [0u8; 8];
        let len = self.unbuffered_bytes();
        result[..len].copy_from_slice(self.data);
        let result = u64::from_ne_bytes(result);
        Self::which(result)
    }

    #[inline]
    fn peek_(&self, count: u32) -> u64 {
        if LE {
            self.bit_buf & ((1 << count) - 1)
        } else if count != 0 {
            self.bit_buf >> (BIT_WIDTH - count as usize)
        } else {
            0
        }
    }
    #[inline]
    fn consume_(&mut self, count: u32) {
        if LE {
            self.bit_buf >>= count;
        } else {
            self.bit_buf <<= count;
        }
        self.bit_count -= count;
    }

    #[inline]
    fn refill_shift(&mut self, raw: u64) -> usize {
        self.bit_buf |= if LE {
            raw << self.bit_count
        } else {
            raw >> self.bit_count
        };
        7 - ((self.bit_count as usize >> 3) & 7)
    }

    #[inline]
    fn refill(&mut self) {
        let raw = self.read();
        let shift = self.refill_shift(raw);
        self.data = &self.data[shift..];
        self.bit_count |= MAX_READ_BITS;
    }

    #[inline]
    fn refill_eof(&mut self) {
        let raw = self.read_eof();
        let shift = self.refill_shift(raw);
        let consumed = self.unbuffered_bytes().min(shift);
        self.data = &self.data[consumed..];
        self.bit_count += (consumed * 8) as u32;
    }

    // End of buffer checking is a fascinating topic, see:
    // https://fgiesen.wordpress.com/2016/01/02/end-of-buffer-checks-in-decompressors/
    //
    // We use the so declared "boring" method of using a marker to know when
    // we can't blindly unalign read 64 bits, and duplicate some behavior.
    #[inline]
    fn has_data_for_unaligned_loads(&self) -> bool {
        self.data.len() >= core::mem::size_of::<u64>()
    }

    #[inline]
    fn unbuffered_bytes(&self) -> usize {
        self.data.len()
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
}

macro_rules! gen_read {
    ($name:ident, $t:ty) => {
        #[inline]
        fn $name(&mut self) -> Option<$t> {
            let bits = (core::mem::size_of::<$t>() * 8);
            self.read_bits(bits as u32).map(|x| x as $t)
        }
    };
}

impl<const LE: bool> BitReader for BitterState<'_, LE> {
    gen_read!(read_u8, u8);
    gen_read!(read_i8, i8);
    gen_read!(read_u16, u16);
    gen_read!(read_i16, i16);
    gen_read!(read_u32, u32);
    gen_read!(read_i32, i32);
    gen_read!(read_u64, u64);
    gen_read!(read_i64, i64);

    fn read_bit(&mut self) -> Option<bool> {
        self.read_bits(1).map(|x| x == 1)
    }

    #[inline]
    fn read_f32(&mut self) -> Option<f32> {
        self.read_u32().map(f32::from_bits)
    }

    #[inline]
    fn read_f64(&mut self) -> Option<f64> {
        self.read_u64().map(f64::from_bits)
    }

    #[inline]
    fn read_bits(&mut self, bits: u32) -> Option<u64> {
        debug_assert!(
            bits <= BIT_WIDTH as u32,
            "read request exceeded limit of {} bits, received {}",
            BIT_WIDTH,
            bits
        );

        if self.has_data_for_unaligned_loads() {
            if bits > self.bit_count {
                self.refill();
            }

            if bits <= MAX_READ_BITS {
                let result = self.peek(bits);
                self.consume(bits);
                Some(result)
            } else {
                let lo = self.peek(MAX_READ_BITS);
                self.consume(MAX_READ_BITS);

                self.refill_lookahead();
                let hi_len = bits - MAX_READ_BITS;
                let hi = self.peek(hi_len);
                self.consume(hi_len);
                if LE {
                    Some((hi << MAX_READ_BITS) + lo)
                } else {
                    Some((lo << hi_len) + hi)
                }
            }
        } else if self.has_bits_remaining(bits as usize) {
            self.refill_eof();
            if bits <= MAX_READ_BITS {
                let result = self.peek(bits);
                self.consume(bits);
                Some(result)
            } else {
                let lo = self.peek(MAX_READ_BITS);
                self.consume(MAX_READ_BITS);

                self.refill_eof();
                let hi_len = bits - MAX_READ_BITS;
                let hi = self.peek(hi_len);
                self.consume(hi_len);
                if LE {
                    Some((hi << MAX_READ_BITS) + lo)
                } else {
                    Some((lo << hi_len) + hi)
                }
            }
        } else {
            None
        }
    }

    #[inline]
    fn read_signed_bits(&mut self, bits: u32) -> Option<i64> {
        self.read_bits(bits).map(|x| sign_extend(x, bits))
    }

    #[inline]
    fn bytes_remaining(&self) -> usize {
        self.bytes_remaining()
    }

    #[inline]
    fn unbuffered_bytes_remaining(&self) -> usize {
        self.unbuffered_bytes()
    }

    #[inline]
    fn bits_remaining(&self) -> Option<usize> {
        self.bits_remaining()
    }

    #[inline]
    fn has_bits_remaining(&self, bits: usize) -> bool {
        self.has_bits_remaining(bits)
    }

    #[inline]
    fn read_bytes(&mut self, buf: &mut [u8]) -> bool {
        let lookahead_bytes = (self.bit_count >> 3) as usize;

        // Before we get to fast-path copying we need to consume as much of
        // the lookahead buffer as we can.
        let lookahead_consumption = lookahead_bytes.min(buf.len());
        let (buf_lookahead, buf) = buf.split_at_mut(lookahead_consumption);

        let (head, tail) = if buf.len() <= self.data.len() {
            self.data.split_at(buf.len())
        } else {
            return false;
        };

        for dst in buf_lookahead.iter_mut() {
            *dst = self.peek(8) as u8;
            self.consume(8);
        }

        if self.byte_aligned() {
            // Return if the lookahead buffer was big enough to fill everything
            if buf.is_empty() {
                return true;
            }

            buf.copy_from_slice(head);

            // Since we just consumed the entire lookahead (which isn't normally
            // possible), we reset internal state.
            self.data = tail;
            self.bit_buf = 0;
            self.refill_lookahead();
        } else if let Some((first, buf)) = buf.split_first_mut() {
            // Consume the rest of the lookahead
            let lookahead_remainder = self.bit_count;
            let lookahead_tail = self.peek(lookahead_remainder) as u8;
            self.consume(lookahead_remainder);

            // lookahead now empty, but adjust overlapping data byte
            *first = if LE {
                (head[0] << lookahead_remainder) + lookahead_tail
            } else {
                (head[0] >> lookahead_remainder) + (lookahead_tail << (8 - lookahead_remainder))
            };

            // Then attempt to process multiple 16 bytes at once
            let chunk_size = 16;
            let buf_chunks = buf.len() / chunk_size;
            let chunk_bytes = buf_chunks * chunk_size;

            let (buf_body, buf) = buf.split_at_mut(chunk_bytes);
            if LE {
                read_n_bytes(lookahead_remainder, head, buf_body);
            } else {
                read_n_bytes_be(lookahead_remainder, head, buf_body);
            }

            // Process trailing bytes that don't fit into chunk
            //
            // SAFETY: we know this is safe as chunk_bytes is <= than head.len()
            // and head was split off from data (but the compiler isn't smart
            // enough to deduce this and we want to avoid introducing a panic).
            self.data = unsafe { self.data.get_unchecked(chunk_bytes..) };
            self.bit_buf = 0;
            self.refill_lookahead();
            self.consume(8 - lookahead_remainder);
            self.refill_lookahead();

            for dst in buf.iter_mut() {
                if self.lookahead_bits() < 8 {
                    self.refill_lookahead();
                    debug_assert!(self.lookahead_bits() >= 8);
                }

                *dst = self.peek(8) as u8;
                self.consume(8);
            }
        }

        true
    }

    #[inline]
    fn peek(&self, count: u32) -> u64 {
        debug_assert!(
            count <= self.bit_count,
            "not enough bits in lookahead buffer to fulfill peek ({} vs {})",
            count,
            self.bit_count
        );
        self.peek_(count)
    }

    #[inline]
    fn consume(&mut self, count: u32) {
        debug_assert!(
            count <= self.bit_count,
            "not enough bits in lookahead buffer to fulfill consume ({} vs {})",
            count,
            self.bit_count
        );
        self.consume_(count);
    }

    #[inline]
    fn lookahead_bits(&self) -> u32 {
        self.bit_count
    }

    #[inline]
    fn refill_lookahead(&mut self) {
        if self.has_data_for_unaligned_loads() {
            self.refill();
        } else {
            self.refill_eof();
        }
    }

    #[inline]
    unsafe fn refill_lookahead_unchecked(&mut self) {
        debug_assert!(self.unbuffered_bytes() >= 8);
        let result = self.data.as_ptr().cast::<u64>().read_unaligned();
        let shift = self.refill_shift(Self::which(result));
        self.data = self.data.get_unchecked(shift..);
        self.bit_count |= MAX_READ_BITS;
    }

    #[inline]
    fn is_empty(&self) -> bool {
        !self.has_bits_remaining(1)
    }

    #[inline]
    fn byte_aligned(&self) -> bool {
        self.bit_count % 8 == 0
    }
}

/// Reads bits in the little-endian format
///
/// ```rust
/// use bitter::{BitReader, LittleEndianReader};
/// let mut lebits = LittleEndianReader::new(&[0b0000_0001]);
/// assert_eq!(lebits.read_bit(), Some(true));
/// ```
#[derive(Debug, Clone, Copy)]
pub struct LittleEndianReader<'a>(BitterState<'a, true>);

impl<'a> LittleEndianReader<'a> {
    /// Create a little endian reader from the given byte slice.
    #[inline]
    #[must_use]
    pub fn new(data: &'a [u8]) -> Self {
        Self(BitterState::new(data))
    }
}

impl BitReader for LittleEndianReader<'_> {
    #[inline]
    fn read_bit(&mut self) -> Option<bool> {
        self.0.read_bit()
    }

    #[inline]
    fn read_u8(&mut self) -> Option<u8> {
        self.0.read_u8()
    }

    #[inline]
    fn read_i8(&mut self) -> Option<i8> {
        self.0.read_i8()
    }

    #[inline]
    fn read_u16(&mut self) -> Option<u16> {
        self.0.read_u16()
    }

    #[inline]
    fn read_i16(&mut self) -> Option<i16> {
        self.0.read_i16()
    }

    #[inline]
    fn read_u32(&mut self) -> Option<u32> {
        self.0.read_u32()
    }

    #[inline]
    fn read_i32(&mut self) -> Option<i32> {
        self.0.read_i32()
    }

    #[inline]
    fn read_f32(&mut self) -> Option<f32> {
        self.0.read_f32()
    }

    #[inline]
    fn read_u64(&mut self) -> Option<u64> {
        self.0.read_u64()
    }

    #[inline]
    fn read_i64(&mut self) -> Option<i64> {
        self.0.read_i64()
    }

    #[inline]
    fn read_f64(&mut self) -> Option<f64> {
        self.0.read_f64()
    }

    #[inline]
    fn read_bits(&mut self, bits: u32) -> Option<u64> {
        self.0.read_bits(bits)
    }

    #[inline]
    fn read_signed_bits(&mut self, bits: u32) -> Option<i64> {
        self.0.read_signed_bits(bits)
    }

    #[inline]
    fn bytes_remaining(&self) -> usize {
        self.0.bytes_remaining()
    }

    #[inline]
    fn unbuffered_bytes_remaining(&self) -> usize {
        self.0.unbuffered_bytes()
    }

    #[inline]
    fn bits_remaining(&self) -> Option<usize> {
        self.0.bits_remaining()
    }

    #[inline]
    fn has_bits_remaining(&self, bits: usize) -> bool {
        self.0.has_bits_remaining(bits)
    }

    #[inline]
    fn read_bytes(&mut self, buf: &mut [u8]) -> bool {
        self.0.read_bytes(buf)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    fn peek(&self, count: u32) -> u64 {
        self.0.peek(count)
    }

    #[inline]
    fn consume(&mut self, count: u32) {
        self.0.consume(count);
    }

    #[inline]
    fn lookahead_bits(&self) -> u32 {
        self.0.lookahead_bits()
    }

    #[inline]
    fn refill_lookahead(&mut self) {
        self.0.refill_lookahead();
    }

    #[inline]
    unsafe fn refill_lookahead_unchecked(&mut self) {
        self.0.refill_lookahead_unchecked();
    }

    #[inline]
    fn byte_aligned(&self) -> bool {
        self.0.byte_aligned()
    }
}

/// Reads bits in the big-endian format
///
/// ```rust
/// use bitter::{BitReader, BigEndianReader};
/// let mut bebits = BigEndianReader::new(&[0b1000_0000]);
/// assert_eq!(bebits.read_bit(), Some(true));
/// ```
#[derive(Debug, Clone, Copy)]
pub struct BigEndianReader<'a>(BitterState<'a, false>);

impl<'a> BigEndianReader<'a> {
    /// Create a big endian reader from the given byte slice.
    #[inline]
    #[must_use]
    pub fn new(data: &'a [u8]) -> Self {
        Self(BitterState::new(data))
    }
}

impl BitReader for BigEndianReader<'_> {
    #[inline]
    fn read_bit(&mut self) -> Option<bool> {
        self.0.read_bit()
    }

    #[inline]
    fn read_u8(&mut self) -> Option<u8> {
        self.0.read_u8()
    }

    #[inline]
    fn read_i8(&mut self) -> Option<i8> {
        self.0.read_i8()
    }

    #[inline]
    fn read_u16(&mut self) -> Option<u16> {
        self.0.read_u16()
    }

    #[inline]
    fn read_i16(&mut self) -> Option<i16> {
        self.0.read_i16()
    }

    #[inline]
    fn read_u32(&mut self) -> Option<u32> {
        self.0.read_u32()
    }

    #[inline]
    fn read_i32(&mut self) -> Option<i32> {
        self.0.read_i32()
    }

    #[inline]
    fn read_f32(&mut self) -> Option<f32> {
        self.0.read_f32()
    }

    #[inline]
    fn read_u64(&mut self) -> Option<u64> {
        self.0.read_u64()
    }

    #[inline]
    fn read_i64(&mut self) -> Option<i64> {
        self.0.read_i64()
    }

    #[inline]
    fn read_f64(&mut self) -> Option<f64> {
        self.0.read_f64()
    }

    #[inline]
    fn read_bits(&mut self, bits: u32) -> Option<u64> {
        self.0.read_bits(bits)
    }

    #[inline]
    fn read_signed_bits(&mut self, bits: u32) -> Option<i64> {
        self.0.read_signed_bits(bits)
    }

    #[inline]
    fn bytes_remaining(&self) -> usize {
        self.0.bytes_remaining()
    }

    #[inline]
    fn unbuffered_bytes_remaining(&self) -> usize {
        self.0.unbuffered_bytes()
    }

    #[inline]
    fn bits_remaining(&self) -> Option<usize> {
        self.0.bits_remaining()
    }

    #[inline]
    fn has_bits_remaining(&self, bits: usize) -> bool {
        self.0.has_bits_remaining(bits)
    }

    #[inline]
    fn read_bytes(&mut self, buf: &mut [u8]) -> bool {
        self.0.read_bytes(buf)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    fn peek(&self, count: u32) -> u64 {
        self.0.peek(count)
    }

    #[inline]
    fn consume(&mut self, count: u32) {
        self.0.consume(count);
    }

    #[inline]
    fn lookahead_bits(&self) -> u32 {
        self.0.lookahead_bits()
    }

    #[inline]
    fn refill_lookahead(&mut self) {
        self.0.refill_lookahead();
    }

    #[inline]
    unsafe fn refill_lookahead_unchecked(&mut self) {
        self.0.refill_lookahead_unchecked();
    }

    #[inline]
    fn byte_aligned(&self) -> bool {
        self.0.byte_aligned()
    }
}

/// Read bits in system native-endian format
#[cfg(target_endian = "little")]
pub type NativeEndianReader<'a> = LittleEndianReader<'a>;

/// Read bits in system native-endian format
#[cfg(target_endian = "big")]
pub type NativeEndianReader<'a> = BigEndianReader<'a>;

/// Arbitrary sign extension for manual mode API.
///
/// See [`BitReader::read_signed_bits`] for more information
///
/// It is assumed the input value has zeros for bits above the given position.  
///
/// ```rust
/// use bitter::{BitReader, LittleEndianReader};
/// let mut bits = LittleEndianReader::new(&[0x9c]);
/// bits.refill_lookahead();
/// let bits_to_read = 4;
/// let value = bits.peek(bits_to_read);
/// assert_eq!(value, 12);
/// assert_eq!(bitter::sign_extend(value, bits_to_read), -4);
/// bits.consume(bits_to_read);
/// ```
#[inline]
#[must_use]
pub fn sign_extend(val: u64, bits: u32) -> i64 {
    // Branchless sign extension from bit twiddling hacks:
    // https://graphics.stanford.edu/~seander/bithacks.html#VariableSignExtend
    //
    // The 3 operation approach with division turned out to be significantly slower,
    // and so was not used.
    debug_assert!(val.leading_zeros() as usize >= (BIT_WIDTH - bits as usize));
    let m = 1i64.wrapping_shl(bits.wrapping_sub(1));
    #[allow(clippy::cast_possible_wrap)]
    let val = val as i64;
    (val ^ m) - m
}

#[inline]
fn read_n_bytes(rem: u32, input: &[u8], out: &mut [u8]) {
    let mask = (1 << rem) - 1;
    let shift = 8 - rem;

    for (i, o) in input.windows(2).zip(out.iter_mut()) {
        let left_part = (i[0] >> shift) & mask;
        let right_part = i[1] << rem;
        *o = left_part + right_part;
    }
}

#[inline]
fn read_n_bytes_be(rem: u32, input: &[u8], out: &mut [u8]) {
    let mask = (1 << rem) - 1;

    for (i, o) in input.windows(2).zip(out.iter_mut()) {
        let left_part = (i[0] & mask) << (8 - rem);
        let right_part = i[1] >> rem;
        *o = left_part | right_part;
    }
}

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
    fn test_zero_bit_reads() {
        let mut bits = LittleEndianReader::new(&[0xff]);
        assert_eq!(bits.peek(0), 0);
        bits.consume(0);
        assert_eq!(bits.read_bits(0), Some(0));

        assert_eq!(bits.read_u8(), Some(0xff));
        assert_eq!(bits.read_bits(0), Some(0));
        assert_eq!(bits.peek(0), 0);
        bits.consume(0);
        assert_eq!(bits.peek(0), 0);
        bits.consume(0);
        assert_eq!(bits.read_bits(0), Some(0));
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
    fn test_whole_bytes_shift() {
        let mut bits = LittleEndianReader::new(&[
            0xdf, 0xed, 0xfe, 0xdf, 0xed, 0xae, 0xba, 0xcb, 0xdc, 0xfd, 0xdf, 0xed, 0xfe, 0xdf,
            0x0d,
        ]);

        assert_eq!(bits.read_bits(4), Some(0x0f));
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
    fn test_whole_bytes_large() {
        let mut data = vec![0u8; 76];
        data[0] = 0b0000_0101;
        data[6] = 0b0000_1000;
        data[7] = 0b0000_0010;
        data[8] = 0b0000_0011;
        data[28] = 0b0000_0000;
        data[29] = 0b1111_1111;
        data[74] = 0b1000_0000;
        data[75] = 0b1011_1111;

        let mut bitter = LittleEndianReader::new(&data);
        assert_eq!(bitter.read_bit(), Some(true));

        let mut buf = [0u8; 75];
        assert!(bitter.read_bytes(&mut buf));

        // prefix
        assert_eq!(buf[0], 0b0000_0010);
        assert_eq!(buf[6], 0b0000_0100);

        // body
        assert_eq!(buf[7], 0b1000_0001);
        assert_eq!(buf[8], 0b0000_0001);
        assert_eq!(buf[28], 0b1000_0000);

        // suffix
        assert_eq!(buf[74], 0b1100_0000);
        assert_eq!(bitter.read_bits(7), Some(0b0101_1111));
        assert_eq!(bitter.read_bit(), None);
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
    fn test_f64_reads() {
        let mut bits = LittleEndianReader::new(&[0u8; 8]);
        assert_eq!(bits.read_f64(), Some(0.0));
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
        assert_eq!(bits.unbuffered_bytes_remaining(), 2);
        assert!(bits.read_bit().is_some());
        assert!(!bits.is_empty());
        assert_eq!(bits.bytes_remaining(), 1);
        assert_eq!(bits.unbuffered_bytes_remaining(), 0);
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
        assert!(!bits.has_bits_remaining(usize::MAX));
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

        assert_eq!(bits.read_i16(), Some(i16::MIN));
    }

    #[test]
    fn i16_max_test() {
        let data = [0b1111_1111, 0b0111_1111];
        let mut bits = LittleEndianReader::new(&data[..]);

        assert_eq!(bits.read_i16(), Some(i16::MAX));
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
    fn read_bits_64() {
        let mut bits = LittleEndianReader::new(&[
            0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45,
            0x67, 0x89,
        ]);
        assert_eq!(bits.read_bits(64), Some(0x8967452301efcdab));
        assert_eq!(bits.read_bits(64), Some(0x8967452301efcdab));
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

    #[test]
    fn test_bytes_remaining() {
        let mut bits = LittleEndianReader::new(&[0xff, 0x04]);
        assert_eq!(bits.bytes_remaining(), 2);
        assert_eq!(bits.unbuffered_bytes_remaining(), 2);
        assert_eq!(bits.read_bit(), Some(true));
        assert_eq!(bits.unbuffered_bytes_remaining(), 0);
        assert_eq!(bits.bytes_remaining(), 1);
        assert_eq!(bits.read_u8(), Some(0x7f));
        assert!(bits.has_bits_remaining(7));
        assert_eq!(bits.read_bits(7), Some(0x02));
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
    fn test_zero_bit_reads() {
        let mut bits = BigEndianReader::new(&[0xff]);
        assert_eq!(bits.peek(0), 0);
        bits.consume(0);
        assert_eq!(bits.read_bits(0), Some(0));

        assert_eq!(bits.read_u8(), Some(0xff));
        assert_eq!(bits.read_bits(0), Some(0));
        assert_eq!(bits.peek(0), 0);
        bits.consume(0);
        assert_eq!(bits.peek(0), 0);
        bits.consume(0);
        assert_eq!(bits.read_bits(0), Some(0));
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
    fn test_whole_bytes_shift() {
        let mut bits = BigEndianReader::new(&[
            0xdf, 0xed, 0xfe, 0xdf, 0xed, 0xae, 0xba, 0xcb, 0xdc, 0xfd, 0xdf, 0xed, 0xfe, 0xdf,
            0x0d,
        ]);

        assert_eq!(bits.read_bits(4), Some(0x0d));
        assert_eq!(bits.read_u16(), Some(u16::from_be_bytes([0xfe, 0xdf])));
        let mut out = [0u8; 8];
        assert!(bits.read_bytes(&mut out));
        assert_eq!(
            u64::from_be_bytes(out),
            u64::from_be_bytes([0xed, 0xfe, 0xda, 0xeb, 0xac, 0xbd, 0xcf, 0xdd])
        );

        assert_eq!(
            bits.read_u32(),
            Some(u32::from_be_bytes([0xfe, 0xdf, 0xed, 0xf0]))
        );
    }

    #[test]
    fn test_whole_bytes_trailing() {
        let mut bits =
            BigEndianReader::new(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]);

        assert!(bits.read_bytes(&mut [0]));
        assert_eq!(bits.read_bits(0), Some(0));
    }

    #[test]
    fn test_whole_bytes_large() {
        let mut data = vec![0u8; 76];
        data[0] = 0b0000_0101;
        data[6] = 0b0000_1000;
        data[7] = 0b0000_0010;
        data[8] = 0b0000_0011;
        data[28] = 0b0000_0000;
        data[29] = 0b1111_1111;
        data[74] = 0b1000_0000;
        data[75] = 0b1011_1111;

        let mut bitter = BigEndianReader::new(&data);
        assert_eq!(bitter.read_bit(), Some(false));

        let mut buf = [0u8; 75];
        assert!(bitter.read_bytes(&mut buf));

        // prefix
        assert_eq!(buf[0], 0b0000_1010);
        assert_eq!(buf[6], 0b0001_0000);

        // body
        assert_eq!(buf[7], 0b0000_0100);
        assert_eq!(buf[8], 0b0000_0110);
        assert_eq!(buf[28], 0b0000_0001);

        // suffix
        assert_eq!(buf[74], 0b0000_0001);
        assert_eq!(bitter.read_bits(7), Some(0b0011_1111));
        assert_eq!(bitter.read_bit(), None);
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
    fn read_bits_64() {
        let mut bits = BigEndianReader::new(&[
            0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45,
            0x67, 0x89,
        ]);
        assert_eq!(bits.read_bits(64), Some(0xabcdef0123456789));
        assert_eq!(bits.read_bits(64), Some(0xabcdef0123456789));
    }

    #[test]
    fn test_signed_bits() {
        let mut bits = BigEndianReader::new(&[0xe7, 0x39, 0xce, 0x73, 0x9C, 0xE7, 0x39, 0xC0]);

        for _ in 0..12 {
            assert_eq!(bits.read_signed_bits(5), Some(-4));
        }
    }
}
