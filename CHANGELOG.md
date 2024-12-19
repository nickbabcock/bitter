## 0.7.1 - 2024-12-19

- Expose the number of unbuffered bytes remaining via `BitReader::unbuffered_bytes_remaining`
- Restore `read_bytes` optimization for unaligned big endian readers for 10x throughput improvement

## 0.7.0 - 2024-05-14

- Revert `read_bytes` optimization for unaligned big endian readers due to correctness issues
- Add support to `read_bits` for reading any number of bits up to 64 bits
- Add `BitReader::read_u64`, `BitReader::read_i64`, and `BitReader::read_f64`
- Add support to `read_bits`, `peek`, and `consume` of zero bits
- Add `BitReader::lookahead_bits` that returns the number of bits in the lookahead buffer
- Allow `peek` and `consume` to accept arguments up to `BitReader::lookahead_bits`
- Remove the return value from `BitReader::refill_lookahead`, which can now be found in `BitReader::lookahead_bits`
- MSRV increased to 1.51
- Most `unsafe` code has been converted to their safe equivalents without a loss in performance

### Migration

The return value of `BitReader::refill_lookahead` has been removed and can be replaced with:

```rust
let data: [u8; 1] = [0xab];
let mut bits = LittleEndianReader::new(&data);

// BEFORE:
// let left = bits.refill_lookahead();

// AFTER:
bits.refill_lookahead();
let left = bits.lookahead_bits();
```

## 0.6.2 - 2024-01-14

- `read_bytes` performance impovements: 35-40% for small reads and up to 22x for large byte unaligned reads.
- Bitter constructors and `sign_extend` have been annotated with `#[must_use]`

## 0.6.1 - 2022-10-24

- Performance improvement for `read_signed_bits` with branchless sign extension
- Expose `bitter:sign_extend` for those who want sign extension with manual mode
- Clearer error message for `peek(0)`

## 0.6.0 - 2022-08-31

See PR #21 for more details, but this is a large and breaking change in the name more performance! The short of it:

- Bit reads now capped at 56 bits
- Most unchecked method have been removed
- Users now can manually control when to trigger lookahead buffer refills to best take advantage of patterns in their data
- MSRV bumped to 1.48.0

## 0.5.1 - 2021-07-11

- Mark remaining non-generic functions as inline

## 0.5.0 - 2021-01-23

This is a big and breaking release but hopefully at the end of the changelog you'll be in agreement that the improvements are very much worth it. I'm confident that the current API will hold up much better and I'm committed to releasing 1.0 if no unforseen flaws are encountered.

### BigEndian and NativeEndian APIs

- `BigGet` has been renamed to `LittleEndianReader` to better reflect its name in light of:
- Introduction of `BigEndianReader` and `NativeEndianReader` alias
- A trait, `BitReader` that is the new home for consuming bits with `read_u8`

Instead of writing:

```rust
use bitter::BitGet;
let mut bitter = BitGet::new(&[0xff, 0x04]);
assert_eq!(bitter.read_bit(), Some(true));
assert_eq!(bitter.read_u8(), Some(0x7f));
```

One will now write:

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
assert_eq!(bitter.read_bit(), Some(true));
assert_eq!(bitter.read_u8(), Some(0x7f));
```

### Support Bit Reads up to 64 bits

Instead of

```rust
assert_eq!(bitter.read_u32_bits(7), Some(0x02));
```

The `read_u32_bits` family has been replaced with:

```rust
assert_eq!(bitter.read_bits(7), Some(0x02));
```

The new API:

- can process process up to 64 bits instead of 32 bits
- comes at no performance cost for 64bit systems

### Support Two's Complement for Arbitrary Bit Widths

The following functions have been removed:

```
read_i32_bits
read_i32_bits_unchecked
```

The use cases for these functions had been extremely limited.

It is more intuitive that when the user requests 3 bits that are
signed that these three bits are treated as 3 bits of two's complement,
meaning that the top bit would make the result negative. To give an
example, if the next three bits are encountered:

```
111
```

Then the result should be -1. Arbitrarily wide two's complement support
had not been possible until today. This functionality is now exposed in
two new functions:

```
read_signed_bits
read_signed_bits_unchecked
```

### Rework `read_bytes` to Accept Mutable Buffer

By moving `read_bytes` to accept a mutable buffer:

- Remove all allocations (hidden or otherwise) from the API
- Increase performance in both aligned and unaligned scenarios

Instead of

```rust
use bitter::BitGet;
let mut bitter = BitGet::new(&[0b1010_1010, 0b0101_0101]);
assert_eq!(
    bitter.read_bytes(2).map(|x| x.into_owned()),
    Some(vec![0b1010_1010, 0b0101_0101])
)
```

write:

```rust
use bitter::{BitReader, LittleEndianReader};
let mut buf = [0u8; 2];
let mut bitter = LittleEndianReader::new(&[0b1010_1010, 0b0101_0101]);
assert!(bitter.read_bytes(&mut buf));
assert_eq!(&buf, &[0b1010_1010, 0b0101_0101]);
```

The new API should be more reminiscent of the Read trait's read method,
which also takes a mutable buffer, but instead of returning a result of
bytes read we know that either we'll fill the entire buffer or there
isn't enough data.

### Other Improvements

- Enable `no_std` builds
- Add `read_f64` and `read_f64_unchecked`
- Bump edition to 2018

## 0.4.1 - 2020-11-21

Maintenance release that trims down the number of files in crate so that the download size is smaller

## 0.4.0 - 2019-12-17

Fix has_bits_remaining at max value to avoid overflow
 
The read_bits_max function is now split into two halves:

- `read_bits_max` which takes one fewer argument
- `read_bits_max_computed` which takes the same arguments but the bits argument should now be one less.

The first justification is that

```
bits.read_bits_max(100);
```

reads better than

```
bits.read_bits_max(7, 100);
```

It's less prone to error. If one were to use the new API with the
incorrect bit width, a debug assertion will fail. Using the single
argument, `read_bits_max`, one can't call it incorrectly.

If one already has the bit width of the max value alread calculated then
use the `read_bits_max_computed` function. Keep in mind it has to
satisfy:

```
max(bit_width(max), 1) == bits + 1);
```

The new APIs and assertions fix a potential underflow when 0 is the max
to value read.

## 0.3.2 - 2019-05-23

* A 10%-50% performance improvement to unchecked API (and checked APIs but to a lesser extent)

## 0.3.1 - 2019-01-30

* In 0.3.0 a performance optimization was used that satisfied valgrind's memcheck but failed LLVM's AddressSanitizer with a heap-buffer-overflow despite the overflowed bytes never being acted upon. This optimization has been removed to increase bitter's friendliness.
* Fix bug in `read_bytes`
* Fix bug in `has_bits_remaining`

## 0.3.0 - 2019-01-23

- Breaking change: `bits_remaining` would exhibit overflow when the data was long enough that counting the number of bits (`data.len() * 8`) would overflow. The API has been changed to return `Option<usize>`. Prefer `has_bits_remaining` instead
- Version 0.2.0 did not live up to performance expectations, so it's implementation has been rolled back. Instead of reverting back to byteorder, which will verify that every 8 byte cache read has enough data to be fulfilled, byteorder's internal implementation can be extracted so that one can always read into the 8 byte cache. While this does load undefined memory into the cache, the undefined bytes are never referenced, which appeases valgrind. The upside is that this simplifies implementation (ie: makes it easier to audit) and improved performance 15-25% over bitter v1.
- Consequently, unchecked APIs now will exhibit undefined behavior if abused instead of panicking.
- Rust 1.26 now required

## 0.2.0 - 2019-01-20

- Remove byteorder dependency (so bitter is dependency free)
- Requires Rust 1.32 or later

## 0.1.0 - 2018-01-25

* Initial release
