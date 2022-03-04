# Bitter

***Reading bits until the bitter end***

![ci](https://github.com/nickbabcock/bitter/workflows/ci/badge.svg) [![](https://docs.rs/bitter/badge.svg)](https://docs.rs/bitter) [![Version](https://img.shields.io/crates/v/bitter.svg?style=flat-square)](https://crates.io/crates/bitter)

Bitter takes a slice of byte data and reads bits in a desired endian format platform agonistically.

## Features

 - ✔ support for little endian, big endian, and native endian formats
 - ✔ request an arbitrary amount of bits (up to 64 bits)
 - ✔ ergonomic requests for common data types (eg: `u8` ... `u64`, `f32`, etc)
 - ✔ > 5 GB/s throughput when reading large number of bits
 - ✔ > 1 GB/s throughput when reading single digit sized chunks of bits
 - ✔ two APIs: one for safety and one for speed
 - ✔ zero allocations
 - ✔ zero dependencies
 - ✔ `no_std` compatible

## Example

```rust
use bitter::{BitReader, LittleEndianReader};
let mut bitter = LittleEndianReader::new(&[0xff, 0x04]);
assert_eq!(bitter.read_bit(), Some(true));
assert_eq!(bitter.read_u8(), Some(0x7f));
assert_eq!(bitter.read_bits(7), Some(0x02));
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
    assert_eq!(bitter.read_bits_unchecked(7), 0x02);
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

## Comparison to other libraries

Bitter is hardly the first Rust library for handling bits.
[nom](https://crates.io/crates/nom),
[bitvec](https://github.com/bitvecto-rs/bitvec),
[bitstream_io](https://crates.io/crates/bitstream-io), and
[bitreader](https://crates.io/crates/bitreader) are all crates that deal with bit reading.
The reason why someone would choose bitter is speed.

![bench-bit-reads.png](assets/bench-bit-reads.png)

Takeaways:

* Bitter unchecked APIs yield the greatest throughput (reads per second)
* Bitter checked APIs cost less than half the throughput of bitter unchecked APIs
* Bitter is the fastest Rust bit reading library

## Benchmarking

Benchmarks are ran with the following command:

```bash
(cd compare && cargo clean && RUSTFLAGS="-C target-cpu=native" cargo bench)
find ./compare/target -path "*bit-reading*" -wholename "*/new/raw.csv" -print0 \
  | xargs -0 xsv cat rows > assets/bitter-benchmark-data.csv
```

And can be analyzed with the R script found in the assets directory. Keep in mind, benchmarks will vary by machine
