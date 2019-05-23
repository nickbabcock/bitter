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
