        // group.bench_with_input(BenchmarkId::new("bitter-xl-auto", i), &i, |b, param| {
        //     b.iter(|| {
        //         let mut bitter =
        //             LittleEndianReaderXl::new(&DATA[..], (u64::from(i) * ITER) as usize);
        //         bitter.read_bits(1);
        //         if *param <= bitter::MAX_READ_BITS {
        //             for _ in 0..ITER {
        //                 black_box(bitter.read_bits(*param));
        //             }
        //         } else {
        //             for _ in 0..ITER {
        //                 let lo = bitter.read_bits(bitter::MAX_READ_BITS).unwrap();
        //                 let hi_bits = *param - bitter::MAX_READ_BITS;
        //                 let hi = bitter.read_bits(hi_bits).unwrap();
        //                 black_box((hi << bitter::MAX_READ_BITS) + lo);
        //             }
        //         }
        //     })
        // });

        // group.bench_with_input(BenchmarkId::new("bitter-xl-manual", i), &i, |b, param| {
        //     b.iter(|| {
        //         let mut bitter =
        //             LittleEndianReaderXl::new(&DATA[..], (u64::from(i) * ITER) as usize);
        //         bitter.read_bits(1);
        //         manual(bitter, *param);
        //     })
        // });

    // group.bench_function("bitter-xl-auto", |b| {
    //     b.iter(|| {
    //         let mut bits = LittleEndianReaderXl::new(&DATA, (ITER * 8) as usize);
    //         for _ in 0..ITER {
    //             black_box(bits.read_bits(2));
    //             black_box(bits.read_bits(18));
    //             black_box(bits.read_bits(18));
    //             black_box(bits.read_bits(18));
    //         }
    //     })
    // });

    // group.bench_function("bitter-xl-manual", |b| {
    //     b.iter(|| {
    //         let mut bits = LittleEndianReaderXl::new(&DATA, (ITER * 8) as usize);
    //         for _ in 0..ITER {
    //             let len = bits.refill_lookahead();
    //             assert!(len >= 56);

    //             black_box(bits.peek(2));
    //             bits.consume(2);

    //             black_box(bits.peek(18));
    //             bits.consume(18);

    //             black_box(bits.peek(18));
    //             bits.consume(18);

    //             black_box(bits.peek(18));
    //             bits.consume(18);
    //         }
    //     })
    // });

    // group.bench_function("bitter-xl-auto", |b| {
    //     b.iter(|| {
    //         let mut bits = LittleEndianReaderXl::new(&DATA, (ITER * 8) as usize);
    //         for _ in 0..ITER {
    //             black_box(bits.read_bits(4));
    //             black_box(bits.read_bits(1));
    //             black_box(bits.read_bits(19));
    //             black_box(bits.read_bits(19));
    //             black_box(bits.read_bits(19));
    //         }
    //     })
    // });

    // group.bench_function("bitter-xl-manual", |b| {
    //     b.iter(|| {
    //         let mut bits = LittleEndianReaderXl::new(&DATA, (ITER * 8) as usize);
    //         for _ in 0..ITER {
    //             let len = bits.refill_lookahead();
    //             assert!(len >= 24);
    //             black_box(bits.peek(4));
    //             bits.consume(4);

    //             black_box(bits.peek(1));
    //             bits.consume(1);

    //             black_box(bits.peek(19));
    //             bits.consume(19);

    //             let len = bits.refill_lookahead();
    //             assert!(len > 36);
    //             black_box(bits.peek(19));
    //             bits.consume(19);

    //             black_box(bits.peek(19));
    //             bits.consume(19);
    //         }
    //     })
    // });


/*

#[quickcheck]
fn test_xl_read(mut data: Vec<u8>) {
    let old_len = data.len();
    data.extend_from_slice(&[0u8; 8]);

    let mut lebits = LittleEndianReader::new(&data[..old_len]);
    let mut lebits2 = LittleEndianReaderXl::new(&data, old_len);

    while lebits.has_bits_remaining(5) {
        assert!(lebits2.has_bits_remaining(5));
        assert_eq!(lebits.byte_aligned(), lebits2.byte_aligned());
        assert_eq!(lebits2.bits_remaining(), lebits2.bits_remaining());
        assert_eq!(lebits.read_bits(5), lebits2.read_bits(5));
    }

    let mut lebits = LittleEndianReader::new(&data[..old_len]);
    let mut lebits2 = LittleEndianReaderXl::new(&data, old_len);
    while lebits.has_bits_remaining(17) {
        assert_eq!(lebits.refill_lookahead(), lebits2.refill_lookahead());
        assert_eq!(lebits.peek(17), lebits2.peek(17));
        lebits.consume(17);
        lebits2.consume(17);
    }
}

*/


// #[cfg(test)]
// mod xl_tests {
//     use crate::*;

//     fn make_xl(data: &[u8]) -> Vec<u8> {
//         let mut v = Vec::with_capacity(data.len() + 8);
//         v.extend_from_slice(data);
//         v.extend_from_slice(&[0u8; 8]);
//         v
//     }

//     #[test]
//     fn test_byte_reads() {
//         let od: &[u8] = &[0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2];
//         let data = make_xl(&od);
//         let mut bitter = LittleEndianReaderXl::new(&data, od.len());
//         assert_eq!(bitter.read_bits(8), Some(0xff));
//         assert_eq!(bitter.read_bits(8), Some(0xfe));
//         assert_eq!(bitter.read_bits(8), Some(0xfa));
//         assert_eq!(bitter.read_bits(8), Some(0xf7));
//         assert_eq!(bitter.read_bits(8), Some(0xf5));
//         assert_eq!(bitter.read_bits(8), Some(0xf0));
//         assert_eq!(bitter.read_bits(8), Some(0xb1));
//         assert_eq!(bitter.read_bits(8), Some(0xb2));
//         assert_eq!(bitter.read_bits(8), None);
//     }

//     #[test]
//     fn test_manual_mode_xl() {
//         let od: &[u8] = &[0u8; 4];
//         let data = make_xl(&od);

//         let mut lebits = LittleEndianReader::new(&data[..4]);
//         let mut lebits2 = LittleEndianReaderXl::new(&data, 4);

//         assert_eq!(lebits.refill_lookahead(), lebits2.refill_lookahead());
//         assert_eq!(lebits.peek(17), lebits2.peek(17));
//         lebits.consume(17);
//         lebits2.consume(17);
//     }
// }


/*


macro_rules! generate_bitter_end_xl {
    ($(#[$meta:meta])* $name:ident, $which:ident, $shift:tt) => {
        $(#[$meta])*
        pub struct $name<'a> {
            /// Current lookahead buffer contents
            bit_buf: u64,

            /// Pointer of next byte for lookahead
            bit_ptr: *const u8,

            /// One past the last element of the given data
            end_ptr: *const u8,

            /// Number of bits in buffer
            bit_count: u32,

            phantom: ::core::marker::PhantomData<&'a [u8]>,
        }

        impl<'a> $name<'a> {
            #[inline]
            pub fn new(data: &'a [u8], len: usize) -> Self {
                assert!(
                    len + 8 <= data.len(),
                    "an extra large bit reader requires data to be over provisioned by at least 8 bytes"
                );
                let rng = data[..len].as_ptr_range();

                let mut res = Self {
                    bit_ptr: rng.start,
                    end_ptr: rng.end,
                    bit_buf: 0,
                    bit_count: 0,
                    phantom: ::core::marker::PhantomData,
                };

                res.refill();
                res
            }

            base_reader!($which);

            #[inline]
            fn refill(&mut self) -> u32 {
                self.bit_buf |= unsafe { self.read() } $shift self.bit_count;

                let consumed = (63 - (self.bit_count) as usize) >> 3;
                self.bit_ptr = unsafe { self.bit_ptr.add(consumed) };
                if self.bit_ptr <= self.end_ptr {
                    self.bit_count |= MAX_READ_BITS;
                    MAX_READ_BITS
                } else {
                    self.refill_eof(consumed)
                }
            }

            fn refill_eof(&mut self, consumed: usize) -> u32 {
                let prev_ptr = unsafe { self.bit_ptr.sub(consumed) };
                let count = (self.end_ptr as usize) - (prev_ptr as usize);
                self.bit_count += (count as u32) * 8;
                self.bit_ptr = self.end_ptr;
                self.bit_count
            }
        }

        impl<'a> BitReader for $name<'a> {
            base_bit_reader!($name);

            #[inline]
            fn read_bits(&mut self, count: u32) -> Option<u64> {
                if count > self.bit_count && count > self.refill() {
                    return None;
                }

                let result = self.peek(count);
                self.consume(count);
                Some(result)
            }

            #[inline]
            fn refill_lookahead(&mut self) -> u32 {
                self.refill()
            }
        }
    }
}

generate_bitter_end_xl!(
    LittleEndianReaderXl,
    to_le,
    <<
);

impl<'a> LittleEndianReaderXl<'a> {
    #[inline]
    fn peek_(&self, count: u32) -> u64 {
        self.bit_buf & ((1 << count) - 1)
    }

    #[inline]
    fn consume_(&mut self, count: u32) {
        self.bit_buf >>= count;
    }
}

generate_bitter_end_xl!(
    BigEndianReaderXl,
    to_le,
    >>
);

impl<'a> BigEndianReaderXl<'a> {
    #[inline]
    fn peek_(&self, count: u32) -> u64 {
        self.bit_buf >> (BIT_WIDTH - count as usize)
    }

    #[inline]
    fn consume_(&mut self, count: u32) {
        self.bit_buf <<= count;
    }
}

*/