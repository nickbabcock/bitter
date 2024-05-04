use bitreader::BitReader as BR;
use bitstream_io::{BitRead, BitReader as bio_br, LittleEndian};
use bitter;
use bitter::{BitReader, LittleEndianReader};
use bitvec::{field::BitField, order::Lsb0, view::BitView};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::io::Cursor;

static DATA: [u8; 0x10_000] = [0; 0x10_000];

const ITER: u64 = 1000;

// It may seem like cheating to pass in a constant used for loop unrolling, but
// the whole point of manual and unchecked mode is that one can write code that
// can exploit data patterns and this was a good compromise. This could have
// been cranked up to 11 and have the amount of bits be a constant propagated
// into here, but that seemed unfair.
fn bit_reading<const N: u32, const UNCHECKED: bool, T: BitReader>(mut bitter: T, bits: u32) {
    let iterations = ITER / N as u64;
    for _ in 0..iterations {
        if UNCHECKED {
            unsafe { bitter.refill_lookahead_unchecked() }
        } else {
            bitter.refill_lookahead()
        };

        for _ in 0..N {
            black_box(bitter.peek(bits));
            bitter.consume(bits);
        }
    }
}

fn bitting(c: &mut Criterion) {
    let parameters: Vec<u32> = (1..65).collect();

    let mut group = c.benchmark_group("bit-reading");
    for i in parameters {
        group.throughput(Throughput::Bytes((i as u64 * ITER) / 8));

        group.bench_with_input(BenchmarkId::new("bitter-auto", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                bitter.read_bits(1);
                if *param <= bitter::MAX_READ_BITS {
                    for _ in 0..ITER {
                        black_box(bitter.read_bits(*param));
                    }
                } else {
                    for _ in 0..ITER {
                        let lo = bitter.read_bits(bitter::MAX_READ_BITS).unwrap();
                        let hi_bits = *param - bitter::MAX_READ_BITS;
                        let hi = bitter.read_bits(hi_bits).unwrap();
                        black_box((hi << bitter::MAX_READ_BITS) + lo);
                    }
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitter-manual", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                bitter.read_bits(1);
                match *param {
                    1..=3 => bit_reading::<16, false, _>(bitter, *param),
                    4..=7 => bit_reading::<8, false, _>(bitter, *param),
                    8..=14 => bit_reading::<4, false, _>(bitter, *param),
                    15..=28 => bit_reading::<2, false, _>(bitter, *param),
                    29..=56 => bit_reading::<1, false, _>(bitter, *param),
                    x => {
                        for _ in 0..ITER {
                            let lo_len = bitter.lookahead_bits();
                            let lo = bitter.peek(lo_len);
                            bitter.consume(lo_len);

                            bitter.refill_lookahead();
                            let left = x - lo_len;
                            let hi_len = bitter.lookahead_bits().min(left);
                            let hi = bitter.peek(hi_len);
                            bitter.consume(hi_len);

                            if hi_len == left {
                                black_box((hi << lo_len) + lo);
                            } else {
                                bitter.refill_lookahead();
                                let left = x - lo_len - hi_len;
                                let hi2 = bitter.peek(left);
                                bitter.consume(left);
                                black_box((hi2 << (lo_len + hi_len)) + (hi << lo_len) + lo);
                            }
                        }
                    }
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitter-unchecked", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                bitter.read_bits(1);
                match *param {
                    1..=3 => bit_reading::<16, true, _>(bitter, *param),
                    4..=7 => bit_reading::<8, true, _>(bitter, *param),
                    8..=14 => bit_reading::<4, true, _>(bitter, *param),
                    15..=28 => bit_reading::<2, true, _>(bitter, *param),
                    29..=56 => bit_reading::<1, true, _>(bitter, *param),
                    x => {
                        for _ in 0..ITER {
                            let lo_len = bitter.lookahead_bits();
                            let lo = bitter.peek(lo_len);
                            bitter.consume(lo_len);

                            unsafe { bitter.refill_lookahead_unchecked() };
                            let left = x - lo_len;
                            let hi_len = bitter.lookahead_bits().min(left);
                            let hi = bitter.peek(hi_len);
                            bitter.consume(hi_len);

                            if hi_len == left {
                                black_box((hi << lo_len) + lo);
                            } else {
                                unsafe { bitter.refill_lookahead_unchecked() };
                                let left = x - lo_len - hi_len;
                                let hi2 = bitter.peek(left);
                                bitter.consume(left);
                                black_box((hi2 << (lo_len + hi_len)) + (hi << lo_len) + lo);
                            }
                        }
                    }
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitreader", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = BR::new(&DATA);
                bitter.read_u32(1).unwrap();
                for _ in 0..ITER {
                    black_box(bitter.read_u64(*param as u8).unwrap());
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitstream-io", i), &i, |b, param| {
            b.iter(|| {
                let mut cursor = Cursor::new(&DATA[..]);
                {
                    let mut bits = bio_br::endian(&mut cursor, LittleEndian);
                    bits.read_bit().unwrap();
                    for _ in 0..ITER {
                        black_box(bits.read::<u64>(*param as u32).unwrap());
                    }
                }
            });
        });

        group.bench_with_input(BenchmarkId::new("bitvec", i), &i, |b, param| {
            b.iter(|| {
                let mut bits = DATA.view_bits::<Lsb0>();
                bits = &bits[1..];
                for _ in 0..ITER {
                    let (curr, next) = bits.split_at(*param as usize);
                    black_box(curr.load_le::<u64>());
                    bits = next;
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitbuffer", i), &i, |b, param| {
            b.iter(|| {
                let buffer = bitbuffer::BitReadBuffer::new(&DATA[..], bitbuffer::LittleEndian);
                let mut stream = bitbuffer::BitReadStream::new(buffer);
                stream.skip_bits(1).unwrap();
                for _ in 0..ITER {
                    black_box(stream.read_int::<u64>(*param as usize).unwrap());
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitcursor", i), &i, |b, param| {
            b.iter(|| {
                let mut cursor = llvm_bitcursor::BitCursor::new(&DATA[..]);
                cursor.read(1).unwrap();

                // bitcursor does not support 64 bit reads
                if *param == 64 {
                    for _ in 0..ITER {
                        black_box(cursor.read(63).unwrap() + (cursor.read(1).unwrap() << 63));
                    }
                } else {
                    for _ in 0..ITER {
                        black_box(cursor.read(*param as usize).unwrap());
                    }
                }
            })
        });
    }

    group.finish();
}

fn real_world1(c: &mut Criterion) {
    // Parse a rocket league Quaternion, which is bit reads of 2 + 18 + 18 + 18 = 56;
    let mut group = c.benchmark_group("real-world-1");

    group.throughput(Throughput::Bytes((56 as u64 * ITER) / 8));

    group.bench_function("bitter-auto", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&DATA);
            for _ in 0..ITER {
                black_box(bits.read_bits(2));
                black_box(bits.read_bits(18));
                black_box(bits.read_bits(18));
                black_box(bits.read_bits(18));
            }
        })
    });

    group.bench_function("bitter-manual", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&DATA);
            for _ in 0..ITER {
                bits.refill_lookahead();
                assert!(bits.lookahead_bits() >= bitter::MAX_READ_BITS);

                black_box(bits.peek(2));
                bits.consume(2);

                black_box(bits.peek(18));
                bits.consume(18);

                black_box(bits.peek(18));
                bits.consume(18);

                black_box(bits.peek(18));
                bits.consume(18);
            }
        })
    });

    group.bench_function("bitter-unchecked", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&DATA);
            for _ in 0..ITER {
                unsafe { bits.refill_lookahead_unchecked() };

                black_box(bits.peek(2));
                bits.consume(2);

                black_box(bits.peek(18));
                bits.consume(18);

                black_box(bits.peek(18));
                bits.consume(18);

                black_box(bits.peek(18));
                bits.consume(18);
            }
        })
    });

    group.finish();
}

fn real_world2(c: &mut Criterion) {
    // Parse a rocket league Vector3i (simiplified)
    let mut group = c.benchmark_group("real-world-2");

    group.throughput(Throughput::Bytes((62 as u64 * ITER) / 8));

    group.bench_function("bitter-auto", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&DATA);
            for _ in 0..ITER {
                black_box(bits.read_bits(4));
                black_box(bits.read_bits(1));
                black_box(bits.read_bits(19));
                black_box(bits.read_bits(19));
                black_box(bits.read_bits(19));
            }
        })
    });

    group.bench_function("bitter-manual", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&DATA);
            for _ in 0..ITER {
                bits.refill_lookahead();
                assert!(bits.lookahead_bits() >= 24);
                black_box(bits.peek(4));
                bits.consume(4);

                black_box(bits.peek(1));
                bits.consume(1);

                black_box(bits.peek(19));
                bits.consume(19);

                bits.refill_lookahead();
                assert!(bits.lookahead_bits() > 36);
                black_box(bits.peek(19));
                bits.consume(19);

                black_box(bits.peek(19));
                bits.consume(19);
            }
        })
    });

    group.bench_function("bitter-unchecked", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&DATA);
            for _ in 0..ITER {
                unsafe { bits.refill_lookahead_unchecked() };

                black_box(bits.peek(4));
                bits.consume(4);

                black_box(bits.peek(1));
                bits.consume(1);

                black_box(bits.peek(19));
                bits.consume(19);

                unsafe { bits.refill_lookahead_unchecked() };

                black_box(bits.peek(19));
                bits.consume(19);

                black_box(bits.peek(19));
                bits.consume(19);
            }
        })
    });

    group.finish();
}

fn read_bytes(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_bytes");

    for i in &[5, 20, 80, 240, 960] {
        let iterations = DATA.len() / *i;
        group.throughput(Throughput::Bytes((iterations * *i) as u64));

        group.bench_with_input(BenchmarkId::new("aligned", i), &i, |b, param| {
            let mut buf = vec![0u8; **param];
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                for _ in 0..iterations {
                    assert!(black_box(bitter.read_bytes(&mut buf)));
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("unaligned", i), &i, |b, param| {
            let mut buf = vec![0u8; **param];
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                bitter.read_bit();
                for _ in 0..iterations {
                    assert!(black_box(bitter.read_bytes(&mut buf)));
                }
            })
        });
    }

    group.finish();
}

fn signed(c: &mut Criterion) {
    let mut group = c.benchmark_group("signed_reads");

    let bits_to_read = 33;
    group.throughput(Throughput::Bytes((bits_to_read as u64 * ITER) / 8));

    group.bench_function("auto", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bits.read_signed_bits(bits_to_read));
            }
        })
    });

    group.bench_function("manual", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                let _len = bits.refill_lookahead();
                let val = bits.peek(bits_to_read);
                bits.consume(bits_to_read);
                black_box(bitter::sign_extend(val, bits_to_read));
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bitting,
    real_world1,
    real_world2,
    read_bytes,
    signed
);

criterion_main!(benches);
