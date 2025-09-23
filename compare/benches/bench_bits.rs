use bitreader::BitReader as BR;
use bitstream_io::{BitRead, BitReader as bio_br, LittleEndian};
use bitter::{BitReader, BitWriter, LittleEndianReader, LittleEndianWriter};
use bitvec::{field::BitField, order::Lsb0, view::BitView};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::io::{Cursor, Write};

const ITER: u64 = 1000;

// It may seem like cheating to pass in a constant used for loop unrolling, but
// the whole point of manual and unchecked mode is that one can write code that
// can exploit data patterns and this was a good compromise. This could have
// been cranked up to 11 and have the amount of bits be a constant propagated
// into here, but that seemed unfair.
#[inline]
fn bit_reading<const N: u32, const UNCHECKED: bool, T: BitReader>(mut bitter: T, bits: u32) -> u64 {
    let iterations = ITER / N as u64;
    let mut result = 0;
    for _ in 0..iterations {
        if UNCHECKED {
            unsafe { bitter.refill_lookahead_unchecked() }
        } else {
            bitter.refill_lookahead()
        };

        for _ in 0..N {
            result |= bitter.peek(bits);
            bitter.consume(bits);
        }
    }
    result
}

fn gen_data() -> Vec<u8> {
    std::iter::repeat_with(|| fastrand::u8(..))
        .take(10000)
        .collect()
}

fn bitting(c: &mut Criterion) {
    let parameters: Vec<u32> = (1..65).collect();
    let data = gen_data();

    let mut group = c.benchmark_group("bit-reading");
    for i in parameters {
        group.throughput(Throughput::Bytes((i as u64 * ITER) / 8));

        group.bench_with_input(BenchmarkId::new("bitter-auto", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&data);
                let mut result = bitter.read_bits(1)?;
                for _ in 0..ITER {
                    result |= bitter.read_bits(*param)?;
                }
                Some(result)
            })
        });

        group.bench_with_input(BenchmarkId::new("bitter-manual", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&data);
                bitter.refill_lookahead();
                bitter.consume(1);
                match *param {
                    1..=3 => bit_reading::<16, false, _>(bitter, *param),
                    4..=7 => bit_reading::<8, false, _>(bitter, *param),
                    8..=14 => bit_reading::<4, false, _>(bitter, *param),
                    15..=28 => bit_reading::<2, false, _>(bitter, *param),
                    29..=56 => bit_reading::<1, false, _>(bitter, *param),
                    x => {
                        let mut result = 0;
                        for _ in 0..ITER {
                            bitter.refill_lookahead();
                            let lo = bitter.peek(bitter::MAX_READ_BITS);
                            bitter.consume(bitter::MAX_READ_BITS);

                            let hi_bits = x - bitter::MAX_READ_BITS;
                            bitter.refill_lookahead();

                            let hi = bitter.peek(hi_bits);
                            bitter.consume(hi_bits);

                            let read = (hi << bitter::MAX_READ_BITS) + lo;
                            result |= read;
                        }
                        result
                    }
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitter-unchecked", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&data);
                unsafe { bitter.refill_lookahead_unchecked() };
                bitter.consume(1);
                match *param {
                    1..=3 => bit_reading::<16, true, _>(bitter, *param),
                    4..=7 => bit_reading::<8, true, _>(bitter, *param),
                    8..=14 => bit_reading::<4, true, _>(bitter, *param),
                    15..=28 => bit_reading::<2, true, _>(bitter, *param),
                    29..=56 => bit_reading::<1, true, _>(bitter, *param),
                    x => {
                        let mut result = 0;
                        for _ in 0..ITER {
                            unsafe { bitter.refill_lookahead_unchecked() }

                            let lo = bitter.peek(bitter::MAX_READ_BITS);
                            bitter.consume(bitter::MAX_READ_BITS);

                            let hi_bits = x - bitter::MAX_READ_BITS;
                            unsafe { bitter.refill_lookahead_unchecked() }

                            let hi = bitter.peek(hi_bits);
                            bitter.consume(hi_bits);

                            let read = (hi << bitter::MAX_READ_BITS) + lo;
                            result |= read;
                        }
                        result
                    }
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitreader", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = BR::new(&data);
                let mut result = bitter.read_u64(1)?;
                for _ in 0..ITER {
                    result |= bitter.read_u64(*param as u8)?;
                }
                let result: bitreader::Result<u64> = Ok(result);
                result
            })
        });

        group.bench_with_input(BenchmarkId::new("bitstream-io", i), &i, |b, param| {
            b.iter(|| {
                let mut cursor = Cursor::new(&data[..]);
                {
                    let mut bits = bio_br::endian(&mut cursor, LittleEndian);
                    let mut result = bits.read::<1, u64>()?;
                    for _ in 0..ITER {
                        result |= bits.read_var::<u64>(*param)?;
                    }
                    let result: Result<u64, std::io::Error> = Ok(result);
                    result
                }
            });
        });

        group.bench_with_input(BenchmarkId::new("bitvec", i), &i, |b, param| {
            b.iter(|| {
                let mut bits = data.view_bits::<Lsb0>();
                bits = &bits[1..];
                let mut result = 0;
                for _ in 0..ITER {
                    let (curr, next) = bits.split_at(*param as usize);
                    result |= curr.load_le::<u64>();
                    bits = next;
                }
                Some(result)
            })
        });

        group.bench_with_input(BenchmarkId::new("bitbuffer", i), &i, |b, param| {
            b.iter(|| {
                let buffer = bitbuffer::BitReadBuffer::new(&data, bitbuffer::LittleEndian);
                let mut stream = bitbuffer::BitReadStream::new(buffer);
                stream.skip_bits(1)?;
                let mut result = 0;
                for _ in 0..ITER {
                    result |= stream.read_int::<u64>(*param as usize)?;
                }
                let result: bitbuffer::Result<u64> = Ok(result);
                result
            })
        });

        group.bench_with_input(BenchmarkId::new("bitcursor", i), &i, |b, param| {
            b.iter(|| {
                let mut cursor = llvm_bitcursor::BitCursor::new(&data);
                let mut result = cursor.read(1)?;

                // bitcursor does not support 64 bit reads
                if *param == 64 {
                    for _ in 0..ITER {
                        result |= cursor.read(63)?;
                        result |= cursor.read(1)? << 63;
                    }
                } else {
                    for _ in 0..ITER {
                        result |= cursor.read(*param as usize)?;
                    }
                }

                Ok::<_, llvm_bitcursor::error::Error>(result)
            })
        });
    }

    group.finish();
}

fn real_world1(c: &mut Criterion) {
    // Parse a rocket league Quaternion, which is bit reads of 2 + 18 + 18 + 18 = 56;
    let mut group = c.benchmark_group("real-world-1");

    let data = gen_data();

    group.throughput(Throughput::Bytes((56 * ITER) / 8));

    group.bench_function("bitter-auto", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                let a = bits.read_bits(2)?;
                let b = bits.read_bits(18)?;
                let c = bits.read_bits(18)?;
                let d = bits.read_bits(18)?;
                result |= a + b + c + d;
            }
            Some(result)
        })
    });

    group.bench_function("bitter-manual", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                bits.refill_lookahead();

                if bits.lookahead_bits() < 56 {
                    return None;
                }

                let a = bits.peek(2);
                bits.consume(2);

                let b = bits.peek(18);
                bits.consume(18);

                let c = bits.peek(18);
                bits.consume(18);

                let d = bits.peek(18);
                bits.consume(18);

                result |= a + b + c + d;
            }
            Some(result)
        })
    });

    group.bench_function("bitter-unchecked", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                unsafe { bits.refill_lookahead_unchecked() };

                let a = bits.peek(2);
                bits.consume(2);

                let b = bits.peek(18);
                bits.consume(18);

                let c = bits.peek(18);
                bits.consume(18);

                let d = bits.peek(18);
                bits.consume(18);

                result |= a + b + c + d;
            }
            result
        })
    });

    group.bench_function("bitreader", |b| {
        b.iter(|| {
            let mut bits = BR::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                let a = bits.read_u8(2)? as u64;
                let b = bits.read_u32(18)? as u64;
                let c = bits.read_u32(18)? as u64;
                let d = bits.read_u32(18)? as u64;
                result |= a + b + c + d;
            }
            let result: bitreader::Result<u64> = Ok(result);
            result
        })
    });

    group.bench_function("bitstream-io", |b| {
        b.iter(|| {
            let mut cursor = Cursor::new(&data[..]);
            {
                let mut bits = bio_br::endian(&mut cursor, LittleEndian);
                let mut result = 0;
                for _ in 0..ITER {
                    let a = bits.read::<2, u8>()? as u64;
                    let b = bits.read::<18, u32>()? as u64;
                    let c = bits.read::<18, u32>()? as u64;
                    let d = bits.read::<18, u32>()? as u64;
                    result |= a + b + c + d;
                }
                let result: Result<u64, std::io::Error> = Ok(result);
                result
            }
        })
    });

    group.bench_function("bitvec", |b| {
        b.iter(|| {
            let mut bits = data.view_bits::<Lsb0>();
            let mut result = 0;
            for _ in 0..ITER {
                let (curr, next) = bits.split_at(2);
                let a = curr.load_le::<u64>();
                bits = next;

                let (curr, next) = bits.split_at(18);
                let b = curr.load_le::<u64>();
                bits = next;

                let (curr, next) = bits.split_at(18);
                let c = curr.load_le::<u64>();
                bits = next;

                let (curr, next) = bits.split_at(18);
                let d = curr.load_le::<u64>();
                bits = next;

                result |= a + b + c + d;
            }
            Some(result)
        })
    });

    group.bench_function("bitbuffer", |b| {
        b.iter(|| {
            let buffer = bitbuffer::BitReadBuffer::new(&data, bitbuffer::LittleEndian);
            let mut stream = bitbuffer::BitReadStream::new(buffer);
            let mut result = 0;
            for _ in 0..ITER {
                let a = stream.read_int::<u64>(2)?;
                let b = stream.read_int::<u64>(18)?;
                let c = stream.read_int::<u64>(18)?;
                let d = stream.read_int::<u64>(18)?;
                result |= a + b + c + d;
            }
            let result: bitbuffer::Result<u64> = Ok(result);
            result
        })
    });

    group.bench_function("bitcursor", |b| {
        b.iter(|| {
            let mut cursor = llvm_bitcursor::BitCursor::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                let a = cursor.read(2)?;
                let b = cursor.read(18)?;
                let c = cursor.read(18)?;
                let d = cursor.read(18)?;
                result |= a + b + c + d;
            }
            Ok::<_, llvm_bitcursor::error::Error>(result)
        })
    });

    group.finish();
}

fn real_world2(c: &mut Criterion) {
    // Parse a rocket league Vector3i (simiplified)
    let mut group = c.benchmark_group("real-world-2");

    let data = gen_data();
    group.throughput(Throughput::Bytes((62 * ITER) / 8));

    group.bench_function("bitter-auto", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                let a = bits.read_bits(4)?;
                let b = bits.read_bits(1)?;
                let c = bits.read_bits(19)?;
                let d = bits.read_bits(19)?;
                let e = bits.read_bits(19)?;
                result |= a + b + c + d + e;
            }
            Some(result)
        })
    });

    group.bench_function("bitter-manual", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                bits.refill_lookahead();
                if bits.lookahead_bits() < 24 {
                    return None;
                }
                let a = bits.peek(4);
                bits.consume(4);

                let b = bits.peek(1);
                bits.consume(1);

                let c = bits.peek(19);
                bits.consume(19);

                bits.refill_lookahead();
                assert!(bits.lookahead_bits() > 36);
                let d = bits.peek(19);
                bits.consume(19);

                let e = bits.peek(19);
                bits.consume(19);
                result |= a + b + c + d + e;
            }
            Some(result)
        })
    });

    group.bench_function("bitter-unchecked", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                unsafe { bits.refill_lookahead_unchecked() };

                let a = bits.peek(4);
                bits.consume(4);

                let b = bits.peek(1);
                bits.consume(1);

                let c = bits.peek(19);
                bits.consume(19);

                unsafe { bits.refill_lookahead_unchecked() };

                let d = bits.peek(19);
                bits.consume(19);

                let e = bits.peek(19);
                bits.consume(19);
                result |= a + b + c + d + e;
            }
            result
        })
    });

    group.finish();
}

fn read_bytes(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_bytes");
    let data = gen_data();

    for i in &[4, 8, 16, 80, 240, 960] {
        let iterations = (data.len() / *i) - 1;
        group.throughput(Throughput::Bytes((iterations * *i) as u64));

        group.bench_with_input(BenchmarkId::new("aligned", i), &i, |b, param| {
            let mut buf = vec![0u8; **param];
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&data);
                let mut result = true;
                for _ in 0..iterations {
                    result &= bitter.read_bytes(&mut buf);
                }
                result
            })
        });

        group.bench_with_input(BenchmarkId::new("unaligned", i), &i, |b, param| {
            let mut buf = vec![0u8; **param];
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&data);
                bitter.read_bit();
                let mut result = true;
                for _ in 0..iterations {
                    result &= bitter.read_bytes(&mut buf);
                }
                result
            })
        });
    }

    group.finish();
}

fn signed(c: &mut Criterion) {
    let mut group = c.benchmark_group("signed_reads");

    let data = gen_data();
    let bits_to_read = 33;
    group.throughput(Throughput::Bytes((bits_to_read as u64 * ITER) / 8));

    group.bench_function("auto", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                result |= bits.read_signed_bits(bits_to_read)?;
            }
            Some(result)
        })
    });

    group.bench_function("manual", |b| {
        b.iter(|| {
            let mut bits = LittleEndianReader::new(&data);
            let mut result = 0;
            for _ in 0..ITER {
                bits.refill_lookahead();
                let val = bits.peek(bits_to_read);
                bits.consume(bits_to_read);
                result |= bitter::sign_extend(val, bits_to_read);
            }
            result
        })
    });

    group.finish();
}

fn random_bit_reads(c: &mut Criterion) {
    let mut group = c.benchmark_group("random");

    // Generate 1000 random bit read sizes between 1 and 63
    let bit_read_requests: Vec<u32> = (0..1000).map(|_| fastrand::u32(1..=63)).collect();

    // Calculate total bits to ensure we have enough data
    let total_bits: u32 = bit_read_requests.iter().sum();
    let required_bytes = total_bits.div_ceil(8) as usize + 1000;
    let data: Vec<u8> = std::iter::repeat_with(|| fastrand::u8(..))
        .take(required_bytes)
        .collect();

    group.throughput(Throughput::Bytes(total_bits as u64 / 8));

    group.bench_function("bitter-auto", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&data);
            let mut result = 0u64;
            for &bits in &bit_read_requests {
                let val = bitter.read_bits(bits)?;
                result = result.wrapping_add(val);
            }
            Some(result)
        })
    });

    group.bench_function("bitter-manual", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&data);
            let mut result = 0u64;

            for &bits_to_read in &bit_read_requests {
                if bits_to_read <= bitter::MAX_READ_BITS {
                    if bits_to_read > bitter.lookahead_bits() {
                        bitter.refill_lookahead();
                    }
                    let val = bitter.peek(bits_to_read);
                    bitter.consume(bits_to_read);
                    result = result.wrapping_add(val);
                } else {
                    // Handle large reads by stitching together multiple reads
                    let lo_bits = bitter::MAX_READ_BITS;
                    let hi_bits = bits_to_read - bitter::MAX_READ_BITS;

                    bitter.refill_lookahead();
                    let lo = bitter.peek(lo_bits);
                    bitter.consume(lo_bits);

                    bitter.refill_lookahead();
                    let hi = bitter.peek(hi_bits);
                    bitter.consume(hi_bits);

                    let val = (hi << bitter::MAX_READ_BITS) + lo;
                    result = result.wrapping_add(val);
                }
            }
            result
        })
    });

    group.bench_function("bitter-unchecked", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&data);
            let mut result = 0u64;

            for &bits_to_read in &bit_read_requests {
                if bits_to_read <= bitter::MAX_READ_BITS {
                    if bits_to_read > bitter.lookahead_bits() {
                        unsafe { bitter.refill_lookahead_unchecked() };
                    }
                    let val = bitter.peek(bits_to_read);
                    bitter.consume(bits_to_read);
                    result = result.wrapping_add(val);
                } else {
                    // Handle large reads by stitching together multiple reads
                    let lo_bits = bitter::MAX_READ_BITS;
                    let hi_bits = bits_to_read - bitter::MAX_READ_BITS;

                    unsafe { bitter.refill_lookahead_unchecked() };
                    let lo = bitter.peek(lo_bits);
                    bitter.consume(lo_bits);

                    unsafe { bitter.refill_lookahead_unchecked() };
                    let hi = bitter.peek(hi_bits);
                    bitter.consume(hi_bits);

                    let val = (hi << bitter::MAX_READ_BITS) + lo;
                    result = result.wrapping_add(val);
                }
            }
            result
        })
    });

    group.bench_function("bitreader", |b| {
        b.iter(|| {
            let mut bitter = BR::new(&data);
            let mut result = 0u64;
            for &bits in &bit_read_requests {
                let val = bitter.read_u64(bits as u8)?;
                result = result.wrapping_add(val);
            }
            Ok::<_, bitreader::BitReaderError>(result)
        })
    });

    group.bench_function("bitstream-io", |b| {
        b.iter(|| {
            let mut cursor = Cursor::new(&data[..]);
            let mut bits = bio_br::endian(&mut cursor, LittleEndian);
            let mut result = 0u64;
            for &bits_to_read in &bit_read_requests {
                let val = bits.read_var::<u64>(bits_to_read)?;
                result = result.wrapping_add(val);
            }
            Ok::<_, std::io::Error>(result)
        })
    });

    group.bench_function("bitvec", |b| {
        b.iter(|| {
            let mut bits_view = data.view_bits::<Lsb0>();
            let mut result = 0u64;
            for &bits_to_read in &bit_read_requests {
                if bits_view.len() >= bits_to_read as usize {
                    let (curr, next) = bits_view.split_at(bits_to_read as usize);
                    let val = curr.load_le::<u64>();
                    result = result.wrapping_add(val);
                    bits_view = next;
                }
            }
            result
        })
    });

    group.bench_function("bitbuffer", |b| {
        b.iter(|| {
            let buffer = bitbuffer::BitReadBuffer::new(&data, bitbuffer::LittleEndian);
            let mut stream = bitbuffer::BitReadStream::new(buffer);
            let mut result = 0u64;
            for &bits_to_read in &bit_read_requests {
                let val = stream.read_int::<u64>(bits_to_read as usize)?;
                result = result.wrapping_add(val);
            }
            Ok::<_, bitbuffer::BitError>(result)
        })
    });

    group.bench_function("bitcursor", |b| {
        b.iter(|| {
            let mut cursor = llvm_bitcursor::BitCursor::new(&data);
            let mut result = 0u64;
            for &bits_to_read in &bit_read_requests {
                let val = cursor.read(bits_to_read as usize)?;
                result = result.wrapping_add(val);
            }
            Ok::<_, llvm_bitcursor::error::Error>(result)
        })
    });

    group.finish();
}

fn write_bytes(c: &mut Criterion) {
    let data = gen_data();

    let mut group = c.benchmark_group("write_bytes");


    for i in &[4, 8, 16, 80, 240, 960] {
        let iterations = (data.len() / *i) - 1;
        group.throughput(Throughput::Bytes((iterations * *i) as u64));

        group.bench_with_input(BenchmarkId::new("aligned", i), &i, |b, param| {
            let mut buf = vec![0u8; **param];
            b.iter(|| {
                let mut bitter = LittleEndianWriter::new(&mut buf);
                for _ in 0..iterations {
                    bitter.write_bytes(&data)?;
                }

                Ok::<_, std::io::Error>(())
            })
        });

        group.bench_with_input(BenchmarkId::new("unaligned", i), &i, |b, param| {
            let mut buf = vec![0u8; **param];
            b.iter(|| {
                let mut bitter = LittleEndianWriter::new(&mut buf);
                bitter.write_bit(true);
                for _ in 0..iterations {
                    bitter.write_bytes(&data)?;
                }

                Ok::<_, std::io::Error>(())
            })
        });
    }

    group.finish();

}

criterion_group!(
    benches,
    bitting,
    real_world1,
    real_world2,
    read_bytes,
    signed,
    random_bit_reads,
    write_bytes
);

criterion_main!(benches);
