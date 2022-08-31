use bitreader::BitReader as BR;
use bitstream_io::{BitRead, BitReader as bio_br, LittleEndian};
use bitter;
use bitter::{BitReader, LittleEndianReader};
use bitvec::{field::BitField, order::Lsb0, view::BitView};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::io::Cursor;

static DATA: [u8; 0x10_000] = [0; 0x10_000];

const ITER: u64 = 1000;

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
                const X1: u32 = bitter::MAX_READ_BITS / 4;
                const X11: u32 = X1 + 1;
                const X2: u32 = bitter::MAX_READ_BITS / 2;
                const X21: u32 = X2 + 1;
                match *param {
                    x @ 0..=X1 => {
                        let runs = x * 4;
                        let mut len = bitter.refill_lookahead();
                        for _ in 0..(ITER / 4) {
                            if len < runs {
                                len = bitter.refill_lookahead();
                            }
            
                            black_box(bitter.peek(x));
                            bitter.consume(x);
            
                            black_box(bitter.peek(x));
                            bitter.consume(x);
            
                            black_box(bitter.peek(x));
                            bitter.consume(x);
            
                            black_box(bitter.peek(x));
                            bitter.consume(x);
                            len -= runs;
                        }
                    }
                    x @ X11..=X2 => {
                        let runs = x * 2;
                        let mut len = bitter.refill_lookahead();
                        for _ in 0..(ITER / 2) {
                            if len < runs {
                                len = bitter.refill_lookahead();
                            }
            
                            black_box(bitter.peek(x));
                            bitter.consume(x);
            
                            black_box(bitter.peek(x));
                            bitter.consume(x);
            
                            len -= runs;
                        }
                    }
                    x @ X21..=bitter::MAX_READ_BITS => {
                        for _ in 0..ITER {
                            bitter.refill_lookahead();
                            black_box(bitter.peek(x));
                            bitter.consume(x);
                        }
                    }
                    x => {
                        for _ in 0..ITER {
                            bitter.refill_lookahead();
                            let lo = bitter.peek(bitter::MAX_READ_BITS);
                            bitter.consume(bitter::MAX_READ_BITS);
            
                            let hi_bits = x - bitter::MAX_READ_BITS;
                            bitter.refill_lookahead();
            
                            let hi = bitter.peek(hi_bits);
                            bitter.consume(hi_bits);
            
                            black_box((hi << bitter::MAX_READ_BITS) + lo);
                        }
                    }
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitter-unchecked", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                bitter.read_bits(1);

                const X1: u32 = bitter::MAX_READ_BITS / 4;
                const X11: u32 = X1 + 1;
                const X2: u32 = bitter::MAX_READ_BITS / 2;
                const X21: u32 = X2 + 1;
                match *param {
                    x @ 0..=X1 => {
                        let runs = x * 4;
                        unsafe { bitter.refill_lookahead_unchecked() }
                        let mut len = bitter::MAX_READ_BITS;
                        for _ in 0..(ITER / 4) {
                            if len < runs {
                                unsafe { bitter.refill_lookahead_unchecked() }
                                len = bitter::MAX_READ_BITS;
                            }

                            black_box(bitter.peek(x));
                            bitter.consume(x);

                            black_box(bitter.peek(x));
                            bitter.consume(x);

                            black_box(bitter.peek(x));
                            bitter.consume(x);

                            black_box(bitter.peek(x));
                            bitter.consume(x);
                            len -= runs;
                        }
                    }
                    x @ X11..=X2 => {
                        let runs = x * 2;
                        unsafe { bitter.refill_lookahead_unchecked() }
                        let mut len = bitter::MAX_READ_BITS;
                        for _ in 0..(ITER / 2) {
                            if len < runs {
                                unsafe { bitter.refill_lookahead_unchecked() }
                                len = bitter::MAX_READ_BITS;
                            }

                            black_box(bitter.peek(x));
                            bitter.consume(x);

                            black_box(bitter.peek(x));
                            bitter.consume(x);

                            len -= runs;
                        }
                    }
                    x @ X21..=bitter::MAX_READ_BITS => {
                        for _ in 0..ITER {
                            unsafe { bitter.refill_lookahead_unchecked() }
                            black_box(bitter.peek(x));
                            bitter.consume(x);
                        }
                    }
                    x => {
                        for _ in 0..ITER {
                            unsafe { bitter.refill_lookahead_unchecked() }

                            let lo = bitter.peek(bitter::MAX_READ_BITS);
                            bitter.consume(bitter::MAX_READ_BITS);

                            let hi_bits = x - bitter::MAX_READ_BITS;
                            unsafe { bitter.refill_lookahead_unchecked() }

                            let hi = bitter.peek(hi_bits);
                            bitter.consume(hi_bits);

                            black_box((hi << bitter::MAX_READ_BITS) + lo);
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

criterion_group!(benches, bitting,);

criterion_main!(benches);
