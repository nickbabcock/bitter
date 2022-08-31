use bitter::{BitReader, LittleEndianReader};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

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
                let len = bits.refill_lookahead();
                assert!(len >= bitter::MAX_READ_BITS);

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
                let len = bits.refill_lookahead();
                assert!(len >= 24);
                black_box(bits.peek(4));
                bits.consume(4);

                black_box(bits.peek(1));
                bits.consume(1);

                black_box(bits.peek(19));
                bits.consume(19);

                let len = bits.refill_lookahead();
                assert!(len > 36);
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

    group.bench_function("aligned", |b| {
        b.iter(|| {
            let mut buf = [0u8; 7];
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bytes(&mut buf));
            }
        })
    });

    group.bench_function("unaligned", |b| {
        b.iter(|| {
            let mut buf = [0u8; 7];
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            bitter.read_bit();
            for _ in 0..ITER {
                black_box(bitter.read_bytes(&mut buf));
            }
        })
    });

    group.finish();
}

criterion_group!(benches, bitting, read_bytes, real_world1, real_world2,);

criterion_main!(benches);
