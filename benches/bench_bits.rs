use bitter;
#[macro_use]
extern crate criterion;
#[macro_use]
extern crate nom;

use bitreader::BitReader as BR;
use bitstream_io::{BitRead, BitReader as bio_br, LittleEndian};
use bitter::{BitReader, LittleEndianReader};
use criterion::{black_box, BenchmarkId, Criterion, Throughput};
use nom::bitvec::{order::Lsb0, prelude::BitField, view::BitView};
use std::io::Cursor;

static DATA: [u8; 0x10_000] = [0; 0x10_000];

const ITER: u64 = 1000;

fn bitting(c: &mut Criterion) {
    let parameters: Vec<i32> = (1..64).collect();

    let mut group = c.benchmark_group("bit-reading");
    for i in parameters {
        group.throughput(Throughput::Bytes((i as u64 * ITER) / 8));

        group.bench_with_input(BenchmarkId::new("bitter-checked", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                bitter.read_bit();
                for _ in 0..ITER {
                    black_box(bitter.read_bits(*param));
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("bitter-unchecked", i), &i, |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                bitter.read_bit();
                for _ in 0..ITER {
                    black_box(bitter.read_bits_unchecked(*param));
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

        group.bench_with_input(BenchmarkId::new("nom", i), &i, |b, param| {
            b.iter(|| {
                let mut d = &DATA[..];
                let mut pos = 1;
                for _ in 0..ITER {
                    let ((left, new_pos), _): ((&[u8], usize), u64) =
                        take_bits!((&d[..], pos), *param as usize).unwrap();
                    pos = new_pos;
                    d = left;
                }
            })
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
    }

    group.finish();
}

macro_rules! ben {
    ($ex1:expr, $ex2:expr) => {
        |b| {
            b.iter(|| {
                let mut bits = $ex1;
                for _ in 0..ITER {
                    black_box($ex2(&mut bits));
                }
            });
        }
    };
}

fn eight_bits(c: &mut Criterion) {
    let mut group = c.benchmark_group("eight_bits");
    group.throughput(Throughput::Bytes(ITER));

    group.bench_function(
        "bitter_arbitrary_unchecked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_bits_unchecked(8)
        ),
    );

    group.bench_function(
        "bitter_arbitrary_checked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_bits(8).unwrap()
        ),
    );

    group.bench_function(
        "bitter_byte_unchecked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_u8_unchecked()
        ),
    );

    group.bench_function(
        "bitter_byte_checked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_u8().map(u32::from)
        ),
    );

    group.finish();
}

fn sixtyfour_bits(c: &mut Criterion) {
    let mut group = c.benchmark_group("sixtyfour_bits");
    group.throughput(Throughput::Bytes(
        ::std::mem::size_of::<u64>() as u64 * ITER,
    ));

    group.bench_function(
        "bitter_byte_unchecked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_u64_unchecked()
        ),
    );

    group.bench_function(
        "bitter_byte_checked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_u64()
        ),
    );

    group.finish();
}

fn remaining(c: &mut Criterion) {
    let mut group = c.benchmark_group("remaining");
    group.bench_function("bitter_approx_bytes", |b| {
        b.iter(|| LittleEndianReader::new(&DATA).approx_bytes_remaining())
    });

    group.bench_function("bitter_has_remaining", |b| {
        b.iter(|| LittleEndianReader::new(&DATA).has_bits_remaining(16))
    });

    group.bench_function("bitter_bits_remaining", |b| {
        b.iter(|| LittleEndianReader::new(&DATA).bits_remaining())
    });

    group.finish();
}

fn read_bits_max(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_bits_max");
    group.bench_function("read_bits_max_checked", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_max(22));
            }
        })
    });

    group.bench_function("read_bits_max_computed", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_max_computed(4, 22));
            }
        })
    });

    group.bench_function("read_bits_max_computed_unchecked", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_max_computed_unchecked(4, 22));
            }
        })
    });

    group.bench_function("read_bits_max_unchecked", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_max_unchecked(22));
            }
        })
    });

    group.finish();
}

fn bit_width(c: &mut Criterion) {
    c.bench_function("bitwidth", |b| b.iter(|| bitter::bit_width(black_box(20))));
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

criterion_group!(
    benches,
    bitting,
    eight_bits,
    sixtyfour_bits,
    remaining,
    read_bits_max,
    bit_width,
    read_bytes
);

criterion_main!(benches);
