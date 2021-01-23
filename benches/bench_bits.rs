use bitter;
#[macro_use]
extern crate criterion;
#[macro_use]
extern crate nom;

use bitreader::BitReader as BR;
use bitstream_io::{BitRead, BitReader as bio_br, LittleEndian};
use bitter::{BitReader, LittleEndianReader};
use criterion::{black_box, Benchmark, Criterion, ParameterizedBenchmark, Throughput};
use std::io::Cursor;

static DATA: [u8; 0x10_000] = [0; 0x10_000];

const ITER: u64 = 1000;

fn bitting(c: &mut Criterion) {
    let parameters: Vec<i32> = (1..33).collect();
    let bench = ParameterizedBenchmark::new(
        "bitter-checked",
        |b, param| {
            b.iter(|| {
                let mut bitter = LittleEndianReader::new(&DATA[..]);
                for _ in 0..ITER {
                    black_box(bitter.read_bits(*param));
                }
            })
        },
        parameters.clone(),
    )
    .with_function("bitter-unchecked", |b, param| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_unchecked(*param));
            }
        })
    })
    .with_function("bitreader", |b, param| {
        b.iter(|| {
            let mut bitter = BR::new(&DATA);
            for _ in 0..ITER {
                black_box(bitter.read_u32(*param as u8).unwrap());
            }
        })
    })
    .with_function("bitstream-io", |b, param| {
        b.iter(|| {
            let mut cursor = Cursor::new(&DATA[..]);
            {
                let mut bits = bio_br::endian(&mut cursor, LittleEndian);
                for _ in 0..ITER {
                    black_box(bits.read::<u32>(*param as u32).unwrap());
                }
            }
        })
    })
    .with_function("nom", |b, param| {
        b.iter(|| {
            let mut d = &DATA[..];
            let mut pos = 0;
            for _ in 0..ITER {
                let ((left, new_pos), _): ((&[u8], usize), u32) =
                    take_bits!((&d[..], pos), *param as usize).unwrap();
                pos = new_pos;
                d = left;
            }
        })
    })
    .throughput(|p| Throughput::Bytes(((*p as u64) * ITER) / 8));

    c.bench("bit-reading", bench);
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
    let bench = Benchmark::new(
        "bitter_arbitrary_unchecked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_bits_unchecked(8)
        ),
    )
    .with_function(
        "bitter_arbitrary_checked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_bits(8).unwrap()
        ),
    )
    .with_function(
        "bitter_byte_unchecked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_u8_unchecked()
        ),
    )
    .with_function(
        "bitter_byte_checked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_u8().map(u32::from)
        ),
    )
    .throughput(Throughput::Bytes(ITER));

    c.bench("eight_bits", bench);
}

fn sixtyfour_bits(c: &mut Criterion) {
    let bench = Benchmark::new(
        "bitter_byte_unchecked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_u64_unchecked()
        ),
    )
    .with_function(
        "bitter_byte_checked",
        ben!(
            LittleEndianReader::new(&DATA),
            |x: &mut LittleEndianReader<'_>| x.read_u64()
        ),
    )
    .throughput(Throughput::Bytes(
        ::std::mem::size_of::<u64>() as u64 * ITER,
    ));

    c.bench("sixtyfour_bits", bench);
}

fn remaining(c: &mut Criterion) {
    let bench = Benchmark::new("bitter_approx_bytes", |b| {
        b.iter(|| LittleEndianReader::new(&DATA).approx_bytes_remaining())
    })
    .with_function("bitter_has_remaining", |b| {
        b.iter(|| LittleEndianReader::new(&DATA).has_bits_remaining(16))
    })
    .with_function("bitter_bits_remaining", |b| {
        b.iter(|| LittleEndianReader::new(&DATA).bits_remaining())
    });

    c.bench("remaining", bench);
}

fn read_bits_max(c: &mut Criterion) {
    let bench = Benchmark::new("read_bits_max_checked", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_max(22));
            }
        })
    })
    .with_function("read_bits_max_computed", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_max_computed(4, 22));
            }
        })
    })
    .with_function("read_bits_max_computed_unchecked", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_max_computed_unchecked(4, 22));
            }
        })
    })
    .with_function("read_bits_max_unchecked", |b| {
        b.iter(|| {
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bits_max_unchecked(22));
            }
        })
    });

    c.bench("read_bits_max", bench);
}

fn bit_width(c: &mut Criterion) {
    let bench = Benchmark::new("bit_width", |b| b.iter(|| bitter::bit_width(black_box(20))));

    c.bench("remaining", bench);
}

fn read_bytes(c: &mut Criterion) {
    let bench = Benchmark::new("aligned", |b| {
        b.iter(|| {
            let mut buf = [0u8; 7];
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_bytes(&mut buf));
            }
        })
    })
    .with_function("unaligned", |b| {
        b.iter(|| {
            let mut buf = [0u8; 7];
            let mut bitter = LittleEndianReader::new(&DATA[..]);
            bitter.read_bit();
            for _ in 0..ITER {
                black_box(bitter.read_bytes(&mut buf));
            }
        })
    });

    c.bench("read_bytes", bench);
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
