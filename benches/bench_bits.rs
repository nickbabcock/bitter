extern crate bitreader;
extern crate bitstream_io;
extern crate bitter;
#[macro_use]
extern crate criterion;
#[macro_use]
extern crate nom;
extern crate bitterv1;

use bitreader::BitReader;
use bitstream_io::{BitReader as bio_br, LE};
use bitter::BitGet;
use bitterv1::BitGet as BitGetV1;
use criterion::{black_box, Benchmark, Criterion, ParameterizedBenchmark, Throughput};
use std::io::Cursor;

static DATA: [u8; 0x10_000] = [0; 0x10_000];

const ITER: u32 = 1000;

fn bitting(c: &mut Criterion) {
    let parameters: Vec<i32> = (1..33).collect();
    let bench = ParameterizedBenchmark::new(
        "bitter-checked",
        |b, param| {
            b.iter(|| {
                let mut bitter = BitGet::new(&DATA[..]);
                for _ in 0..ITER {
                    black_box(bitter.read_u32_bits(*param));
                }
            })
        },
        parameters.clone(),
    )
    .with_function("bitter-unchecked", |b, param| {
        b.iter(|| {
            let mut bitter = BitGet::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_u32_bits_unchecked(*param));
            }
        })
    })
    .with_function("bitterv1", |b, param| {
        b.iter(|| {
            let mut bitter = BitGetV1::new(&DATA[..]);
            for _ in 0..ITER {
                black_box(bitter.read_u32_bits_unchecked(*param));
            }
        })
    })
    .with_function("bitreader", |b, param| {
        b.iter(|| {
            let mut bitter = BitReader::new(&DATA);
            for _ in 0..ITER {
                black_box(bitter.read_u32(*param as u8).unwrap());
            }
        })
    })
    .with_function("bitstream-io", |b, param| {
        b.iter(|| {
            let mut cursor = Cursor::new(&DATA[..]);
            {
                let mut bits = bio_br::<LE>::new(&mut cursor);
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
                let ((left, new_pos), _) = take_bits!((&d[..], pos), u32, *param as usize).unwrap();
                pos = new_pos;
                d = left;
            }
        })
    })
    .throughput(|p| Throughput::Bytes((*p as u32 * ITER) / 8));

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
        ben!(BitGet::new(&DATA), |x: &mut BitGet| x
            .read_u32_bits_unchecked(8)),
    )
    .with_function(
        "bitter_arbitrary_checked",
        ben!(BitGet::new(&DATA), |x: &mut BitGet| x
            .read_u32_bits(8)
            .unwrap()),
    )
    .with_function(
        "bitter_byte_unchecked",
        ben!(BitGet::new(&DATA), |x: &mut BitGet| x.read_u8_unchecked()),
    )
    .with_function(
        "bitter_byte_checked",
        ben!(BitGet::new(&DATA), |x: &mut BitGet| x
            .read_u8()
            .map(u32::from)),
    )
    .throughput(Throughput::Bytes(ITER));

    c.bench("eight_bits", bench);
}

fn sixtyfour_bits(c: &mut Criterion) {
    let bench = Benchmark::new(
        "bitter_byte_unchecked",
        ben!(BitGet::new(&DATA), |x: &mut BitGet| x.read_u64_unchecked()),
    )
    .with_function(
        "bitter_byte_checked",
        ben!(BitGet::new(&DATA), |x: &mut BitGet| x.read_u64()),
    )
    .throughput(Throughput::Bytes(::std::mem::size_of::<u64>() as u32 * ITER));

    c.bench("sixtyfour_bits", bench);
}

fn remaining(c: &mut Criterion) {
    let bench = Benchmark::new("bitter_approx_bytes", |b| {
        b.iter(|| BitGet::new(&DATA).approx_bytes_remaining())
    })
    .with_function("bitter_has_remaining", |b| {
        b.iter(|| BitGet::new(&DATA).has_bits_remaining(16))
    })
    .with_function("bitter_bits_remaining", |b| {
        b.iter(|| BitGet::new(&DATA).bits_remaining())
    });

    c.bench("remaining", bench);
}

criterion_group!(benches, bitting, eight_bits, sixtyfour_bits, remaining);

criterion_main!(benches);
