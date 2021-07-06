use bitreader::BitReader as BR;
use bitstream_io::{BitRead, BitReader as bio_br, LittleEndian};
use bitter;
use bitter::{BitReader, LittleEndianReader};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use nom::{
    bitvec::{order::Lsb0, prelude::BitField, view::BitView},
    take_bits,
};
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

criterion_group!(benches, bitting,);

criterion_main!(benches);
