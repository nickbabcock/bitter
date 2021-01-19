extern crate quickcheck;
#[macro_use]
extern crate quickcheck_macros;
extern crate bitter;
extern crate bitterv1;

#[quickcheck]
fn read_bytes_eq(k1: u8, data: Vec<u8>) -> bool {
    let mut bits = bitter::BitGet::new(data.as_slice());
    let mut buf = vec![0u8; usize::from(k1)];
    if !bits.read_bytes(&mut buf) {
        k1 > data.len() as u8
    } else {
        buf.as_slice() == &data[..usize::from(k1)]
    }
}

#[quickcheck]
fn has_bits_remaining_bit_reads(data: Vec<u8>) -> bool {
    let mut bits = bitter::BitGet::new(data.as_slice());
    (1..128).all(|_x| bits.has_bits_remaining(1) == bits.read_bit().is_some())
}

#[quickcheck]
fn has_bits_remaining(data: Vec<u8>) -> bool {
    let mut bits = bitter::BitGet::new(data.as_slice());
    (1..32).all(|x| bits.has_bits_remaining(x) == bits.read_u32_bits(x as i32).is_some()) &&
        bits.has_bits_remaining(8) == bits.read_u8().is_some() &&
        bits.has_bits_remaining(16) == bits.read_u16().is_some() &&
        bits.has_bits_remaining(32) == bits.read_u32().is_some() &&
        bits.has_bits_remaining(64) == bits.read_u64().is_some()
}

#[quickcheck]
fn read_bytes_bits(data: Vec<u8>) -> bool {
    if data.len() <= 1 {
        return true;
    }

    let mut bits = bitter::BitGet::new(data.as_slice());
    bits.read_u32_bits_unchecked(3);

    let mut buf = vec![0u8; data.len() - 1];
    bits.read_bytes(&mut buf)
}

#[quickcheck]
fn v1_eq(data: Vec<u8>) -> bool {
    let mut bits = bitter::BitGet::new(data.as_slice());
    let mut bitsv1 = bitterv1::BitGet::new(data.as_slice());
    let mut buf = vec![0u8; 3];

    bits.read_u32_bits(3) == bitsv1.read_u32_bits(3)
        && bits.read_u8() == bitsv1.read_u8()
        && bits.read_bits_max(20) == bitsv1.read_bits_max(5, 20)
        && bits.read_bit() == bitsv1.read_bit()
        && (bits.read_bytes(&mut buf) == bitsv1.read_bytes(3).is_some())
        && bits.read_u32_bits(13) == bitsv1.read_u32_bits(13)
        && bits.read_u8() == bitsv1.read_u8()
}
