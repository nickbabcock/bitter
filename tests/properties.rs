extern crate quickcheck;
#[macro_use]
extern crate quickcheck_macros;
extern crate bitter;
extern crate bitterv1;

#[quickcheck]
fn read_bytes_length(k1: u8, data: Vec<u8>) -> bool {
    let mut bits = bitter::BitGet::new(data.as_slice());
    match bits.read_bytes(k1 as i32) {
        None => true,
        Some(bytes) => bytes.len() == k1 as usize,
    }
}

#[quickcheck]
fn read_bytes_eq(data: Vec<u8>) -> bool {
    let mut bits = bitter::BitGet::new(data.as_slice());
    match bits.read_bytes(data.len() as i32) {
        None => true,
        Some(bytes) => bytes == data.as_slice(),
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
    let bytes = bits.read_bytes((data.len() - 1) as i32).unwrap();
    bytes.len() == data.len() - 1
}

#[quickcheck]
fn v1_eq(data: Vec<u8>) -> bool {
    let mut bits = bitter::BitGet::new(data.as_slice());
    let mut bitsv1 = bitter::BitGet::new(data.as_slice());

    bits.read_u32_bits(3) == bitsv1.read_u32_bits(3)
        && bits.read_u8() == bitsv1.read_u8()
        && bits.read_bits_max(5, 20) == bitsv1.read_bits_max(5, 20)
        && bits.read_bit() == bitsv1.read_bit()
        && bits.read_bytes(3) == bitsv1.read_bytes(3)
        && bits.read_u32_bits(13) == bitsv1.read_u32_bits(13)
        && bits.read_u8() == bitsv1.read_u8()
}
