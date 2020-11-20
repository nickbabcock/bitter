#![no_main]
use libfuzzer_sys::fuzz_target;
use bitter;
use bitterv1;

fuzz_target!(|data: &[u8]| {
    let mut bits = bitter::BitGet::new(data);
    let mut bitsv1 = bitterv1::BitGet::new(data);

    let res = bits.read_u32_bits(3) == bitsv1.read_u32_bits(3) &&
        bits.read_u8() == bitsv1.read_u8() &&
        bits.read_bits_max(20) == bitsv1.read_bits_max(5, 20) &&
        bits.read_bit() == bitsv1.read_bit() &&
        bits.read_bytes(3).map(|x| x == bitsv1.read_bytes(3).unwrap()).unwrap_or(true) &&
        bits.read_u32_bits(13) == bitsv1.read_u32_bits(13) &&
        bits.read_u8() == bitsv1.read_u8() &&
        bits.read_bits_max(20) == bitsv1.read_bits_max(5, 20) &&
        bits.read_bit() == bitsv1.read_bit() &&
        bits.read_bytes(3).map(|x| x == bitsv1.read_bytes(3).unwrap()).unwrap_or(true) &&
        bits.read_u32_bits(13) == bitsv1.read_u32_bits(13) &&
        bits.read_u8() == bitsv1.read_u8();

    if !res {
        println!("Not equal!: {:?}", data);
        panic!("Not equal!");
    }
});
