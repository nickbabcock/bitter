#![no_main]
use libfuzzer_sys::fuzz_target;
use bitter::{LittleEndianBits, BitOrder};

fuzz_target!(|data: &[u8]| {
    let mut bits = LittleEndianBits::new(data);
    let mut bitsv1 = bitterv1::BitGet::new(data);
    let mut buf1 = [0u8; 3];

    let res = bits.read_u32_bits(3) == bitsv1.read_u32_bits(3) &&
        bits.read_u8() == bitsv1.read_u8() &&
        bits.read_bits_max(20) == bitsv1.read_bits_max(5, 20) &&
        bits.read_bit() == bitsv1.read_bit() &&
        bits.read_bytes(&mut buf1) == bitsv1.read_bytes(3).is_some() &&
        bits.read_u32_bits(13) == bitsv1.read_u32_bits(13) &&
        bits.read_u8() == bitsv1.read_u8() &&
        bits.read_bits_max(20) == bitsv1.read_bits_max(5, 20) &&
        bits.read_bit() == bitsv1.read_bit() &&
        bits.read_bytes(&mut buf1) == bitsv1.read_bytes(3).is_some() &&
        bits.read_u32_bits(13) == bitsv1.read_u32_bits(13) &&
        bits.read_u8() == bitsv1.read_u8();

    if !res {
        println!("Not equal!: {:?}", data);
        panic!("Not equal!");
    }
});
