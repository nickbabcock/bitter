extern crate bitter;
extern crate bitterv1;

use bitter::{BigEndianBits, BitReader, LittleEndianBits};

#[test]
fn regression1() {
    let data = vec![0b0000_0010, 0b0011_1111, 0b1011_1100];
    let mut bits = bitter::LittleEndianBits::new(data.as_slice());
    let mut bitsv1 = bitterv1::BitGet::new(data.as_slice());

    assert_eq!(bits.read_u32_bits(3), bitsv1.read_u32_bits(3));
    assert_eq!(bits.read_u8(), bitsv1.read_u8());
    assert_eq!(bits.read_bit(), bitsv1.read_bit());
    assert_eq!(bits.read_u32_bits(13), bitsv1.read_u32_bits(13));
}

#[test]
fn test_f32_endian() {
    let bits = 0x41480000u32;
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianBits::new(&le_data);
    let mut bebits = BigEndianBits::new(&be_data);

    assert_eq!(lebits.read_f32(), Some(12.5f32));
    assert_eq!(bebits.read_f32(), Some(12.5f32));
}

#[test]
fn read_byte_eq() {
    let data = vec![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
}

#[test]
fn read_byte_eq2() {
    let data = vec![1, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
    assert_eq!(lebits.read_u8(), bebits.read_u8());
}

#[test]
fn remaining_bits_le() {
    let data: &[u8] = &[0, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut lebits = LittleEndianBits::new(data);
    assert!(lebits.has_bits_remaining(65));
    for _ in 0..65 {
        assert!(!lebits.read_bit().unwrap());
    }
}

#[test]
fn has_bits_remaining_bit_reads_test_case() {
    let data = &[0, 0, 0, 0, 0, 0, 0, 0];
    let mut bits = LittleEndianBits::new(data);
    assert!((1..128).all(|_x| bits.has_bits_remaining(1) == bits.read_bit().is_some()))
}
