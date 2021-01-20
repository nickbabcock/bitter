extern crate bitter;
extern crate bitterv1;

use bitter::BitOrder;

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
