use bitter::{BigEndianReader, BitReader, LittleEndianReader};

#[test]
fn test_f32_endian() {
    let bits = 0x41480000u32;
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    assert_eq!(lebits.read_f32(), Some(12.5f32));
    assert_eq!(bebits.read_f32(), Some(12.5f32));
}

#[test]
fn read_byte_eq() {
    let data = vec![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1];
    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut bebits = BigEndianReader::new(data.as_slice());

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
    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut bebits = BigEndianReader::new(data.as_slice());

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
fn read_byte_le_unchecked() {
    let data = vec![1, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut lebits = LittleEndianReader::new(data.as_slice());

    assert_eq!(lebits.read_u8_unchecked(), 1);
    assert_eq!(lebits.read_u8_unchecked(), 0);
    assert_eq!(lebits.read_u8_unchecked(), 0);
    assert_eq!(lebits.read_u8_unchecked(), 0);
    assert_eq!(lebits.read_u8_unchecked(), 0);
    assert_eq!(lebits.read_u8_unchecked(), 0);
    assert_eq!(lebits.read_u8_unchecked(), 0);
    assert_eq!(lebits.read_u8_unchecked(), 0);
    assert_eq!(lebits.read_u8_unchecked(), 0);

    assert!(lebits.is_empty());
}

#[test]
fn read_byte_be_unchecked() {
    let data = vec![1, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut bits = BigEndianReader::new(data.as_slice());

    assert_eq!(bits.read_u8_unchecked(), 1);
    assert_eq!(bits.read_u8_unchecked(), 0);
    assert_eq!(bits.read_u8_unchecked(), 0);
    assert_eq!(bits.read_u8_unchecked(), 0);
    assert_eq!(bits.read_u8_unchecked(), 0);
    assert_eq!(bits.read_u8_unchecked(), 0);
    assert_eq!(bits.read_u8_unchecked(), 0);
    assert_eq!(bits.read_u8_unchecked(), 0);
    assert_eq!(bits.read_u8_unchecked(), 0);

    assert!(bits.is_empty());
}

#[test]
fn read_byte_be() {
    let data = vec![1, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut bits = BigEndianReader::new(data.as_slice());

    assert_eq!(bits.read_u8(), Some(1));
    assert_eq!(bits.read_u8(), Some(0));
    assert_eq!(bits.read_u8(), Some(0));
    assert_eq!(bits.read_u8(), Some(0));
    assert_eq!(bits.read_u8(), Some(0));
    assert_eq!(bits.read_u8(), Some(0));
    assert_eq!(bits.read_u8(), Some(0));
    assert_eq!(bits.read_u8(), Some(0));
    assert_eq!(bits.read_u8(), Some(0));

    assert!(bits.is_empty());
}

#[test]
fn read_byte_eq_unchecked() {
    let data = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut bebits = BigEndianReader::new(data.as_slice());

    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());
    assert_eq!(lebits.read_u8_unchecked(), bebits.read_u8_unchecked());

    assert!(lebits.is_empty());
    assert!(bebits.is_empty());
}

#[test]
fn remaining_bits_le() {
    let data: &[u8] = &[0, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut lebits = LittleEndianReader::new(data);
    assert!(lebits.has_bits_remaining(65));
    for _ in 0..65 {
        assert!(!lebits.read_bit().unwrap());
    }
}

#[test]
fn has_bits_remaining_bit_reads_test_case() {
    let data = &[0, 0, 0, 0, 0, 0, 0, 0];
    let mut bits = LittleEndianReader::new(data);
    assert!((1..128).all(|_x| bits.has_bits_remaining(1) == bits.read_bit().is_some()))
}
