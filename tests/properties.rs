use bitter::{BigEndianReader, BitReader, LittleEndianReader, MAX_READ_BITS};
use quickcheck::TestResult;
use quickcheck_macros::quickcheck;

fn _test_bit_reads_auto<T: BitReader>(mut bitter: T, data: &[u8]) {
    assert!(bitter.has_bits_remaining(data.len() * 8));
    assert!(!bitter.has_bits_remaining(data.len() * 8 + 1));
    assert_eq!(bitter.read_bits(1), Some(0));
    assert_eq!(bitter.read_bits(1), Some(1));
    assert_eq!(bitter.read_bits(1), Some(0));
    assert_eq!(bitter.read_bits(1), Some(1));
    assert_eq!(bitter.read_bits(1), Some(0));
    assert_eq!(bitter.read_bits(1), Some(1));
    assert_eq!(bitter.read_bits(1), Some(0));
    assert_eq!(bitter.read_bits(1), Some(1));

    assert!(bitter.has_bits_remaining(8));
    assert_eq!(bitter.read_bits(1), Some(1));
    assert_eq!(bitter.read_bits(1), Some(0));
    assert_eq!(bitter.read_bits(1), Some(1));
    assert_eq!(bitter.read_bits(1), Some(0));
    assert_eq!(bitter.read_bits(1), Some(1));
    assert_eq!(bitter.read_bits(1), Some(0));
    assert_eq!(bitter.read_bits(1), Some(1));
    assert_eq!(bitter.read_bits(1), Some(0));

    if data.len() == 2 {
        assert_eq!(bitter.read_bits(1), None);
    }

    assert!(bitter.has_bits_remaining((data.len() - 2) * 8));
    assert!(!bitter.has_bits_remaining((data.len() - 2) * 8 + 1));
}

#[quickcheck]
fn test_bit_reads_le_auto(mut data: Vec<u8>) {
    data.insert(0, 0b0101_0101);
    data.insert(0, 0b1010_1010);

    let bitter = LittleEndianReader::new(&data);
    _test_bit_reads_auto(bitter, &data);
}

#[quickcheck]
fn test_bit_reads_le_manual(mut data: Vec<u8>) -> TestResult {
    if data.len() < 2 {
        return TestResult::discard();
    }

    data[..2].copy_from_slice(&[0b1010_1010, 0b0101_0101]);

    let mut bitter = LittleEndianReader::new(&data);

    let buffered = bitter.refill_lookahead();
    assert!(buffered >= 16);
    assert!(bitter.has_bits_remaining(data.len() * 8));
    assert!(!bitter.has_bits_remaining(data.len() * 8 + 1));
    assert_eq!(bitter.peek(1), 0);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 1);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 0);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 1);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 0);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 1);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 0);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 1);
    bitter.consume(1);

    assert!(bitter.has_bits_remaining(8));
    assert_eq!(bitter.peek(1), 1);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 0);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 1);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 0);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 1);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 0);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 1);
    bitter.consume(1);
    assert_eq!(bitter.peek(1), 0);
    bitter.consume(1);

    assert!(bitter.has_bits_remaining((data.len() - 2) * 8));
    assert!(!bitter.has_bits_remaining((data.len() - 2) * 8 + 1));
    assert_eq!(
        bitter.refill_lookahead() as usize,
        ((data.len() - 2) * 8).min(56)
    );

    TestResult::passed()
}

#[quickcheck]
fn test_has_remaining_bits_bit_by_bit(data: Vec<u8>) {
    let mut bitter = LittleEndianReader::new(&data);
    for _ in 0..200 {
        assert_eq!(bitter.has_bits_remaining(1), bitter.read_bits(1).is_some());
    }
}

#[quickcheck]
fn test_16_bit_reads(mut data: Vec<u8>) -> TestResult {
    if data.len() < 2 {
        return TestResult::discard();
    }

    data[..2].copy_from_slice(&[0b1010_1010, 0b0101_0101]);
    let mut bitter = LittleEndianReader::new(&data);
    assert_eq!(bitter.read_bits(16), Some(0b0101_0101_1010_1010));
    TestResult::passed()
}

#[quickcheck]
fn test_read_bytes(mut data: Vec<u8>) {
    let mut buf = [0u8; 2];
    if data.len() < 2 {
        let mut bitter = LittleEndianReader::new(&data);
        assert!(bitter.read_bytes(&mut buf[..data.len()]));
        assert_eq!(&buf[..data.len()], &data);
        return;
    }

    data[..2].copy_from_slice(&[0b1010_1010, 0b0101_0101]);

    let mut bitter = LittleEndianReader::new(&data);
    assert!(bitter.read_bytes(&mut buf));
    assert_eq!(&buf, &[0b1010_1010, 0b0101_0101]);

    let mut bitter = LittleEndianReader::new(&data);
    assert_eq!(bitter.read_bits(1), Some(0));
    if data.len() == 2 {
        assert!(!bitter.read_bytes(&mut buf));
    }
    assert!(bitter.read_bytes(&mut buf[..1]));
    assert_eq!(&buf[..1], &[0b1101_0101]);

    let mut remainder = vec![0u8; bitter.bytes_remaining()];
    assert!(bitter.read_bytes(&mut remainder));
}

#[quickcheck]
fn read_bytes_eq(k1: u8, data: Vec<u8>) -> bool {
    let mut bits = LittleEndianReader::new(data.as_slice());
    let mut buf = vec![0u8; usize::from(k1)];
    if !bits.read_bytes(&mut buf) {
        k1 > data.len() as u8
    } else {
        buf.as_slice() == &data[..usize::from(k1)]
    }
}

#[quickcheck]
fn test_bit_reads(data: Vec<u8>) {
    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut bebits = BigEndianReader::new(data.as_slice());

    while !lebits.is_empty() {
        lebits.read_bit();
    }

    while !bebits.is_empty() {
        bebits.read_bit();
    }
}

fn _test_bit_reads2<T: BitReader>(mut bitter: T, bits: u32) {
    let chunk = bits % 56 + 1;
    while bitter.has_bits_remaining(chunk as usize) {
        let len = bitter.refill_lookahead();
        assert!(len <= MAX_READ_BITS && len >= chunk);
        assert_eq!(
            bitter.has_bits_remaining(bitter::MAX_READ_BITS as usize),
            len == MAX_READ_BITS
        );

        bitter.peek(chunk);
        bitter.consume(chunk);
    }
}

#[quickcheck]
fn test_bit_reads2(bits: u32, data: Vec<u8>) {
    let lebits = LittleEndianReader::new(data.as_slice());
    _test_bit_reads2(lebits, bits);

    let bebits = BigEndianReader::new(data.as_slice());
    _test_bit_reads2(bebits, bits);
}

#[quickcheck]
fn has_bits_remaining_bit_reads(data: Vec<u8>) -> bool {
    let mut bits = LittleEndianReader::new(data.as_slice());
    (1..128).all(|_x| bits.has_bits_remaining(1) == bits.read_bit().is_some())
}

#[quickcheck]
fn has_bits_remaining_be_bit_reads(data: Vec<u8>) -> bool {
    let mut bits = BigEndianReader::new(data.as_slice());
    (1..128).all(|_x| bits.has_bits_remaining(1) == bits.read_bit().is_some())
}

#[quickcheck]
fn has_bits_remaining(data: Vec<u8>) -> bool {
    let mut bits = LittleEndianReader::new(data.as_slice());
    (1..32).all(|x| bits.has_bits_remaining(x) == bits.read_bits(x as u32).is_some())
        && bits.has_bits_remaining(8) == bits.read_u8().is_some()
        && bits.has_bits_remaining(16) == bits.read_u16().is_some()
        && bits.has_bits_remaining(32) == bits.read_u32().is_some()
}

#[quickcheck]
fn read_byte_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut bebits = BigEndianReader::new(data.as_slice());

    for _ in &data {
        if lebits.read_u8() != bebits.read_u8() {
            return false;
        }
    }

    lebits.is_empty() && bebits.is_empty()
}

#[quickcheck]
fn read_byte_unchecked_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut bebits = BigEndianReader::new(data.as_slice());

    for _ in &data {
        assert_eq!(lebits.read_u8(), bebits.read_u8());
    }

    lebits.is_empty() && bebits.is_empty()
}

#[quickcheck]
fn read_byte_alternate(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut bebits = BigEndianReader::new(data.as_slice());

    for (i, x) in data.iter().enumerate() {
        if i % 3 == 0 {
            let val = lebits.read_u8().unwrap();
            if val != *x || val != bebits.read_u8().unwrap() {
                return false;
            }
        } else {
            lebits.refill_lookahead();
            let le_peek = lebits.peek(8) as u8;
            lebits.consume(8);

            bebits.refill_lookahead();
            let be_peek = bebits.peek(8) as u8;
            bebits.consume(8);
            if le_peek != *x || le_peek != be_peek {
                return false;
            }
        }
    }

    lebits.is_empty() && bebits.is_empty()
}

#[quickcheck]
fn read_u16_eq(x: u16) -> bool {
    let le_data = x.to_le_bytes();
    let be_data = x.to_be_bytes();
    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_u16() == bebits.read_u16()
}

#[quickcheck]
fn read_u32_eq(x: u32) -> bool {
    let le_data = x.to_le_bytes();
    let be_data = x.to_be_bytes();
    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_u32() == bebits.read_u32()
}

#[quickcheck]
fn has_bits_remaining_bit_reads_ends(reads: u8, data: Vec<u8>) -> bool {
    fn test_fn<B: BitReader>(bits: &mut B, reads: u8) -> bool {
        let mut result = true;
        if bits.has_bits_remaining(usize::from(reads)) {
            for _ in 0..reads {
                result &= bits.read_bit().is_some();
            }
        }

        result
    }

    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut bebits = LittleEndianReader::new(data.as_slice());

    test_fn(&mut lebits, reads) && test_fn(&mut bebits, reads)
}

#[quickcheck]
fn read_u32_val_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_u32() == bebits.read_u32()
}

#[quickcheck]
fn read_f32_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    match (lebits.read_f32(), bebits.read_f32()) {
        (Some(y), Some(x)) => (x.is_nan() && y.is_nan()) || x == y,
        _ => false,
    }
}

#[quickcheck]
fn read_le_signed_bits(a: i8, b: i16, c: i32) -> bool {
    let mut data = Vec::new();
    data.extend_from_slice(&(a.to_le_bytes()));
    data.extend_from_slice(&(b.to_le_bytes()));
    data.extend_from_slice(&(c.to_le_bytes()));
    let mut lebits = LittleEndianReader::new(data.as_slice());

    lebits.read_signed_bits(8).map(|x| x as i8) == Some(a)
        && lebits.read_signed_bits(16).map(|x| x as i16) == Some(b)
        && lebits.read_signed_bits(32).map(|x| x as i32) == Some(c)
}

#[quickcheck]
fn read_le_signed_bits2(a: i8, b: i16, c: i32) -> bool {
    let mut data = Vec::new();
    data.extend_from_slice(&(a.to_le_bytes()));
    data.extend_from_slice(&(b.to_le_bytes()));
    data.extend_from_slice(&(c.to_le_bytes()));
    let mut lebits = LittleEndianReader::new(data.as_slice());
    let mut lebits2 = LittleEndianReader::new(data.as_slice());

    lebits.read_signed_bits(8).map(|x| x as i8) == lebits2.read_i8()
        && lebits.read_signed_bits(16).map(|x| x as i16) == lebits2.read_i16()
        && lebits.read_signed_bits(32).map(|x| x as i32) == lebits2.read_i32()
}

#[quickcheck]
fn read_be_signed_bits(a: i8, b: i16, c: i32) -> bool {
    let mut data = Vec::new();
    data.extend_from_slice(&(a.to_be_bytes()));
    data.extend_from_slice(&(b.to_be_bytes()));
    data.extend_from_slice(&(c.to_be_bytes()));
    let mut bebits = BigEndianReader::new(data.as_slice());

    bebits.read_signed_bits(8).map(|x| x as i8) == Some(a)
        && bebits.read_signed_bits(16).map(|x| x as i16) == Some(b)
        && bebits.read_signed_bits(32).map(|x| x as i32) == Some(c)
}

#[quickcheck]
fn read_be_signed_bits2(a: i8, b: i16, c: i32) -> bool {
    let mut data = Vec::new();
    data.extend_from_slice(&(a.to_be_bytes()));
    data.extend_from_slice(&(b.to_be_bytes()));
    data.extend_from_slice(&(c.to_be_bytes()));
    let mut bebits = BigEndianReader::new(data.as_slice());
    let mut bebits2 = BigEndianReader::new(data.as_slice());

    bebits.read_signed_bits(8).map(|x| x as i8) == bebits2.read_i8()
        && bebits.read_signed_bits(16).map(|x| x as i16) == bebits2.read_i16()
        && bebits.read_signed_bits(32).map(|x| x as i32) == bebits2.read_i32()
}
