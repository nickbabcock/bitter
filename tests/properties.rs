use bitter::{BigEndianReader, BitReader, LittleEndianReader};
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

    bitter.refill_lookahead();
    assert!(bitter.lookahead_bits() >= 16);
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
    bitter.refill_lookahead();
    assert!(bitter.lookahead_bits() as usize <= ((data.len() - 2) * 8),);

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
fn test_read_bytes_large(mut data: Vec<u8>, buf_len: u8) {
    let buf_len = buf_len.saturating_add(75);
    let mut buf = vec![0u8; usize::from(buf_len)];
    if data.len() < buf.len() + 1 {
        let mut bitter = LittleEndianReader::new(&data);
        assert!(bitter.read_bytes(&mut buf[..data.len()]));
        assert_eq!(&buf[..data.len()], &data);
        return;
    }

    data[0] = 0b0000_0101;
    data[1] &= 0b1111_1110; // turn off low bit for bit read
    data[6] = 0b0000_1000;
    data[7] = 0b0000_0010;
    data[8] = 0b0000_0011;
    data[9] &= 0b1111_1110; // turn off low bit for bit read
    data[28] = 0b0000_0000;
    data[29] = 0b1111_1111;
    data[74] = 0b1000_0000;
    data[75] = 0b1011_1111;

    let mut bitter = LittleEndianReader::new(&data);
    assert_eq!(bitter.read_u8(), Some(0b0000_0101));
    assert!(bitter.read_bytes(&mut buf));
    assert_eq!(buf[5], 0b0000_1000);
    assert_eq!(buf[6], 0b0000_0010);
    assert_eq!(buf[7], 0b0000_0011);
    assert_eq!(buf[27], 0b0000_0000);
    assert_eq!(buf[28], 0b1111_1111);
    assert_eq!(buf[73], 0b1000_0000);
    assert_eq!(buf[74], 0b1011_1111);

    let mut bitter = LittleEndianReader::new(&data);
    assert_eq!(bitter.read_bit(), Some(true));
    assert!(bitter.read_bytes(&mut buf));
    assert_eq!(buf[0], 0b0000_0010);
    assert_eq!(buf[6], 0b0000_0100);
    assert_eq!(buf[7], 0b1000_0001);
    assert_eq!(buf[8], 0b0000_0001);
    assert_eq!(buf[28], 0b1000_0000);
    assert_eq!(buf[74], 0b1100_0000);
}

fn _test_read_bytes_equiv<T: BitReader>(mut bitter1: T, mut bitter2: T, buf_len: u8, shift: u8) {
    let mut buf1 = vec![0u8; usize::from(buf_len)];
    let mut buf2 = vec![0u8; usize::from(buf_len)];

    let shift = shift as u32 % 65;
    assert_eq!(bitter1.read_bits(shift), bitter2.read_bits(shift));

    if !bitter1.has_bits_remaining(buf1.len() * 8) {
        assert!(!bitter1.read_bytes(&mut buf1));
        return;
    }

    for x in buf1.iter_mut() {
        *x = bitter1.read_u8().unwrap();
    }

    assert!(bitter2.read_bytes(&mut buf2));
    assert_eq!(buf1.as_slice(), buf2.as_slice());
    assert_eq!(bitter1.read_bits(shift), bitter2.read_bits(shift));
}

#[quickcheck]
fn test_read_bytes_equiv_le(data: Vec<u8>, buf_len: u8, shift: u8) {
    let bitter1 = LittleEndianReader::new(&data);
    let bitter2 = LittleEndianReader::new(&data);

    _test_read_bytes_equiv(bitter1, bitter2, buf_len, shift);
}

#[quickcheck]
fn test_read_bytes_equiv_be(data: Vec<u8>, buf_len: u8, shift: u8) {
    let bitter1 = BigEndianReader::new(&data);
    let bitter2 = BigEndianReader::new(&data);

    _test_read_bytes_equiv(bitter1, bitter2, buf_len, shift);
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
        assert!(lebits.read_bit().is_some());
    }

    while !bebits.is_empty() {
        assert!(bebits.read_bit().is_some());
    }
}

fn _test_bit_reads2<T: BitReader>(mut bitter: T, bits: u32) {
    let chunk = bits % 64 + 1;
    while bitter.has_bits_remaining(chunk as usize) {
        let mut chunk_remaining = chunk;
        while chunk_remaining > 0 {
            if bitter.lookahead_bits() == 0 {
                bitter.refill_lookahead();
                assert!(bitter.lookahead_bits() > 0);
            }

            let to_read = bitter.lookahead_bits().min(chunk_remaining);
            let res = bitter.peek(to_read);
            bitter.consume(to_read);
            let _ = bitter::sign_extend(res, to_read);
            chunk_remaining -= to_read;
        }
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

#[quickcheck]
fn read_ergonomics(i8: i8, u8: u8, i16: i16, u16: u16, i32: i32, u32: u32, i64: i64, u64: u64) {
    let ff32 = f32::from_bits(u32);
    let ff64 = f64::from_bits(u64);

    let mut data = Vec::new();
    data.extend_from_slice(&i8.to_le_bytes());
    data.extend_from_slice(&u8.to_le_bytes());
    data.extend_from_slice(&i16.to_le_bytes());
    data.extend_from_slice(&u16.to_le_bytes());
    data.extend_from_slice(&i32.to_le_bytes());
    data.extend_from_slice(&u32.to_le_bytes());
    data.extend_from_slice(&i64.to_le_bytes());
    data.extend_from_slice(&u64.to_le_bytes());
    data.extend_from_slice(&ff32.to_le_bytes());
    data.extend_from_slice(&ff64.to_le_bytes());

    let mut data2 = Vec::new();
    data2.extend_from_slice(&i8.to_be_bytes());
    data2.extend_from_slice(&u8.to_be_bytes());
    data2.extend_from_slice(&i16.to_be_bytes());
    data2.extend_from_slice(&u16.to_be_bytes());
    data2.extend_from_slice(&i32.to_be_bytes());
    data2.extend_from_slice(&u32.to_be_bytes());
    data2.extend_from_slice(&i64.to_be_bytes());
    data2.extend_from_slice(&u64.to_be_bytes());
    data2.extend_from_slice(&ff32.to_be_bytes());
    data2.extend_from_slice(&ff64.to_be_bytes());

    let mut lebits = LittleEndianReader::new(&data);

    assert_eq!(lebits.read_i8(), Some(i8));
    assert_eq!(lebits.read_u8(), Some(u8));
    assert_eq!(lebits.read_i16(), Some(i16));
    assert_eq!(lebits.read_u16(), Some(u16));
    assert_eq!(lebits.read_i32(), Some(i32));
    assert_eq!(lebits.read_u32(), Some(u32));
    assert_eq!(lebits.read_i64(), Some(i64));
    assert_eq!(lebits.read_u64(), Some(u64));

    assert!(
        (ff32.is_nan() && lebits.read_f32().unwrap().is_nan()) || lebits.read_f32() == Some(ff32)
    );

    assert!(
        (ff64.is_nan() && lebits.read_f64().unwrap().is_nan()) || lebits.read_f64() == Some(ff64)
    );

    let mut bebits = BigEndianReader::new(&data2);
    assert_eq!(bebits.read_i8(), Some(i8));
    assert_eq!(bebits.read_u8(), Some(u8));
    assert_eq!(bebits.read_i16(), Some(i16));
    assert_eq!(bebits.read_u16(), Some(u16));
    assert_eq!(bebits.read_i32(), Some(i32));
    assert_eq!(bebits.read_u32(), Some(u32));
    assert_eq!(bebits.read_i64(), Some(i64));
    assert_eq!(bebits.read_u64(), Some(u64));

    assert!(
        (ff32.is_nan() && bebits.read_f32().unwrap().is_nan()) || bebits.read_f32() == Some(ff32)
    );

    assert!(
        (ff64.is_nan() && bebits.read_f64().unwrap().is_nan()) || bebits.read_f64() == Some(ff64)
    );
}

#[test]
fn remainder_lifetime() {
    fn helper<'a>(reader: &LittleEndianReader<'a>) -> bitter::Remainder<'a> {
        reader.remainder()
    }

    // The whole point of this test is to fail at compile time if the
    // remainder() function doesn't return the slice with the same
    // lifetime as the underlying data.
    let reader = LittleEndianReader::new(&[]);
    helper(&reader);
}
