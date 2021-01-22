extern crate quickcheck;
#[macro_use]
extern crate quickcheck_macros;
extern crate bitter;
extern crate bitterv1;

use bitter::{BigEndianReader, BitReader, LittleEndianReader};

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
    (1..32).all(|x| bits.has_bits_remaining(x) == bits.read_u32_bits(x as i32).is_some())
        && bits.has_bits_remaining(8) == bits.read_u8().is_some()
        && bits.has_bits_remaining(16) == bits.read_u16().is_some()
        && bits.has_bits_remaining(32) == bits.read_u32().is_some()
        && bits.has_bits_remaining(64) == bits.read_u64().is_some()
}

#[quickcheck]
fn read_bytes_bits(data: Vec<u8>) -> bool {
    if data.len() <= 1 {
        return true;
    }

    let mut bits = LittleEndianReader::new(data.as_slice());
    bits.read_u32_bits_unchecked(3);

    let mut buf = vec![0u8; data.len() - 1];
    bits.read_bytes(&mut buf)
}

#[quickcheck]
fn v1_eq(data: Vec<u8>) -> bool {
    let mut bits = LittleEndianReader::new(data.as_slice());
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
        if lebits.read_u8_unchecked() != bebits.read_u8_unchecked() {
            return false;
        }
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
            let val = lebits.read_u8_unchecked();
            if val != *x || val != bebits.read_u8_unchecked() {
                return false;
            }
        }
    }

    lebits.is_empty() && bebits.is_empty()
}

#[quickcheck]
fn read_u64_le_alternate(data: Vec<u64>) -> bool {
    let mut ledata: Vec<u8> = Vec::new();
    for x in &data {
        ledata.extend_from_slice(&x.to_le_bytes());
    }
    let mut lebits = LittleEndianReader::new(ledata.as_slice());
    for _ in 0..64 {
        lebits.read_bit();
    }

    for (i, x) in data.iter().skip(1).enumerate() {
        if i % 3 == 0 {
            if lebits.read_u64().unwrap() != *x {
                return false;
            }
        } else {
            if lebits.read_u64_unchecked() != *x {
                return false;
            }
        }
    }

    lebits.is_empty()
}

#[quickcheck]
fn read_u64_be_alternate(data: Vec<u64>) -> bool {
    let mut bedata: Vec<u8> = Vec::new();
    for x in &data {
        bedata.extend_from_slice(&x.to_be_bytes());
    }
    let mut bebits = BigEndianReader::new(bedata.as_slice());
    for _ in 0..64 {
        bebits.read_bit();
    }

    for (i, x) in data.iter().skip(1).enumerate() {
        if i % 3 == 0 {
            if bebits.read_u64().unwrap() != *x {
                return false;
            }
        } else {
            if bebits.read_u64_unchecked() != *x {
                return false;
            }
        }
    }

    bebits.is_empty()
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
fn read_u64_eq(x: u64) -> bool {
    let le_data = x.to_le_bytes();
    let be_data = x.to_be_bytes();
    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_u64() == bebits.read_u64()
}

#[quickcheck]
fn read_u16_unchecked_eq(x: u16) -> bool {
    let le_data = x.to_le_bytes();
    let be_data = x.to_be_bytes();
    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_u16_unchecked() == bebits.read_u16_unchecked()
}

#[quickcheck]
fn read_u32_unchecked_eq(x: u32) -> bool {
    let le_data = x.to_le_bytes();
    let be_data = x.to_be_bytes();
    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_u32_unchecked() == bebits.read_u32_unchecked()
}

#[quickcheck]
fn read_u64_unchecked_eq(x: u64) -> bool {
    let le_data = x.to_le_bytes();
    let be_data = x.to_be_bytes();
    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_u64_unchecked() == bebits.read_u64_unchecked()
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
fn read_u32_unchecked_val_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    let le = lebits.read_u32_unchecked();
    le == bebits.read_u32_unchecked() && le == bits
}

#[quickcheck]
fn read_f32_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_f32() == bebits.read_f32()
}

#[quickcheck]
fn read_f32_unchecked_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianReader::new(&le_data);
    let mut bebits = BigEndianReader::new(&be_data);

    lebits.read_f32_unchecked() == bebits.read_f32_unchecked()
}

#[quickcheck]
fn back_to_back_le_u64(x: u64, y: u64) -> bool {
    let mut data = Vec::new();
    data.extend_from_slice(&(x.to_le_bytes()));
    data.extend_from_slice(&(y.to_le_bytes()));
    let mut bits = LittleEndianReader::new(data.as_slice());
    bits.read_u64() == Some(x) && bits.read_u64() == Some(y)
}

#[quickcheck]
fn back_to_back_le_unchecked_u64(x: u64, y: u64) -> bool {
    let mut data = Vec::new();
    data.extend_from_slice(&(x.to_le_bytes()));
    data.extend_from_slice(&(y.to_le_bytes()));
    let mut bits = LittleEndianReader::new(data.as_slice());
    bits.read_u64_unchecked() == x && bits.read_u64_unchecked() == y
}

#[quickcheck]
fn back_to_back_be_u64(x: u64, y: u64) -> bool {
    let mut data = Vec::new();
    data.extend_from_slice(&(x.to_be_bytes()));
    data.extend_from_slice(&(y.to_be_bytes()));
    let mut bits = BigEndianReader::new(data.as_slice());
    bits.read_u64() == Some(x) && bits.read_u64() == Some(y)
}

#[quickcheck]
fn back_to_back_be_unchecked_u64(x: u64, y: u64) -> bool {
    let mut data = Vec::new();
    data.extend_from_slice(&(x.to_be_bytes()));
    data.extend_from_slice(&(y.to_be_bytes()));
    let mut bits = BigEndianReader::new(data.as_slice());
    bits.read_u64_unchecked() == x && bits.read_u64_unchecked() == y
}
