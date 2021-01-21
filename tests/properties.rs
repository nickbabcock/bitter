extern crate quickcheck;
#[macro_use]
extern crate quickcheck_macros;
extern crate bitter;
extern crate bitterv1;

use bitter::{BigEndianBits, BitOrder, LittleEndianBits};

#[quickcheck]
fn read_bytes_eq(k1: u8, data: Vec<u8>) -> bool {
    let mut bits = LittleEndianBits::new(data.as_slice());
    let mut buf = vec![0u8; usize::from(k1)];
    if !bits.read_bytes(&mut buf) {
        k1 > data.len() as u8
    } else {
        buf.as_slice() == &data[..usize::from(k1)]
    }
}

#[quickcheck]
fn has_bits_remaining_bit_reads(data: Vec<u8>) -> bool {
    let mut bits = LittleEndianBits::new(data.as_slice());
    (1..128).all(|_x| bits.has_bits_remaining(1) == bits.read_bit().is_some())
}

#[quickcheck]
fn has_bits_remaining(data: Vec<u8>) -> bool {
    let mut bits = LittleEndianBits::new(data.as_slice());
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

    let mut bits = LittleEndianBits::new(data.as_slice());
    bits.read_u32_bits_unchecked(3);

    let mut buf = vec![0u8; data.len() - 1];
    bits.read_bytes(&mut buf)
}

#[quickcheck]
fn v1_eq(data: Vec<u8>) -> bool {
    let mut bits = LittleEndianBits::new(data.as_slice());
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
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    lebits.read_u8() == bebits.read_u8()
}

#[quickcheck]
fn read_u16_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    lebits.read_u16().map(|x| x.to_be()) == bebits.read_u16()
}

#[quickcheck]
fn read_u32_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    lebits.read_u32().map(|x| x.to_be()) == bebits.read_u32()
}

#[quickcheck]
fn read_u64_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    lebits.read_u64().map(|x| x.to_be()) == bebits.read_u64()
}

#[quickcheck]
fn read_byte_unchecked_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    lebits.has_bits_remaining(8) == bebits.has_bits_remaining(8)
        && (!lebits.has_bits_remaining(8)
            || lebits.read_u8_unchecked() == bebits.read_u8_unchecked())
}

#[quickcheck]
fn read_u16_unchecked_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    lebits.has_bits_remaining(16) == bebits.has_bits_remaining(16)
        && (!lebits.has_bits_remaining(16)
            || lebits.read_u16_unchecked().to_be() == bebits.read_u16_unchecked())
}

#[quickcheck]
fn read_u32_unchecked_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    lebits.has_bits_remaining(32) == bebits.has_bits_remaining(32)
        && (!lebits.has_bits_remaining(32)
            || lebits.read_u32_unchecked().to_be() == bebits.read_u32_unchecked())
}

#[quickcheck]
fn read_u64_unchecked_eq(data: Vec<u8>) -> bool {
    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = BigEndianBits::new(data.as_slice());

    lebits.has_bits_remaining(64) == bebits.has_bits_remaining(64)
        && (!lebits.has_bits_remaining(64)
            || lebits.read_u64_unchecked().to_be() == bebits.read_u64_unchecked())
}

#[quickcheck]
fn has_bits_remaining_bit_reads_ends(reads: u8, data: Vec<u8>) -> bool {
    fn test_fn<B: BitOrder>(bits: &mut B, reads: u8) -> bool {
        let mut result = true;
        if bits.has_bits_remaining(usize::from(reads)) {
            for _ in 0..reads {
                result &= bits.read_bit().is_some();
            }
        }

        result
    }

    let mut lebits = LittleEndianBits::new(data.as_slice());
    let mut bebits = LittleEndianBits::new(data.as_slice());

    test_fn(&mut lebits, reads) && test_fn(&mut bebits, reads)
}

#[quickcheck]
fn read_u32_val_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianBits::new(&le_data);
    let mut bebits = BigEndianBits::new(&be_data);

    lebits.read_u32() == bebits.read_u32()
}

#[quickcheck]
fn read_u32_unchecked_val_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianBits::new(&le_data);
    let mut bebits = BigEndianBits::new(&be_data);

    let le = lebits.read_u32_unchecked();
    le == bebits.read_u32_unchecked() && le == bits
}

#[quickcheck]
fn read_f32_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianBits::new(&le_data);
    let mut bebits = BigEndianBits::new(&be_data);

    lebits.read_f32() == bebits.read_f32()
}

#[quickcheck]
fn read_f32_unchecked_eq(bits: u32) -> bool {
    let le_data = bits.to_le_bytes();
    let be_data = bits.to_be_bytes();

    let mut lebits = LittleEndianBits::new(&le_data);
    let mut bebits = BigEndianBits::new(&be_data);

    lebits.read_f32_unchecked() == bebits.read_f32_unchecked()
}
