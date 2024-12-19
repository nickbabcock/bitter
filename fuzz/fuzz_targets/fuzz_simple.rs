#![no_main]
use bitter::{BigEndianReader, BitReader, LittleEndianReader};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let size = LittleEndianReader::new(data).read_u32().unwrap_or(0);

    let mut bits = LittleEndianReader::new(data);

    loop {
        if bits.read_bits(17).is_none() {
            assert!(!bits.has_bits_remaining(17));
            break;
        }
    }

    let mut lebits = LittleEndianReader::new(data);
    let mut bebits = BigEndianReader::new(data);
    for &i in data {
        assert_eq!(lebits.read_u8().unwrap(), i);
        assert_eq!(bebits.read_u8().unwrap(), i);
    }

    assert_eq!(lebits.read_u8(), None);
    assert_eq!(bebits.read_u8(), None);
    assert!(lebits.is_empty());
    assert!(bebits.is_empty());

    let mut bitter = LittleEndianReader::new(data);
    let mut i = 0;
    while bitter.lookahead_bits() != 0 {
        let read = (i % 56 + 1) % bitter.lookahead_bits() as u32 + 1;
        i += 1;
        bitter.peek(read);
        bitter.consume(read);
        if bitter.lookahead_bits() == 0 {
            bitter.refill_lookahead();
        }
    }

    use bitstream_io::BitRead;

    let bits = (size % bitter::MAX_READ_BITS) + 1;
    let mut io = bitstream_io::BitReader::endian(data, bitstream_io::LittleEndian);
    let mut bitter = LittleEndianReader::new(&data);

    while bitter.has_bits_remaining(bits as usize) {
        assert_eq!(io.read(bits).ok(), bitter.read_bits(bits))
    }

    let mut io = bitstream_io::BitReader::endian(data, bitstream_io::BigEndian);
    let mut bitter = BigEndianReader::new(&data);

    while bitter.has_bits_remaining(bits as usize) {
        assert_eq!(io.read(bits).ok(), bitter.read_bits(bits))
    }

    let mut io = bitstream_io::BitReader::endian(data, bitstream_io::BigEndian);
    let mut bitter = BigEndianReader::new(&data);
    assert_eq!(io.read(bits).ok(), bitter.read_bits(bits));
    let mut out1 = vec![0; 12];
    let mut out2 = vec![0; 12];
    let result1 = io.read_bytes(&mut out1);
    let result2 = bitter.read_bytes(&mut out2);
    assert_eq!(result1.is_ok(), result2);
    if result2 {
        assert_eq!(out1, out2);
    }
});
