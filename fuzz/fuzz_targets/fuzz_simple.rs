#![no_main]
use libfuzzer_sys::fuzz_target;
use bitter::{LittleEndianReader, BitReader};

fuzz_target!(|data: &[u8]| {
    let mut bits = LittleEndianReader::new(data);

    loop {
        if bits.read_bits(17).is_none() {
            assert!(!bits.has_bits_remaining(17));
            break;
        }
    }
});
