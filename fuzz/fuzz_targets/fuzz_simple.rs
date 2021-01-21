#![no_main]
use libfuzzer_sys::fuzz_target;
use bitter::{LittleEndianBits, BitReader};

fuzz_target!(|data: &[u8]| {
    let mut bits = bitter::LittleEndianBits::new(data);

    loop {
        if bits.read_u32_bits(17).is_none() {
            break;
        }
    }
});
