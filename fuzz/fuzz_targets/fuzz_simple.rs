#![no_main]
use libfuzzer_sys::fuzz_target;
use bitter;

fuzz_target!(|data: &[u8]| {
    let mut bits = bitter::BitGet::new(data);

    loop {
        if bits.read_u32_bits(17).is_none() {
            break;
        }
    }
});
