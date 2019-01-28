#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate bitter;

fuzz_target!(|data: &[u8]| {
    let mut bits = bitter::BitGet::new(data);

    // A simple fuzz to ensure we satisfy the llvm heap sanitizer
    bits.read_u32_bits(17);
});
