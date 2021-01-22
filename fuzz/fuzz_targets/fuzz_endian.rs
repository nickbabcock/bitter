#![no_main]
use libfuzzer_sys::fuzz_target;
use bitter::{LittleEndianBits, BitReader, BigEndianBits};

fuzz_target!(|data: &[u8]| {
    let mut lebits = LittleEndianBits::new(data);
    let mut bebits = BigEndianBits::new(data);
    for &i in data {
        assert_eq!(lebits.read_u8().unwrap(), i);
        assert_eq!(bebits.read_u8().unwrap(), i);
    }

    assert_eq!(lebits.read_u8(), None);
    assert_eq!(bebits.read_u8(), None);
    assert!(lebits.is_empty());
    assert!(bebits.is_empty());
});