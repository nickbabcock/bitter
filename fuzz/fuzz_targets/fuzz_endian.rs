#![no_main]
use libfuzzer_sys::fuzz_target;
use bitter::{LittleEndianReader, BitReader, BigEndianReader};

fuzz_target!(|data: &[u8]| {
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
});