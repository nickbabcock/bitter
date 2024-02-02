use bitter::BitReader;
use std::io::Read;

// Using debug_assertions as a poor man's way to omit no_panic compilation on
// unoptimized builds.
#[cfg_attr(not(debug_assertions), no_panic::no_panic)]
#[inline(never)]
fn read_data(data: &[u8]) -> Option<i64> {
    let mut reader = bitter::LittleEndianReader::new(data);
    let result = reader.read_signed_bits(27)?;
    let mut buf = [0u8; 10];
    if !reader.read_bytes(&mut buf) {
        return None;
    }

    Some(result + i64::from(buf[0]))
}

fn main() {
    let stdin = std::io::stdin();
    let mut data = Vec::new();
    stdin.lock().read_to_end(&mut data).unwrap();
    println!("{:?}", read_data(&data));
}
