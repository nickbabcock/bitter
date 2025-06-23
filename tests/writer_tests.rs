#![cfg(feature = "std")]

use bitter::*;

#[test]
fn test_write_read_roundtrip_le() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);
        writer.write_u8(0xab).unwrap();
        writer.flush().unwrap();
    }

    let mut reader = LittleEndianReader::new(&buffer);
    assert_eq!(reader.read_u8(), Some(0xab));
}

#[test]
fn test_write_read_roundtrip_le_complex() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);
        writer.write_bit(true).unwrap();
        writer.write_bit(false).unwrap();
        writer.write_u8(0xab).unwrap();
        writer.write_u16(0x1234).unwrap();
        writer.write_u32(0xdeadbeef).unwrap();
        writer.write_u64(0x123456789abcdef0).unwrap();
        writer.write_f32(12.5).unwrap();
        writer.write_f64(42.125).unwrap();
        writer.write_bits(5, 0x1f).unwrap();
        writer.write_signed_bits(4, -3).unwrap();
        writer.flush().unwrap();
    }

    let mut reader = LittleEndianReader::new(&buffer);
    assert_eq!(reader.read_bit(), Some(true));
    assert_eq!(reader.read_bit(), Some(false));
    assert_eq!(reader.read_u8(), Some(0xab));
    assert_eq!(reader.read_u16(), Some(0x1234));
    assert_eq!(reader.read_u32(), Some(0xdeadbeef));
    assert_eq!(reader.read_u64(), Some(0x123456789abcdef0));
    assert_eq!(reader.read_f32(), Some(12.5));
    assert_eq!(reader.read_f64(), Some(42.125));
    assert_eq!(reader.read_bits(5), Some(0x1f));
    assert_eq!(reader.read_signed_bits(4), Some(-3));
}

#[test]
fn test_write_read_roundtrip_be() {
    let mut buffer = Vec::new();
    {
        let mut writer = BigEndianWriter::new(&mut buffer);
        writer.write_bit(true).unwrap();
        writer.write_bit(false).unwrap();
        writer.write_u8(0xab).unwrap();
        writer.write_u16(0x1234).unwrap();
        writer.write_u32(0xdeadbeef).unwrap();
        writer.write_u64(0x123456789abcdef0).unwrap();
        writer.write_f32(12.5).unwrap();
        writer.write_f64(42.125).unwrap();
        writer.write_bits(5, 0x1f).unwrap();
        writer.write_signed_bits(4, -3).unwrap();
        writer.flush().unwrap();
    }

    let mut reader = BigEndianReader::new(&buffer);
    assert_eq!(reader.read_bit(), Some(true));
    assert_eq!(reader.read_bit(), Some(false));
    assert_eq!(reader.read_u8(), Some(0xab));
    assert_eq!(reader.read_u16(), Some(0x1234));
    assert_eq!(reader.read_u32(), Some(0xdeadbeef));
    assert_eq!(reader.read_u64(), Some(0x123456789abcdef0));
    assert_eq!(reader.read_f32(), Some(12.5));
    assert_eq!(reader.read_f64(), Some(42.125));
    assert_eq!(reader.read_bits(5), Some(0x1f));
    assert_eq!(reader.read_signed_bits(4), Some(-3));
}

#[test]
fn test_bit_alignment() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);
        assert!(writer.byte_aligned());
        writer.write_bit(true).unwrap();
        assert!(!writer.byte_aligned());
        writer.write_bits(7, 0x7f).unwrap();
        assert!(writer.byte_aligned());
        writer.flush().unwrap();
    }

    let mut reader = LittleEndianReader::new(&buffer);
    assert!(reader.byte_aligned());
    assert_eq!(reader.read_bit(), Some(true));
    assert!(!reader.byte_aligned());
    assert_eq!(reader.read_bits(7), Some(0x7f));
    assert!(reader.byte_aligned());
}

#[test]
fn test_native_endian() {
    let mut buffer = Vec::new();
    {
        let mut writer = NativeEndianWriter::new(&mut buffer);
        writer.write_u32(0x12345678).unwrap();
        writer.flush().unwrap();
    }

    let mut reader = NativeEndianReader::new(&buffer);
    assert_eq!(reader.read_u32(), Some(0x12345678));
}

#[test]
fn test_various_bit_counts() {
    for bits in 1..=64 {
        let value = if bits == 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };

        let mut buffer = Vec::new();
        {
            let mut writer = LittleEndianWriter::new(&mut buffer);
            writer.write_bits(bits, value).unwrap();
            writer.flush().unwrap();
        }

        let mut reader = LittleEndianReader::new(&buffer);
        assert_eq!(
            reader.read_bits(bits),
            Some(value),
            "Failed for {} bits",
            bits
        );
    }
}

#[test]
fn test_signed_bits_negative() {
    let test_cases = vec![
        (1, -1i64, 1u64),
        (4, -1i64, 0xf),
        (4, -8i64, 0x8),
        (8, -128i64, 0x80),
        (16, -32768i64, 0x8000),
    ];

    for (bits, signed_val, expected_unsigned) in test_cases {
        let mut buffer = Vec::new();
        {
            let mut writer = LittleEndianWriter::new(&mut buffer);
            writer.write_signed_bits(bits, signed_val).unwrap();
            writer.flush().unwrap();
        }

        let mut reader = LittleEndianReader::new(&buffer);
        assert_eq!(reader.read_bits(bits), Some(expected_unsigned));

        let mut reader = LittleEndianReader::new(&buffer);
        assert_eq!(reader.read_signed_bits(bits), Some(signed_val));
    }
}

#[test]
fn test_mixed_operations() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);
        writer.write_bits(3, 0b101).unwrap();
        writer.write_u8(0xff).unwrap();
        writer.write_bits(2, 0b11).unwrap();
        writer.write_u16(0x1234).unwrap();
        writer.write_bit(false).unwrap();
        writer.flush().unwrap();
    }

    let mut reader = LittleEndianReader::new(&buffer);
    assert_eq!(reader.read_bits(3), Some(0b101));
    assert_eq!(reader.read_u8(), Some(0xff));
    assert_eq!(reader.read_bits(2), Some(0b11));
    assert_eq!(reader.read_u16(), Some(0x1234));
    assert_eq!(reader.read_bit(), Some(false));
}

#[test]
fn test_zero_bits() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);
        writer.write_bits(0, 0).unwrap();
        writer.write_u8(0x42).unwrap();
        writer.write_bits(0, 0).unwrap();
        writer.flush().unwrap();
    }

    let mut reader = LittleEndianReader::new(&buffer);
    assert_eq!(reader.read_bits(0), Some(0));
    assert_eq!(reader.read_u8(), Some(0x42));
    assert_eq!(reader.read_bits(0), Some(0));
}

#[test]
fn test_flush_padding_le() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);
        writer.write_bits(3, 0b101).unwrap();
        writer.flush().unwrap();
    }

    assert_eq!(buffer.len(), 1);
    // In little endian, 3 bits 0b101 should be at the low end: xxxxx101 where x is zero padding
    // So we expect: 0000_0101 = 0x05
    assert_eq!(buffer[0], 0b00000101);
    assert_eq!(buffer[0] & 0b111, 0b101); // Verify our bits are there
    assert_eq!(buffer[0] & 0b1111_1000, 0); // Verify padding is zero
}

#[test]
fn test_flush_padding_be() {
    let mut buffer = Vec::new();
    {
        let mut writer = BigEndianWriter::new(&mut buffer);
        writer.write_bits(3, 0b101).unwrap();
        writer.flush().unwrap();
    }

    assert_eq!(buffer.len(), 1);
    // In big endian, the 3 bits should be in the high bits
    // 0b101 (value 5) written in big endian should appear as: 101xxxxx where x is padding
    // So we expect: 1010_0000 = 0xA0
    assert_eq!(buffer[0] & 0b1110_0000, 0b1010_0000);
    assert_eq!(buffer[0] & 0b0001_1111, 0);

    // Verify the actual value matches our expectation
    assert_eq!(buffer[0], 0b1010_0000);
}

#[test]
fn test_into_inner() {
    let mut buffer = Vec::new();
    let writer = LittleEndianWriter::new(&mut buffer);
    let inner = writer.into_inner().unwrap();
    assert!(std::ptr::eq(inner, &buffer));
}

#[test]
fn test_write_bytes_aligned_le() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);

        // Ensure we're byte-aligned
        assert!(writer.byte_aligned());

        // Write bytes using fast path
        let test_data = [0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF];
        writer.write_bytes(&test_data).unwrap();

        // Should still be byte-aligned after writing complete bytes
        assert!(writer.byte_aligned());

        writer.flush().unwrap();
    }

    // Verify data was written correctly
    assert_eq!(buffer, &[0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF]);

    // Verify we can read it back correctly
    let mut reader = LittleEndianReader::new(&buffer);
    assert_eq!(reader.read_u8(), Some(0x12));
    assert_eq!(reader.read_u8(), Some(0x34));
    assert_eq!(reader.read_u8(), Some(0x56));
    assert_eq!(reader.read_u8(), Some(0x78));
    assert_eq!(reader.read_u8(), Some(0xAB));
    assert_eq!(reader.read_u8(), Some(0xCD));
    assert_eq!(reader.read_u8(), Some(0xEF));
}

#[test]
fn test_write_bytes_aligned_be() {
    let mut buffer = Vec::new();
    {
        let mut writer = BigEndianWriter::new(&mut buffer);

        // Ensure we're byte-aligned
        assert!(writer.byte_aligned());

        // Write bytes using fast path
        let test_data = [0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF];
        writer.write_bytes(&test_data).unwrap();

        // Should still be byte-aligned after writing complete bytes
        assert!(writer.byte_aligned());

        writer.flush().unwrap();
    }

    // Verify data was written correctly
    assert_eq!(buffer, &[0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF]);

    // Verify we can read it back correctly
    let mut reader = BigEndianReader::new(&buffer);
    assert_eq!(reader.read_u8(), Some(0x12));
    assert_eq!(reader.read_u8(), Some(0x34));
    assert_eq!(reader.read_u8(), Some(0x56));
    assert_eq!(reader.read_u8(), Some(0x78));
    assert_eq!(reader.read_u8(), Some(0xAB));
    assert_eq!(reader.read_u8(), Some(0xCD));
    assert_eq!(reader.read_u8(), Some(0xEF));
}

#[test]
fn test_write_bytes_unaligned_le() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);

        // Write a single bit to make writer unaligned
        writer.write_bit(true).unwrap();
        assert!(!writer.byte_aligned());

        // Write bytes using slow path (unaligned)
        let test_data = [0xFF, 0x00, 0xAA];
        writer.write_bytes(&test_data).unwrap();

        writer.flush().unwrap();
    }

    // Verify we can read it back correctly
    let mut reader = LittleEndianReader::new(&buffer);
    assert_eq!(reader.read_bit(), Some(true));
    assert_eq!(reader.read_u8(), Some(0xFF));
    assert_eq!(reader.read_u8(), Some(0x00));
    assert_eq!(reader.read_u8(), Some(0xAA));
}

#[test]
fn test_write_bytes_unaligned_be() {
    let mut buffer = Vec::new();
    {
        let mut writer = BigEndianWriter::new(&mut buffer);

        // Write some bits to make writer unaligned
        writer.write_bits(3, 0b101).unwrap();
        assert!(!writer.byte_aligned());

        // Write bytes using slow path (unaligned)
        let test_data = [0xFF, 0x00, 0xAA];
        writer.write_bytes(&test_data).unwrap();

        writer.flush().unwrap();
    }

    // Verify we can read it back correctly
    let mut reader = BigEndianReader::new(&buffer);
    assert_eq!(reader.read_bits(3), Some(0b101));
    assert_eq!(reader.read_u8(), Some(0xFF));
    assert_eq!(reader.read_u8(), Some(0x00));
    assert_eq!(reader.read_u8(), Some(0xAA));
}

#[test]
fn test_write_bytes_mixed_aligned_unaligned_le() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);

        // Start aligned, write bytes (fast path)
        assert!(writer.byte_aligned());
        let data1 = [0x11, 0x22];
        writer.write_bytes(&data1).unwrap();
        assert!(writer.byte_aligned());

        // Write bits to become unaligned
        writer.write_bits(4, 0xF).unwrap();
        assert!(!writer.byte_aligned());

        // Write bytes while unaligned (slow path)
        let data2 = [0x33, 0x44];
        writer.write_bytes(&data2).unwrap();

        // Write more bits
        writer.write_bits(4, 0xA).unwrap();
        assert!(writer.byte_aligned());

        // Write bytes again while aligned (fast path)
        let data3 = [0x55, 0x66];
        writer.write_bytes(&data3).unwrap();

        writer.flush().unwrap();
    }

    // Verify we can read it back correctly
    let mut reader = LittleEndianReader::new(&buffer);
    assert_eq!(reader.read_u8(), Some(0x11));
    assert_eq!(reader.read_u8(), Some(0x22));
    assert_eq!(reader.read_bits(4), Some(0xF));
    assert_eq!(reader.read_u8(), Some(0x33));
    assert_eq!(reader.read_u8(), Some(0x44));
    assert_eq!(reader.read_bits(4), Some(0xA));
    assert_eq!(reader.read_u8(), Some(0x55));
    assert_eq!(reader.read_u8(), Some(0x66));
}

#[test]
fn test_write_bytes_mixed_aligned_unaligned_be() {
    let mut buffer = Vec::new();
    {
        let mut writer = BigEndianWriter::new(&mut buffer);

        // Start aligned, write bytes (fast path)
        assert!(writer.byte_aligned());
        let data1 = [0x11, 0x22];
        writer.write_bytes(&data1).unwrap();
        assert!(writer.byte_aligned());

        // Write bits to become unaligned
        writer.write_bits(4, 0xF).unwrap();
        assert!(!writer.byte_aligned());

        // Write bytes while unaligned (slow path)
        let data2 = [0x33, 0x44];
        writer.write_bytes(&data2).unwrap();

        // Write more bits
        writer.write_bits(4, 0xA).unwrap();
        assert!(writer.byte_aligned());

        // Write bytes again while aligned (fast path)
        let data3 = [0x55, 0x66];
        writer.write_bytes(&data3).unwrap();

        writer.flush().unwrap();
    }

    // Verify we can read it back correctly
    let mut reader = BigEndianReader::new(&buffer);
    assert_eq!(reader.read_u8(), Some(0x11));
    assert_eq!(reader.read_u8(), Some(0x22));
    assert_eq!(reader.read_bits(4), Some(0xF));
    assert_eq!(reader.read_u8(), Some(0x33));
    assert_eq!(reader.read_u8(), Some(0x44));
    assert_eq!(reader.read_bits(4), Some(0xA));
    assert_eq!(reader.read_u8(), Some(0x55));
    assert_eq!(reader.read_u8(), Some(0x66));
}

#[test]
fn test_write_bytes_empty_buffer() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);

        // Test writing empty buffer (should be no-op)
        writer.write_bytes(&[]).unwrap();
        assert!(writer.byte_aligned());

        // Write some data, then empty buffer again
        writer.write_u8(0x42).unwrap();
        writer.write_bytes(&[]).unwrap();

        writer.flush().unwrap();
    }

    assert_eq!(buffer, &[0x42]);
}

#[test]
fn test_write_bytes_large_aligned() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);

        // Create large data to test bulk write efficiency
        let large_data: Vec<u8> = (0..1000).map(|i| (i % 256) as u8).collect();

        // Should use fast path since we're byte-aligned
        assert!(writer.byte_aligned());
        writer.write_bytes(&large_data).unwrap();
        assert!(writer.byte_aligned());

        writer.flush().unwrap();
    }

    // Verify data matches exactly
    let expected: Vec<u8> = (0..1000).map(|i| (i % 256) as u8).collect();
    assert_eq!(buffer, expected);
}

#[test]
fn test_write_bytes_vs_individual_writes() {
    let test_data = [0xDE, 0xAD, 0xBE, 0xEF];

    // Test individual byte writes
    let mut buffer1 = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer1);
        for &byte in &test_data {
            writer.write_u8(byte).unwrap();
        }
        writer.flush().unwrap();
    }

    // Test bulk write_bytes
    let mut buffer2 = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer2);
        writer.write_bytes(&test_data).unwrap();
        writer.flush().unwrap();
    }

    // Results should be identical
    assert_eq!(buffer1, buffer2);
    assert_eq!(buffer1, test_data);
}

#[test]
fn test_drop_flushes_buffer() {
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);
        writer.write_bits(5, 0b10101).unwrap();
        // Writer is dropped here, should flush automatically
    }

    // Buffer should contain the flushed data
    assert_eq!(buffer.len(), 1);
    assert_eq!(buffer[0], 0b10101); // Our 5 bits
}

#[test]
fn test_drop_flushes_buffer_be() {
    let mut buffer = Vec::new();
    {
        let mut writer = BigEndianWriter::new(&mut buffer);
        writer.write_bits(3, 0b101).unwrap();
        // Writer is dropped here, should flush automatically
    }

    // Buffer should contain the flushed data
    assert_eq!(buffer.len(), 1);
    // In big endian, 3 bits should be in high positions: 101xxxxx
    assert_eq!(buffer[0], 0b10100000);
}

#[test]
fn test_into_inner_flushes_buffer() {
    let mut original_buffer = Vec::new();
    let writer = {
        let mut writer = LittleEndianWriter::new(&mut original_buffer);
        writer.write_bits(6, 0b110011).unwrap();
        writer
    };

    // into_inner should flush the buffer before returning
    let recovered_buffer = writer.into_inner().unwrap();

    // Check that it's the same buffer reference
    assert!(std::ptr::eq(recovered_buffer, &original_buffer));

    // Check that the buffer was flushed with zero padding
    assert_eq!(original_buffer.len(), 1);
    assert_eq!(original_buffer[0], 0b110011); // 6 bits + 2 zero-padded bits
}

#[test]
fn test_into_inner_error_recovery() {
    use std::io::{Error, ErrorKind};

    #[derive(Debug)]
    struct FailingWriter {
        should_fail_flush: bool,
    }

    impl std::io::Write for FailingWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            if self.should_fail_flush && !buf.is_empty() {
                Err(Error::new(ErrorKind::Other, "write failed during flush"))
            } else {
                Ok(buf.len())
            }
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    let failing_writer = FailingWriter {
        should_fail_flush: true,
    };
    let mut writer = LittleEndianWriter::new(failing_writer);
    // Write enough bits to force a partial byte that needs flushing
    writer.write_bits(3, 0b101).unwrap();

    // into_inner should fail and allow recovery
    match writer.into_inner() {
        Ok(_) => panic!("Expected error"),
        Err(into_inner_error) => {
            // Check error details
            let error = into_inner_error.error();
            assert_eq!(error.kind(), ErrorKind::Other);
            assert_eq!(error.to_string(), "write failed during flush");

            // Recover the writer
            let mut recovered_writer = into_inner_error.into_inner();

            // Fix the underlying writer to not fail
            recovered_writer.get_mut().should_fail_flush = false;

            // Now into_inner should succeed
            let _recovered_inner = recovered_writer.into_inner().unwrap();
        }
    }
}

#[test]
fn test_drop_vs_into_inner_flush_equivalence() {
    // Test that Drop and into_inner produce the same results
    let test_bits = [(3, 0b101), (5, 0b11010), (2, 0b11)];

    // Test Drop behavior
    let mut buffer1 = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer1);
        for &(bits, value) in &test_bits {
            writer.write_bits(bits, value).unwrap();
        }
        // Drop happens here
    }

    // Test into_inner behavior
    let mut buffer2 = Vec::new();
    let writer = {
        let mut writer = LittleEndianWriter::new(&mut buffer2);
        for &(bits, value) in &test_bits {
            writer.write_bits(bits, value).unwrap();
        }
        writer
    };
    let _recovered = writer.into_inner().unwrap();

    // Both should produce identical results
    assert_eq!(buffer1, buffer2);
}

#[test]
fn test_zero_padding_footgun_warning() {
    // This test demonstrates the potential "footgun" behavior of automatic zero padding
    // that might surprise users who don't expect the padding bits.

    // Case 1: Writing exactly 5 bits and expecting only those bits
    let mut buffer = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer);
        writer.write_bits(5, 0b11111).unwrap(); // All ones in 5 bits
                                                // Drop happens here - this will zero-pad the remaining 3 bits!
    }

    // The user might expect the byte to be 0b11111 (31) but it's actually 0b00011111 (31)
    // In this case it happens to work out the same, but let's try a different example:
    assert_eq!(buffer[0], 0b00011111); // 5 bits + 3 zero-padded bits

    // Case 2: Big-endian padding can be more surprising
    let mut buffer_be = Vec::new();
    {
        let mut writer = BigEndianWriter::new(&mut buffer_be);
        writer.write_bits(3, 0b111).unwrap(); // 3 ones
                                              // Drop happens here - pads low bits with zeros
    }

    // User might expect 0b111 (7) but gets 0b11100000 (224) due to positioning and padding
    assert_eq!(buffer_be[0], 0b11100000); // 3 bits + 5 zero-padded bits

    // Case 3: Demonstrating why explicit control is better
    let mut buffer_explicit = Vec::new();
    {
        let mut writer = LittleEndianWriter::new(&mut buffer_explicit);
        writer.write_bits(6, 0b101010).unwrap(); // 6 bits

        // If user wants different padding behavior, they should handle it explicitly:
        // writer.write_bits(2, 0b11).unwrap(); // Explicit padding with ones instead of zeros

        writer.flush().unwrap(); // Explicit flush with zero padding
    }

    assert_eq!(buffer_explicit[0], 0b00101010); // 6 bits + 2 zero-padded bits

    // The key insight: automatic zero-padding on drop/flush can silently change
    // the meaning of your data if you're not expecting it!
}
