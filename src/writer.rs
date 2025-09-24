use std::error::Error;
use std::fmt;
use std::io::{Result, Write};
use std::mem::ManuallyDrop;

/// Write bits in a given endian order
///
/// The `BitWriter` trait provides methods for writing data bit-by-bit to any type
/// that implements `std::io::Write`. It supports writing individual bits, standard
/// data types (integers, floats), and arbitrary bit sequences.
///
/// # Examples
///
/// ```rust
/// use bitter::{BitWriter, LittleEndianWriter};
///
/// let mut buffer = Vec::new();
/// let mut writer = LittleEndianWriter::new(&mut buffer);
///
/// writer.write_bit(true).unwrap();
/// writer.write_u8(0xff).unwrap();
/// writer.write_bits(4, 0xA).unwrap();
/// writer.flush().unwrap();
/// ```
pub trait BitWriter {
    /// Write a single bit
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_bit(true).unwrap();
    ///     writer.write_bit(false).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// assert_eq!(buffer, &[0b01]);
    /// ```
    fn write_bit(&mut self, bit: bool) -> Result<()>;

    /// Write 8 bits as a byte
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_u8(0xAB).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// assert_eq!(buffer, &[0xAB]);
    /// ```
    fn write_u8(&mut self, value: u8) -> Result<()>;

    /// Write 8 bits as a signed byte
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_i8(-42).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// assert_eq!(buffer, &[(-42i8) as u8]);
    /// ```
    fn write_i8(&mut self, value: i8) -> Result<()>;

    /// Write 16 bits as an unsigned short
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_u16(0x1234).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// // Little endian: least significant byte first
    /// assert_eq!(buffer, &[0x34, 0x12]);
    /// ```
    fn write_u16(&mut self, value: u16) -> Result<()>;

    /// Write 16 bits as a signed short
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, BigEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = BigEndianWriter::new(&mut buffer);
    ///     writer.write_i16(-1000).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// // Big endian: most significant byte first
    /// let expected = (-1000i16).to_be_bytes();
    /// assert_eq!(buffer, expected.as_slice());
    /// ```
    fn write_i16(&mut self, value: i16) -> Result<()>;

    /// Write 32 bits as an unsigned int
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_u32(0xDEADBEEF).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// assert_eq!(buffer, &[0xEF, 0xBE, 0xAD, 0xDE]);
    /// ```
    fn write_u32(&mut self, value: u32) -> Result<()>;

    /// Write 32 bits as a signed int
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_i32(-123456).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// let expected = (-123456i32).to_le_bytes();
    /// assert_eq!(buffer, expected.as_slice());
    /// ```
    fn write_i32(&mut self, value: i32) -> Result<()>;

    /// Write 32 bits as a floating point
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_f32(3.14159).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// let expected = 3.14159f32.to_le_bytes();
    /// assert_eq!(buffer, expected.as_slice());
    /// ```
    fn write_f32(&mut self, value: f32) -> Result<()>;

    /// Write 64 bits as an unsigned long
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, BigEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = BigEndianWriter::new(&mut buffer);
    ///     writer.write_u64(0x123456789ABCDEF0).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// let expected = 0x123456789ABCDEF0u64.to_be_bytes();
    /// assert_eq!(buffer, expected.as_slice());
    /// ```
    fn write_u64(&mut self, value: u64) -> Result<()>;

    /// Write 64 bits as a signed long
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_i64(-9876543210).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// let expected = (-9876543210i64).to_le_bytes();
    /// assert_eq!(buffer, expected.as_slice());
    /// ```
    fn write_i64(&mut self, value: i64) -> Result<()>;

    /// Write 64 bits as a floating point
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_f64(2.718281828459045).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// let expected = 2.718281828459045f64.to_le_bytes();
    /// assert_eq!(buffer, expected.as_slice());
    /// ```
    fn write_f64(&mut self, value: f64) -> Result<()>;

    /// Write an arbitrary number of bits (up to and including 64) as unsigned value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     
    ///     // Write 12 bits with value 0xABC
    ///     writer.write_bits(12, 0xABC).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// // 0xABC = 2748 = 1010 1011 1100 in binary
    /// // In little endian, this gets packed as: [0xBC, 0x0A]
    /// assert_eq!(buffer, &[0xBC, 0x0A]);
    /// ```
    fn write_bits(&mut self, bits: u32, value: u64) -> Result<()>;

    /// Write an arbitrary number of bits (up to and including 64) as signed value
    ///
    /// The value is sign-extended or truncated to fit the specified number of bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     
    ///     // Write -3 in 4 bits (will be 0b1101 in two's complement)
    ///     writer.write_signed_bits(4, -3).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// // -3 in 4 bits = 0b1101, padded with zeros to complete the byte
    /// assert_eq!(buffer, &[0x0D]); // 0b0000_1101
    /// ```
    fn write_signed_bits(&mut self, bits: u32, value: i64) -> Result<()>;

    /// Returns the number of bits written in the current partial byte
    ///
    /// When the writer is byte-aligned, this returns 0. Otherwise, it returns
    /// the number of bits (1-7) already written in the current byte.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let mut writer = LittleEndianWriter::new(&mut buffer);
    ///
    /// assert_eq!(writer.unaligned_bits(), 0); // Byte-aligned
    ///
    /// writer.write_bit(true).unwrap();
    /// assert_eq!(writer.unaligned_bits(), 1); // 1 bit in current byte
    ///
    /// writer.write_bits(7, 0x7F).unwrap();
    /// assert_eq!(writer.unaligned_bits(), 0); // Aligned again (1+7=8)
    /// ```
    fn unaligned_bits(&self) -> u32;

    /// Write the provided buffer as bytes
    ///
    /// This method writes the entire buffer as a sequence of bytes. If the writer
    /// is not currently byte-aligned, the bytes will be written starting from the
    /// current bit position, potentially spanning across byte boundaries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///
    ///     // Write some bytes
    ///     let data = [0xAB, 0xCD, 0xEF];
    ///     writer.write_bytes(&data).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// assert_eq!(buffer, &[0xAB, 0xCD, 0xEF]);
    /// ```
    ///
    /// # Byte Alignment
    ///
    /// When not byte-aligned, bytes are written bit by bit:
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///
    ///     writer.write_bit(true).unwrap();  // Not byte-aligned
    ///     writer.write_bytes(&[0xFF]).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// // The 0xFF byte gets shifted due to the initial bit
    /// assert_eq!(buffer, &[0xFF, 0x01]);  // 0xFF shifted + remaining bit
    /// ```
    fn write_bytes(&mut self, buf: &[u8]) -> Result<()>;

    /// Flush any buffered bits, padding with zeros if necessary
    ///
    /// This method ensures all pending bits are written to the underlying writer.
    /// If there are partial bits remaining, they are **zero-padded** to complete
    /// the current byte.
    ///
    /// # Zero Padding Behavior
    ///
    /// **Important**: When flushing partial bytes, the remaining bits are always
    /// padded with zeros. This behavior can affect data interpretation if you're
    /// not expecting it:
    ///
    /// - Little-endian: Zero bits are added to the high-order positions
    /// - Big-endian: Zero bits are added to the low-order positions
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_bits(3, 0b101).unwrap(); // Write 3 bits
    ///     // Buffer is still empty until we flush
    ///     writer.flush().unwrap(); // Force write with zero padding
    /// }
    ///
    /// assert_eq!(buffer.len(), 1);
    /// assert_eq!(buffer[0], 0b00000101); // 3 bits + 5 zero-padded bits
    /// ```
    ///
    /// For big-endian, padding appears in different positions:
    ///
    /// ```rust
    /// use bitter::{BitWriter, BigEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = BigEndianWriter::new(&mut buffer);
    ///     writer.write_bits(3, 0b101).unwrap(); // Write 3 bits  
    ///     writer.flush().unwrap(); // Force write with zero padding
    /// }
    ///
    /// assert_eq!(buffer.len(), 1);
    /// assert_eq!(buffer[0], 0b10100000); // 3 bits + 5 zero-padded bits
    /// ```
    fn flush(&mut self) -> Result<()>;
}

#[derive(Debug)]
struct BitterWriter<W: Write, const LE: bool> {
    writer: W,
    bit_buf: u64,
    bit_count: u32,
}

impl<W: Write, const LE: bool> BitterWriter<W, LE> {
    #[inline]
    pub fn new(writer: W) -> Self {
        Self {
            writer,
            bit_buf: 0,
            bit_count: 0,
        }
    }

    /// Unwraps this `BitterWriter`, returning the underlying writer.
    ///
    /// The buffer is flushed before returning the writer. If an error occurs
    /// while flushing, both the error and the writer are returned.
    ///
    /// # Errors
    ///
    /// An [`IntoInnerError`] will be returned if an error occurs while flushing the buffer.
    /// This allows recovery of the original writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let mut writer = LittleEndianWriter::new(&mut buffer);
    /// writer.write_bits(3, 0b101).unwrap();
    ///
    /// let buffer = writer.into_inner().unwrap();
    /// assert_eq!(buffer.len(), 1);
    /// ```
    #[inline]
    pub fn into_inner(self) -> std::result::Result<W, IntoInnerError<BitterWriter<W, LE>>> {
        let mut this = ManuallyDrop::new(self);
        match this.flush_impl() {
            Ok(()) => {
                // Safety: double-drops are prevented by putting `this` in a ManuallyDrop that is never dropped
                let writer = unsafe { std::ptr::read(&this.writer) };
                Ok(writer)
            }
            Err(e) => {
                // Safety: Convert back to owned value for error case
                let this = unsafe { ManuallyDrop::take(&mut this) };
                Err(IntoInnerError::new(e, this))
            }
        }
    }

    /// Gets a reference to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let writer = LittleEndianWriter::new(&mut buffer);
    ///
    /// // Get a reference to the underlying buffer
    /// let buffer_ref = writer.get_ref();
    /// ```
    #[inline]
    pub fn get_ref(&self) -> &W {
        &self.writer
    }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// It is inadvisable to directly write to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let mut writer = LittleEndianWriter::new(&mut buffer);
    ///
    /// // Get a mutable reference to the underlying buffer
    /// let buffer_ref = writer.get_mut();
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut W {
        &mut self.writer
    }

    #[inline]
    fn flush_impl(&mut self) -> Result<()> {
        if self.bit_count > 0 {
            let remaining_bits = 8 - (self.bit_count % 8);
            if remaining_bits != 8 {
                self.write_bits_internal(remaining_bits, 0)?;
            }
        }
        Ok(())
    }

    #[inline]
    fn flush_bytes(&mut self) -> Result<()> {
        let full_bytes = (self.bit_count / 8) as usize;
        let flush_bits = full_bytes * 8;
        if full_bytes > 0 {
            let bytes = if LE {
                self.bit_buf.to_le_bytes()
            } else {
                self.bit_buf.to_be_bytes()
            };
            self.writer.write_all(&bytes[..full_bytes])?;

            if full_bytes < 8 {
                if LE {
                    self.bit_buf >>= flush_bits;
                } else {
                    self.bit_buf <<= flush_bits;
                }
                self.bit_count -= flush_bits as u32;
            } else {
                self.bit_buf = 0;
                self.bit_count = 0;
            }
        }
        Ok(())
    }

    #[inline]
    fn write_bits_internal(&mut self, mut bits: u32, mut value: u64) -> Result<()> {
        debug_assert!(bits <= 64);
        debug_assert!(bits == 0 || bits == 64 || value < (1u64 << bits));

        while bits > 0 {
            let space_in_buf = 64 - self.bit_count;
            let bits_to_write = std::cmp::min(bits, space_in_buf);

            let chunk = if LE {
                value
                    & if bits_to_write == 64 {
                        u64::MAX
                    } else {
                        (1u64 << bits_to_write) - 1
                    }
            } else {
                value >> (bits - bits_to_write)
            };

            if LE {
                self.bit_buf |= chunk << self.bit_count;
                if bits_to_write == 64 {
                    value = 0;
                } else {
                    value >>= bits_to_write;
                }
            } else {
                self.bit_buf |= chunk << (space_in_buf - bits_to_write);
                if bits == bits_to_write {
                    value = 0;
                } else {
                    value &= (1u64 << (bits - bits_to_write)) - 1;
                }
            }

            self.bit_count += bits_to_write;
            bits -= bits_to_write;

            // Flush full bytes
            self.flush_bytes()?;
        }

        Ok(())
    }
}

impl<W: Write, const LE: bool> Drop for BitterWriter<W, LE> {
    fn drop(&mut self) {
        // We ignore errors here since drop should not panic and there's
        // nothing meaningful we can do with the error in this context
        let _ = self.flush_impl();
    }
}

impl<W: Write, const LE: bool> BitWriter for BitterWriter<W, LE> {
    #[inline]
    fn write_bit(&mut self, bit: bool) -> Result<()> {
        self.write_bits_internal(1, bit as u64)
    }

    #[inline]
    fn write_u8(&mut self, value: u8) -> Result<()> {
        self.write_bits_internal(8, value as u64)
    }

    #[inline]
    fn write_i8(&mut self, value: i8) -> Result<()> {
        self.write_bits_internal(8, value as u8 as u64)
    }

    #[inline]
    fn write_u16(&mut self, value: u16) -> Result<()> {
        self.write_bits_internal(16, value as u64)
    }

    #[inline]
    fn write_i16(&mut self, value: i16) -> Result<()> {
        self.write_bits_internal(16, value as u16 as u64)
    }

    #[inline]
    fn write_u32(&mut self, value: u32) -> Result<()> {
        self.write_bits_internal(32, value as u64)
    }

    #[inline]
    fn write_i32(&mut self, value: i32) -> Result<()> {
        self.write_bits_internal(32, value as u32 as u64)
    }

    #[inline]
    fn write_f32(&mut self, value: f32) -> Result<()> {
        self.write_bits_internal(32, value.to_bits() as u64)
    }

    #[inline]
    fn write_u64(&mut self, value: u64) -> Result<()> {
        self.write_bits_internal(64, value)
    }

    #[inline]
    fn write_i64(&mut self, value: i64) -> Result<()> {
        self.write_bits_internal(64, value as u64)
    }

    #[inline]
    fn write_f64(&mut self, value: f64) -> Result<()> {
        self.write_bits_internal(64, value.to_bits())
    }

    #[inline]
    fn write_bits(&mut self, bits: u32, value: u64) -> Result<()> {
        self.write_bits_internal(bits, value)
    }

    #[inline]
    fn write_signed_bits(&mut self, bits: u32, value: i64) -> Result<()> {
        if bits == 0 {
            return Ok(());
        }
        let mask = if bits == 64 {
            !0u64
        } else {
            (1u64 << bits) - 1
        };
        self.write_bits_internal(bits, value as u64 & mask)
    }

    #[inline]
    fn unaligned_bits(&self) -> u32 {
        self.bit_count % 8
    }

    #[inline]
    fn write_bytes(&mut self, buf: &[u8]) -> Result<()> {
        if self.unaligned_bits() == 0 {
            // Fast path: if we're byte-aligned, we can write directly to the underlying writer
            self.writer.write_all(buf)?;
        } else {
            // Slow path: we write in chunks when possible to write as fast as possible
            let mut chunks = buf.chunks_exact(8);
            for c in chunks.by_ref() {
                let arr = [c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]];
                let value = if LE {
                    u64::from_le_bytes(arr)
                } else {
                    u64::from_be_bytes(arr)
                };
                self.write_bits_internal(64, value)?;
            }

            for &byte in chunks.remainder() {
                self.write_bits_internal(8, byte as u64)?;
            }
        }
        Ok(())
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        self.flush_impl()
    }
}

/// Writes bits in the little-endian format
///
/// `LittleEndianWriter` writes bits starting from the least significant bit (LSB).
/// Individual bits are packed into bytes with the first bit written going to the
/// LSB position, and multi-byte values are written with the least significant
/// byte first.
///
/// # Examples
///
/// ```rust
/// use bitter::{BitWriter, LittleEndianWriter};
///
/// let mut buffer = Vec::new();
/// {
///     let mut writer = LittleEndianWriter::new(&mut buffer);
///
///     // Write some mixed data
///     writer.write_bit(true).unwrap();           // 1 bit
///     writer.write_u8(0xFF).unwrap();           // 8 bits  
///     writer.write_u16(0x1234).unwrap();        // 16 bits
///     writer.write_bits(4, 0xA).unwrap();       // 4 more bits
///     writer.flush().unwrap();
/// }
///
/// // Data is written in little-endian bit order
/// println!("Written {} bytes", buffer.len());
/// ```
///
/// # Bit Ordering
///
/// In little-endian format:
/// - Individual bits are written from LSB to MSB within each byte
/// - Multi-byte values have their least significant byte written first
/// - This matches the bit ordering used by `LittleEndianReader`
#[derive(Debug)]
pub struct LittleEndianWriter<W: Write>(BitterWriter<W, true>);

impl<W: Write> LittleEndianWriter<W> {
    /// Create a little endian writer from the given Write implementation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = LittleEndianWriter::new(&mut buffer);
    ///     writer.write_u32(0x12345678).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// // Little endian: least significant byte first
    /// assert_eq!(buffer, &[0x78, 0x56, 0x34, 0x12]);
    /// ```
    #[inline]
    pub fn new(writer: W) -> Self {
        Self(BitterWriter::new(writer))
    }

    /// Unwraps this `LittleEndianWriter`, returning the underlying writer.
    ///
    /// The buffer is flushed before returning the writer. If an error occurs
    /// while flushing, both the error and the writer are returned.
    ///
    /// # Errors
    ///
    /// An [`IntoInnerError`] will be returned if an error occurs while flushing the buffer.
    /// This allows recovery of the original writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let mut writer = LittleEndianWriter::new(&mut buffer);
    /// writer.write_u8(42).unwrap();
    ///
    /// let buffer = writer.into_inner().unwrap();
    /// assert_eq!(buffer, &[42]);
    /// ```
    #[inline]
    pub fn into_inner(self) -> std::result::Result<W, IntoInnerError<LittleEndianWriter<W>>> {
        self.0.into_inner().map_err(|inner_error| {
            IntoInnerError::new(inner_error.error, LittleEndianWriter(inner_error.writer))
        })
    }

    /// Gets a reference to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let writer = LittleEndianWriter::new(&mut buffer);
    ///
    /// // Get a reference to the underlying buffer
    /// let buffer_ref = writer.get_ref();
    /// ```
    #[inline]
    pub fn get_ref(&self) -> &W {
        self.0.get_ref()
    }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// It is inadvisable to directly write to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, LittleEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let mut writer = LittleEndianWriter::new(&mut buffer);
    ///
    /// // Get a mutable reference to the underlying buffer
    /// let buffer_ref = writer.get_mut();
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut W {
        self.0.get_mut()
    }
}

impl<W: Write> BitWriter for LittleEndianWriter<W> {
    #[inline]
    fn write_bit(&mut self, bit: bool) -> Result<()> {
        self.0.write_bit(bit)
    }

    #[inline]
    fn write_u8(&mut self, value: u8) -> Result<()> {
        self.0.write_u8(value)
    }

    #[inline]
    fn write_i8(&mut self, value: i8) -> Result<()> {
        self.0.write_i8(value)
    }

    #[inline]
    fn write_u16(&mut self, value: u16) -> Result<()> {
        self.0.write_u16(value)
    }

    #[inline]
    fn write_i16(&mut self, value: i16) -> Result<()> {
        self.0.write_i16(value)
    }

    #[inline]
    fn write_u32(&mut self, value: u32) -> Result<()> {
        self.0.write_u32(value)
    }

    #[inline]
    fn write_i32(&mut self, value: i32) -> Result<()> {
        self.0.write_i32(value)
    }

    #[inline]
    fn write_f32(&mut self, value: f32) -> Result<()> {
        self.0.write_f32(value)
    }

    #[inline]
    fn write_u64(&mut self, value: u64) -> Result<()> {
        self.0.write_u64(value)
    }

    #[inline]
    fn write_i64(&mut self, value: i64) -> Result<()> {
        self.0.write_i64(value)
    }

    #[inline]
    fn write_f64(&mut self, value: f64) -> Result<()> {
        self.0.write_f64(value)
    }

    #[inline]
    fn write_bits(&mut self, bits: u32, value: u64) -> Result<()> {
        self.0.write_bits(bits, value)
    }

    #[inline]
    fn write_signed_bits(&mut self, bits: u32, value: i64) -> Result<()> {
        self.0.write_signed_bits(bits, value)
    }

    #[inline]
    fn unaligned_bits(&self) -> u32 {
        self.0.unaligned_bits()
    }

    #[inline]
    fn write_bytes(&mut self, buf: &[u8]) -> Result<()> {
        self.0.write_bytes(buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        self.0.flush()
    }
}

impl<W: Write> Write for LittleEndianWriter<W> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.write_bytes(buf)?;
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        BitWriter::flush(self)
    }
}

/// Writes bits in the big-endian format
///
/// `BigEndianWriter` writes bits starting from the most significant bit (MSB).
/// Individual bits are packed into bytes with the first bit written going to the
/// MSB position, and multi-byte values are written with the most significant
/// byte first.
///
/// # Examples
///
/// ```rust
/// use bitter::{BitWriter, BigEndianWriter};
///
/// let mut buffer = Vec::new();
/// {
///     let mut writer = BigEndianWriter::new(&mut buffer);
///
///     // Write some mixed data
///     writer.write_bit(true).unwrap();           // 1 bit
///     writer.write_u8(0xFF).unwrap();           // 8 bits  
///     writer.write_u16(0x1234).unwrap();        // 16 bits
///     writer.write_bits(4, 0xA).unwrap();       // 4 more bits
///     writer.flush().unwrap();
/// }
///
/// // Data is written in big-endian bit order
/// println!("Written {} bytes", buffer.len());
/// ```
///
/// # Bit Ordering
///
/// In big-endian format:
/// - Individual bits are written from MSB to LSB within each byte
/// - Multi-byte values have their most significant byte written first
/// - This matches the bit ordering used by `BigEndianReader`
#[derive(Debug)]
pub struct BigEndianWriter<W: Write>(BitterWriter<W, false>);

impl<W: Write> BigEndianWriter<W> {
    /// Create a big endian writer from the given Write implementation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, BigEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// {
    ///     let mut writer = BigEndianWriter::new(&mut buffer);
    ///     writer.write_u32(0x12345678).unwrap();
    ///     writer.flush().unwrap();
    /// }
    ///
    /// // Big endian: most significant byte first
    /// assert_eq!(buffer, &[0x12, 0x34, 0x56, 0x78]);
    /// ```
    #[inline]
    pub fn new(writer: W) -> Self {
        Self(BitterWriter::new(writer))
    }

    /// Unwraps this `BigEndianWriter`, returning the underlying writer.
    ///
    /// The buffer is flushed before returning the writer. If an error occurs
    /// while flushing, both the error and the writer are returned.
    ///
    /// # Errors
    ///
    /// An [`IntoInnerError`] will be returned if an error occurs while flushing the buffer.
    /// This allows recovery of the original writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, BigEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let mut writer = BigEndianWriter::new(&mut buffer);
    /// writer.write_u8(42).unwrap();
    ///
    /// let buffer = writer.into_inner().unwrap();
    /// assert_eq!(buffer, &[42]);
    /// ```
    #[inline]
    pub fn into_inner(self) -> std::result::Result<W, IntoInnerError<BigEndianWriter<W>>> {
        self.0.into_inner().map_err(|inner_error| {
            IntoInnerError::new(inner_error.error, BigEndianWriter(inner_error.writer))
        })
    }

    /// Gets a reference to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, BigEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let writer = BigEndianWriter::new(&mut buffer);
    ///
    /// // Get a reference to the underlying buffer
    /// let buffer_ref = writer.get_ref();
    /// ```
    #[inline]
    pub fn get_ref(&self) -> &W {
        self.0.get_ref()
    }

    /// Gets a mutable reference to the underlying writer.
    ///
    /// It is inadvisable to directly write to the underlying writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use bitter::{BitWriter, BigEndianWriter};
    ///
    /// let mut buffer = Vec::new();
    /// let mut writer = BigEndianWriter::new(&mut buffer);
    ///
    /// // Get a mutable reference to the underlying buffer
    /// let buffer_ref = writer.get_mut();
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut W {
        self.0.get_mut()
    }
}

impl<W: Write> BitWriter for BigEndianWriter<W> {
    #[inline]
    fn write_bit(&mut self, bit: bool) -> Result<()> {
        self.0.write_bit(bit)
    }

    #[inline]
    fn write_u8(&mut self, value: u8) -> Result<()> {
        self.0.write_u8(value)
    }

    #[inline]
    fn write_i8(&mut self, value: i8) -> Result<()> {
        self.0.write_i8(value)
    }

    #[inline]
    fn write_u16(&mut self, value: u16) -> Result<()> {
        self.0.write_u16(value)
    }

    #[inline]
    fn write_i16(&mut self, value: i16) -> Result<()> {
        self.0.write_i16(value)
    }

    #[inline]
    fn write_u32(&mut self, value: u32) -> Result<()> {
        self.0.write_u32(value)
    }

    #[inline]
    fn write_i32(&mut self, value: i32) -> Result<()> {
        self.0.write_i32(value)
    }

    #[inline]
    fn write_f32(&mut self, value: f32) -> Result<()> {
        self.0.write_f32(value)
    }

    #[inline]
    fn write_u64(&mut self, value: u64) -> Result<()> {
        self.0.write_u64(value)
    }

    #[inline]
    fn write_i64(&mut self, value: i64) -> Result<()> {
        self.0.write_i64(value)
    }

    #[inline]
    fn write_f64(&mut self, value: f64) -> Result<()> {
        self.0.write_f64(value)
    }

    #[inline]
    fn write_bits(&mut self, bits: u32, value: u64) -> Result<()> {
        self.0.write_bits(bits, value)
    }

    #[inline]
    fn write_signed_bits(&mut self, bits: u32, value: i64) -> Result<()> {
        self.0.write_signed_bits(bits, value)
    }

    #[inline]
    fn unaligned_bits(&self) -> u32 {
        self.0.unaligned_bits()
    }

    #[inline]
    fn write_bytes(&mut self, buf: &[u8]) -> Result<()> {
        self.0.write_bytes(buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        self.0.flush()
    }
}

impl<W: Write> Write for BigEndianWriter<W> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.write_bytes(buf)?;
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        BitWriter::flush(self)
    }
}

/// Write bits in system native-endian format
#[cfg(target_endian = "little")]
pub type NativeEndianWriter<W> = LittleEndianWriter<W>;

/// Write bits in system native-endian format
#[cfg(target_endian = "big")]
pub type NativeEndianWriter<W> = BigEndianWriter<W>;

/// An error returned by calling `into_inner` on a writer.
///
/// Combines an error that happened while flushing the buffer, and the buffered
/// writer object which may be used to recover from the condition.
///
/// # Examples
///
/// ```rust
/// use bitter::{BitWriter, LittleEndianWriter};
/// use std::io::{Error, ErrorKind};
///
/// #[derive(Debug)]
/// struct FailingWriter;
///
/// impl std::io::Write for FailingWriter {
///     fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
///         Err(Error::new(ErrorKind::Other, "write failed"))
///     }
///     
///     fn flush(&mut self) -> std::io::Result<()> {
///         Err(Error::new(ErrorKind::Other, "flush failed"))
///     }
/// }
///
/// let failing_writer = FailingWriter;
/// let mut writer = LittleEndianWriter::new(failing_writer);
/// writer.write_bit(true).unwrap();
///
/// let into_inner_error = writer.into_inner().unwrap_err();
///
/// // Access the error that occurred during flushing
/// let flush_error = into_inner_error.error();
/// println!("Flush failed: {}", flush_error);
///
/// // Recover the original writer for potential retry
/// let recovered_writer = into_inner_error.into_inner();
/// ```
#[derive(Debug)]
pub struct IntoInnerError<W> {
    error: std::io::Error,
    writer: W,
}

impl<W> IntoInnerError<W> {
    fn new(error: std::io::Error, writer: W) -> Self {
        Self { error, writer }
    }

    /// Returns the error which caused the call to `into_inner()` to fail.
    ///
    /// This error was returned when attempting to flush the internal buffer.
    pub fn error(&self) -> &std::io::Error {
        &self.error
    }

    /// Returns the writer instance which generated the error.
    pub fn into_inner(self) -> W {
        self.writer
    }
}

impl<W> fmt::Display for IntoInnerError<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to flush buffer in into_inner: {}", self.error)
    }
}

impl<W: fmt::Debug> Error for IntoInnerError<W> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.error)
    }
}
