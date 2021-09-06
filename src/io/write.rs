use std::io::{Write, Result};

pub struct LittleEndianIoWriter<W> {
    data: u8,
    pos: usize,
    inner: W,
}

impl<W: Write> LittleEndianIoWriter<W> {
    pub fn new(inner: W) -> Self {
        Self {
            data: 0,
            pos: 0,
            inner,
        }
    }

    fn write_slice(&mut self, buf: &[u8]) -> Result<()> {
        for byte in buf {
            self.write_u8(*byte)?;
        }

        Ok(())
    }

    pub fn get_ref(&self) -> &W {
        &self.inner
    }

    pub fn get_mut(&mut self) -> &mut W {
        &mut self.inner
    }
    
    pub fn into_inner(self) -> W {
        self.inner
    }

    pub fn is_mid_byte(&self) -> bool {
        self.pos != 0
    }

    pub fn write_bit(&mut self, x: bool) -> Result<()> {
        self.data |= (x as u8) << self.pos;
        self.pos += 1;
        self.pos &= 7;
        if self.pos == 0 {
            self.inner.write_all(&[self.data])?;
            self.data = 0;
        }
        Ok(())
    }

    pub fn write_u8(&mut self, x: u8) -> Result<()> {
        let next_data = x.wrapping_shl(8 - self.pos as u32);
        self.data |= x >> self.pos;
        self.inner.write_all(&[self.data])?;
        self.data = next_data;
        Ok(())
    }

    pub fn write_u16(&mut self, x: u16) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_u32(&mut self, x: u32) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_u64(&mut self, x: u64) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_i8(&mut self, x: i8) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_i16(&mut self, x: i16) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_i32(&mut self, x: i32) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_i64(&mut self, x: i64) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_f32(&mut self, x: f32) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_f64(&mut self, x: f64) -> Result<()> {
        self.write_slice(&x.to_le_bytes())
    }

    pub fn write_bits(&mut self,  bits: i32, value: u64) -> Result<()> {
        let bts = bits as usize;
        let data = value.to_le_bytes();
        let whole_bytes = bts / 8;

        self.write_slice(&data[..whole_bytes])?;

        let remainder = bts % 8;
        if remainder != 0 {
            let mut partial_byte = data[whole_bytes];
            for _ in 0..remainder {
                let bit = partial_byte & 1 == 1;
                self.write_bit(bit)?;
                partial_byte >>= 1;
            }
        }
        Ok(())
    }

    pub fn write_signed_bits(&mut self, bits: i32, value: i64) -> Result<()> {
        todo!()
    }
}

impl<W: Write> Write for LittleEndianIoWriter<W> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.write_slice(buf).map(|_| buf.len())
    }

    fn flush(&mut self) -> Result<()> {
        if self.pos != 0 {
            self.write_all(&[self.data])?;
            self.pos = 0;
            self.data = 0;
        }

        Ok(())
    }
}

// impl<W: Write> Drop for LittleEndianIoWriter<W> {
//     fn drop(&mut self) {
//         if self.inner.is_some() && !self.panicked {
//             // dtors should not panic, so we ignore a failed flush
//             let _r = self.flush_buf();
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eight_on_bits_write() {
        let mut result = [0u8; 1];
        let mut writer = LittleEndianIoWriter::new(&mut result[..]);
        for _ in 0..8 {
            writer.write_bit(true).unwrap();
        }

        assert_eq!(result, &[0xffu8][..]);
    }

    #[test]
    fn eight_off_bits_write() {
        let mut result = [0u8; 1];
        let mut writer = LittleEndianIoWriter::new(&mut result[..]);
        for _ in 0..8 {
            writer.write_bit(false).unwrap();
        }

        assert_eq!(result, &[0x0u8][..]);
    }

    #[test]
    fn byte_write() {
        let mut result = [0u8; 1];
        let mut writer = LittleEndianIoWriter::new(&mut result[..]);
        writer.write_u8(0xff).unwrap();
        assert_eq!(result, &[0xffu8][..]);
    }
}