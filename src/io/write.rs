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

    pub fn write_bit(&mut self, x: bool) -> Result<()> {
        self.data |= (x as u8) << self.pos;
        self.pos &= 7;
        if self.pos == 0 {
            self.inner.write_all(&[self.data])?;
            self.data = 0;
        }
        Ok(())
    }
}

impl<W: Write> Write for LittleEndianIoWriter<W> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        todo!()
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


    }
}