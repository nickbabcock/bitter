use crate::{bit_mask, BitReader, LittleEndianReader, BIT_WIDTH};
use std::io::{Error, ErrorKind, Read, Result};

trait ReadExt {
    fn read_at_least(&mut self, buf: &mut [u8], len: usize) -> Result<usize>;
}

impl<R> ReadExt for R
where
    R: Read,
{
    fn read_at_least(&mut self, buf: &mut [u8], len: usize) -> Result<usize> {
        let mut pos = 0;
        while pos < len {
            let read = match self.read(&mut buf[pos..]) {
                Ok(0) => return Err(Error::new(ErrorKind::UnexpectedEof, "Unexpected EOF")),
                Ok(n) => n,
                Err(ref e) if e.kind() == ErrorKind::Interrupted => 0,
                Err(e) => return Err(e),
            };

            pos += read;
        }

        Ok(pos)
    }
}

pub trait BitIoReader: Read {
    type Inner;

    fn get_mut(&mut self) -> &mut Self::Inner;
    fn get_ref(&mut self) -> &mut Self::Inner;
    fn into_inner(self) -> Self::Inner;
    fn read_bit(&mut self) -> Result<bool>;
    fn read_u8(&mut self) -> Result<u8>;
    fn read_u16(&mut self) -> Result<u16>;
    fn read_u32(&mut self) -> Result<u32>;
    fn read_u64(&mut self) -> Result<u64>;
    fn read_i8(&mut self) -> Result<i8>;
    fn read_i16(&mut self) -> Result<i16>;
    fn read_i32(&mut self) -> Result<i32>;
    fn read_i64(&mut self) -> Result<i64>;
    fn read_f32(&mut self) -> Result<f32>;
    fn read_f64(&mut self) -> Result<f64>;
    fn read_bits(&mut self, bits: i32) -> Result<u64>;
    fn read_signed_bits(&mut self, bits: i32) -> Result<i64>;
}

pub struct LittleEndianIoReader<R> {
    buf: Vec<u8>,
    bits: LittleEndianReader<'static>,
    inner: R,
}

impl<R: Read> LittleEndianIoReader<R> {
    pub fn new(inner: R) -> LittleEndianIoReader<R> {
        let buf = vec![0u8; 8192];
        let bits = LittleEndianReader::new(&[]);
        LittleEndianIoReader { buf, bits, inner }
    }
}

impl<R> BitIoReader for LittleEndianIoReader<R>
where
    R: Read,
{
    type Inner = R;

    fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    fn get_ref(&mut self) -> &mut R {
        &mut self.inner
    }

    fn into_inner(self) -> R {
        self.inner
    }

    #[inline]
    fn read_bit(&mut self) -> Result<bool> {
        self.read_bits(1).map(|x| x != 0)
    }

    #[inline]
    fn read_u8(&mut self) -> Result<u8> {
        self.read_bits((core::mem::size_of::<u8>() * 8) as i32)
            .map(|x| x as u8)
    }

    #[inline]
    fn read_u16(&mut self) -> Result<u16> {
        self.read_bits((core::mem::size_of::<u16>() * 8) as i32)
            .map(|x| x as u16)
    }

    #[inline]
    fn read_u32(&mut self) -> Result<u32> {
        self.read_bits((core::mem::size_of::<u32>() * 8) as i32)
            .map(|x| x as u32)
    }

    #[inline]
    fn read_u64(&mut self) -> Result<u64> {
        self.read_bits((core::mem::size_of::<u64>() * 8) as i32)
            .map(|x| x as u64)
    }

    #[inline]
    fn read_i8(&mut self) -> Result<i8> {
        self.read_bits((core::mem::size_of::<i8>() * 8) as i32)
            .map(|x| x as i8)
    }

    #[inline]
    fn read_i16(&mut self) -> Result<i16> {
        self.read_bits((core::mem::size_of::<i16>() * 8) as i32)
            .map(|x| x as i16)
    }

    #[inline]
    fn read_i32(&mut self) -> Result<i32> {
        self.read_bits((core::mem::size_of::<i32>() * 8) as i32)
            .map(|x| x as i32)
    }

    #[inline]
    fn read_i64(&mut self) -> Result<i64> {
        self.read_bits((core::mem::size_of::<i64>() * 8) as i32)
            .map(|x| x as i64)
    }

    #[inline]
    fn read_f32(&mut self) -> Result<f32> {
        self.read_u32().map(f32::from_bits)
    }

    #[inline]
    fn read_f64(&mut self) -> Result<f64> {
        self.read_u64().map(f64::from_bits)
    }

    #[inline]
    fn read_bits(&mut self, bits: i32) -> Result<u64> {
        if let Some(x) = self.bits.read_bits(bits) {
            return Ok(x);
        }

        let bits_remaining = self.bits.bits_remaining().unwrap() as i32;
        let left = bits - bits_remaining;

        let high = if bits_remaining == 0 {
            0
        } else {
            self.bits.read_bits_unchecked(bits_remaining) << (left as u64)
        };

        let to_read = (left / 8) + ((left % 8 != 0) as i32);
        let read = self.inner.read_at_least(&mut self.buf, to_read as usize)?;
        let sl = self.buf.as_slice();

        // SAFETY: As long as the vec does not reallocate, this is safe
        let sl: &'static [u8] = unsafe { std::mem::transmute(sl) };
        self.bits = LittleEndianReader::new(&sl[..read]);
        let low = self.bits.read_bits_unchecked(left);

        Ok(high + low)
    }

    #[inline]
    fn read_signed_bits(&mut self, bits: i32) -> Result<i64> {
        let bts = bits as usize;
        self.read_bits(bits).map(|x| {
            if x.leading_zeros() == (BIT_WIDTH - bts) as u32 {
                (x as i64) - (bit_mask(bts) + 1) as i64
            } else {
                x as i64
            }
        })
    }
}

impl<R> Read for LittleEndianIoReader<R>
where
    R: Read,
{
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        // Best case: we have enough data cached to read everything
        if self.bits.read_bytes(buf) {
            return Ok(buf.len());
        }

        let len = buf.len();
        let byte_offset = self.bits.is_mid_byte() as usize;

        // Else we first read all the remaining bytes in the bit reader
        let left = self.bits.approx_bytes_remaining() - byte_offset;
        let (has, to_fill) = buf.split_at_mut(left);
        let did_read = self.bits.read_bytes(has);
        debug_assert!(did_read);

        let read = self.inner.read(&mut self.buf[byte_offset..])?;
        if read == 0 {
            return Ok(has.len());
        }

        let sl = self.buf.as_slice();

        // SAFETY: As long as the vec does not reallocate, this is safe
        let sl: &'static [u8] = unsafe { std::mem::transmute(sl) };

        // SAFETY: We can unwrap as the bit reader has less than a byte left
        let new_read = 8 - self.bits.bits_remaining().unwrap();
        self.bits = LittleEndianReader::new(&sl[..read]);
        if new_read != 8 && new_read != 0 {
            self.bits.read_bits(new_read as i32).unwrap();
        }

        let (has2, rest) = to_fill.split_at_mut(read.min(to_fill.len()));
        let did_read = self.bits.read_bytes(has2);
        debug_assert!(did_read);

        Ok(len - rest.len())
    }
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use super::*;

    #[test]
    fn test_bit_reads() {
        let mut reader = LittleEndianIoReader::new(&[0b1010_1010, 0b0101_0101][..]);
        assert_eq!(reader.read_bit().unwrap(), false);
        assert_eq!(reader.read_bit().unwrap(), true);
        assert_eq!(reader.read_bit().unwrap(), false);
        assert_eq!(reader.read_bit().unwrap(), true);
        assert_eq!(reader.read_bit().unwrap(), false);
        assert_eq!(reader.read_bit().unwrap(), true);
        assert_eq!(reader.read_bit().unwrap(), false);
        assert_eq!(reader.read_bit().unwrap(), true);

        assert_eq!(reader.read_bit().unwrap(), true);
        assert_eq!(reader.read_bit().unwrap(), false);
        assert_eq!(reader.read_bit().unwrap(), true);
        assert_eq!(reader.read_bit().unwrap(), false);
        assert_eq!(reader.read_bit().unwrap(), true);
        assert_eq!(reader.read_bit().unwrap(), false);
        assert_eq!(reader.read_bit().unwrap(), true);
        assert_eq!(reader.read_bit().unwrap(), false);

        assert!(reader.read_bit().is_err());
    }

    #[test]
    fn test_16_bits_reads() {
        let mut reader = LittleEndianIoReader::new(&[0b1010_1010, 0b0101_0101][..]);
        assert_eq!(reader.read_bits(16).unwrap(), 0b0101_0101_1010_1010);
    }

    #[test]
    fn empty_reader() {
        let mut buf = [0u8; 100];
        let mut reader = LittleEndianIoReader::new(&[][..]);
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 0);
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 0);
    }

    #[test]
    fn single_byte_reader() {
        let mut buf = [0u8; 100];
        let mut reader = LittleEndianIoReader::new(&[0xff][..]);
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 1);
        assert_eq!(&buf[..1], [0xff]);
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 0);
    }

    #[test]
    fn test_read_bytes() {
        let mut buf = [0u8; 2];
        let mut reader = LittleEndianIoReader::new(&[0b1010_1010, 0b0101_0101][..]);
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 2);
        assert_eq!(&buf, &[0b1010_1010, 0b0101_0101]);

        let mut reader = LittleEndianIoReader::new(&[0b1010_1010, 0b0101_0101][..]);
        assert_eq!(reader.read_bit().unwrap(), false);
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 1);
        assert_eq!(&buf[..1], &[0b1101_0101]);
    }

    #[test]
    fn test_read_bytes2() {
        let mut reader = LittleEndianIoReader::new(&[0, 0][..]);
        let mut buf = [0u8; 1];
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 1);
        assert_eq!(&buf, &[0]);
    }

    #[test]
    fn test_read_bytes3() {
        let mut reader = LittleEndianIoReader::new(&[0, 120][..]);
        let mut buf = [0u8; 1];
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 1);
        assert_eq!(&buf, &[0]);
        assert_eq!(reader.read_bits(8).unwrap(), 120);
    }

    #[test]
    fn test_read_bytes4() {
        let mut reader = LittleEndianIoReader::new(&[119, 0, 120][..]);
        assert_eq!(reader.read_bits(8).unwrap(), 119);
        let mut buf = [0u8; 1];
        assert_eq!(reader.read(&mut buf[..]).unwrap(), 1);
        assert_eq!(&buf, &[0]);
        assert_eq!(reader.read_bits(8).unwrap(), 120);
    }

    #[test]
    fn test_u8_reads() {
        let mut reader =
            LittleEndianIoReader::new(&[0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2][..]);
        assert_eq!(reader.read_u8().unwrap(), 0xff);
        assert_eq!(reader.read_u8().unwrap(), 0xfe);
        assert_eq!(reader.read_u8().unwrap(), 0xfa);
        assert_eq!(reader.read_u8().unwrap(), 0xf7);
        assert_eq!(reader.read_u8().unwrap(), 0xf5);
        assert_eq!(reader.read_u8().unwrap(), 0xf0);
        assert_eq!(reader.read_u8().unwrap(), 0xb1);
        assert_eq!(reader.read_u8().unwrap(), 0xb2);
        assert!(reader.read_u8().is_err());
    }

    #[test]
    fn test_u64_reads() {
        let mut bitter = LittleEndianIoReader::new(
            &[
                0xff, 0xfe, 0xfa, 0xf7, 0xf5, 0xf0, 0xb1, 0xb2, 0x01, 0xff, 0xfe, 0xfa, 0xf7, 0xf5,
                0xf0, 0xb1, 0xb3,
            ][..],
        );
        assert_eq!(bitter.read_u64().unwrap(), 0xb2b1_f0f5_f7fa_feff);
        assert_eq!(bitter.read_u8().unwrap(), 0x01);
        assert_eq!(bitter.read_u64().unwrap(), 0xb3b1_f0f5_f7fa_feff);
    }

    #[test]
    fn test_u32_bit_read() {
        let mut bitter = LittleEndianIoReader::new(&[0xff, 0x00, 0xab, 0xcd][..]);
        assert_eq!(bitter.read_bits(32).unwrap(), 0xcdab00ff);
    }

    #[test]
    fn test_u32_reads() {
        let mut bitter = LittleEndianIoReader::new(
            &[
                0xff,
                0x00,
                0xab,
                0xcd,
                0b1111_1110,
                0b0000_0001,
                0b0101_0110,
                0b1001_1011,
                0b0101_0101,
            ][..],
        );
        assert_eq!(bitter.read_u32().unwrap(), 0xcdab00ff);
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.read_u32().unwrap(), 0xcdab00ff);
        assert_eq!(bitter.read_bit().unwrap(), false);
    }

    #[test]
    fn test_f32_reads() {
        let mut bitter = LittleEndianIoReader::new(
            &[
                0b0111_1011,
                0b0001_0100,
                0b1010_1110,
                0b0011_1101,
                0b1111_0110,
                0b0010_1000,
                0b0101_1100,
                0b0111_1011,
                0b0000_0010,
            ][..],
        );
        assert_eq!(bitter.read_f32().unwrap(), 0.085);
        assert_eq!(bitter.read_bit().unwrap(), false);
        assert_eq!(bitter.read_f32().unwrap(), 0.085);
    }

    #[test]
    fn test_u32_bits() {
        let mut bitter = LittleEndianIoReader::new(&[0xff, 0xdd, 0xee, 0xff, 0xdd, 0xee][..]);
        assert_eq!(bitter.read_bits(10).unwrap(), 0x1ff);
        assert_eq!(bitter.read_bits(10).unwrap(), 0x3b7);
        assert_eq!(bitter.read_bits(10).unwrap(), 0x3fe);
        assert_eq!(bitter.read_bits(10).unwrap(), 0x377);
    }

    #[test]
    fn test_u32_bits2() {
        let mut bitter = LittleEndianIoReader::new(
            &[
                0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
                0xe7,
            ][..],
        );
        for _ in 0..10 {
            assert_eq!(bitter.read_bits(5).unwrap(), 28);
        }
    }

    #[test]
    fn test_signed_bits2() {
        let mut bitter = LittleEndianIoReader::new(
            &[
                0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
                0xe7,
            ][..],
        );

        for _ in 0..10 {
            assert_eq!(bitter.read_signed_bits(5).unwrap(), -4);
        }
    }

    #[test]
    fn i16_test() {
        let data = [0b1111_1111, 0b1111_1111];
        let mut bits = LittleEndianIoReader::new(&data[..]);

        assert_eq!(bits.read_i16().unwrap(), i16::from_le_bytes(data));
    }

    #[test]
    fn i16_min_test() {
        let data = [0b0000_0000, 0b1000_0000];
        let mut bits = LittleEndianIoReader::new(&data[..]);

        assert_eq!(bits.read_i16().unwrap(), core::i16::MIN);
    }

    #[test]
    fn i16_max_test() {
        let data = [0b1111_1111, 0b0111_1111];
        let mut bits = LittleEndianIoReader::new(&data[..]);

        assert_eq!(bits.read_i16().unwrap(), core::i16::MAX);
    }

    #[test]
    fn back_to_back_le_u64() {
        let mut data = Vec::new();
        data.extend_from_slice(&(1u64.to_le_bytes()));
        data.extend_from_slice(&(0u64.to_le_bytes()));
        let mut bits = LittleEndianIoReader::new(data.as_slice());
        assert_eq!(bits.read_u64().unwrap(), 1);
        assert_eq!(bits.read_u64().unwrap(), 0);
    }

    #[test]
    fn pushed_le_u64() {
        let mut data = Vec::new();
        data.extend_from_slice(&(0u64.to_le_bytes()));
        data.extend_from_slice(&(1u64.to_le_bytes()));
        let mut bits = LittleEndianIoReader::new(data.as_slice());
        for _ in 0..8 {
            assert_eq!(bits.read_u8().unwrap(), 0);
        }
        assert_eq!(bits.read_u64().unwrap(), 1);
    }

    #[test]
    fn read_bits_64() {
        let data = 1u64.to_le_bytes();
        let mut bits = LittleEndianIoReader::new(&data[..]);
        assert_eq!(bits.read_bits(64).unwrap(), 1);
    }

    #[test]
    fn read_bits_52() {
        let data = [0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88];
        let mut bits = LittleEndianIoReader::new(&data[..]);
        assert_eq!(bits.read_bits(4).unwrap(), 0xf);
        assert_eq!(bits.read_bits(52).unwrap(), 0x99aabbccddeef);
    }

    #[test]
    fn regression1() {
        let data = vec![0b0000_0010, 0b0011_1111, 0b1011_1100];
        let mut bits = LittleEndianIoReader::new(data.as_slice());

        assert_eq!(bits.read_bits(3).unwrap(), 2);
        assert_eq!(bits.read_u8().unwrap(), 224);
        assert_eq!(bits.read_bit().unwrap(), true);
    }

    #[test]
    fn regression2() {
        let data = vec![2, 63, 63, 2, 63, 2, 0, 0, 0];
        let mut bits = LittleEndianIoReader::new(data.as_slice());

        assert_eq!(bits.read_bits(3).unwrap(), 2);
        assert_eq!(bits.read_u8().unwrap(), 224);
    }

    #[test]
    fn test_signed_bits2_buffer() {
        let buffer = BufReader::with_capacity(
            2,
            &[
                0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39, 0xe7, 0x9c, 0x73, 0xce, 0x39,
                0xe7,
            ][..],
        );
        let mut bitter = LittleEndianIoReader::new(buffer);

        for _ in 0..10 {
            assert_eq!(bitter.read_signed_bits(5).unwrap(), -4);
        }
    }
}
