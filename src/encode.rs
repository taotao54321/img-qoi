use std::io::Write;
use std::num::NonZeroUsize;

use arrayvec::ArrayVec;
use byteorder::{WriteBytesExt as _, BE};

use crate::error::{QoiError, QoiResult};
use crate::pixel::{DiffOrColor, PixelDict, PixelDiff, QoiPixel};
use crate::qoi::{
    QoiChannels, QOI_PADDING_LEN, QOI_TAG_COLOR, QOI_TAG_DIFF_16, QOI_TAG_DIFF_24, QOI_TAG_DIFF_8,
    QOI_TAG_INDEX, QOI_TAG_RUN_16, QOI_TAG_RUN_8,
};

const RUN_MAX: u16 = 33 + 0x1FFF;

/// Encodes pixels from [`IntoIterator`] to QOI body (without header), and writes it to [`Write`].
///
/// Encodes exactly `pixel_count` pixels.
///
/// # Errors
///
/// * Returns error if `pixels` yields less than `pixel_count` pixels.
/// * Returns error if write operation fails.
pub fn qoi_encode_from_iter<W, I>(
    wtr: &mut W,
    pixel_count: NonZeroUsize,
    pixels: I,
) -> QoiResult<()>
where
    W: Write,
    I: IntoIterator<Item = QoiPixel>,
{
    let mut pixels = pixels.into_iter();

    let mut enc = Encoder::new(wtr);
    for _ in 0..pixel_count.get() {
        let px = pixels
            .next()
            .ok_or_else(|| QoiError::new_encode("premature end of pixels"))?;
        enc.update(px)?;
    }
    enc.finalize()?;

    Ok(())
}

/// Encodes pixels on memory to QOI body (without header), and writes it to [`Write`].
///
/// Encodes exactly `pixel_count` pixels.
///
/// `channels` specifies the pixel format in `buf`. RGBA8 and RGB8 are supported.
///
/// # Errors
///
/// * Returns error if write operation fails.
///
/// # Panics
///
/// * Panics if `buf` is too small.
pub fn qoi_encode_from_buffer<W, T>(
    wtr: &mut W,
    pixel_count: NonZeroUsize,
    buf: T,
    channels: QoiChannels,
) -> QoiResult<()>
where
    W: Write,
    T: AsRef<[u8]>,
{
    let buf = buf.as_ref();

    let buf_len_min = channels
        .byte_count()
        .checked_mul(pixel_count.get())
        .unwrap_or_else(|| panic!("overflow in buffer size calculation"));
    assert!(buf.len() >= buf_len_min, "buffer is too small");

    let pixels = buf
        .chunks_exact(channels.byte_count())
        .map(|chunk| channels.read_pixel_from_buffer(chunk));

    let mut enc = Encoder::new(wtr);
    for px in pixels {
        enc.update(px)?;
    }
    enc.finalize()?;

    Ok(())
}

#[derive(Debug)]
struct Encoder<'a, W> {
    wtr: &'a mut W,
    px_prev: QoiPixel,
    dict: PixelDict,
    run: u16,
}

impl<'a, W: Write> Encoder<'a, W> {
    fn new(wtr: &'a mut W) -> Self {
        Self {
            wtr,
            px_prev: QoiPixel::new(0, 0, 0, 255),
            dict: PixelDict::new(),
            run: 0,
        }
    }

    fn update(&mut self, px: QoiPixel) -> std::io::Result<()> {
        if px == self.px_prev {
            self.run += 1;
            if self.run == RUN_MAX {
                self.flush_run()?;
            }
            return Ok(());
        }

        self.flush_run()?;

        let hash = PixelDict::hash(px);

        if px == self.dict[hash] {
            encode_chunk_index(self.wtr, hash)?;
        } else {
            match px.sub(self.px_prev) {
                DiffOrColor::Diff(PixelDiff::Diff8(diff)) => encode_chunk_diff_8(self.wtr, diff)?,
                DiffOrColor::Diff(PixelDiff::Diff16(diff)) => encode_chunk_diff_16(self.wtr, diff)?,
                DiffOrColor::Diff(PixelDiff::Diff24 { diff_r, diff_gba }) => {
                    encode_chunk_diff_24(self.wtr, diff_r, diff_gba)?
                }
                DiffOrColor::Color(mask) => encode_chunk_color(self.wtr, mask, px)?,
            }

            self.dict[hash] = px;
        }

        self.px_prev = px;

        Ok(())
    }

    fn finalize(mut self) -> std::io::Result<()> {
        self.flush_run()?;

        // always emit 4-Byte zero padding.
        // though it is valid to embed data in padding, it might confuse some decoders.
        //
        // ref: https://github.com/phoboslab/qoi/issues/17
        self.wtr.write_all(&[0; QOI_PADDING_LEN])
    }

    fn flush_run(&mut self) -> std::io::Result<()> {
        match self.run {
            0 => {}
            1..=32 => encode_chunk_run_8(self.wtr, self.run as u8)?,
            33..=RUN_MAX => encode_chunk_run_16(self.wtr, self.run)?,
            _ => unreachable!(),
        }

        self.run = 0;

        Ok(())
    }
}

fn encode_chunk_index(wtr: &mut impl Write, idx: u8) -> std::io::Result<()> {
    debug_assert!((0..=0x3F).contains(&idx));

    let value = (QOI_TAG_INDEX << 6) | idx;
    wtr.write_u8(value)
}

fn encode_chunk_run_8(wtr: &mut impl Write, run: u8) -> std::io::Result<()> {
    debug_assert!((1..=32).contains(&run));

    let value = (QOI_TAG_RUN_8 << 5) | (run - 1);
    wtr.write_u8(value)
}

fn encode_chunk_run_16(wtr: &mut impl Write, run: u16) -> std::io::Result<()> {
    debug_assert!((33..=RUN_MAX).contains(&run));

    let value = (u16::from(QOI_TAG_RUN_16) << 13) | (run - 33);
    wtr.write_u16::<BE>(value)
}

fn encode_chunk_diff_8(wtr: &mut impl Write, diff: u8) -> std::io::Result<()> {
    let value = (QOI_TAG_DIFF_8 << 6) | diff;
    wtr.write_u8(value)
}

fn encode_chunk_diff_16(wtr: &mut impl Write, diff: u16) -> std::io::Result<()> {
    let value = (u16::from(QOI_TAG_DIFF_16) << 13) | diff;
    wtr.write_u16::<BE>(value)
}

fn encode_chunk_diff_24(wtr: &mut impl Write, diff_r: u8, diff_gba: u16) -> std::io::Result<()> {
    let value =
        (u32::from(QOI_TAG_DIFF_24) << 20) | (u32::from(diff_r) << 15) | u32::from(diff_gba);
    wtr.write_u24::<BE>(value)
}

fn encode_chunk_color(wtr: &mut impl Write, mask: u8, px: QoiPixel) -> std::io::Result<()> {
    // avoid heap allocation.
    let mut buf = ArrayVec::<u8, 5>::new();

    let first = (QOI_TAG_COLOR << 4) | mask;
    unsafe {
        buf.push_unchecked(first);
    }

    if (mask & (1 << 3)) != 0 {
        unsafe {
            buf.push_unchecked(px.r());
        }
    }
    if (mask & (1 << 2)) != 0 {
        unsafe {
            buf.push_unchecked(px.g());
        }
    }
    if (mask & (1 << 1)) != 0 {
        unsafe {
            buf.push_unchecked(px.b());
        }
    }
    if (mask & (1 << 0)) != 0 {
        unsafe {
            buf.push_unchecked(px.a());
        }
    }

    wtr.write_all(&buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn encode_from_iter(pixels: impl AsRef<[(u8, u8, u8, u8)]>) -> Vec<u8> {
        let pixels = pixels
            .as_ref()
            .iter()
            .map(|&(r, g, b, a)| QoiPixel::new(r, g, b, a));
        let pixel_count = NonZeroUsize::new(pixels.len()).unwrap();
        let mut buf = Vec::<u8>::new();
        qoi_encode_from_iter(&mut buf, pixel_count, pixels).unwrap();
        buf
    }

    fn encode_from_buffer(buf_in: impl AsRef<[u8]>, channels: QoiChannels) -> Vec<u8> {
        let buf_in = buf_in.as_ref();
        assert_eq!(buf_in.len() % channels.byte_count(), 0);
        let pixel_count = buf_in.len() / channels.byte_count();
        let pixel_count = NonZeroUsize::new(pixel_count).unwrap();
        let mut buf_out = Vec::<u8>::new();
        qoi_encode_from_buffer(&mut buf_out, pixel_count, buf_in, channels).unwrap();
        buf_out
    }

    #[test]
    #[allow(clippy::identity_op)]
    #[allow(clippy::unusual_byte_groupings)]
    fn test_encode() {
        assert_eq!(
            encode_from_iter([(0, 0, 0, 255); 32]),
            [(QOI_TAG_RUN_8 << 5) | 31, 0, 0, 0, 0]
        );

        assert_eq!(
            encode_from_iter([(0, 0, 0, 255); 33 + 0x100]),
            [(QOI_TAG_RUN_16 << 5) | 0x01, 0x00, 0, 0, 0, 0]
        );

        #[rustfmt::skip]
        assert_eq!(
            encode_from_iter([
                (11, 22, 33, 44),
                (55, 66, 77, 88),
                (11, 22, 33, 44),
            ]),
            [
                (QOI_TAG_COLOR << 4) | 0xF, 11, 22, 33, 44,
                (QOI_TAG_COLOR << 4) | 0xF, 55, 66, 77, 88,
                (QOI_TAG_INDEX << 6) | PixelDict::hash(QoiPixel::new(11, 22, 33, 44)),
                0, 0, 0, 0,
            ]
        );

        assert_eq!(
            encode_from_iter([(254, 0, 1, 255)]),
            [(QOI_TAG_DIFF_8 << 6) | 0b00_10_11, 0, 0, 0, 0]
        );

        assert_eq!(
            encode_from_iter([(240, 248, 7, 255)]),
            [(QOI_TAG_DIFF_16 << 5) | 0b00000, 0b0000_1111, 0, 0, 0, 0]
        );

        #[rustfmt::skip]
        assert_eq!(
            encode_from_iter([(15, 240, 247, 8)]),
            [
                (QOI_TAG_DIFF_24 << 4) | 0b1111, 0b1_00000_00, 0b111_11001,
                0, 0, 0, 0,
            ]
        );

        // If only one component differ, QOI_COLOR is better than QOI_DIFF_24.
        assert_eq!(
            encode_from_iter([(0, 10, 0, 255)]),
            [(QOI_TAG_COLOR << 4) | 0b0100, 10, 0, 0, 0, 0]
        );
        assert_eq!(
            encode_from_iter([(0, 0, 10, 255)]),
            [(QOI_TAG_COLOR << 4) | 0b0010, 10, 0, 0, 0, 0]
        );
        assert_eq!(
            encode_from_iter([(0, 0, 0, 10)]),
            [(QOI_TAG_COLOR << 4) | 0b0001, 10, 0, 0, 0, 0]
        );
    }

    #[test]
    fn test_encode_from_iter_error() {
        assert!(qoi_encode_from_iter(
            &mut std::io::sink(),
            NonZeroUsize::new(4).unwrap(),
            [QoiPixel::new(0, 0, 0, 255); 4]
        )
        .is_ok());
        assert!(qoi_encode_from_iter(
            &mut std::io::sink(),
            NonZeroUsize::new(3).unwrap(),
            [QoiPixel::new(0, 0, 0, 255); 4]
        )
        .is_ok());
    }

    #[test]
    fn test_encode_from_buffer_rgba() {
        assert_eq!(
            encode_from_buffer(
                [0, 0, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255],
                QoiChannels::Rgba
            ),
            [(QOI_TAG_RUN_8 << 5) | 2, 0, 0, 0, 0]
        );
    }

    #[test]
    #[should_panic(expected = "buffer is too small")]
    fn test_encode_from_buffer_rgba_panic() {
        let _ = qoi_encode_from_buffer(
            &mut std::io::sink(),
            NonZeroUsize::new(1).unwrap(),
            [0, 0, 0],
            QoiChannels::Rgba,
        );
    }

    #[test]
    fn test_encode_from_buffer_rgb() {
        assert_eq!(
            encode_from_buffer([0, 0, 0, 0, 0, 0, 0, 0, 0], QoiChannels::Rgb),
            [(QOI_TAG_RUN_8 << 5) | 2, 0, 0, 0, 0]
        );
    }

    #[test]
    #[should_panic(expected = "buffer is too small")]
    fn test_encode_from_buffer_rgb_panic() {
        let _ = qoi_encode_from_buffer(
            &mut std::io::sink(),
            NonZeroUsize::new(1).unwrap(),
            [0, 0],
            QoiChannels::Rgb,
        );
    }
}
