use std::io::Read;
use std::num::NonZeroUsize;

use arrayvec::ArrayVec;
use byteorder::{ReadBytesExt as _, BE};

use crate::error::{QoiError, QoiResult};
use crate::pixel::{PixelDict, PixelDiff, QoiPixel};
use crate::qoi::{
    QoiChannels, QOI_PADDING_LEN, QOI_TAG_COLOR, QOI_TAG_DIFF_16, QOI_TAG_DIFF_24, QOI_TAG_DIFF_8,
    QOI_TAG_INDEX, QOI_TAG_RUN_16, QOI_TAG_RUN_8,
};

/// Decoded QOI chunk.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum QoiDecodedChunk {
    /// Single pixel.
    Single(QoiPixel),

    /// Run-length pixels.
    Run(QoiPixel, u16),
}

/// Decodes QOI body (without header) from [`Read`], and returns an iterator of [`QoiResult`]`<`[`QoiDecodedChunk`]`>`.
///
/// Decodes exactly `pixel_count` pixels.
///
/// When the iterator has been run out, `rdr` does not necessarily point immediately after the QOI body.
/// Because QOI encoders can append a padding in some different ways.
/// (See [phoboslab/qoi#17](https://github.com/phoboslab/qoi/issues/17))
///
/// # Errors
///
/// Returned iterator yields an error in following cases:
///
/// * Encountered premature end of chunks before `pixel_count` pixels have been decoded.
/// * QOI body is not properly padded at the end.
/// * Pixel sequence is terminated in the middle of a run-length chunk.
/// * Read operation fails.
pub fn qoi_decode<R>(rdr: &mut R, pixel_count: NonZeroUsize) -> QoiDecodedChunks<R>
where
    R: Read,
{
    QoiDecodedChunks::new(rdr, pixel_count)
}

/// Iterator which yields [`QoiResult`]`<`[`QoiDecodedChunk`]`>`. See [`qoi_decode`].
#[derive(Debug)]
pub struct QoiDecodedChunks<'a, R> {
    rdr: &'a mut R,
    pixel_remain: usize,
    px: QoiPixel,
    dict: PixelDict,
}

impl<'a, R: Read> QoiDecodedChunks<'a, R> {
    fn new(rdr: &'a mut R, pixel_count: NonZeroUsize) -> Self {
        Self {
            rdr,
            pixel_remain: pixel_count.get(),
            px: QoiPixel::new(0, 0, 0, 255),
            dict: PixelDict::new(),
        }
    }

    fn next_impl(&mut self) -> QoiResult<Option<QoiDecodedChunk>> {
        if self.pixel_remain == 0 {
            return Ok(None);
        }

        // pixel_remain > 0, so read next chunk.
        let op = self.rdr.read_u8()?;
        let run = self.read_chunk_and_update(op)?;
        debug_assert!(run > 0);

        self.pixel_remain = self
            .pixel_remain
            .checked_sub(usize::from(run))
            .ok_or_else(|| {
                QoiError::new_decode(
                    "pixel sequence must not end in the middle of a run-length chunk",
                )
            })?;

        if self.pixel_remain == 0 {
            // pixel sequence ended. read and discard the shortest padding necessary.
            let mut buf = ArrayVec::<u8, 4>::new();
            unsafe {
                buf.set_len(padding_len_min(op));
            }
            self.rdr.read_exact(&mut buf)?;
        }

        Ok(if run == 1 {
            Some(QoiDecodedChunk::Single(self.px))
        } else {
            Some(QoiDecodedChunk::Run(self.px, run))
        })
    }

    /// Reads next QOI chunk which starts which op, updates internal state, and returns
    /// the pixel run-length of the chunk.
    fn read_chunk_and_update(&mut self, op: u8) -> QoiResult<u16> {
        if let Some(run) = decode_chunk_run_8(op) {
            return Ok(u16::from(run));
        }

        if let Some(run) = decode_chunk_run_16(self.rdr, op) {
            let run = run?;
            return Ok(run);
        }

        if let Some(idx) = decode_chunk_index(op) {
            self.px = self.dict[idx];
            return Ok(1);
        }

        // all other chunk types have a single pixel, and need to update `PixelDict`.

        self.px = if let Some(diff) = decode_chunk_diff_8(op) {
            self.px.add(diff)
        } else if let Some(diff) = decode_chunk_diff_16(self.rdr, op) {
            let diff = diff?;
            self.px.add(diff)
        } else if let Some(diff) = decode_chunk_diff_24(self.rdr, op) {
            let diff = diff?;
            self.px.add(diff)
        } else {
            decode_chunk_color(self.rdr, op, self.px)?
        };

        let hash = PixelDict::hash(self.px);
        self.dict[hash] = self.px;

        Ok(1)
    }
}

impl<R: Read> Iterator for QoiDecodedChunks<'_, R> {
    type Item = QoiResult<QoiDecodedChunk>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_impl().transpose()
    }
}

fn decode_chunk_index(op: u8) -> Option<u8> {
    ((op >> 6) == QOI_TAG_INDEX).then(|| op & 0x3F)
}

fn decode_chunk_run_8(op: u8) -> Option<u8> {
    ((op >> 5) == QOI_TAG_RUN_8).then(|| 1 + (op & 0x1F))
}

fn decode_chunk_run_16(rdr: &mut impl Read, op: u8) -> Option<std::io::Result<u16>> {
    ((op >> 5) == QOI_TAG_RUN_16).then(|| {
        let arg = rdr.read_u8()?;
        let run = 33 + ((u16::from(op & 0x1F) << 8) | u16::from(arg));
        Ok(run)
    })
}

fn decode_chunk_diff_8(op: u8) -> Option<PixelDiff> {
    ((op >> 6) == QOI_TAG_DIFF_8).then(|| PixelDiff::Diff8(op & 0x3F))
}

fn decode_chunk_diff_16(rdr: &mut impl Read, op: u8) -> Option<std::io::Result<PixelDiff>> {
    ((op >> 5) == QOI_TAG_DIFF_16).then(|| {
        let arg = rdr.read_u8()?;
        let diff = (u16::from(op & 0x1F) << 8) | u16::from(arg);
        Ok(PixelDiff::Diff16(diff))
    })
}

fn decode_chunk_diff_24(rdr: &mut impl Read, op: u8) -> Option<std::io::Result<PixelDiff>> {
    ((op >> 4) == QOI_TAG_DIFF_24).then(|| {
        let arg = rdr.read_u16::<BE>()?;
        let diff_r = ((op & 0xF) << 1) | ((arg >> 15) as u8);
        let diff_gba = arg & 0x7FFF;
        Ok(PixelDiff::Diff24 { diff_r, diff_gba })
    })
}

fn decode_chunk_color(rdr: &mut impl Read, op: u8, px: QoiPixel) -> std::io::Result<QoiPixel> {
    debug_assert_eq!(op >> 4, QOI_TAG_COLOR);

    let r = if (op & (1 << 3)) != 0 {
        rdr.read_u8()?
    } else {
        px.r()
    };
    let g = if (op & (1 << 2)) != 0 {
        rdr.read_u8()?
    } else {
        px.g()
    };
    let b = if (op & (1 << 1)) != 0 {
        rdr.read_u8()?
    } else {
        px.b()
    };
    let a = if (op & (1 << 0)) != 0 {
        rdr.read_u8()?
    } else {
        px.a()
    };

    Ok(QoiPixel::new(r, g, b, a))
}

fn padding_len_min(op: u8) -> usize {
    if (op >> 5) == QOI_TAG_RUN_16 || (op >> 5) == QOI_TAG_DIFF_16 {
        QOI_PADDING_LEN - 1
    } else if (op >> 4) == QOI_TAG_DIFF_24 {
        QOI_PADDING_LEN - 2
    } else if (op >> 4) == QOI_TAG_COLOR {
        QOI_PADDING_LEN - (op & 0xF).count_ones() as usize
    } else {
        // QOI_INDEX, QOI_RUN_8, QOI_DIFF_8
        QOI_PADDING_LEN
    }
}

/// Decodes QOI body (without header) from [`Read`], and writes pixels to an existing buffer.
///
/// Decodes exactly `pixel_count` pixels.
///
/// `channels` specifies the pixel format in `buf`. RGBA8 and RGB8 are supported.
///
/// When this function has finished, `rdr` does not necessarily point immediately after the QOI body.
/// Because QOI encoders can append a padding in some different ways.
/// (See [phoboslab/qoi#17](https://github.com/phoboslab/qoi/issues/17))
///
/// # Errors
///
/// * Returns error if encountered premature end of chunks before `pixel_count` pixels have been decoded.
/// * Returns error if QOI body is not properly padded at the end.
/// * Returns error if pixel sequence is terminated in the middle of a run-length chunk.
/// * Returns error if read operation fails.
///
/// # Panics
///
/// * Panics if `buf` is too small.
pub fn qoi_decode_to_buffer<R>(
    rdr: &mut R,
    pixel_count: NonZeroUsize,
    buf: &mut [u8],
    channels: QoiChannels,
) -> QoiResult<()>
where
    R: Read,
{
    let buf_len_min = channels
        .byte_count()
        .checked_mul(pixel_count.get())
        .unwrap_or_else(|| panic!("overflow in buffer size calculation"));
    assert!(buf.len() >= buf_len_min, "buffer is too small");

    let mut i = 0;
    let mut write = move |px: QoiPixel| {
        channels.write_pixel_to_buffer(&mut buf[i..], px);
        i += channels.byte_count();
    };

    for dc in qoi_decode(rdr, pixel_count) {
        let dc = dc?;

        match dc {
            QoiDecodedChunk::Single(px) => write(px),
            QoiDecodedChunk::Run(px, run) => {
                for _ in 0..run {
                    write(px);
                }
            }
        }
    }

    Ok(())
}

/// Decodes QOI body (without header) from [`Read`], and writes pixels to a new [`Vec`].
///
/// Decodes exactly `pixel_count` pixels.
///
/// `channels` specifies the pixel format in `buf`. RGBA8 and RGB8 are supported.
///
/// When this function has finished, `rdr` does not necessarily point immediately after the QOI body.
/// Because QOI encoders can append a padding in some different ways.
/// (See [phoboslab/qoi#17](https://github.com/phoboslab/qoi/issues/17))
///
/// # Errors
///
/// * Returns error if encountered premature end of chunks before `pixel_count` pixels have been decoded.
/// * Returns error if QOI body is not properly padded at the end.
/// * Returns error if pixel sequence is terminated in the middle of a run-length chunk.
/// * Returns error if read operation fails.
///
/// # Panics
///
/// * Panics if the needed buffer size exceeds [`usize::MAX`].
pub fn qoi_decode_to_vec<R>(
    rdr: &mut R,
    pixel_count: NonZeroUsize,
    channels: QoiChannels,
) -> QoiResult<Vec<u8>>
where
    R: Read,
{
    let cap = channels
        .byte_count()
        .checked_mul(pixel_count.get())
        .unwrap_or_else(|| panic!("overflow in buffer size calculation"));

    let mut buf = Vec::<u8>::with_capacity(cap);
    let mut write = |px: QoiPixel| {
        channels
            .write_pixel(&mut buf, px)
            .expect("write to Vec should succeed");
    };

    for dc in qoi_decode(rdr, pixel_count) {
        let dc = dc?;

        match dc {
            QoiDecodedChunk::Single(px) => write(px),
            QoiDecodedChunk::Run(px, run) => {
                for _ in 0..run {
                    write(px);
                }
            }
        }
    }

    Ok(buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decode(body: impl AsRef<[u8]>, pixel_count: usize) -> QoiResult<Vec<QoiDecodedChunk>> {
        let mut body = body.as_ref();
        let pixel_count = NonZeroUsize::new(pixel_count).unwrap();
        qoi_decode(&mut body, pixel_count).collect()
    }

    fn decode_to_buffer(
        body: impl AsRef<[u8]>,
        pixel_count: usize,
        buf: &mut [u8],
        channels: QoiChannels,
    ) -> QoiResult<()> {
        let mut body = body.as_ref();
        let pixel_count = NonZeroUsize::new(pixel_count).unwrap();
        qoi_decode_to_buffer(&mut body, pixel_count, buf, channels)
    }

    fn decode_to_vec(
        body: impl AsRef<[u8]>,
        pixel_count: usize,
        channels: QoiChannels,
    ) -> QoiResult<Vec<u8>> {
        let mut body = body.as_ref();
        let pixel_count = NonZeroUsize::new(pixel_count).unwrap();
        qoi_decode_to_vec(&mut body, pixel_count, channels)
    }

    fn dc_single(r: u8, g: u8, b: u8, a: u8) -> QoiDecodedChunk {
        QoiDecodedChunk::Single(QoiPixel::new(r, g, b, a))
    }

    fn dc_run((r, g, b, a): (u8, u8, u8, u8), run: u16) -> QoiDecodedChunk {
        QoiDecodedChunk::Run(QoiPixel::new(r, g, b, a), run)
    }

    #[test]
    #[allow(clippy::identity_op)]
    #[allow(clippy::unusual_byte_groupings)]
    fn test_decode() {
        #[rustfmt::skip]
        let input: &[(usize, &[u8])] = &[
            (2, &[(QOI_TAG_RUN_8 << 5) | 1]),
            (1, &[(QOI_TAG_INDEX << 6) | 0]),
            (1, &[(QOI_TAG_COLOR << 4) | 0b1111, 12, 34, 56, 78]),
            (1, &[(QOI_TAG_INDEX << 6) | PixelDict::hash(QoiPixel::new(12, 34, 56, 78))]),
            (1, &[(QOI_TAG_RUN_8 << 5) | 0]),
            (32, &[(QOI_TAG_RUN_8 << 5) | 31]),
            (33, &[(QOI_TAG_RUN_16 << 5) | 0, 0]),
            (33 + 0x1FFF, &[(QOI_TAG_RUN_16 << 5) | 0x1F, 0xFF]),
            (1, &[(QOI_TAG_DIFF_8 << 6) | 0b_00_11_01]),
            (1, &[(QOI_TAG_DIFF_16 << 5) | 0b00000, 0b0000_1111]),
            (1, &[(QOI_TAG_DIFF_24 << 4) | 0b1111, 0b1_11111_11, 0b000_00000]),
            (1, &[(QOI_TAG_COLOR << 4) | 0b0000]),
            (1, &[(QOI_TAG_COLOR << 4) | 0b1000, 44]),
            (1, &[(QOI_TAG_COLOR << 4) | 0b0100, 33]),
            (1, &[(QOI_TAG_COLOR << 4) | 0b0010, 22]),
            (1, &[(QOI_TAG_COLOR << 4) | 0b0001, 11]),
            (1, &[(QOI_TAG_COLOR << 4) | 0b1010, 99, 88]),
        ];

        let body: Vec<u8> = input
            .iter()
            .flat_map(|&(_, buf)| buf)
            .copied()
            .chain([0_u8; 4]) // padding
            .collect();
        let pixel_count: usize = input.iter().map(|&(n, _)| n).sum();

        let expect = [
            dc_run((0, 0, 0, 255), 2),
            dc_single(0, 0, 0, 0),
            dc_single(12, 34, 56, 78),
            dc_single(12, 34, 56, 78),
            dc_single(12, 34, 56, 78),
            dc_run((12, 34, 56, 78), 32),
            dc_run((12, 34, 56, 78), 33),
            dc_run((12, 34, 56, 78), 33 + 0x1FFF),
            dc_single(10, 35, 55, 78),
            dc_single(250, 27, 62, 78),
            dc_single(9, 42, 70, 62),
            dc_single(9, 42, 70, 62),
            dc_single(44, 42, 70, 62),
            dc_single(44, 33, 70, 62),
            dc_single(44, 33, 22, 62),
            dc_single(44, 33, 22, 11),
            dc_single(99, 33, 88, 11),
        ];

        assert_eq!(decode(body, pixel_count).unwrap(), expect);
    }

    #[test]
    fn test_decode_error_premature_end_of_chunks() {
        assert!(decode([], 1).is_err());
        assert!(decode([0; 4], 1).is_err());

        assert!(decode([(QOI_TAG_RUN_8 << 5) | 31, 0, 0, 0, 0], 32).is_ok());
        assert!(decode([(QOI_TAG_RUN_8 << 5) | 31, 0, 0, 0, 0], 33).is_err());

        assert!(decode(
            [(QOI_TAG_RUN_16 << 5) | 0x1F, 0xFF, 0, 0, 0, 0],
            33 + 0x1FFF
        )
        .is_ok());
        assert!(decode(
            [(QOI_TAG_RUN_16 << 5) | 0x1F, 0xFF, 0, 0, 0, 0],
            33 + 0x2000
        )
        .is_err());

        assert!(decode([(QOI_TAG_INDEX << 6) | 1, 0, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_INDEX << 6) | 1, 0, 0, 0, 0], 2).is_err());

        assert!(decode([(QOI_TAG_DIFF_8 << 6) | 1, 0, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_DIFF_8 << 6) | 1, 0, 0, 0, 0], 2).is_err());

        assert!(decode([(QOI_TAG_DIFF_16 << 5) | 1, 1, 0, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_DIFF_16 << 5) | 1, 1, 0, 0, 0, 0], 2).is_err());

        assert!(decode([(QOI_TAG_DIFF_24 << 4) | 1, 1, 1, 0, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_DIFF_24 << 4) | 1, 1, 1, 0, 0, 0, 0], 2).is_err());

        assert!(decode([(QOI_TAG_COLOR << 4) | 0b1010, 1, 1, 0, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_COLOR << 4) | 0b1010, 1, 1, 0, 0, 0, 0], 2).is_err());

        assert!(decode([(QOI_TAG_COLOR << 4) | 0b1111, 1, 1, 1, 1, 0, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_COLOR << 4) | 0b1111, 1, 1, 1, 1, 0, 0, 0, 0], 2).is_err());
    }

    #[test]
    fn test_decode_error_premature_end_of_padding() {
        assert!(decode([(QOI_TAG_RUN_8 << 5) | 31, 0, 0, 0, 0], 32).is_ok());
        assert!(decode([(QOI_TAG_RUN_8 << 5) | 31, 0, 0, 0], 32).is_err());

        assert!(decode([(QOI_TAG_RUN_16 << 5) | 0x1F, 0xFF, 0, 0, 0], 33 + 0x1FFF).is_ok());
        assert!(decode([(QOI_TAG_RUN_16 << 5) | 0x1F, 0xFF, 0, 0], 33 + 0x1FFF).is_err());

        assert!(decode([(QOI_TAG_INDEX << 6) | 1, 0, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_INDEX << 6) | 1, 0, 0, 0], 1).is_err());

        assert!(decode([(QOI_TAG_DIFF_8 << 6) | 1, 0, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_DIFF_8 << 6) | 1, 0, 0, 0], 1).is_err());

        assert!(decode([(QOI_TAG_DIFF_16 << 5) | 1, 1, 0, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_DIFF_16 << 5) | 1, 1, 0, 0], 1).is_err());

        assert!(decode([(QOI_TAG_DIFF_24 << 4) | 1, 1, 1, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_DIFF_24 << 4) | 1, 1, 1, 0], 1).is_err());

        assert!(decode([(QOI_TAG_COLOR << 4) | 0b1010, 1, 1, 0, 0], 1).is_ok());
        assert!(decode([(QOI_TAG_COLOR << 4) | 0b1010, 1, 1, 0], 1).is_err());

        assert!(decode([(QOI_TAG_COLOR << 4) | 0b1111, 1, 1, 1, 1], 1).is_ok());
    }

    #[test]
    fn test_decode_error_middle_of_chunk() {
        assert!(decode([(QOI_TAG_RUN_8 << 5) | 31, 0, 0, 0, 0], 31).is_err());

        assert!(decode(
            [(QOI_TAG_RUN_16 << 5) | 0x1F, 0xFF, 0, 0, 0, 0],
            33 + 0x1FFE
        )
        .is_err());
    }

    #[test]
    fn test_decode_to_buffer() {
        let body = [(QOI_TAG_COLOR << 4) | 0b1111, 11, 22, 33, 44];

        {
            let mut buf = [0; 4];
            decode_to_buffer(body, 1, &mut buf, QoiChannels::Rgba).unwrap();
            assert_eq!(buf, [11, 22, 33, 44]);
        }
        {
            let mut buf = [0; 3];
            decode_to_buffer(body, 1, &mut buf, QoiChannels::Rgb).unwrap();
            assert_eq!(buf, [11, 22, 33]);
        }
    }

    #[test]
    #[should_panic(expected = "buffer is too small")]
    fn test_decode_to_buffer_panic_rgba() {
        let body = [(QOI_TAG_INDEX << 6) | 1, 0, 0, 0, 0];
        let mut buf = [0; 3];
        let channels = QoiChannels::Rgba;
        let _ = decode_to_buffer(body, 1, &mut buf, channels);
    }

    #[test]
    #[should_panic(expected = "buffer is too small")]
    fn test_decode_to_buffer_panic_rgb() {
        let body = [(QOI_TAG_INDEX << 6) | 1, 0, 0, 0, 0];
        let mut buf = [0; 2];
        let channels = QoiChannels::Rgb;
        let _ = decode_to_buffer(body, 1, &mut buf, channels);
    }

    #[test]
    fn test_decode_to_vec() {
        let body = [(QOI_TAG_COLOR << 4) | 0b1111, 11, 22, 33, 44];

        assert_eq!(
            decode_to_vec(body, 1, QoiChannels::Rgba).unwrap(),
            [11, 22, 33, 44]
        );
        assert_eq!(
            decode_to_vec(body, 1, QoiChannels::Rgb).unwrap(),
            [11, 22, 33]
        );
    }
}
