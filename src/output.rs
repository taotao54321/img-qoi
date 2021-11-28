use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use byteorder::{ByteOrder as _, BE};

use crate::encode::{qoi_encode_from_buffer, qoi_encode_from_iter};
use crate::error::QoiResult;
use crate::pixel::QoiPixel;
use crate::qoi::{QoiChannels, QoiDesc, QOI_HEADER_LEN, QOI_MAGIC};

/// Saves QOI format (with header) to file. Pixels are obtained from [`IntoIterator`].
///
/// Encodes exactly `desc.pixel_count()` pixels.
///
/// # Errors
///
/// * For writing header and encoding body, the same as [`qoi_write_from_iter`].
/// * Returns error if filesystem/write operation fails.
pub fn qoi_save_from_iter<P, I>(path: P, desc: &QoiDesc, pixels: I) -> QoiResult<()>
where
    P: AsRef<Path>,
    I: IntoIterator<Item = QoiPixel>,
{
    let wtr = File::create(path)?;
    let mut wtr = BufWriter::new(wtr);

    qoi_write_from_iter(&mut wtr, desc, pixels)?;

    wtr.flush()?;

    Ok(())
}

/// Saves QOI format (with header) to file. Pixels are obtained from a pixel buffer.
///
/// Encodes exactly `desc.pixel_count()` pixels.
///
/// # Errors
///
/// * For writing header and encoding body, the same as [`qoi_write_from_buffer`].
/// * Returns error if filesystem/write operation fails.
pub fn qoi_save_from_buffer<P, T>(
    path: P,
    desc: &QoiDesc,
    buf: T,
    channels: QoiChannels,
) -> QoiResult<()>
where
    P: AsRef<Path>,
    T: AsRef<[u8]>,
{
    let wtr = File::create(path)?;
    let mut wtr = BufWriter::new(wtr);

    qoi_write_from_buffer(&mut wtr, desc, buf, channels)?;

    wtr.flush()?;

    Ok(())
}

/// Writes QOI format (with header) to [`Write`]. Pixels are obtained from [`IntoIterator`].
///
/// Encodes exactly `desc.pixel_count()` pixels.
///
/// # Errors
///
/// * Returns error if `pixels` yields less than `desc.pixel_count()` pixels.
/// * Returns error if write operation fails.
pub fn qoi_write_from_iter<W, I>(wtr: &mut W, desc: &QoiDesc, pixels: I) -> QoiResult<()>
where
    W: Write,
    I: IntoIterator<Item = QoiPixel>,
{
    qoi_write_header(wtr, desc)?;

    qoi_encode_from_iter(wtr, desc.pixel_count(), pixels)
}

/// Writes QOI format (with header) to [`Write`]. Pixels are obtained from a pixel buffer.
///
/// Encodes exactly `desc.pixel_count()` pixels.
///
/// `channels` specifies the format of returned pixel buffer. RGBA8 and RGB8 are supported.
/// Note that the `desc.channels()` value is always ignored.
///
/// # Errors
///
/// * Returns error if write operation fails.
///
/// # Panics
///
/// * Panics if `buf` is too small.
pub fn qoi_write_from_buffer<W, T>(
    wtr: &mut W,
    desc: &QoiDesc,
    buf: T,
    channels: QoiChannels,
) -> QoiResult<()>
where
    W: Write,
    T: AsRef<[u8]>,
{
    qoi_write_header(wtr, desc)?;

    qoi_encode_from_buffer(wtr, desc.pixel_count(), buf, channels)
}

/// Writes QOI header to [`Write`].
///
/// # Errors
///
/// * Returns error if write operation fails.
pub fn qoi_write_header<W>(wtr: &mut W, desc: &QoiDesc) -> QoiResult<()>
where
    W: Write,
{
    let mut header = [0; QOI_HEADER_LEN];

    header[..4].copy_from_slice(QOI_MAGIC);

    BE::write_u32(&mut header[4..], desc.width().get());
    BE::write_u32(&mut header[8..], desc.height().get());
    header[12] = match desc.channels() {
        QoiChannels::Rgba => 4,
        QoiChannels::Rgb => 3,
    };
    header[13] = desc.colorspace();

    wtr.write_all(&header)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::num::NonZeroU32;

    use crate::qoi::{QOI_TAG_COLOR, QOI_TAG_RUN_8};

    #[test]
    fn test_write_from_iter() {
        fn f(desc: QoiDesc, pixels: impl AsRef<[(u8, u8, u8, u8)]>) -> Vec<u8> {
            let pixels = pixels
                .as_ref()
                .iter()
                .map(|&(r, g, b, a)| QoiPixel::new(r, g, b, a));
            let mut buf = Vec::<u8>::new();
            qoi_write_from_iter(&mut buf, &desc, pixels).unwrap();
            buf
        }

        #[rustfmt::skip]
        assert_eq!(
            f(
                QoiDesc::new(NonZeroU32::new(4).unwrap(), NonZeroU32::new(8).unwrap()),
                [(0, 0, 0, 255); 32]
            ),
            [
                b'q', b'o', b'i', b'f', 0, 0, 0, 4, 0, 0, 0, 8, 4, 1,
                (QOI_TAG_RUN_8 << 5) | 31,
                0, 0, 0, 0
            ]
        );
    }

    #[test]
    fn test_write_from_buffer() {
        fn f(desc: QoiDesc, buf_in: impl AsRef<[u8]>, channels: QoiChannels) -> Vec<u8> {
            let mut buf_out = Vec::<u8>::new();
            qoi_write_from_buffer(&mut buf_out, &desc, buf_in, channels).unwrap();
            buf_out
        }

        #[rustfmt::skip]
        assert_eq!(
            f(
                QoiDesc::new(
                    NonZeroU32::new(2).unwrap(),
                    NonZeroU32::new(1).unwrap()
                ),
                [11, 22, 33, 44, 55, 66, 77, 88],
                QoiChannels::Rgba
            ),
            [
                b'q', b'o', b'i', b'f', 0, 0, 0, 2, 0, 0, 0, 1, 4, 1,
                (QOI_TAG_COLOR << 4) | 0xF, 11, 22, 33, 44,
                (QOI_TAG_COLOR << 4) | 0xF, 55, 66, 77, 88,
                0, 0, 0, 0,
            ]
        );
    }

    #[test]
    fn test_write_header() {
        fn f(desc: QoiDesc) -> Vec<u8> {
            let mut buf = Vec::<u8>::new();
            qoi_write_header(&mut buf, &desc).unwrap();
            buf
        }

        assert_eq!(
            f(QoiDesc::with_color_info(
                NonZeroU32::new(0x280).unwrap(),
                NonZeroU32::new(0x1E0).unwrap(),
                QoiChannels::Rgba,
                1
            )),
            [b'q', b'o', b'i', b'f', 0, 0, 0x02, 0x80, 0, 0, 0x01, 0xE0, 4, 1]
        );

        assert_eq!(
            f(QoiDesc::with_color_info(
                NonZeroU32::new(0x280).unwrap(),
                NonZeroU32::new(0x1E0).unwrap(),
                QoiChannels::Rgb,
                42
            )),
            [b'q', b'o', b'i', b'f', 0, 0, 0x02, 0x80, 0, 0, 0x01, 0xE0, 3, 42]
        );
    }
}
