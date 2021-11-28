use std::fs::File;
use std::io::{BufReader, Read};
use std::num::NonZeroU32;
use std::path::Path;

use byteorder::{ByteOrder as _, BE};

use crate::decode::{qoi_decode, qoi_decode_to_vec, QoiDecodedChunks};
use crate::error::{QoiError, QoiResult};
use crate::qoi::{QoiChannels, QoiDesc, QOI_HEADER_LEN, QOI_MAGIC};

/// Loads QOI format (with header) from file. Returns a image description and a newly allocated pixel buffer.
///
/// `channels` specifies the format of returned pixel buffer. RGBA8 and RGB8 are supported.
/// Note that the channels value in the header is always ignored.
///
/// This function reads a pixel count from the header, and decodes that number of pixels
/// unconditionally. If you treat QOI files from untrusted sources, it might be a problem. In such
/// cases, consider to use [`qoi_read`] or [`qoi_read_header`].
///
/// # Errors
///
/// * For reading header and decoding body, the same as [`qoi_read_to_vec`].
/// * Returns error if filesystem/read operation fails.
pub fn qoi_open<P>(path: P, channels: QoiChannels) -> QoiResult<(QoiDesc, Vec<u8>)>
where
    P: AsRef<Path>,
{
    let rdr = File::open(path)?;
    let mut rdr = BufReader::new(rdr);

    qoi_read_to_vec(&mut rdr, channels)
}

/// Reads QOI format (with header) from [`Read`], and returns a image description and an iterator
/// of [`QoiResult`]`<`[`QoiDecodedChunk`]`>`.
///
/// When the iterator has been run out, `rdr` does not necessarily point immediately after the QOI body.
/// Because QOI encoders can append a padding in some different ways.
/// (See [phoboslab/qoi#17](https://github.com/phoboslab/qoi/issues/17))
///
/// This function reads a pixel count from the header, and returned iterator tries to yield that
/// number of pixels. So, be careful if you treat inputs from untrusted sources.
///
/// # Errors
///
/// * For reading QOI header, the same as [`qoi_read_header`].
/// * Returned iterator yields an error under the same condition as [`qoi_decode`].
///
/// [`QoiDecodedChunk`]: crate::decode::QoiDecodedChunk
pub fn qoi_read<R>(rdr: &mut R) -> QoiResult<(QoiDesc, QoiDecodedChunks<R>)>
where
    R: Read,
{
    let desc = qoi_read_header(rdr)?;

    let dcs = qoi_decode(rdr, desc.pixel_count());

    Ok((desc, dcs))
}

/// Reads QOI format (with header) from [`Read`]. Returns a image description and a newly allocated pixel buffer.
///
/// `channels` specifies the format of returned pixel buffer. RGBA8 and RGB8 are supported.
/// Note that the channels value in the header is always ignored.
///
/// # Errors
///
/// * For reading QOI header, the same as [`qoi_read_header`].
/// * For decoding QOI body, the same as [`qoi_decode_to_vec`].
/// * Returns error if filesystem/read operation fails.
pub fn qoi_read_to_vec<R>(rdr: &mut R, channels: QoiChannels) -> QoiResult<(QoiDesc, Vec<u8>)>
where
    R: Read,
{
    let desc = qoi_read_header(rdr)?;

    let buf = qoi_decode_to_vec(rdr, desc.pixel_count(), channels)?;

    Ok((desc, buf))
}

/// Reads QOI header from [`Read`], and returns [`QoiDesc`].
///
/// After this function successfully returns, `rdr` is guaranteed to point immediately after the
/// QOI header.
///
/// # Errors
///
/// * Returns error if the header is invalid. (e.g. width is 0)
/// * Returns error if the pixel count exceeds [`usize::MAX`].
/// * Returns error if read operation fails.
pub fn qoi_read_header<R>(rdr: &mut R) -> QoiResult<QoiDesc>
where
    R: Read,
{
    let mut header = [0; QOI_HEADER_LEN];
    rdr.read_exact(&mut header)?;

    if &header[..4] != QOI_MAGIC {
        return Err(QoiError::new_header("QOI magic not found"));
    }

    let width = BE::read_u32(&header[4..]);
    let height = BE::read_u32(&header[8..]);
    let channels = header[12];
    let colorspace = header[13];

    if (width as usize).checked_mul(height as usize).is_none() {
        return Err(QoiError::new_header("pixel count exceeds usize::MAX"));
    }
    let width = NonZeroU32::new(width).ok_or_else(|| QoiError::new_header("width is 0"))?;
    let height = NonZeroU32::new(height).ok_or_else(|| QoiError::new_header("height is 0"))?;

    let channels = match channels {
        3 => QoiChannels::Rgb,
        4 => QoiChannels::Rgba,
        _ => {
            return Err(QoiError::new_header(format!(
                "invalid channels value: {}",
                channels
            )));
        }
    };

    let desc = QoiDesc::with_color_info(width, height, channels, colorspace);

    Ok(desc)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::decode::QoiDecodedChunk;
    use crate::pixel::QoiPixel;
    use crate::qoi::{QOI_TAG_COLOR, QOI_TAG_RUN_8};

    fn read_to_vec(qoi: impl AsRef<[u8]>, channels: QoiChannels) -> QoiResult<(QoiDesc, Vec<u8>)> {
        let mut qoi = qoi.as_ref();
        qoi_read_to_vec(&mut qoi, channels)
    }

    fn read_header(qoi: impl AsRef<[u8]>) -> QoiResult<QoiDesc> {
        let mut qoi = qoi.as_ref();
        qoi_read_header(&mut qoi)
    }

    #[test]
    fn test_read() {
        fn f(qoi: impl AsRef<[u8]>) -> QoiResult<(QoiDesc, Vec<QoiDecodedChunk>)> {
            let mut qoi = qoi.as_ref();
            let (desc, dcs) = qoi_read(&mut qoi)?;
            let dcs = dcs.into_iter().collect::<Result<_, _>>()?;
            Ok((desc, dcs))
        }

        #[rustfmt::skip]
        assert_eq!(
            f([
                b'q', b'o', b'i', b'f', 0, 0, 0, 3, 0, 0, 0, 11, 4, 1,
                (QOI_TAG_RUN_8 << 5) | 31,
                (QOI_TAG_COLOR << 4) | 0xF, 11, 22, 33, 44,
                0, 0, 0, 0
            ])
            .unwrap(),
            (
                QoiDesc::with_color_info(
                    NonZeroU32::new(3).unwrap(),
                    NonZeroU32::new(11).unwrap(),
                    QoiChannels::Rgba,
                    1
                ),
                vec![
                    QoiDecodedChunk::Run(QoiPixel::new(0, 0, 0, 255), 32),
                    QoiDecodedChunk::Single(QoiPixel::new(11, 22, 33, 44))
                ]
            )
        );
    }

    #[test]
    #[allow(clippy::identity_op)]
    fn test_read_to_vec() {
        #[rustfmt::skip]
        assert_eq!(
            read_to_vec(
                [
                    b'q', b'o', b'i', b'f', 0, 0, 0, 2, 0, 0, 0, 1, 4, 1,
                    (QOI_TAG_RUN_8 << 5) | 0,
                    (QOI_TAG_COLOR << 4) | 0xF, 11, 22, 33, 44,
                    0, 0, 0, 0
                ],
                QoiChannels::Rgba
            )
            .unwrap(),
            (
                QoiDesc::with_color_info(
                    NonZeroU32::new(2).unwrap(),
                    NonZeroU32::new(1).unwrap(),
                    QoiChannels::Rgba,
                    1
                ),
                vec![0, 0, 0, 255, 11, 22, 33, 44]
            )
        );

        #[rustfmt::skip]
        assert_eq!(
            read_to_vec(
                [
                    b'q', b'o', b'i', b'f', 0, 0, 0, 2, 0, 0, 0, 1, 3, 42,
                    (QOI_TAG_RUN_8 << 5) | 0,
                    (QOI_TAG_COLOR << 4) | 0xF, 11, 22, 33, 44,
                    0, 0, 0, 0
                ],
                QoiChannels::Rgb
            )
            .unwrap(),
            (
                QoiDesc::with_color_info(
                    NonZeroU32::new(2).unwrap(),
                    NonZeroU32::new(1).unwrap(),
                    QoiChannels::Rgb,
                    42
                ),
                vec![0, 0, 0, 11, 22, 33]
            )
        );
    }

    #[test]
    fn test_read_header() {
        assert_eq!(
            read_header([b'q', b'o', b'i', b'f', 0, 0, 0x02, 0x80, 0, 0, 0x01, 0xE0, 4, 1])
                .unwrap(),
            QoiDesc::with_color_info(
                NonZeroU32::new(0x0280).unwrap(),
                NonZeroU32::new(0x01E0).unwrap(),
                QoiChannels::Rgba,
                1
            )
        );

        assert_eq!(
            read_header([b'q', b'o', b'i', b'f', 0, 0, 0x02, 0x80, 0, 0, 0x01, 0xE0, 3, 42])
                .unwrap(),
            QoiDesc::with_color_info(
                NonZeroU32::new(0x0280).unwrap(),
                NonZeroU32::new(0x01E0).unwrap(),
                QoiChannels::Rgb,
                42
            )
        );
    }

    #[test]
    fn test_read_header_error() {
        assert!(read_header([]).is_err());
        assert!(read_header(b"qoiF").is_err());

        // both width and header must be positive.
        assert!(read_header([b'q', b'o', b'i', b'f', 0, 0, 0, 1, 0, 0, 0, 1, 3, 1]).is_ok());
        assert!(read_header([b'q', b'o', b'i', b'f', 0, 0, 0, 0, 0, 0, 0, 1, 3, 1]).is_err());
        assert!(read_header([b'q', b'o', b'i', b'f', 0, 0, 0, 1, 0, 0, 0, 0, 3, 1]).is_err());

        // channels value must be 3 or 4.
        assert!(read_header([b'q', b'o', b'i', b'f', 0, 0, 0, 1, 0, 0, 0, 1, 4, 1]).is_ok());
        assert!(read_header([b'q', b'o', b'i', b'f', 0, 0, 0, 1, 0, 0, 0, 1, 2, 1]).is_err());
        assert!(read_header([b'q', b'o', b'i', b'f', 0, 0, 0, 1, 0, 0, 0, 1, 5, 1]).is_err());
    }
}
