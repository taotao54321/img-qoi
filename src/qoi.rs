use std::num::{NonZeroU32, NonZeroUsize};

use byteorder::{ByteOrder as _, WriteBytesExt as _, BE};

use crate::pixel::QoiPixel;

/// QOI image description.
///
/// The pixel count of `QoiDesc` is guaranteed not to exceed [`usize::MAX`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct QoiDesc {
    width: NonZeroU32,
    height: NonZeroU32,
    channels: QoiChannels,
    colorspace: u8,
}

impl QoiDesc {
    /// Creates QOI image description with width and height.
    ///
    /// * `channels` value is set to [`QoiChannels::Rgba`].
    /// * `colorspace` value is set to `0b0001`.
    ///
    /// # Panics
    ///
    /// * Panics if the pixel count (`width * height`) exceeds [`usize::MAX`].
    pub fn new(width: NonZeroU32, height: NonZeroU32) -> Self {
        Self::with_color_info(width, height, QoiChannels::Rgba, 0b0001)
    }

    /// Creates QOI image description with width, height, channels, and colorspace.
    ///
    /// # Panics
    ///
    /// * Panics if the pixel count (`width * height`) exceeds [`usize::MAX`].
    pub fn with_color_info(
        width: NonZeroU32,
        height: NonZeroU32,
        channels: QoiChannels,
        colorspace: u8,
    ) -> Self {
        assert!(
            (width.get() as usize)
                .checked_mul(height.get() as usize)
                .is_some(),
            "pixel count overflow"
        );

        Self {
            width,
            height,
            channels,
            colorspace,
        }
    }

    /// Returns the width of this image in pixels.
    pub fn width(&self) -> NonZeroU32 {
        self.width
    }

    /// Returns the height of this image in pixels.
    pub fn height(&self) -> NonZeroU32 {
        self.height
    }

    /// Returns the channels of this image (RGB8 or RGBA8).
    ///
    /// This value is purely informative, and it does not change the behavior of codec.
    pub fn channels(&self) -> QoiChannels {
        self.channels
    }

    /// Returns the colorspace value of this image.
    ///
    /// This value usually means as follows:
    ///
    /// * Red component is linear if bit3 is 1, otherwise gamma compressed.
    /// * Green component is linear if bit2 is 1, otherwise gamma compressed.
    /// * Blue component is linear if bit1 is 1, otherwise gamma compressed.
    /// * Alpha component is linear if bit0 is 1, otherwise gamma compressed.
    ///
    /// This value is purely informative, and it does not change the behavior of codec.
    pub fn colorspace(&self) -> u8 {
        self.colorspace
    }

    /// Returns the pixel count of this image.
    pub fn pixel_count(&self) -> NonZeroUsize {
        NonZeroUsize::new((self.width.get() as usize) * (self.height.get() as usize))
            .expect("pixel count should be positive")
    }
}

/// QOI channels (RGBA8 or RGB8).
///
/// * When converting `QoiPixel` to RGB8, alpha value is simply discarded.
/// * When converting RGB8 to `QoiPixel`, alpha value is set to 255.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum QoiChannels {
    /// RGB8.
    Rgb,

    /// RGBA8.
    Rgba,
}

impl QoiChannels {
    pub(crate) fn byte_count(self) -> usize {
        match self {
            Self::Rgb => 3,
            Self::Rgba => 4,
        }
    }

    pub(crate) fn read_pixel_from_buffer(self, buf: impl AsRef<[u8]>) -> QoiPixel {
        let buf = buf.as_ref();

        match self {
            Self::Rgb => {
                let value = BE::read_u24(buf);
                QoiPixel::from_raw((value << 8) | 0xFF)
            }
            Self::Rgba => {
                let value = BE::read_u32(buf);
                QoiPixel::from_raw(value)
            }
        }
    }

    pub(crate) fn write_pixel<W>(self, wtr: &mut W, px: QoiPixel) -> std::io::Result<()>
    where
        W: std::io::Write,
    {
        match self {
            Self::Rgb => wtr.write_u24::<BE>(px.get() >> 8),
            Self::Rgba => wtr.write_u32::<BE>(px.get()),
        }
    }

    pub(crate) fn write_pixel_to_buffer(self, buf: &mut [u8], px: QoiPixel) {
        match self {
            Self::Rgb => BE::write_u24(buf, px.get() >> 8),
            Self::Rgba => BE::write_u32(buf, px.get()),
        }
    }
}

pub(crate) const QOI_PADDING_LEN: usize = 4;

pub(crate) const QOI_TAG_INDEX: u8 = 0b00;
pub(crate) const QOI_TAG_RUN_8: u8 = 0b010;
pub(crate) const QOI_TAG_RUN_16: u8 = 0b011;
pub(crate) const QOI_TAG_DIFF_8: u8 = 0b10;
pub(crate) const QOI_TAG_DIFF_16: u8 = 0b110;
pub(crate) const QOI_TAG_DIFF_24: u8 = 0b1110;
pub(crate) const QOI_TAG_COLOR: u8 = 0b1111;

pub(crate) const QOI_MAGIC: &[u8] = b"qoif";
pub(crate) const QOI_HEADER_LEN: usize = 14;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_qoi_desc_new() {
        let desc = QoiDesc::new(NonZeroU32::new(400).unwrap(), NonZeroU32::new(300).unwrap());

        assert_eq!(desc.width().get(), 400);
        assert_eq!(desc.height().get(), 300);
        assert_eq!(desc.channels(), QoiChannels::Rgba);
        assert_eq!(desc.colorspace(), 0b0001);
        assert_eq!(desc.pixel_count().get(), 400 * 300);
    }

    #[test]
    fn test_qoi_desc_with_color_info() {
        let desc = QoiDesc::with_color_info(
            NonZeroU32::new(400).unwrap(),
            NonZeroU32::new(300).unwrap(),
            QoiChannels::Rgb,
            42,
        );

        assert_eq!(desc.width().get(), 400);
        assert_eq!(desc.height().get(), 300);
        assert_eq!(desc.channels(), QoiChannels::Rgb);
        assert_eq!(desc.colorspace(), 42);
        assert_eq!(desc.pixel_count().get(), 400 * 300);
    }
}
