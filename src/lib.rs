//! [QOI](https://github.com/phoboslab/qoi) (Quite OK Image) manipulation library.
//!
//! # Examples
//!
//! Convert QOI to PNG (with [`image`] crate):
//!
//! ```no_run
//! use image::RgbaImage;
//! use img_qoi::*;
//!
//! # fn main() -> anyhow::Result<()> {
//! let (desc, buf_rgba) = qoi_open("foo.qoi", QoiChannels::Rgba)?;
//!
//! let img = RgbaImage::from_vec(desc.width().get(), desc.height().get(), buf_rgba).unwrap();
//! img.save("foo.png")?;
//! # Ok(())
//! # }
//! ```
//!
//! Convert PNG to QOI (with [`image`] crate):
//!
//! ```no_run
//! use std::num::NonZeroU32;
//! use img_qoi::*;
//!
//! # fn main() -> anyhow::Result<()> {
//! let img = image::open("foo.png")?;
//! let img = img.to_rgba8();
//!
//! let desc = QoiDesc::new(
//!     NonZeroU32::new(img.width()).unwrap(),
//!     NonZeroU32::new(img.height()).unwrap()
//! );
//!
//! // `RgbaImage` implements `Deref<[u8]>`.
//! qoi_save_from_buffer("foo.qoi", &desc, &*img, QoiChannels::Rgba)?;
//! # Ok(())
//! # }
//! ```
//!
//! [`image`]: https://docs.rs/image/

mod decode;
mod encode;
mod error;
mod input;
mod output;
mod pixel;
mod qoi;

pub use self::decode::*;
pub use self::encode::*;
pub use self::error::*;
pub use self::input::*;
pub use self::output::*;
pub use self::pixel::*;
pub use self::qoi::*;
