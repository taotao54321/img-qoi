# [QOI](https://github.com/phoboslab/qoi) (Quite OK Image) manipulation library

[Documentaion](https://docs.rs/img-qoi)

## Examples

Convert QOI to PNG (with [`image`](https://docs.rs/image/) crate):

```rust
use image::RgbaImage;
use img_qoi::*;

let (desc, buf_rgba) = qoi_open("foo.qoi", QoiChannels::Rgba)?;

let img = RgbaImage::from_vec(desc.width().get(), desc.height().get(), buf_rgba).unwrap();
img.save("foo.png")?;
```

Convert PNG to QOI (with [`image`](https://docs.rs/image/) crate):

```rust
use std::num::NonZeroU32;
use img_qoi::*;

let img = image::open("foo.png")?;
let img = img.to_rgba8();

let desc = QoiDesc::new(
    NonZeroU32::new(img.width()).unwrap(),
    NonZeroU32::new(img.height()).unwrap()
);

// `RgbaImage` implements `Deref<[u8]>`.
qoi_save_from_buffer("foo.qoi", &desc, &*img, QoiChannels::Rgba)?;
```

## License

MIT
