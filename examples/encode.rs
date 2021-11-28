use std::num::NonZeroU32;
use std::path::PathBuf;

use structopt::StructOpt;

use img_qoi::*;

#[derive(Debug, StructOpt)]
#[structopt(about = "Converts various formats to QOI format. Example: encode foo.png foo.qoi")]
struct Opt {
    #[structopt(parse(from_os_str))]
    path_in: PathBuf,

    #[structopt(parse(from_os_str))]
    path_out: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();

    let img = image::open(opt.path_in)?;
    let img = img.to_rgba8();

    let desc = QoiDesc::new(
        NonZeroU32::new(img.width()).unwrap(),
        NonZeroU32::new(img.height()).unwrap(),
    );

    // `RgbaImage` implements `Deref<[u8]>`.
    qoi_save_from_buffer(opt.path_out, &desc, &*img, QoiChannels::Rgba)?;

    Ok(())
}
