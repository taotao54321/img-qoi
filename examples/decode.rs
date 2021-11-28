use std::path::PathBuf;

use image::RgbaImage;
use structopt::StructOpt;

use img_qoi::*;

#[derive(Debug, StructOpt)]
#[structopt(about = "Converts QOI format to various formats. Example: decode foo.qoi foo.png")]
struct Opt {
    #[structopt(parse(from_os_str))]
    path_in: PathBuf,

    #[structopt(parse(from_os_str))]
    path_out: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();

    let (desc, buf_rgba) = qoi_open(opt.path_in, QoiChannels::Rgba)?;

    let img = RgbaImage::from_vec(desc.width().get(), desc.height().get(), buf_rgba)
        .expect("buffer should contain `width * height` pixels");

    img.save(opt.path_out)?;

    Ok(())
}
