use std::ops::RangeInclusive;

/// RGBA8 pixel.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct QoiPixel(u32);

impl QoiPixel {
    /// Creates RGBA8 pixel from channel components.
    pub const fn new(r: u8, g: u8, b: u8, a: u8) -> Self {
        let r = r as u32;
        let g = g as u32;
        let b = b as u32;
        let a = a as u32;
        Self((r << 24) | (g << 16) | (b << 8) | a)
    }

    /// Returns the red channel component of this pixel.
    pub const fn r(self) -> u8 {
        (self.0 >> 24) as u8
    }

    /// Returns the green channel component of this pixel.
    pub const fn g(self) -> u8 {
        (self.0 >> 16) as u8
    }

    /// Returns the blue channel component of this pixel.
    pub const fn b(self) -> u8 {
        (self.0 >> 8) as u8
    }

    /// Returns the alpha channel component of this pixel.
    pub const fn a(self) -> u8 {
        self.0 as u8
    }

    pub(crate) const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    pub(crate) const fn get(self) -> u32 {
        self.0
    }

    pub(crate) const fn add(self, rhs: PixelDiff) -> Self {
        match rhs {
            PixelDiff::Diff8(diff) => {
                let dr = (diff >> 4).wrapping_add(*DIFF_RANGE_2.start() as u8);
                let dg = ((diff >> 2) & 3).wrapping_add(*DIFF_RANGE_2.start() as u8);
                let db = (diff & 3).wrapping_add(*DIFF_RANGE_2.start() as u8);

                let r = self.r().wrapping_add(dr);
                let g = self.g().wrapping_add(dg);
                let b = self.b().wrapping_add(db);

                Self::new(r, g, b, self.a())
            }
            PixelDiff::Diff16(diff) => {
                let dr = ((diff >> 8) as u8).wrapping_add(*DIFF_RANGE_5.start() as u8);
                let dg = (((diff >> 4) & 0xF) as u8).wrapping_add(*DIFF_RANGE_4.start() as u8);
                let db = ((diff & 0xF) as u8).wrapping_add(*DIFF_RANGE_4.start() as u8);

                let r = self.r().wrapping_add(dr);
                let g = self.g().wrapping_add(dg);
                let b = self.b().wrapping_add(db);

                Self::new(r, g, b, self.a())
            }
            PixelDiff::Diff24 { diff_r, diff_gba } => {
                let dr = diff_r.wrapping_add(*DIFF_RANGE_5.start() as u8);
                let dg = ((diff_gba >> 10) as u8).wrapping_add(*DIFF_RANGE_5.start() as u8);
                let db = (((diff_gba >> 5) & 0x1F) as u8).wrapping_add(*DIFF_RANGE_5.start() as u8);
                let da = ((diff_gba & 0x1F) as u8).wrapping_add(*DIFF_RANGE_5.start() as u8);

                let r = self.r().wrapping_add(dr);
                let g = self.g().wrapping_add(dg);
                let b = self.b().wrapping_add(db);
                let a = self.a().wrapping_add(da);

                Self::new(r, g, b, a)
            }
        }
    }

    /// Returns `self - rhs`.
    pub(crate) const fn sub(self, rhs: Self) -> DiffOrColor {
        const fn in_bounds(range: RangeInclusive<i8>, value: i8) -> bool {
            *range.start() <= value && value <= *range.end()
        }

        let dr = self.r().wrapping_sub(rhs.r()) as i8;
        let dg = self.g().wrapping_sub(rhs.g()) as i8;
        let db = self.b().wrapping_sub(rhs.b()) as i8;
        let da = self.a().wrapping_sub(rhs.a()) as i8;

        // QOI_DIFF_8 and QOI_DIFF_16 are always not worse than QOI_COLOR.

        if da == 0 {
            if in_bounds(DIFF_RANGE_2, dr)
                && in_bounds(DIFF_RANGE_2, dg)
                && in_bounds(DIFF_RANGE_2, db)
            {
                return DiffOrColor::Diff(PixelDiff::diff8_from_unbiased(dr, dg, db));
            }
            if in_bounds(DIFF_RANGE_5, dr)
                && in_bounds(DIFF_RANGE_4, dg)
                && in_bounds(DIFF_RANGE_4, db)
            {
                return DiffOrColor::Diff(PixelDiff::diff16_from_unbiased(dr, dg, db));
            }
        }

        // If only one component differ, QOI_COLOR is better than QOI_DIFF_24.

        let mask = (((dr != 0) as u8) << 3)
            | (((dg != 0) as u8) << 2)
            | (((db != 0) as u8) << 1)
            | ((da != 0) as u8);

        if mask.count_ones() >= 2
            && in_bounds(DIFF_RANGE_5, dr)
            && in_bounds(DIFF_RANGE_5, dg)
            && in_bounds(DIFF_RANGE_5, db)
            && in_bounds(DIFF_RANGE_5, da)
        {
            return DiffOrColor::Diff(PixelDiff::diff24_from_unbiased(dr, dg, db, da));
        }

        DiffOrColor::Color(mask)
    }
}

impl From<[u8; 4]> for QoiPixel {
    fn from(rgba: [u8; 4]) -> Self {
        Self::new(rgba[0], rgba[1], rgba[2], rgba[3])
    }
}

pub(crate) const DIFF_RANGE_2: RangeInclusive<i8> = -2..=1;
pub(crate) const DIFF_RANGE_4: RangeInclusive<i8> = -8..=7;
pub(crate) const DIFF_RANGE_5: RangeInclusive<i8> = -16..=15;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DiffOrColor {
    Diff(PixelDiff),
    Color(u8), // mask: 0b0000rgba (same as QOI_COLOR)
}

/// Pixel differences (QOI_DIFF_8, QOI_DIFF_16, QOI_DIFF_24).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum PixelDiff {
    Diff8(u8),   // 0b00rrggbb (same as QOI_DIFF_8)
    Diff16(u16), // 0b000rrrrr_ggggbbbb (same as QOI_DIFF_16)
    Diff24 {
        diff_r: u8,    // 0b000rrrrr
        diff_gba: u16, // 0b0gggggbbbbbaaaaa
    },
}

impl PixelDiff {
    pub(crate) const fn diff8_from_biased(r: u8, g: u8, b: u8) -> Self {
        Self::Diff8((r << 4) | (g << 2) | b)
    }

    pub(crate) const fn diff8_from_unbiased(r: i8, g: i8, b: i8) -> Self {
        let r = (r as u8).wrapping_sub(*DIFF_RANGE_2.start() as u8);
        let g = (g as u8).wrapping_sub(*DIFF_RANGE_2.start() as u8);
        let b = (b as u8).wrapping_sub(*DIFF_RANGE_2.start() as u8);

        Self::diff8_from_biased(r, g, b)
    }

    pub(crate) const fn diff16_from_biased(r: u8, g: u8, b: u8) -> Self {
        let r = r as u16;
        let g = g as u16;
        let b = b as u16;

        Self::Diff16((r << 8) | (g << 4) | b)
    }

    pub(crate) const fn diff16_from_unbiased(r: i8, g: i8, b: i8) -> Self {
        let r = (r as u8).wrapping_sub(*DIFF_RANGE_5.start() as u8);
        let g = (g as u8).wrapping_sub(*DIFF_RANGE_4.start() as u8);
        let b = (b as u8).wrapping_sub(*DIFF_RANGE_4.start() as u8);

        Self::diff16_from_biased(r, g, b)
    }

    pub(crate) const fn diff24_from_biased(r: u8, g: u8, b: u8, a: u8) -> Self {
        let g = g as u16;
        let b = b as u16;
        let a = a as u16;

        let diff_gba = (g << 10) | (b << 5) | a;

        Self::Diff24 {
            diff_r: r,
            diff_gba,
        }
    }

    pub(crate) const fn diff24_from_unbiased(r: i8, g: i8, b: i8, a: i8) -> Self {
        let r = (r as u8).wrapping_sub(*DIFF_RANGE_5.start() as u8);
        let g = (g as u8).wrapping_sub(*DIFF_RANGE_5.start() as u8);
        let b = (b as u8).wrapping_sub(*DIFF_RANGE_5.start() as u8);
        let a = (a as u8).wrapping_sub(*DIFF_RANGE_5.start() as u8);

        Self::diff24_from_biased(r, g, b, a)
    }
}

#[derive(Debug)]
pub(crate) struct PixelDict([QoiPixel; 64]);

impl PixelDict {
    pub(crate) const fn new() -> Self {
        Self([QoiPixel::new(0, 0, 0, 0); 64])
    }

    pub(crate) const fn hash(px: QoiPixel) -> u8 {
        (px.r() ^ px.g() ^ px.b() ^ px.a()) & 0x3F
    }
}

impl std::ops::Index<u8> for PixelDict {
    type Output = QoiPixel;

    fn index(&self, i: u8) -> &Self::Output {
        &self.0[usize::from(i)]
    }
}

impl std::ops::IndexMut<u8> for PixelDict {
    fn index_mut(&mut self, i: u8) -> &mut Self::Output {
        &mut self.0[usize::from(i)]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pixel_diff_8(r: i8, g: i8, b: i8) -> PixelDiff {
        debug_assert!(DIFF_RANGE_2.contains(&r));
        debug_assert!(DIFF_RANGE_2.contains(&g));
        debug_assert!(DIFF_RANGE_2.contains(&b));
        PixelDiff::diff8_from_unbiased(r, g, b)
    }

    fn pixel_diff_16(r: i8, g: i8, b: i8) -> PixelDiff {
        debug_assert!(DIFF_RANGE_5.contains(&r));
        debug_assert!(DIFF_RANGE_4.contains(&g));
        debug_assert!(DIFF_RANGE_4.contains(&b));
        PixelDiff::diff16_from_unbiased(r, g, b)
    }

    fn pixel_diff_24(r: i8, g: i8, b: i8, a: i8) -> PixelDiff {
        debug_assert!(DIFF_RANGE_5.contains(&r));
        debug_assert!(DIFF_RANGE_5.contains(&g));
        debug_assert!(DIFF_RANGE_5.contains(&b));
        debug_assert!(DIFF_RANGE_5.contains(&a));
        PixelDiff::diff24_from_unbiased(r, g, b, a)
    }

    #[test]
    fn test_pixel() {
        let px = QoiPixel::new(1, 2, 3, 4);

        assert_eq!(px.r(), 1);
        assert_eq!(px.g(), 2);
        assert_eq!(px.b(), 3);
        assert_eq!(px.a(), 4);

        assert_eq!(px, QoiPixel::from([1, 2, 3, 4]));
    }

    #[test]
    fn test_pixel_add() {
        let px = QoiPixel::new(0, 0, 0, 255);

        assert_eq!(
            px.add(pixel_diff_8(-2, 0, 1)),
            QoiPixel::new(254, 0, 1, 255)
        );

        assert_eq!(
            px.add(pixel_diff_16(-16, -8, 7)),
            QoiPixel::new(240, 248, 7, 255)
        );

        assert_eq!(
            px.add(pixel_diff_24(15, -16, -9, 9)),
            QoiPixel::new(15, 240, 247, 8)
        );
    }

    #[test]
    fn test_pixel_sub() {
        let px = QoiPixel::new(0, 0, 0, 255);

        assert_eq!(px.sub(px), DiffOrColor::Diff(pixel_diff_8(0, 0, 0)));

        assert_eq!(
            px.sub(QoiPixel::new(2, 0, 255, 255)),
            DiffOrColor::Diff(pixel_diff_8(-2, 0, 1))
        );

        assert_eq!(
            px.sub(QoiPixel::new(16, 8, 249, 255)),
            DiffOrColor::Diff(pixel_diff_16(-16, -8, 7))
        );

        assert_eq!(
            px.sub(QoiPixel::new(241, 16, 9, 247)),
            DiffOrColor::Diff(pixel_diff_24(15, -16, -9, 8))
        );

        assert_eq!(
            px.sub(QoiPixel::new(1, 1, 30, 255)),
            DiffOrColor::Color(0b1110)
        );
        assert_eq!(
            px.sub(QoiPixel::new(0, 1, 30, 254)),
            DiffOrColor::Color(0b0111)
        );
        assert_eq!(
            px.sub(QoiPixel::new(1, 1, 30, 254)),
            DiffOrColor::Color(0b1111)
        );

        // If only one component differ, QOI_COLOR is better than QOI_DIFF_24.
        assert_eq!(
            px.sub(QoiPixel::new(0, 9, 0, 255)),
            DiffOrColor::Color(0b0100)
        );
        assert_eq!(
            px.sub(QoiPixel::new(0, 0, 9, 255)),
            DiffOrColor::Color(0b0010)
        );
        assert_eq!(
            px.sub(QoiPixel::new(0, 0, 0, 254)),
            DiffOrColor::Color(0b0001)
        );
    }
}
