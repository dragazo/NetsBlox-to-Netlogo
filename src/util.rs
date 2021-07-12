use std::fmt::{self, Debug, Display};

pub fn indent(code: &str) -> String {
    code.lines().map(|s| format!("    {}", s)).collect::<Vec<_>>().join("\n")
}

pub struct Punctuated<'a, T: Iterator + Clone>(pub T, pub &'a str);
impl<'a, T: Iterator + Clone> Debug for Punctuated<'a, T> where <T as Iterator>::Item: Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut vals = self.0.clone().into_iter();
        if let Some(first) = vals.next() {
            write!(f, "{:?}", first)?;
            for rest in vals {
                write!(f, "{}{:?}", self.1, rest)?;
            }
        }
        Ok(())
    }
}
impl<'a, T: Iterator + Clone> Display for Punctuated<'a, T> where <T as Iterator>::Item: Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut vals = self.0.clone().into_iter();
        if let Some(first) = vals.next() {
            write!(f, "{}", first)?;
            for rest in vals {
                write!(f, "{}{}", self.1, rest)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct RGB(f32, f32, f32);
impl RGB {
    pub fn new(r: f32, g: f32, b: f32) -> Self {
        assert!(r >= 0.0 && r <= 255.0 && g >= 0.0 && g <= 255.0 && b >= 0.0 && b <= 255.0);
        Self(r, g, b)
    }
    #[cfg(test)]
    pub fn to_hex(&self) -> u32 {
        let (r, g, b) = (self.0.round() as u32, self.1.round() as u32, self.2.round() as u32);
        (r << 16) | (g << 8) | b
    }
    pub fn to_inner(&self) -> (f32, f32, f32) {
        (self.0, self.1, self.2)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct HSV(f32, f32, f32);
impl HSV {
    pub fn new(h: f32, s: f32, v: f32) -> Self {
        assert!(h >= 0.0 && h < 360.0 && s >= 0.0 && s <= 1.0 && v >= 0.0 && v <= 1.0);
        Self(h, s, v)
    }
    pub fn to_rgb(&self) -> RGB { // algorithm source: https://www.rapidtables.com/convert/color/hsv-to-rgb.html
        let (h, s, v) = (self.0, self.1, self.2);
        let c = v * s;
        let hp = h / 60.0;
        let x = c * (1.0 - (hp % 2.0 - 1.0).abs());
        let m = v - c;

        let (r, g, b) = [(c, x, 0.0), (x, c, 0.0), (0.0, c, x), (0.0, x, c), (x, 0.0, c), (c, 0.0, x)][hp as usize];
        RGB::new((r + m) * 255.0, (g + m) * 255.0, (b + m) * 255.0)
    }
}

#[test] fn test_hsv_to_rgb() {
    assert_eq!(HSV::new(0.0, 0.07, 0.36).to_rgb().to_hex(), 0x5C5555);
    assert_eq!(HSV::new(25.0, 0.5, 0.25).to_rgb().to_hex(), 0x402D20);
    assert_eq!(HSV::new(49.0, 0.75, 0.12).to_rgb().to_hex(), 0x1F1A08);
    assert_eq!(HSV::new(65.0, 0.12, 0.87).to_rgb().to_hex(), 0xDCDEC3);
    assert_eq!(HSV::new(90.0, 0.22, 0.55).to_rgb().to_hex(), 0x7D8C6D);
    assert_eq!(HSV::new(90.0, 0.22, 0.55).to_rgb().to_hex(), 0x7D8C6D);
    assert_eq!(HSV::new(120.0, 0.26, 0.91).to_rgb().to_hex(), 0xACE8AC);
    assert_eq!(HSV::new(175.0, 0.97, 0.04).to_rgb().to_hex(), 0x000A09);
    assert_eq!(HSV::new(180.0, 1.0, 1.0).to_rgb().to_hex(), 0x00FFFF);
    assert_eq!(HSV::new(211.0, 0.11, 0.59).to_rgb().to_hex(), 0x868E96);
    assert_eq!(HSV::new(299.0, 0.58, 0.91).to_rgb().to_hex(), 0xE661E8);
    assert_eq!(HSV::new(310.0, 0.33, 0.77).to_rgb().to_hex(), 0xC484BA);
}
