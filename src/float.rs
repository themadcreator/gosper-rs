//! Lossy floating point conversion to/from continued fractions.
//!
//! This method is lossy because the modified Lentz algorithm[^1] uses constant
//! thresholds to terminate computation.
//!
//! # Example
//!
//! ```rust
//! # use gosper::*;
//! use num::ToPrimitive;
//! use gosper::float::{Solver, Float};
//!
//! let lentz = Solver::from(1.21);
//!
//! let c = ContinuedFraction::new(terms::Regular(lentz));
//! assert_eq!(format!("{}", c), "1.21");
//! assert_eq!(format!("{:#}", c), "[1;4,1,3,4,1]");
//!
//! let Float(f) = Float::from(&mut c.iter().map(|i| i.to_i32().unwrap()));
//! assert_eq!(f, 1.2100000000000002);
//! ```
//!
//! [^1]: §5.2. Press, W. H., Teukolsky, S. A., Vetterling, W. T.,, Flannery, B.
//!     P. (2007). Numerical Recipes 3rd Edition: The Art of Scientific
//!     Computing. Cambridge University Press. ISBN: 0521880688
use num::{BigInt, FromPrimitive};

/// Floating point newtype
pub struct Float(pub f64);

/// Evaluate or create a regular continued fraction using the modified lentz
pub struct Solver {
    val: f64,
    index: u32,
    lentz: Lentz,
}

impl Solver {
    pub fn new(val: f64) -> Solver {
        Solver {
            val,
            index: 0,
            lentz: Lentz::new(),
        }
    }
}

impl Iterator for Solver {
    type Item = BigInt;

    // Numerical Recipes §5.2
    fn next(&mut self) -> Option<Self::Item> {
        if self.lentz.done {
            return None;
        }

        if self.val == 0.0 {
            self.lentz.done = true;
            None
        } else if self.index == 0 {
            // swap sign for first convergent only
            let sign = if self.val >= 0.0 { 1.0 } else { -1.0 };
            self.val *= sign;

            // extract integer part
            let b = self.val.floor();
            self.val -= b;

            self.lentz.first(b);
            self.index += 1;

            if self.lentz.done {
                return None;
            }
            return Some(BigInt::from_f64(sign * b).unwrap());
        } else {
            self.val = 1.0 / self.val;

            let b = self.val.floor();
            self.val -= b;
            self.lentz.next(b);

            // not certain about this
            if self.lentz.done {
                return None;
            }
            return Some(BigInt::from_f64(b).unwrap());
        }
    }
}

/// Algorithm state for the lentz method
pub struct Lentz {
    d: f64,
    c: f64,
    f: f64,
    done: bool,
}

impl Lentz {
    // Numerical Recipes §5.2
    const EPS: f64 = 1e-15;
    const TINY: f64 = 1e-30;

    fn new() -> Lentz {
        Lentz {
            d: 0.0,
            c: 0.0,
            f: 0.0,
            done: false,
        }
    }

    fn first(&mut self, b: f64) -> f64 {
        self.f = b;

        if self.f == 0.0 {
            self.f = Self::TINY;
        }
        self.c = self.f;
        self.d = 0.0;

        b
    }

    fn next(&mut self, b: f64) -> f64 {
        self.d += b;
        if self.d == 0.0 {
            self.d = Self::TINY;
        }
        self.c = b + 1.0 / self.c;
        if self.c == 0.0 {
            self.c = Self::TINY;
        }
        self.d = 1.0 / self.d;

        let delta = self.c * self.d;
        self.done = (delta - 1.0).abs() < Self::EPS;

        self.f *= delta;
        self.f
    }
}

impl From<f64> for Float {
    fn from(value: f64) -> Self {
        Self(value)
    }
}

impl<F> From<F> for Solver
where
    Float: From<F>,
{
    fn from(value: F) -> Self {
        let Float(f) = value.into();
        Solver::new(f)
    }
}

impl<'a, I> From<&'a mut I> for Float
where
    I: Iterator,
    f64: From<I::Item>,
{
    fn from(terms: &mut I) -> Self {
        let mut term: Option<I::Item> = terms.next();
        if let Some(t) = term {
            let mut lentz = Lentz::new();
            let mut f = lentz.first(f64::from(t));

            term = terms.next();
            while let Some(t) = term {
                if lentz.done {
                    break;
                }
                f = lentz.next(f64::from(t));
                term = terms.next();
            }
            Float(f)
        } else {
            Float(0.0)
        }
    }
}

#[cfg(test)]
mod tests {
    use num::ToPrimitive;
    use std::f64::consts;

    use super::{Float, Solver};

    fn from_f64_i32(f: f64) -> impl Iterator<Item = i32> {
        Solver::from(f).map(|i| i.to_i32().unwrap())
    }

    #[test]
    fn it_converts_from_floats() {
        let c = from_f64_i32(0.5);
        assert!(c.eq([0, 2]));
    }

    #[test]
    fn it_converts_into_floats() {
        let Float(f) = Float::from(&mut [0, 2].into_iter());
        assert_eq!(f, 0.5);
    }

    #[test]
    fn it_converts_negatives() {
        let c = from_f64_i32(-consts::PI);
        assert!(c.take(5).eq([-3, 7, 15, 1, 292]));
    }

    #[test]
    fn it_converts_zero() {
        let c = from_f64_i32(0.0);
        assert!(c.eq([]));
    }

    #[test]
    fn it_partially_converts_from_pi() {
        let c = from_f64_i32(consts::PI);
        assert!(c.take(13).eq([
            3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1,
            14, // partial convergents of pi. See https://oeis.org/A001203
        ]));
    }

    #[test]
    fn it_partially_converts_from_sqrt_2() {
        let c = from_f64_i32(consts::SQRT_2);
        assert!(c.take(14).eq([
            1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // partial convergents of sqrt(2)
        ]));
    }

    #[test]
    fn it_partially_converts_from_ln_2() {
        let c = from_f64_i32(consts::LN_2);
        assert!(c.take(10).eq([
            0, 1, 2, 3, 1, 6, 3, 1, 1,
            2, // partial convergents of ln(2). See https://oeis.org/A016730
        ]));
    }
}
