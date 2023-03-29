//! Rationals and integers projectively extended to include `Infinity`
//!
//! Allows divide by zero
//!
//! ```text
//! a / 0 = inf
//! ```
//!
//! - [0] <https://en.wikipedia.org/wiki/Stereographic_projection>
//! - [1] <https://en.wikipedia.org/wiki/Projectively_extended_real_line>
//!
//! # Example
//!
//! ```rust
//! use gosper::extended::ExtendedInt;
//! use num::BigInt;
//!
//! let num = BigInt::from(100);
//! let den = BigInt::from(0);
//! let divided = ExtendedInt::divide_ints(&num, &den); // 100 / 0 = inf
//!
//! assert!(matches!(divided, ExtendedInt::Infinity));
//! ```

use num::{BigInt, Signed, Zero};

use crate::rational::Rational;

/// A trait for infinity types
pub trait Infinity {
    type Infinity;
    fn infinity() -> Self::Infinity;
    fn is_infinite(&self) -> bool;
}

/// Projectively extended integers
#[derive(Debug)]
pub enum ExtendedInt {
    Infinity,
    Finite(BigInt),
}

impl ExtendedInt {
    /// Integer division including zero. If the denominator is zero, returns
    /// [`Infinity`](ExtendedInt::Infinity), otherwise returns the integer
    /// division result in a [`Finite`](ExtendedInt::Finite) variant.
    pub fn divide_ints(a: &BigInt, b: &BigInt) -> ExtendedInt {
        if Zero::is_zero(b) {
            ExtendedInt::Infinity
        } else {
            ExtendedInt::Finite(a / b)
        }
    }

    pub fn absolute_difference(&self, other: &ExtendedInt) -> ExtendedInt {
        use ExtendedInt::*;
        match (self, other) {
            (Finite(a), Finite(b)) => Finite((a - b).abs()),
            (Infinity, Infinity) => Finite(BigInt::zero()),
            _ => Infinity,
        }
    }

    pub fn greater_than(&self, other: &ExtendedInt) -> bool {
        use ExtendedInt::*;
        match (self, other) {
            (Finite(a), Finite(b)) => a.gt(b),
            (Infinity, Finite(_)) => true,
            (Finite(_), Infinity) => false,
            (Infinity, Infinity) => false,
        }
    }
}

/// Returns [`Infinity`](ExtendedInt::Infinity) if the option is [`None`]
/// otherwise wraps it in a [`Finite`](ExtendedInt::Finite) variant.
///
/// This has specific meaning in the context of regular continued fractions.
/// The termination of an iterator of terms is equivalent to an infinite
/// term.
impl From<Option<BigInt>> for ExtendedInt {
    fn from(value: Option<BigInt>) -> Self {
        match value {
            Some(f) => ExtendedInt::Finite(f),
            None => ExtendedInt::Infinity,
        }
    }
}

impl Infinity for ExtendedInt {
    type Infinity = ExtendedInt;

    fn infinity() -> ExtendedInt {
        ExtendedInt::Infinity
    }

    fn is_infinite(&self) -> bool {
        matches!(self, ExtendedInt::Infinity)
    }
}

/// Projectively extended rationals
pub enum ExtendedRational {
    Infinity,
    Finite(Rational),
}

impl From<Option<Rational>> for ExtendedRational {
    fn from(value: Option<Rational>) -> Self {
        match value {
            Some(Rational(_, den)) if den.is_zero() => ExtendedRational::Infinity,
            Some(rat) => ExtendedRational::Finite(rat),
            None => ExtendedRational::Infinity,
        }
    }
}

impl Infinity for ExtendedRational {
    type Infinity = ExtendedRational;

    fn infinity() -> ExtendedRational {
        ExtendedRational::Infinity
    }

    fn is_infinite(&self) -> bool {
        matches!(self, ExtendedRational::Infinity)
    }
}
