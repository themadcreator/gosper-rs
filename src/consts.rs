//! Constants that can produce [`Regular`](terms::Regular) continued fraction
//! terms.
//!
//! # Example
//!
//! ```rust
//! use gosper::{consts, display, ContinuedFraction};
//!
//! let pi = display::Decimal::from(consts::Pi);
//! assert_eq!(format!("{:.10}", pi), "3.1415926535");
//!
//! let exp_2 = display::Decimal::from(consts::Exp(2));
//! assert_eq!(format!("{:.10}", exp_2), "7.3890560989");
//!
//! let e = ContinuedFraction::from(consts::E);
//! assert_eq!(format!("{:.10}", &e * &e), "7.3890560989");
//! ```

use std::iter::{repeat, Repeat};

use num::{BigInt, One};

use crate::{generalized::GeneralizedContinuedFraction, terms};

/// ϕ, the Golden Ratio
///
/// Approximately 1
///
/// The continued fraction terms for Phi are `[1; 1, 1, 1, 1, ...]`, so we
/// simply use a [`std::iter::Repeat`].
///
/// <https://en.wikipedia.org/wiki/Golden_ratio>
///
/// ```rust
/// # use gosper::{consts, ContinuedFraction};
/// let phi = ContinuedFraction::from(consts::Phi);
/// assert_eq!(format!("{:.5}", phi), "1.61803");
/// assert_eq!(format!("{:#.5}", phi), "[1;1,1,1,1,1]");
/// ```
pub struct Phi;

impl From<Phi> for terms::Regular<Repeat<BigInt>> {
    fn from(_: Phi) -> Self {
        terms::Regular(repeat(BigInt::one()))
    }
}

/// π
///
/// Approximately 3
///
/// <https://en.wikipedia.org/wiki/Pi>
///
/// ```rust
/// # use gosper::{consts, ContinuedFraction};
/// let pi = ContinuedFraction::from(consts::Pi);
/// assert_eq!(format!("{:.5}", pi), "3.14159");
/// assert_eq!(format!("{:#.5}", pi), "[3;7,15,1,292,1]");
/// ```
pub struct Pi;

impl GeneralizedContinuedFraction for Pi {
    fn num_i(&self, i: usize) -> BigInt {
        match i {
            0 => BigInt::from(0),
            _ => 2 * BigInt::from(i) - 1,
        }
    }

    fn den_i(&self, i: usize) -> BigInt {
        match i {
            1 => BigInt::from(4),
            _ => {
                let a = BigInt::from(i) - 1;
                &a * &a
            }
        }
    }
}

// Todo, this doesn't seem to converge correctly
//
// /// τ, exactly 2π
// ///
// /// Approximately 6
// ///
// /// Tau can [simplify many
// /// expressions](https://www.theoremoftheday.org/QM-maths/Oxford/Tauvpi/ContFrac.pdf)
// /// and happens to have a compact continued fraction generator.
// ///
// /// ```rust
// /// # use gosper::{consts, ContinuedFraction};
// /// let tau = ContinuedFraction::from(consts::Tau);
// /// assert_eq!(format!("{:.50}", tau), "6.28318");
// /// assert_eq!(format!("{:#.50}", tau), "[6;3,1,1,7,2]");
// /// ```
// pub struct Tau;

// impl GeneralizedContinuedFraction for Tau {
//     fn num_i(&self, i: usize) -> BigInt {
//         match i {
//             0 => BigInt::from(6),
//             _ => BigInt::from(12),
//         }
//     }

//     fn den_i(&self, i: usize) -> BigInt {
//         let a = 4 * BigInt::from(i) - 2;
//         &a * &a
//     }
// }

/// e, Euler's number
///
/// Approximately 2.
///
/// <https://en.wikipedia.org/wiki/E_(mathematical_constant)>
///
/// ```rust
/// # use gosper::{consts, ContinuedFraction};
/// let e = ContinuedFraction::from(consts::E);
/// assert_eq!(format!("{:.5}", e), "2.71828");
/// assert_eq!(format!("{:#.5}", e), "[2;1,2,1,1,4]");
/// ```
pub struct E;

impl GeneralizedContinuedFraction for E {
    fn num_i(&self, i: usize) -> BigInt {
        match i {
            i if i <= 1 => BigInt::from(1),
            _ => 1 + BigInt::from(i),
        }
    }

    fn den_i(&self, i: usize) -> BigInt {
        match i {
            1 => BigInt::from(1),
            _ => 1 - BigInt::from(i),
        }
    }
}

/// exp(x), the exponential function
///
/// Computes the exponential function for the argument `x`
///
/// <https://en.wikipedia.org/wiki/Exponential_function>
///
/// ```rust
/// # use gosper::{consts, ContinuedFraction};
/// let exp = ContinuedFraction::from(consts::Exp(3));
/// assert_eq!(format!("{:.5}", exp), "20.08553");
/// assert_eq!(format!("{:#.5}", exp), "[19;0,1,11,1,2]");
/// ```
pub struct Exp(pub i64);

impl GeneralizedContinuedFraction for Exp {
    fn num_i(&self, i: usize) -> BigInt {
        match i {
            i if i <= 1 => BigInt::from(1),
            _ => BigInt::from(self.0) + BigInt::from(i),
        }
    }

    fn den_i(&self, i: usize) -> BigInt {
        match i {
            1 => BigInt::from(self.0),
            _ => BigInt::from(self.0) * (1 - BigInt::from(i)),
        }
    }
}

#[cfg(test)]
mod tests {

    use num::ToPrimitive;

    use crate::terms;

    #[test]
    fn it_emits_pi() {
        let terms::Regular(pi) = terms::Regular::from(super::Pi);

        // See https://oeis.org/A001203
        assert!(pi.take(82).map(|v| v.to_i32().unwrap()).eq([
            3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, 2, 1, 1, 2, 2, 2, 2, 1, 84, 2, 1, 1, 15, 3,
            13, 1, 4, 2, 6, 6, 99, 1, 2, 2, 6, 3, 5, 1, 1, 6, 8, 1, 7, 1, 2, 3, 7, 1, 2, 1, 1, 12,
            1, 1, 1, 3, 1, 1, 8, 1, 1, 2, 1, 6, 1, 1, 5, 2, 2, 3, 1, 2, 4, 4, 16, 1, 161, 45, 1,
        ]
        .into_iter()))
    }

    #[test]
    fn it_emits_pi_decimal() {
        let terms::Decimal(pi) = terms::Decimal::from(terms::Regular::from(super::Pi));

        // See https://oeis.org/A000796
        assert!(pi.take(116).map(|v| v.to_i32().unwrap()).eq([
            3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2, 6, 4, 3, 3, 8, 3, 2,
            7, 9, 5, 0, 2, 8, 8, 4, 1, 9, 7, 1, 6, 9, 3, 9, 9, 3, 7, 5, 1, 0, 5, 8, 2, 0, 9, 7, 4,
            9, 4, 4, 5, 9, 2, 3, 0, 7, 8, 1, 6, 4, 0, 6, 2, 8, 6, 2, 0, 8, 9, 9, 8, 6, 2, 8, 0, 3,
            4, 8, 2, 5, 3, 4, 2, 1, 1, 7, 0, 6, 7, 9, 8, 2, 1, 4, 8, 0, 8, 6, 5, 1, 3, 2, 8, 2, 3,
        ]
        .into_iter()))
    }

    #[test]
    fn it_emits_phi_decimal() {
        let terms::Decimal(phi) = terms::Decimal::from(terms::Regular::from(super::Phi));

        // See https://oeis.org/A001622
        assert!(phi.take(87).map(|v| v.to_i32().unwrap()).eq([
            1, 6, 1, 8, 0, 3, 3, 9, 8, 8, 7, 4, 9, 8, 9, 4, 8, 4, 8, 2, 0, 4, 5, 8, 6, 8, 3, 4, 3,
            6, 5, 6, 3, 8, 1, 1, 7, 7, 2, 0, 3, 0, 9, 1, 7, 9, 8, 0, 5, 7, 6, 2, 8, 6, 2, 1, 3, 5,
            4, 4, 8, 6, 2, 2, 7, 0, 5, 2, 6, 0, 4, 6, 2, 8, 1, 8, 9, 0, 2, 4, 4, 9, 7, 0, 7, 2, 0,
        ]
        .into_iter()))
    }
}
