//! [`Display`] implementations
//!
//! # Example
//!
//! ```rust
//! # use gosper::*;
//! use gosper::display;
//!
//! let regular = display::CompactRegularContinuedFraction::from(consts::Pi);
//! assert_eq!(format!("{:.2}", regular), "[3;7,15]");
//!
//! let decimal = display::Decimal::from(consts::Pi);
//! assert_eq!(format!("{:.2}", decimal), "3.14");
//! ```

use std::{
    cell::RefCell,
    fmt::{Display, Formatter, Result},
    iter::Peekable,
};

use num::{BigInt, Zero};

use crate::{homographic, terms};

/// Default number of terms displayed from an iterator
pub const DEFAULT_PRECISION: usize = 100;

/// An impl of [`Display`] for the decimal representation of a continued
/// fraction.
///
/// The first item from the iterator may be an arbitrary [`BigInt`], but
/// subsequent items will be single positive digits 0 through 9
///
/// The second item will be "." followed by one or more digits.
///
/// This display DOES NOT ROUND the final digit.
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// use gosper::display;
///
/// let display = display::Decimal::from(consts::Pi);
///
/// assert_eq!(
///     format!("{:.100}", display),
///     [
///         "3.1415926535897932384626433832795028841971693993751",
///         "058209749445923078164062862089986280348253421170679",
///     ].join(""),
/// );
/// ```
pub struct Decimal<I: Iterator>(RefCell<homographic::DecimalSolver<I>>);

impl<I, J> From<I> for Decimal<J>
where
    J: Iterator<Item = BigInt>,
    terms::Regular<J>: From<I>,
{
    fn from(value: I) -> Self {
        let terms::Decimal(iter) = terms::Decimal::from(terms::Regular::from(value));
        Self(RefCell::new(iter))
    }
}

impl<I> Display for Decimal<I>
where
    I: Iterator<Item = BigInt>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let decimal_precision = f.precision().unwrap_or(DEFAULT_PRECISION).max(1) + 2;

        let ref mut iter = *self.0.borrow_mut();
        let mut index = 0;
        loop {
            match index {
                0 => f.write_str(&iter.next().unwrap_or_else(|| Zero::zero()).to_string())?,
                1 => f.write_str(".")?,
                2 => f.write_str(&iter.next().unwrap_or_else(|| Zero::zero()).to_string())?,
                _ if index >= decimal_precision => break,
                _ => match iter.next() {
                    Some(i) => f.write_str(&i.to_string())?,
                    None => break,
                },
            }
            index += 1;
        }
        Ok(())
    }
}

/// An impl of [`Display`] that displays the terms of a regular continued
/// fraction in a list-like format
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// use gosper::display;
///
/// let display = display::CompactRegularContinuedFraction::from(consts::Pi);
/// assert_eq!(format!("{:.4}", display), "[3;7,15,1,292]");
/// ```
pub struct CompactRegularContinuedFraction<I: Iterator>(RefCell<Peekable<I>>);

impl<I, J> From<I> for CompactRegularContinuedFraction<J>
where
    J: Iterator<Item = BigInt>,
    terms::Regular<J>: From<I>,
{
    fn from(value: I) -> Self {
        let terms::Regular(iter) = terms::Regular::from(value);
        Self(RefCell::new(iter.peekable()))
    }
}

impl<I> Display for CompactRegularContinuedFraction<I>
where
    I: Iterator,
    I::Item: ToString + Zero,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let precision = f.precision().unwrap_or(DEFAULT_PRECISION).max(1) + 1;

        let ref mut iter = *self.0.borrow_mut();
        let mut index = 0;

        f.write_str("[")?;
        loop {
            match index {
                0 => f.write_str(&iter.next().unwrap_or_else(|| Zero::zero()).to_string())?,
                _ if index >= precision => break,
                _ if iter.peek().is_none() => break,
                1 => {
                    f.write_str(";")?;
                    f.write_str(&iter.next().unwrap().to_string())?;
                }
                _ => {
                    f.write_str(",")?;
                    f.write_str(&iter.next().unwrap().to_string())?;
                }
            }
            index += 1;
        }
        f.write_str("]")?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use num::BigInt;

    use super::*;

    #[test]
    fn it_emits_zero_decimal() {
        let display = Decimal::from(terms::Regular([].into_iter()));
        assert_eq!(format!("{}", display), "0.0");
    }

    #[test]
    fn it_emits_unit_decimal() {
        let display = Decimal::from(terms::Regular([BigInt::from(8)].into_iter()));
        assert_eq!(format!("{}", display), "8.0");
    }

    #[test]
    fn it_emits_fraction_decimal() {
        let display = Decimal::from(terms::Regular(
            [BigInt::from(0), BigInt::from(2)].into_iter(),
        ));
        assert_eq!(format!("{}", display), "0.5");
    }

    #[test]
    fn it_emits_zero_continued_fraction() {
        let display = CompactRegularContinuedFraction::from(terms::Regular([].into_iter()));
        assert_eq!(format!("{:.0}", display), "[0]");
    }

    #[test]
    fn it_emits_unit_continued_fraction() {
        let display =
            CompactRegularContinuedFraction::from(terms::Regular([BigInt::from(8)].into_iter()));
        assert_eq!(format!("{}", display), "[8]");
    }

    #[test]
    fn it_emits_fraction_continued_fraction() {
        let display = CompactRegularContinuedFraction::from(terms::Regular(
            [BigInt::from(0), BigInt::from(2)].into_iter(),
        ));
        assert_eq!(format!("{:.1}", display), "[0;2]");
    }
}
