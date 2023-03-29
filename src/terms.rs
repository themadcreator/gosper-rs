//! Wrapper newtypes for marking continued fraction terms
//!
//! # Example
//!
//! ```rust
//! use gosper::{ContinuedFraction, terms};
//!
//! let regular = terms::Regular::from([1, 2, 3]);
//! let cf = ContinuedFraction::new(regular);
//!
//! assert_eq!(format!("{:#}", cf), "[1;2,3]");
//! ```
use num::BigInt;

use crate::{float, homographic, iter, rational, ContinuedFraction};

/// Wrapper newtype for an iterator of regular continued fraction terms
pub struct Regular<I: Iterator<Item = BigInt>>(pub I);

/// Wrapper newtype for an iterator of generalized continued fraction terms
pub struct Rational<I: Iterator<Item = rational::Rational>>(pub I);

/// Wrapper newtype for an iterator of decimal terms
pub struct Decimal<I: Iterator<Item = BigInt>>(pub I);

pub enum RegularT {}

/// Convert a continued fraction reference to regular terms
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// let a = ContinuedFraction::from(consts::Pi);
///
/// // The turbofish below is necessary to disambiguate the `From` implementation.
/// let regular = terms::Regular::<iter::MemoIter<_>>::from(&a);
/// let b = ContinuedFraction::from(regular);
///
/// // Unless you actually need `terms::Regular`, in practice it's cleaner to `Clone`.
/// let c = a.clone();
///
/// assert_eq!(format!("{:.2} {:.2} {:.2}", &a, &b, &c), "3.14 3.14 3.14");
/// ```
impl<I> From<&ContinuedFraction<I>> for Regular<iter::MemoIter<I>>
where
    I: Iterator<Item = BigInt>,
{
    fn from(value: &ContinuedFraction<I>) -> Self {
        Self(value.iter())
    }
}

/// Convert from iterables of integers
///
/// This implementation is most generic for regular continued fractions. It
/// supports anything that can turn into an [`Iterator`] of any type of item
/// that can be turned into a [`BigInt`].
///
/// # Example
///
/// ```rust
/// # use gosper::*;
///
/// ContinuedFraction::from(vec![1, 2, 3, 4].into_iter());
/// ```
impl<I> From<I> for Regular<iter::ToBigInts<I::IntoIter>>
where
    I: IntoIterator,
    BigInt: From<I::Item>,
{
    fn from(value: I) -> Self {
        Self(iter::ToBigInts(value.into_iter()))
    }
}

/// Convert an integer
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// let cf = ContinuedFraction::from(1_000);
/// assert_eq!(cf.to_f64(), 1000.0);
/// ```
impl<I> From<I> for Regular<iter::Once<BigInt>>
where
    BigInt: From<I>,
{
    fn from(value: I) -> Self {
        Self(iter::Once::from(BigInt::from(value)))
    }
}

/// Convert a rational `num / den` from the tuple of `(num, den)` integers
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// let cf = ContinuedFraction::from((22, 7));
/// assert_eq!(cf.to_f64(), 3.1428571428571423);
/// ```
impl<R> From<R> for Regular<rational::Solver>
where
    rational::Solver: From<R>,
{
    fn from(value: R) -> Self {
        Self(rational::Solver::from(value))
    }
}

/// Lossily convert a 64-bit float using the lentz algorithm
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// let cf = ContinuedFraction::from(3.14);
/// assert_eq!(cf.to_f64(), 3.1399999999999992);
/// ```
impl<T> From<T> for Regular<float::Solver>
where
    float::Solver: From<T>,
{
    fn from(value: T) -> Self {
        Self(float::Solver::from(value))
    }
}

impl<I> From<Rational<I>> for Regular<homographic::GeneralizedSolver<I>>
where
    I: Iterator<Item = rational::Rational>,
{
    fn from(value: Rational<I>) -> Self {
        let Rational(iter) = value;
        Self(homographic::Solver::identity(
            homographic::input::Generalized(iter.peekable()),
            homographic::output::Regular {},
        ))
    }
}

// impl<I, J> From<I> for Decimal<J>
// where
//     J: Iterator<Item = BigInt>,
//     terms::Regular<J>: From<I>,
// {

impl<I, J> From<I> for Decimal<homographic::DecimalSolver<J>>
where
    J: Iterator<Item = BigInt>,
    Regular<J>: From<I>,
{
    fn from(value: I) -> Self {
        let Regular(iter) = Regular::from(value);
        Self(homographic::Solver::identity(
            homographic::input::Regular(iter.peekable()),
            homographic::output::Decimal {},
        ))
    }
}
