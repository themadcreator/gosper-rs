//! # Generalized Continued Fractions
//!
//! [Generalized continued fractions](https://en.wikipedia.org/wiki/Generalized_continued_fraction) are real numbers that have the form:
//! ```text
//! x = n0 / d0 + n1 / (d1 + n2 / (d2 + ...))
//! ```
//!
//! Where `n0` is the only singed term and `d0` is always `1` so that it
//! simplifies to an integer.
//!
//! Several interesting numbers have compact definitions as generalized
//! continued fractions, including transcendental numbers like
//! [`Pi`](crate::consts) and [`e`](crate::consts).
//!
//! These numerator/denominator pairs define [`Rational`] terms, which can be
//! converted to [`Regular`](terms::Regular) by a
//! [`homographic::GeneralizedSolver`].
//!
//! A generalized continued fraction whose denominators are all `1` is by
//! definition a regular continued fraction.
//!
//! Currently only non-terminating generalized continued fraction are supported.
//! See [`GeneralizedContinuedFraction`].
//!
//! # Caveats
//!
//! Technically generalized continued fractions may have signed terms other than
//! `n0`, but this may lead to undefined behavior.

use crate::{homographic, rational::Rational, terms};
use num::{BigInt, One};

/// Trait for defining non-terminating generalized continued fraction
pub trait GeneralizedContinuedFraction {
    fn num_i(&self, i: usize) -> BigInt;
    fn den_i(&self, i: usize) -> BigInt;
}

/// Wrapper for iterating over generalized continued fraction terms
pub struct RationalIter<T>(usize, T);

/// Type alias for homographic solver from generalized to regular continued
/// fractions
pub type GeneralizedSolver<T> = terms::Regular<homographic::GeneralizedSolver<RationalIter<T>>>;

impl<F> Iterator for RationalIter<F>
where
    F: GeneralizedContinuedFraction,
{
    type Item = Rational;

    fn next(&mut self) -> Option<Self::Item> {
        let num = self.1.num_i(self.0);
        let den = match self.0 {
            0 => BigInt::one(),
            _ => self.1.den_i(self.0),
        };
        self.0 += 1;
        Some(Rational(num, den))
    }
}

impl<T> From<T> for GeneralizedSolver<T>
where
    T: GeneralizedContinuedFraction,
{
    fn from(g: T) -> Self {
        GeneralizedSolver::from(terms::Rational(RationalIter(0, g)))
    }
}
