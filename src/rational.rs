//! Arbitrary precision rational numbers
//!
//! A [`Solver`] will emit terms of the equivalent canonical regular continued
//! fraction using the euclidean convergent algorithm[^1].
//!
//! # Example
//!
//! ```rust
//! # use num::{BigInt, ToPrimitive};
//! # use gosper::*;
//! use gosper::rational::{Rational, Solver};
//!
//! let solver = Solver::from((355, 113));
//!
//! let c = ContinuedFraction::new(terms::Regular(solver));
//! assert_eq!(format!("{}", c.display_regular()), "[3;7,16]");
//!
//! let Rational(num, den) = Rational::from(&mut c.iter());
//! assert_eq!(num, BigInt::from(355));
//! assert_eq!(den, BigInt::from(113));
//! ```
//!
//! [^1]: Algorithm 9.3.2. Kornerup, P., & Matula, D.W. (2010). Finite Precision
//!       Number Systems and Arithmetic.

use num::{bigint::Sign, BigInt, One, Zero};

use crate::extended::ExtendedInt;

/// An arbitrary precision rational value
#[derive(Clone)]
pub struct Rational(pub BigInt, pub BigInt);

impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(num, den) = self;
        f.write_fmt(format_args!("({}/{})", num, den))
    }
}

/// Euclidean convergent algorithm state
pub struct State {
    b_2: BigInt,
    p_2: BigInt,
    q_2: BigInt,
    b_1: BigInt,
    p_1: BigInt,
    q_1: BigInt,
}

impl State {
    pub fn rational(num: BigInt, den: BigInt) -> Self {
        Self {
            b_2: num,
            p_2: BigInt::zero(),
            q_2: BigInt::one(),
            b_1: den,
            p_1: BigInt::one(),
            q_1: BigInt::zero(),
        }
    }
}

/// Implements the euclidean convergent algorithm
pub struct Solver {
    state: State,
}

impl Iterator for Solver {
    type Item = BigInt;

    fn next(&mut self) -> Option<Self::Item> {
        let State {
            b_2,
            p_2,
            q_2,
            b_1,
            p_1,
            q_1,
        } = &self.state;

        // handle negative rationals
        let negative = matches!(
            (b_2.sign(), b_1.sign()),
            (Sign::Plus, Sign::Minus) | (Sign::Minus, Sign::Plus)
        );

        match ExtendedInt::divide_ints(b_2, b_1) {
            ExtendedInt::Infinity => None,
            ExtendedInt::Finite(quot) => {
                let a = match negative {
                    true => quot - 1,
                    false => quot,
                };

                let b = b_2 - &a * b_1;
                let p = &a * p_1 + p_2;
                let q = &a * q_1 + q_2;

                self.state = State {
                    b_2: b_1.clone(),
                    p_2: p_1.clone(),
                    q_2: q_1.clone(),
                    b_1: b,
                    p_1: p,
                    q_1: q,
                };

                Some(a)
            }
        }
    }
}

impl<R> From<R> for Solver
where
    Rational: From<R>,
{
    fn from(value: R) -> Self {
        let Rational(num, den) = value.into();
        Self {
            state: State::rational(num, den),
        }
    }
}

impl<N, D> From<(N, D)> for Rational
where
    BigInt: From<N>,
    BigInt: From<D>,
{
    fn from((num, den): (N, D)) -> Self {
        Rational(num.into(), den.into())
    }
}

impl<'a, I> From<&'a mut I> for Rational
where
    I: Iterator<Item = BigInt>,
{
    fn from(value: &mut I) -> Self {
        let mut state = (BigInt::one(), BigInt::zero(), BigInt::zero(), BigInt::one());
        for a in value.by_ref() {
            let (h_1, h_2, k_1, k_2) = state;
            let h = &a * &h_1 + h_2;
            let k = &a * &k_1 + k_2;
            state = (h, h_1, k, k_1);
        }
        Rational(state.0, state.2)
    }
}

#[cfg(test)]
mod tests {
    use num::ToPrimitive;

    use super::*;

    #[test]
    fn it_emits_continued_fraction_for_rational() {
        let solver = Solver::from((277, 642));
        assert!(solver
            .into_iter()
            .map(|i| i.to_i32().unwrap())
            .eq([0, 2, 3, 6, 1, 3, 3]));
    }

    #[test]
    fn it_handles_negative_rationals() {
        let solver1 = Solver::from((-277, 642));
        assert!(solver1
            .into_iter()
            .map(|i| i.to_i32().unwrap())
            .eq([-1, 1, 1, 3, 6, 1, 3, 3]));

        let solver2 = Solver::from((277, -642));
        assert!(solver2
            .into_iter()
            .map(|i| i.to_i32().unwrap())
            .eq([-1, 1, 1, 3, 6, 1, 3, 3]));
    }

    #[test]
    fn it_round_trips_rationals() {
        let mut terms = Solver::from((277, 642));
        let Rational(num, den) = Rational::from(&mut terms);
        assert_eq!(num.to_i32().unwrap(), 277);
        assert_eq!(den.to_i32().unwrap(), 642);
    }
}
