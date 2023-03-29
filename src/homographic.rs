//! Iterative homographic function solver
//!
//! # Background
//!
//! A homographic function takes the following form:
//!
//! ```text
//!         a * x + b
//!  f(x) = ---------
//!         c * x + d
//! ```
//!
//! In general, we wish to compute the output `f(x)`, given the input `x`, so we
//! initialize the function like:
//!
//! ```text
//!         x
//!  f(x) = -
//!         1
//! ```
//!
//! So, `a = 1, d = 1` and all other coefficients `_ = 0`.
//!
//! The key property of this type of function is that it can be evaluated
//! iteratively on the input `x` and output `f(x)`.
//!
//! The [`Solver`] will attempt to factor a well-defined output term from its
//! [`State`]. If it can do so, it will compute a new [`State`] with the output
//! value factored out. Until such an output term can be determined, the
//! [`Solver`] will evaluate `x` input terms into the [`State`].
use crate::extended::{ExtendedInt, Infinity};
use num::{BigInt, FromPrimitive, One, Zero};
use std::iter::Peekable;

/// The state of a homographic function
pub struct State {
    a: BigInt,
    b: BigInt,
    c: BigInt,
    d: BigInt,
}

pub mod input {
    use super::State;
    use crate::{
        extended::{ExtendedInt, ExtendedRational, Infinity},
        rational::Rational,
    };
    use num::BigInt;
    use std::iter::Peekable;

    /// Performs "input" operations on the homographic function state
    pub trait Input {
        type Domain: Infinity;
        fn peek_domain(&mut self) -> Self::Domain;
        fn update_state(&mut self, state: &State) -> State;
    }

    /// Inputs regular continued fraction terms
    pub struct Regular<I>(pub I);
    impl<I> Input for Regular<Peekable<I>>
    where
        I: Iterator<Item = BigInt>,
    {
        type Domain = ExtendedInt;

        fn peek_domain(&mut self) -> Self::Domain {
            ExtendedInt::from(self.0.peek().cloned())
        }

        fn update_state(&mut self, state: &State) -> State {
            let State { a, b, c, d } = state;
            match &ExtendedInt::from(self.0.next()) {
                ExtendedInt::Infinity => State {
                    a: a.clone(),
                    b: a.clone(),
                    c: c.clone(),
                    d: c.clone(),
                },
                ExtendedInt::Finite(p) => State {
                    a: b + a * p,
                    b: a.clone(),
                    c: d + c * p,
                    d: c.clone(),
                },
            }
        }
    }

    /// Inputs generalized continued fraction terms
    ///
    /// See [`crate::generalized`]
    pub struct Generalized<I>(pub I);
    impl<I> Input for Generalized<Peekable<I>>
    where
        I: Iterator<Item = Rational>,
    {
        type Domain = ExtendedRational;

        fn peek_domain(&mut self) -> Self::Domain {
            ExtendedRational::from(self.0.peek().cloned())
        }

        fn update_state(&mut self, state: &State) -> State {
            let State { a, b, c, d } = state;
            match &ExtendedRational::from(self.0.next()) {
                ExtendedRational::Finite(Rational(num, den)) => State {
                    a: a * num + b * den,
                    b: a.clone(),
                    c: c * num + d * den,
                    d: c.clone(),
                },
                _ => unimplemented!("Only infinite general continued fractions are supported"),
            }
        }
    }
}

pub mod output {
    use num::{BigInt, Zero};

    use crate::extended::Infinity;

    use super::State;

    /// Performs "output" operations on the homographic function state
    pub trait Output {
        type Range;
        type Term;

        fn is_done<D: Infinity>(&self, state: &State, domain: &D) -> bool;
        fn well_defined_range<D: Infinity>(&self, state: &State, domain: &D)
            -> Option<Self::Range>;
        fn update_state(&self, state: &State, range: &Self::Range) -> State;
        fn emit(&self, range: &Self::Range) -> Self::Term;
    }

    /// Outputs regular continued fraction terms
    pub struct Regular;
    impl Output for Regular {
        type Range = BigInt;
        type Term = BigInt;

        fn is_done<D: Infinity>(&self, state: &State, domain: &D) -> bool {
            if domain.is_infinite() {
                state.c.is_zero()
            } else {
                state.c.is_zero() && state.d.is_zero()
            }
        }

        fn well_defined_range<D: Infinity>(
            &self,
            state: &State,
            domain: &D,
        ) -> Option<Self::Range> {
            state.factor_integer(domain)
        }

        fn update_state(&self, state: &State, r: &Self::Range) -> State {
            let State { a, b, c, d } = state;
            State {
                a: c.clone(),
                b: d.clone(),
                c: a - c * r,
                d: b - d * r,
            }
        }

        fn emit(&self, r: &Self::Range) -> Self::Term {
            r.clone()
        }
    }

    /// Outputs decimal digits
    pub struct Decimal;
    impl Output for Decimal {
        type Range = BigInt;
        type Term = BigInt;

        fn is_done<D: Infinity>(&self, state: &State, domain: &D) -> bool {
            if domain.is_infinite() {
                state.a.is_zero() // not sure if this is correct
            } else {
                state.a.is_zero() && state.b.is_zero()
            }
        }

        fn well_defined_range<D: Infinity>(
            &self,
            state: &State,
            domain: &D,
        ) -> Option<Self::Range> {
            state.factor_integer(domain)
        }

        fn update_state(&self, state: &State, r: &Self::Range) -> State {
            let State { a, b, c, d } = state;
            State {
                a: (a - c * r) * BigInt::from(10),
                b: (b - d * r) * BigInt::from(10),
                c: c.clone(),
                d: d.clone(),
            }
        }

        fn emit(&self, r: &Self::Range) -> Self::Term {
            r.clone()
        }
    }
}

impl State {
    pub fn identity() -> State {
        State {
            a: BigInt::one(),
            b: BigInt::zero(),
            c: BigInt::zero(),
            d: BigInt::one(),
        }
    }

    pub fn from_i8(a: i8, b: i8, c: i8, d: i8) -> State {
        State {
            a: BigInt::from_i8(a).unwrap(),
            b: BigInt::from_i8(b).unwrap(),
            c: BigInt::from_i8(c).unwrap(),
            d: BigInt::from_i8(d).unwrap(),
        }
    }

    pub fn factor_integer<D: Infinity>(&self, domain: &D) -> Option<BigInt> {
        let State { a, b, c, d } = self;

        if domain.is_infinite() {
            let ac = ExtendedInt::divide_ints(a, c);
            match ac {
                ExtendedInt::Finite(x) => Some(x),
                _ => None,
            }
        } else {
            let ac = ExtendedInt::divide_ints(a, c);
            if matches!(ac, ExtendedInt::Infinity) {
                return None;
            }

            let bd = ExtendedInt::divide_ints(b, d);
            if matches!(bd, ExtendedInt::Infinity) {
                return None;
            }

            match (ac, bd) {
                (ExtendedInt::Finite(x), ExtendedInt::Finite(y)) if x.eq(&y) => Some(x),
                _ => None,
            }
        }
    }
}

/// Homographic function solver
pub struct Solver<I, O> {
    state: State,
    input: I,
    output: O,
}

impl<I, O> Solver<I, O>
where
    I: input::Input,
    O: output::Output,
{
    pub fn identity(input: I, output: O) -> Self {
        Self {
            state: State::identity(),
            input,
            output,
        }
    }
}

impl<I, O> Iterator for Solver<I, O>
where
    I: input::Input,
    O: output::Output,
{
    type Item = O::Term;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let domain = self.input.peek_domain();
            if self.output.is_done(&self.state, &domain) {
                return None;
            }

            let range = self.output.well_defined_range(&self.state, &domain);
            if let Some(r) = range {
                self.state = self.output.update_state(&self.state, &r);
                return Some(self.output.emit(&r));
            } else if !domain.is_infinite() {
                self.state = self.input.update_state(&self.state);
            } else {
                // special case where domain in infinite but no well defined range is available
                // this can occur for 0, for example.
                return None;
            }
        }
    }
}

/// Type alias for `regular continued fraction` → `decimal digits`
pub type DecimalSolver<I> = Solver<input::Regular<Peekable<I>>, output::Decimal>;

/// Type alias for `generalized continued fraction` → `regular continued
/// fraction`
pub type GeneralizedSolver<I> = Solver<input::Generalized<Peekable<I>>, output::Regular>;

#[cfg(test)]
mod tests {
    use crate::{consts, terms};
    use num::ToPrimitive;

    #[test]
    fn it_emits_phi_as_decimal() {
        let terms::Decimal(iter) = terms::Decimal::from(terms::Regular::from(consts::Phi));
        assert!(iter
            .take(10)
            .map(|i| i.to_i32().unwrap())
            .eq([1, 6, 1, 8, 0, 3, 3, 9, 8, 8]));
    }

    #[test]
    fn it_emits_pi_as_decimal() {
        let terms::Decimal(iter) = terms::Decimal::from(terms::Regular::from(consts::Pi));
        assert!(iter
            .take(11)
            .map(|i| i.to_i32().unwrap())
            .eq([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]));
    }

    #[test]
    fn it_emits_pi_as_regular_continued_fraction() {
        let terms::Regular(iter) = terms::Regular::from(consts::Pi);
        assert!(iter
            .take(13)
            .map(|i| i.to_i32().unwrap())
            .eq([3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14]));
    }
}
