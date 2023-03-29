//! Iterative bihomographic function solver
//!
//! # Background
//!
//! A bihomographic function takes the following form:
//!
//! ```text
//!            a + b * x + c * y + d * x * y
//!  f(x, y) = -----------------------------
//!            e + f * x + g * y + h * x * y
//! ```
//!
//! With proper initialization of coefficients of the above function, the solver
//! can compute arithmetic operations (+, -, *, /) for arbitrary regular
//! continued fraction arguments `x` and `y`.
//!
//! For example, to compute `x * y`, we initialize the function like:
//!
//! ```text
//!            x * y
//!  f(x, y) = -----
//!              1
//! ```
//!
//! So, `d = 1, e = 1` and all other coefficients `_ = 0`.
//!
//! The [`Solver`] will output [`BigInt`] terms of the resulting regular
//! continued fraction when the term is well defined. Until the next term can be
//! determined, the solver will read in more terms from the `x` or `y` input.

use num::BigInt;

use crate::{extended::ExtendedInt, terms};

/// Bihomographic function state
pub struct State {
    a: BigInt,
    b: BigInt,
    c: BigInt,
    d: BigInt,
    e: BigInt,
    f: BigInt,
    g: BigInt,
    h: BigInt,
}

impl State {
    // Returns an integer r iff the r can be factored out of the bihomographic
    // function while maintaining integer coefficients in the function.
    //
    // This value can now be emitted as a convergent of the regular continued
    // fraction that the function is trying to compute.
    //
    // If no integer can be cleanly factored out of the function, we return no
    // value.
    pub fn factor_integer(&self) -> Option<BigInt> {
        let State {
            a,
            b,
            c,
            d,
            e,
            f,
            g,
            h,
        } = self;

        let ae = ExtendedInt::divide_ints(a, e);
        if matches!(ae, ExtendedInt::Infinity) {
            return None;
        }

        let bf = ExtendedInt::divide_ints(b, f);
        if matches!(bf, ExtendedInt::Infinity) {
            return None;
        }

        let cg = ExtendedInt::divide_ints(c, g);
        if matches!(cg, ExtendedInt::Infinity) {
            return None;
        }

        let dh = ExtendedInt::divide_ints(d, h);
        if matches!(dh, ExtendedInt::Infinity) {
            return None;
        }

        match (ae, bf, cg, dh) {
            (
                ExtendedInt::Finite(f0),
                ExtendedInt::Finite(f1),
                ExtendedInt::Finite(f2),
                ExtendedInt::Finite(f3),
            ) if f0.eq(&f1) && f1.eq(&f2) && f2.eq(&f3) => Some(f0),
            _ => None,
        }
    }
}

pub mod input {
    use super::State;
    use crate::extended::ExtendedInt;
    use num::BigInt;

    pub enum InputArg {
        X,
        Y,
    }

    pub trait Input {
        fn preferred_arg(&self, state: &State) -> InputArg;
        fn update_state_x(&mut self, state: &State) -> State;
        fn update_state_y(&mut self, state: &State) -> State;
    }

    pub struct Regular<X, Y> {
        pub(super) x: X,
        pub(super) y: Y,
    }

    impl<X, Y> Input for Regular<X, Y>
    where
        X: Iterator<Item = BigInt>,
        Y: Iterator<Item = BigInt>,
    {
        // Heuristically determines if it is preferable to input a convergent from x or
        // y.
        fn preferred_arg(&self, state: &State) -> InputArg {
            let State {
                a, b, c, e, f, g, ..
            } = state;

            let ae = ExtendedInt::divide_ints(a, e);
            let bf = ExtendedInt::divide_ints(b, f);
            let cg = ExtendedInt::divide_ints(c, g);
            let d0 = bf.absolute_difference(&ae);
            let d1 = cg.absolute_difference(&ae);
            match d0.greater_than(&d1) {
                true => InputArg::X,
                false => InputArg::Y,
            }
        }

        fn update_state_x(&mut self, state: &State) -> State {
            let State {
                a,
                b,
                c,
                d,
                e,
                f,
                g,
                h,
            } = state;

            match &self.x.next() {
                None => State {
                    a: b.clone(),
                    b: b.clone(),
                    c: d.clone(),
                    d: d.clone(),
                    e: f.clone(),
                    f: f.clone(),
                    g: h.clone(),
                    h: h.clone(),
                },
                Some(p) => State {
                    a: b.clone(),
                    b: a + b * p,
                    c: d.clone(),
                    d: c + d * p,
                    e: f.clone(),
                    f: e + f * p,
                    g: h.clone(),
                    h: g + h * p,
                },
            }
        }

        fn update_state_y(&mut self, state: &State) -> State {
            let State {
                a,
                b,
                c,
                d,
                e,
                f,
                g,
                h,
            } = state;

            match &self.y.next() {
                None => State {
                    a: c.clone(),
                    b: d.clone(),
                    c: c.clone(),
                    d: d.clone(),
                    e: g.clone(),
                    f: h.clone(),
                    g: g.clone(),
                    h: h.clone(),
                },
                Some(q) => State {
                    a: c.clone(),
                    b: d.clone(),
                    c: a + c * q,
                    d: b + d * q,
                    e: g.clone(),
                    f: h.clone(),
                    g: e + g * q,
                    h: f + h * q,
                },
            }
        }
    }
}

pub mod output {
    use num::{BigInt, Zero};

    use super::State;

    pub trait Output {
        type Term;

        fn is_done(&self, state: &State) -> bool;
        fn well_defined_range(&self, state: &State) -> Option<BigInt>;
        fn update_state(&self, state: &State, range: &BigInt) -> State;
        fn emit(&self, range: &BigInt) -> Self::Term;
    }

    pub struct Regular {}
    impl Output for Regular {
        type Term = BigInt;

        // The factorization has reached a terminal state and the regular
        // continued fraction is complete and exact
        fn is_done(&self, state: &State) -> bool {
            let State { e, f, g, h, .. } = state;
            e.is_zero() && f.is_zero() && g.is_zero() && h.is_zero()
        }

        fn well_defined_range(&self, state: &State) -> Option<BigInt> {
            state.factor_integer()
        }

        fn update_state(&self, state: &State, r: &BigInt) -> State {
            let State {
                a,
                b,
                c,
                d,
                e,
                f,
                g,
                h,
            } = state;

            State {
                a: e.clone(),
                b: f.clone(),
                c: g.clone(),
                d: h.clone(),
                e: a - (e * r),
                f: b - (f * r),
                g: c - (g * r),
                h: d - (h * r),
            }
        }

        fn emit(&self, r: &BigInt) -> Self::Term {
            r.clone()
        }
    }
}

/// Bihomographic function solver
pub struct Solver<I, O> {
    state: State,
    input: I,
    output: O,
}

/// Type alias for regular continued fraction inputs and output
pub type RegularSolver<X, Y> = Solver<input::Regular<X, Y>, output::Regular>;

impl<X, Y> RegularSolver<X, Y>
where
    X: Iterator<Item = BigInt>,
    Y: Iterator<Item = BigInt>,
{
    fn new(x: X, y: Y, state: State) -> Self {
        Solver {
            input: input::Regular { x, y },
            output: output::Regular {},
            state,
        }
    }

    pub fn add(x: X, y: Y) -> Self {
        Self::new(x, y, states::add())
    }

    pub fn subtract(x: X, y: Y) -> Self {
        Self::new(x, y, states::subtract())
    }

    pub fn multiply(x: X, y: Y) -> Self {
        Self::new(x, y, states::multiply())
    }

    pub fn divide(x: X, y: Y) -> Self {
        Self::new(x, y, states::divide())
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
            // TODO in LFT, we use can use the input domain to determine if our output is
            // done
            if self.output.is_done(&self.state) {
                return None;
            }

            let range = self.output.well_defined_range(&self.state);
            if let Some(r) = range {
                self.state = self.output.update_state(&self.state, &r);
                return Some(self.output.emit(&r));
            } else {
                self.state = match self.input.preferred_arg(&self.state) {
                    input::InputArg::X => self.input.update_state_x(&self.state),
                    input::InputArg::Y => self.input.update_state_y(&self.state),
                };
            }
        }
    }
}

impl<X, Y> From<RegularSolver<X, Y>> for terms::Regular<RegularSolver<X, Y>>
where
    X: Iterator<Item = BigInt>,
    Y: Iterator<Item = BigInt>,
{
    fn from(value: RegularSolver<X, Y>) -> Self {
        Self(value)
    }
}

mod states {
    use num::BigInt;

    use super::State;

    enum Coeff {
        I,
        O,
        N,
    }

    impl From<Coeff> for BigInt {
        fn from(value: Coeff) -> Self {
            match &value {
                Coeff::I => BigInt::from(1),
                Coeff::O => BigInt::from(0),
                Coeff::N => BigInt::from(-1),
            }
        }
    }

    type StateCoeffs = (Coeff, Coeff, Coeff, Coeff, Coeff, Coeff, Coeff, Coeff);

    impl From<StateCoeffs> for State {
        fn from((a, b, c, d, e, f, g, h): StateCoeffs) -> Self {
            Self {
                a: a.into(),
                b: b.into(),
                c: c.into(),
                d: d.into(),
                e: e.into(),
                f: f.into(),
                g: g.into(),
                h: h.into(),
            }
        }
    }

    #[rustfmt::skip]
    pub fn add() -> State {
        use Coeff::*;
        State::from((
            O, I, I, O,
            I, O, O, O,
        ))
    }

    #[rustfmt::skip]
    pub fn subtract() -> State {
        use Coeff::*;
        State::from((
            O, I, N, O,
            I, O, O, O,
        ))
    }

    #[rustfmt::skip]
    pub fn multiply() -> State {
        use Coeff::*;
        State::from((
            O, O, O, I,
            I, O, O, O,
        ))
    }

    #[rustfmt::skip]
    pub fn divide() -> State {
        use Coeff::*;
        State::from((
            O, I, O, O,
            O, O, I, O,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::RegularSolver;
    use num::{BigInt, ToPrimitive};

    #[test]
    fn it_adds() {
        let c = RegularSolver::add(
            [BigInt::from(0), BigInt::from(2)].into_iter(),
            [BigInt::from(0), BigInt::from(2)].into_iter(),
        );
        assert!(c.map(|v| v.to_i32().unwrap()).eq([1]));
    }

    #[test]
    fn it_multiplies() {
        let c = RegularSolver::multiply(
            [BigInt::from(0), BigInt::from(2)].into_iter(),
            [BigInt::from(0), BigInt::from(2)].into_iter(),
        );
        assert!(c.map(|v| v.to_i32().unwrap()).eq([0, 4]));
    }
}
