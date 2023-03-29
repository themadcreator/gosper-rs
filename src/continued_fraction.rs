use crate::bihomographic;
use crate::display;
use crate::float;
use crate::homographic;
use crate::iter;
use crate::rational;
use crate::terms;

use num::BigInt;
use num::ToPrimitive;
use num::Zero;

use std::cmp::Ordering;
use std::iter::Take;
use std::ops::{Add, Div, Mul, Sub};

/// Arbitrary precision regular continued fraction
///
/// This struct wraps an iterator of [`BigInt`] terms `a_n` of the regular
/// continued fraction `x`.
///
/// ```text
/// x = a_0 + 1 / (a_1 + 1 / (a_2 + ...))
/// ```
///
/// # Example
///
/// ```rust
/// use gosper::ContinuedFraction;
///
/// // x = 2 + 1 / (3 + 1 / (4 + 1 / 5))
/// let x = ContinuedFraction::from([2, 3, 4, 5]);
///
/// assert_eq!(format!("{:#}", x), "[2;3,4,5]");
/// assert_eq!(format!("{:.10}", x), "2.3088235294");
/// ```
pub struct ContinuedFraction<I: Iterator<Item = BigInt>> {
    terms: iter::Memo<I>,
}

/// We can clone because we use a memo iterator
impl<I> Clone for ContinuedFraction<I>
where
    I: Iterator<Item = BigInt>,
{
    fn clone(&self) -> Self {
        Self {
            terms: self.terms.clone(),
        }
    }
}

impl<I> ContinuedFraction<I>
where
    I: Iterator<Item = BigInt>,
{
    pub fn new(regular: terms::Regular<I>) -> Self {
        let terms::Regular(iter) = regular;
        Self {
            terms: iter::Memo::new(iter),
        }
    }

    /// Returns the integer part of this continued fraction
    ///
    /// By virtue of the structure of a continued fraction, this is simply the
    /// first item to be returned from the term iterator. An empty iterator
    /// indicates [`Zero`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gosper::*;
    /// # use num::{BigInt, FromPrimitive};
    /// let x = ContinuedFraction::from((1_234_567, 8_910));
    /// assert_eq!(x.to_f64(), 138.55970819304153);
    /// assert_eq!(x.to_integer(), BigInt::from(138));
    /// ```
    pub fn to_integer(&self) -> BigInt {
        match &self.iter().next() {
            Some(i) => i.clone(),
            None => BigInt::zero(),
        }
    }

    /// Returns a ([`BigInt`], [`BigInt`]) tuple equal to the exact rational
    /// value of this continued fraction.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gosper::*;
    /// # use num::{BigInt, FromPrimitive};
    /// let x = ContinuedFraction::from([2, 3, 4, 5, 6]);
    /// let (num, den) = x.to_rational();
    /// assert_eq!((num, den), (BigInt::from(972), BigInt::from(421)));
    /// ```
    ///
    /// # Halting
    ///
    /// This method will iterate forever if this continued fraction is
    /// non-terminating.
    ///
    /// ```rust,no_run
    /// # use gosper::*;
    /// let pi = ContinuedFraction::from(consts::Pi);
    /// let (num, den) = pi.to_rational(); // ⚠️ will never return!
    /// ```
    ///
    /// You can work around this by limiting the precision of the continued
    /// fraction
    ///
    /// ```rust
    /// # use gosper::*;
    /// # use num::{BigInt, FromPrimitive};
    /// let pi = ContinuedFraction::from(consts::Pi);
    /// let (num, den) = pi.with_precision(100).to_rational();
    ///
    /// assert_eq!(num.to_string(), "4170888101980193551139105407396069754167439670144501");
    /// assert_eq!(den.to_string(), "1327634917026642108692848192776111345311909093498260");
    /// ```
    pub fn to_rational(&self) -> (BigInt, BigInt) {
        let rational::Rational(num, den) = rational::Rational::from(&mut self.iter());
        (num, den)
    }

    /// Returns a [`f64`] approximation of the value of this continued fraction.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gosper::*;
    /// let a = ContinuedFraction::from((1, 6)); // exact rational 1 / 6
    /// assert_eq!(a.to_f64(), 0.16666666666666663);
    ///
    /// let b = &a + &a;
    /// assert_eq!(b.to_f64(), 0.33333333333333326);
    ///
    /// let c = &b + &b + &b;
    /// assert_eq!(c.to_f64(), 1.0);
    /// ```
    ///
    /// As opposed to [`to_rational()`](ContinuedFraction::to_rational()), this
    /// method will always return if the continued fraction provides enough
    /// terms to produce an "accurate enough" float.
    ///
    /// ```rust
    /// # use gosper::*;
    /// let pi = ContinuedFraction::from(consts::Pi);
    /// assert_eq!(pi.to_f64(), 3.141592653589793);
    /// ```
    pub fn to_f64(&self) -> f64 {
        let float::Float(f) = float::Float::from(&mut self.iter().map_while(|b| b.to_i32()));
        f
    }

    /// Returns a [`DecimalSolver`](homographic::DecimalSolver) that will emit
    /// the decimal digits of this continued fraction value as [`BigInt`]s.
    ///
    /// The first term from the iterator may be arbitrarily large.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gosper::*;
    /// # use num::{ToPrimitive};
    /// let pi = ContinuedFraction::from(consts::Pi);
    /// let kilo = ContinuedFraction::from(1_000);
    ///
    /// let digits = (pi + kilo).to_decimal().take(10);
    ///
    /// assert!(digits.map(|d| d.to_i32().unwrap()).eq([1003, 1, 4, 1, 5, 9, 2, 6, 5, 3].into_iter()));
    /// ```
    pub fn to_decimal(&self) -> homographic::DecimalSolver<iter::MemoIter<I>> {
        let terms::Decimal(iter) = terms::Decimal::from(self);
        iter
    }

    /// Returns an impl of [`Display`](std::fmt::Display) for the decimal
    /// representation of this value.
    ///
    /// Format precision may be used to specify the number of digits after the
    /// decimal point. Minimum is `1`. The default max precision is `100`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gosper::*;
    /// let pi = ContinuedFraction::from(consts::Pi);
    /// assert_eq!(format!("{:.2}", pi.display_decimal()), "3.14");
    /// assert_eq!(format!("{:.2}", pi), "3.14");
    ///
    /// let third = ContinuedFraction::from((1, 3));
    /// assert_eq!(format!("{:.5}", third.display_decimal()), "0.33333");
    /// ```
    pub fn display_decimal(&self) -> display::Decimal<iter::MemoIter<I>> {
        display::Decimal::from(self)
    }

    /// Returns an impl of [`Display`](std::fmt::Display) for the compact
    /// continued fraction representation of this value.
    ///
    /// Format precision may be used to specify the number of terms after the
    /// integer part. The default max precision is `100`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gosper::*;
    /// let pi = ContinuedFraction::from(consts::Pi);
    /// assert_eq!(format!("{:.4}", pi.display_regular()), "[3;7,15,1,292]");
    /// assert_eq!(format!("{:#.4}", pi), "[3;7,15,1,292]");
    ///
    /// let third = ContinuedFraction::from((1, 3));
    /// assert_eq!(format!("{}", third.display_regular()), "[0;3]");
    /// ```
    pub fn display_regular(&self) -> display::CompactRegularContinuedFraction<iter::MemoIter<I>> {
        display::CompactRegularContinuedFraction::from(self)
    }

    /// Limit the precision to a maximum number of regular continued fraction
    /// terms
    ///
    /// ```rust
    /// # use gosper::*;
    /// let pi = ContinuedFraction::from(consts::Pi).with_precision(1_000);
    /// let z = &pi - &pi;
    ///
    /// assert_eq!(z, ContinuedFraction::from(0));
    /// ```
    ///
    /// # Halting
    ///
    /// Without truncating the precision of non-terminating continued fractions,
    /// the solvers may loop forever trying to determine a difference between
    /// `pi - pi` and `0`.
    ///
    /// It is also important which values you truncate. In the example below, we
    /// truncate the result of the subtraction, but the continued fraction
    /// cannot even be determined to the second term because the solvers will
    /// loop forever trying to discern the boundary between two well defined
    /// integers.
    ///
    /// ```rust,no_run
    /// # use gosper::*;
    /// let pi = ContinuedFraction::from(consts::Pi);
    /// let z = &pi - &pi;
    ///
    /// assert_eq!(z.with_precision(2), ContinuedFraction::from(0)); // ⚠️ will never return!
    /// ```
    pub fn with_precision(&self, precision: usize) -> ContinuedFraction<Take<iter::MemoIter<I>>> {
        ContinuedFraction::new(terms::Regular(self.iter().take(precision)))
    }

    /// Returns a new memoized iterator of the terms of this regular continued
    /// fraction
    pub fn iter(&self) -> iter::MemoIter<I> {
        self.terms.iter()
    }
}

/// Create a [`ContinuedFraction`] from anything that can be
/// [`Regular`](terms::Regular) terms
impl<I, J> From<I> for ContinuedFraction<J>
where
    J: Iterator<Item = BigInt>,
    terms::Regular<J>: From<I>,
{
    fn from(value: I) -> Self {
        Self::new(terms::Regular::from(value))
    }
}

impl<'a, I> IntoIterator for &'a ContinuedFraction<I>
where
    I: Iterator<Item = BigInt>,
{
    type IntoIter = iter::MemoIter<I>;
    type Item = I::Item;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Display continued fraction value as string of decimal digits
///
/// Uses a decimal representation by default and the compact continued fraction
/// notation as the alternate formatting (`#`).
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// let pi = ContinuedFraction::from(consts::Pi);
/// assert_eq!(format!("{:.4}", pi), "3.1415");
/// assert_eq!(format!("{:#.4}", pi), "[3;7,15,1,292]");
///
/// let third = ContinuedFraction::from((1, 3));
/// assert_eq!(format!("{:.5}", third), "0.33333");
/// assert_eq!(format!("{:#}", third), "[0;3]");
/// ```
impl<I> std::fmt::Display for ContinuedFraction<I>
where
    I: Iterator<Item = BigInt>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match f.alternate() {
            false => self.display_decimal().fmt(f),
            true => self.display_regular().fmt(f),
        }
    }
}

impl<I> std::fmt::Debug for ContinuedFraction<I>
where
    I: Iterator<Item = BigInt>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:#.5}", self))
    }
}

/// Equality between continued fractions
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// # use num::BigInt;
/// assert!(ContinuedFraction::from([1, 2, 3]) == ContinuedFraction::from([1, 2, 3]));
/// assert!(ContinuedFraction::from(0) == ContinuedFraction::from([] as [BigInt; 0]));
/// assert!(ContinuedFraction::from(0) == ContinuedFraction::from([0]));
/// assert!(ContinuedFraction::from(0) == ContinuedFraction::from((0, 1_000)));
/// assert!(ContinuedFraction::from([1, 2, 3]) == ContinuedFraction::from((10, 7)));
/// ```
impl<I, J> std::cmp::PartialEq<ContinuedFraction<J>> for ContinuedFraction<I>
where
    I: Iterator<Item = BigInt>,
    J: Iterator<Item = BigInt>,
{
    fn eq(&self, other: &ContinuedFraction<J>) -> bool {
        matches!(self.partial_cmp(other), Some(Ordering::Equal))
    }
}

/// Ordering of continued fractions
///
/// # Example
///
/// ```rust
/// # use gosper::*;
/// assert!(ContinuedFraction::from(10) > ContinuedFraction::from(5));
/// assert!(ContinuedFraction::from([1, 2, 3, 1]) > ContinuedFraction::from([1, 2, 3]));
/// assert!(ContinuedFraction::from([1, 2]) > ContinuedFraction::from([1, 3]));
/// assert!(ContinuedFraction::from((1, 2)) > ContinuedFraction::from((1, 3)));
/// ```
impl<I, J> std::cmp::PartialOrd<ContinuedFraction<J>> for ContinuedFraction<I>
where
    I: Iterator<Item = BigInt>,
    J: Iterator<Item = BigInt>,
{
    fn partial_cmp(&self, other: &ContinuedFraction<J>) -> Option<Ordering> {
        let mut a_iter = self.iter();
        let mut b_iter = other.iter();

        let mut index = 0;
        loop {
            match (a_iter.next(), b_iter.next()) {
                // the first term is compared directly
                (Some(a), Some(b)) if index == 0 => match a.cmp(&b) {
                    Ordering::Equal => (),
                    cmp => return Some(cmp),
                },

                // following terms use an inverse comparison due to the structure of a continued
                // fraction
                (Some(a), Some(b)) => match b.cmp(&a) {
                    Ordering::Equal => (),
                    cmp => return Some(cmp),
                },

                // `[0]` and `[]` are both equivalent to zero
                (None, Some(b)) if index == 0 && b.is_zero() => return Some(Ordering::Equal),
                (Some(a), None) if index == 0 && a.is_zero() => return Some(Ordering::Equal),

                // whichever continued fraction has more terms is larger
                (None, Some(_)) => return Some(Ordering::Less),
                (Some(_), None) => return Some(Ordering::Greater),

                // if the continued fractions terminate at the same place, they are equal
                (None, None) => return Some(Ordering::Equal),
            }
            index += 1;
        }
    }
}

macro_rules! arithmetic_operator {
    ($op:ident, $method:ident, $impl:path) => {
        // val op val
        impl<L, R> $op<ContinuedFraction<R>> for ContinuedFraction<L>
        where
            L: Iterator<Item = BigInt>,
            R: Iterator<Item = BigInt>,
        {
            type Output = ContinuedFraction<
                bihomographic::RegularSolver<iter::MemoIter<L>, iter::MemoIter<R>>,
            >;

            fn $method(self, rhs: ContinuedFraction<R>) -> Self::Output {
                ContinuedFraction::from($impl(self.into_iter(), rhs.into_iter()))
            }
        }

        // val op ref
        impl<'a, L, R> $op<&'a ContinuedFraction<R>> for ContinuedFraction<L>
        where
            L: Iterator<Item = BigInt>,
            R: Iterator<Item = BigInt>,
        {
            type Output = ContinuedFraction<
                bihomographic::RegularSolver<iter::MemoIter<L>, iter::MemoIter<R>>,
            >;

            fn $method(self, rhs: &'a ContinuedFraction<R>) -> Self::Output {
                ContinuedFraction::from($impl(self.into_iter(), rhs.iter()))
            }
        }

        // ref op val
        impl<'a, L, R> $op<ContinuedFraction<R>> for &'a ContinuedFraction<L>
        where
            L: Iterator<Item = BigInt>,
            R: Iterator<Item = BigInt>,
        {
            type Output = ContinuedFraction<
                bihomographic::RegularSolver<iter::MemoIter<L>, iter::MemoIter<R>>,
            >;

            fn $method(self, rhs: ContinuedFraction<R>) -> Self::Output {
                ContinuedFraction::from($impl(self.iter(), rhs.into_iter()))
            }
        }

        // ref op ref
        impl<'a, L, R> $op<&'a ContinuedFraction<R>> for &'a ContinuedFraction<L>
        where
            L: Iterator<Item = BigInt>,
            R: Iterator<Item = BigInt>,
        {
            type Output = ContinuedFraction<
                bihomographic::RegularSolver<iter::MemoIter<L>, iter::MemoIter<R>>,
            >;

            fn $method(self, rhs: &'a ContinuedFraction<R>) -> Self::Output {
                ContinuedFraction::from($impl(self.iter(), rhs.iter()))
            }
        }
    };
}

arithmetic_operator!(Add, add, bihomographic::RegularSolver::add);
arithmetic_operator!(Sub, sub, bihomographic::RegularSolver::subtract);
arithmetic_operator!(Mul, mul, bihomographic::RegularSolver::multiply);
arithmetic_operator!(Div, div, bihomographic::RegularSolver::divide);

#[cfg(test)]
mod tests {
    use crate::{consts, ContinuedFraction};
    use num::BigInt;

    fn assert_iters_eq<U, V>(u: U, v: V)
    where
        U: IntoIterator<Item = BigInt>,
        V: IntoIterator,
        BigInt: From<V::Item>,
    {
        assert!(u.into_iter().eq(v.into_iter().map(BigInt::from)));
    }

    fn assert_is_close(a: f64, b: f64) {
        assert!((a - b).abs() < 1e-13)
    }

    #[test]
    fn it_wraps_iter() {
        let a = ContinuedFraction::from(consts::Pi);
        let b = ContinuedFraction::from([3, 7, 15, 1, 292, 1]);
        assert!(a.iter().take(6).eq(b.iter()));
    }

    #[test]
    fn it_adds() {
        let (a, b, c) = (
            ContinuedFraction::from([0, 2]),
            ContinuedFraction::from([0, 2]),
            ContinuedFraction::from([0, 8]),
        );

        let z = &a + &b;
        assert_iters_eq(&z, [1]);

        let y = &a + &b;
        assert_iters_eq(&y, [1]);

        let x = (&a + &b) + &c;
        assert_iters_eq(&x, [1, 8]);

        let w = &c + (&a + &b);
        assert_iters_eq(&w, [1, 8]);

        let v = x + y + z; // <-- consumes x, y, z
        assert_iters_eq(&v, [3, 8]);
    }

    #[test]
    fn it_multiplies() {
        let (a, b, c, d, e) = (
            ContinuedFraction::from([0, 2]),
            ContinuedFraction::from([0, 2]),
            ContinuedFraction::from([0, 8]),
            ContinuedFraction::from([1, 1, 1, 1, 1, 2]),
            ContinuedFraction::from([0, 1, 4, 1, 2, 1, 100, 10, 1]),
        );

        let z = &d * &e;
        assert_iters_eq(&z, [1, 2, 1, 101, 1, 3, 1, 1, 1, 1, 3]);

        let y = &a * &b * &c * &z;
        assert_iters_eq(&y, [0, 23, 1, 50, 3, 1, 3, 44]);
    }

    #[test]
    fn it_divides() {
        let (a, b, c, d, e) = (
            ContinuedFraction::from([0, 2]),
            ContinuedFraction::from([0, 2]),
            ContinuedFraction::from([0, 8]),
            ContinuedFraction::from([1, 1, 1, 1, 1, 2]),
            ContinuedFraction::from([0, 1, 4, 1, 2, 1, 100, 10, 1]),
        );

        let z = &d / &e;
        assert_iters_eq(&z, [1, 1, 21, 2, 10, 2, 1, 10, 2, 1, 5]);

        let y = &a / &b / &c / &z;
        assert_iters_eq(&y, [4, 10, 1, 85, 1, 2, 1, 22, 1, 2]);

        let (fa, fb, fc, fd, fe, fz, fy) = (
            a.to_f64(),
            b.to_f64(),
            c.to_f64(),
            d.to_f64(),
            e.to_f64(),
            z.to_f64(),
            y.to_f64(),
        );
        let fzz = fd / fe;
        assert_is_close(fzz, fz);

        let fyy = fa / fb / fc / fz;
        assert_is_close(fyy, fy);
    }

    #[test]
    fn it_performs_composite() {
        let f = (0.5, 0.123, 0.234);
        let c = (
            ContinuedFraction::from(f.0),
            ContinuedFraction::from(f.1),
            ContinuedFraction::from(f.2),
        );

        let ((fa, fb, fc), (ca, cb, cc)) = (f, c);

        assert_is_close(fa + fb - fc, (&ca + &cb - &cc).to_f64());
        assert_is_close(
            fa + fb - fc + fa + fb,
            (&ca + &cb - &cc + &ca + &cb).to_f64(),
        );
        assert_is_close(
            fa + fb - fc * fa + fb,
            (&ca + &cb - &cc * &ca + &cb).to_f64(),
        );
        assert_is_close(fa * fb + fc, (&ca * &cb + &cc).to_f64());
        assert_is_close(fa - fb / fc, (&ca - &cb / &cc).to_f64());
        assert_is_close(fa / fb * fc, (&ca / &cb * &cc).to_f64());
    }
}
