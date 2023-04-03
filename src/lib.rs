// SPDX-License-Identifier: MIT

#![doc = include_str!("../README.md")]

//! # Examples
//!
//! Create regular [`ContinuedFraction`]s and perform exact arithmetic
//!
//! ```rust
//! use gosper::ContinuedFraction;
//!
//! let a = ContinuedFraction::from(0.5); // from numerical primitives
//! let b = ContinuedFraction::from([1, 2, 5]); // from regular continued fraction terms
//! let c = ContinuedFraction::from((1, 2)); // from rationals
//!
//! let d = a / (b + c);
//!
//! assert_eq!(format!("{:.10}", d), "0.2558139534");
//! assert_eq!(format!("{:#}", d), "[0;3,1,10]");
//! assert_eq!(d, ContinuedFraction::from([0, 3, 1, 10]));
//! ```
//!
//! Arbitrary precision constants
//!
//! ```rust
//! # use gosper::ContinuedFraction;
//! use gosper::consts;
//!
//! let pi = ContinuedFraction::from(consts::Pi);
//!
//! assert_eq!(format!("{:.1000}", pi), "3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491298336733624406566430860213949463952247371907021798609437027705392171762931767523846748184676694051320005681271452635608277857713427577896091736371787214684409012249534301465495853710507922796892589235420199561121290219608640344181598136297747713099605187072113499999983729780499510597317328160963185950244594553469083026425223082533446850352619311881710100031378387528865875332083814206171776691473035982534904287554687311595628638823537875937519577818577805321712268066130019278766111959092164201989");
//! ```
//!
//! Lossy conversion to/from floats
//!
//! ```rust
//! # use gosper::ContinuedFraction;
//! let jenny = ContinuedFraction::from(867.5309);
//! assert_eq!(jenny.to_f64(), 867.5309000000001);
//! ```
//!
//! [^1]: <https://perl.plover.com/classes/cftalk/INFO/gosper.txt>

// re-export dependencies that appears in our public API
pub use num;

// re-export main continued fraction type
mod continued_fraction;
pub use continued_fraction::*;

pub mod bihomographic;
pub mod consts;
pub mod display;
pub mod extended;
pub mod float;
pub mod generalized;
pub mod homographic;
pub mod iter;
pub mod rational;
pub mod terms;
