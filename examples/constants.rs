use clap::{Parser, ValueEnum};
use gosper::{consts, ContinuedFraction};
use num::BigInt;
use std::fmt::Display;

/// Print continued fraction constants
///
/// # Example
///
/// > cargo run --release --example constants -- pi --wrap=50 --format=decimal
#[derive(Parser)]
#[command()]
struct Cli {
    /// The constant to be printed.
    #[arg(value_enum)]
    constant: Constant,

    /// The format of the terms.
    ///
    /// - "regular" will print the convergents of the regular continued fraction
    /// representation of the constant.
    ///
    /// - "decimal" will print the decimal digits of the constant.
    #[arg(long, value_enum, default_value_t, verbatim_doc_comment)]
    format: Format,

    /// Stop printing after this many terms. 0 means never stop. (default: 0)
    #[arg(long, short)]
    num_terms: Option<usize>,

    /// Wraps to a new line after this many terms. (default: 50)
    #[arg(long, short)]
    wrap: Option<usize>,

    /// Include digit counts on every new line. (default: false)
    #[arg(long, short)]
    line_numbers: Option<bool>,
}

#[derive(ValueEnum, Clone)]
enum Constant {
    Pi,
    Phi,
    E,
}

#[derive(ValueEnum, Clone, Default)]
enum Format {
    #[default]
    Regular,
    Decimal,
}

pub fn main() {
    Main(Cli::parse()).main()
}

struct Main(Cli);

impl Main {
    fn main(&self) {
        match self.0.constant {
            Constant::Pi => self.format(ContinuedFraction::from(consts::Pi)),
            Constant::Phi => self.format(ContinuedFraction::from(consts::Phi)),
            Constant::E => self.format(ContinuedFraction::from(consts::E)),
        }
    }

    fn format<I>(&self, cf: ContinuedFraction<I>)
    where
        I: Iterator<Item = BigInt>,
    {
        match self.0.format {
            Format::Regular => self.print(&mut cf.iter()),
            Format::Decimal => self.print(&mut cf.to_decimal()),
        }
    }

    fn print<I>(&self, iter: &mut I)
    where
        I: Iterator,
        I::Item: Display,
    {
        let max = self.0.num_terms.unwrap_or(0);
        let wrap = self.0.wrap.unwrap_or(50);
        let line_numbers = self.0.line_numbers.unwrap_or(false);

        let mut digits = 0;
        loop {
            if line_numbers {
                print!("{:12}: ", digits);
            }

            for _ in 0..wrap {
                print!("{} ", iter.next().unwrap());
                digits += 1;
                if digits == max {
                    println!();
                    return;
                }
            }
            println!();
        }
    }
}
