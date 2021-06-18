//! Contains some helper functions that can be useful.

use crate::Rational;

/// Convenience method for constructing a simple `Rational`.
///
/// ## Example
/// ```rust
/// # use rational::{Rational, extras::*};
/// let one_half = r(1, 2);
/// assert_eq!(one_half, Rational::new(1, 2));
/// ```
pub fn r(n: i128, d: i128) -> Rational {
    Rational::new(n, d)
}

/// Calculate the greatest common divisor of two numbers.
///
/// ## Example
/// ```rust
/// # use rational::extras::*;
/// assert_eq!(gcd(9, 60), 3);
/// assert_eq!(gcd(899, 957), 29);
/// assert_eq!(gcd(-899, 957), 29);
/// ```
pub fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// Create a [continued fraction](https://en.wikipedia.org/wiki/Continued_fraction#Motivation_and_notation).
///
/// ## Notes
/// The size of the numerator and denominator can grow quite quickly with increased lengths of `cont`,
/// so be careful with integer overflow. If `cont` is empty, then the resulting `Rational` will be equal to `init`.
///
/// ## Example
/// ```rust
/// # use rational::extras::*;
/// // to create a rational number that estimates the mathematical constant `e` (~2.7182818...)
/// // we can use the continued fraction [2;1,2,1,1,4,1,1,6,1,1,8]
/// let e = continued_fraction(2, &[1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8]);
/// assert!((e.decimal_value() - std::f64::consts::E).abs() < 0.0000001);
/// ```
pub fn continued_fraction(init: u64, cont: &[u64]) -> Rational {
    let mut r = Rational::new(0, 1);

    for &d in cont.iter().rev() {
        r = Rational::new(1, r + d);
    }

    r + init
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd_test() {
        let eq = |a: i128, b: i128, g: i128| assert_eq!(gcd(a, b), g);
        eq(1, 2, 1);
        eq(5, 4, 1);
        eq(12, 4, 4);
        eq(-74, 44, 2);
    }

    #[test]
    fn repeated_test() {
        let continued = continued_fraction(1, &[2; 15]);

        dbg!(continued, continued.decimal_value());

        assert!((continued.decimal_value() - 2.0_f64.sqrt()).abs() < 0.00000001);

        let continued = continued_fraction(1, &[1; 100]);

        dbg!(continued, continued.decimal_value());

        assert!((continued.decimal_value() - 1.6180339887498).abs() < 0.00001);

        let continued = continued_fraction(
            4,
            &[
                2, 1, 3, 1, 2, 8, 2, 1, 3, 1, 2, 8, 2, 1, 3, 1, 2, 8, 2, 1, 3, 1, 2, 8, 2, 1, 3, 1,
                2, 8, 2, 1, 3, 1, 2, 8,
            ],
        );

        dbg!(continued, continued.decimal_value(), 19.0_f64.sqrt());

        assert!((continued.decimal_value() - 19.0_f64.sqrt()).abs() < 0.00001);
    }

    #[test]
    fn empty_continued_fraction_test() {
        let continued = continued_fraction(1, &[]);
        dbg!(continued, continued.decimal_value());
        assert_eq!(continued, r(1, 1));
    }
}
