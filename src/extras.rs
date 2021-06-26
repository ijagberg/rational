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

pub fn continued_fraction_iter(init: u64, cont: &[u64]) -> ContinuedFractionIter {
    ContinuedFractionIter::new(Rational::new(init, 1), cont)
}

pub struct ContinuedFractionIter<'a> {
    init: Rational,
    fraction: Rational,
    idx: usize,
    cont: &'a [u64],
}

impl<'a> ContinuedFractionIter<'a> {
    fn new(init: Rational, cont: &'a [u64]) -> Self {
        Self {
            init,
            fraction: Rational::zero(),
            idx: 0,
            cont,
        }
    }

    pub fn decimals(self) -> impl Iterator<Item = f64> + 'a {
        self.map(|r| r.decimal_value())
    }
}

impl Iterator for ContinuedFractionIter<'_> {
    type Item = Rational;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cont.is_empty() {
            if self.idx == 0 {
                self.idx += 1;
                Some(self.init)
            } else {
                None
            }
        } else {
            if self.idx > self.cont.len() {
                None
            } else if self.idx == self.cont.len() {
                self.idx += 1;
                Some(self.init + self.fraction)
            } else {
                let curr = self.init + self.fraction;
                self.fraction =
                    Rational::new(1, self.fraction + self.cont[self.cont.len() - self.idx - 1]);
                self.idx += 1;
                Some(curr)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd_test() {
        let eq = |a: i128, b: i128, g: i128| assert_eq!(gcd(a, b), g, "a: {}, b: {}", a, b);
        eq(1, 2, 1);
        eq(5, 4, 1);
        eq(12, 4, 4);
        eq(-74, 44, 2);
    }

    #[test]
    fn repeated_test() {
        use std::f64::consts::*;
        let assert = |init: u64, cont: &[u64], expected: f64| {
            let actual = continued_fraction(init, cont).decimal_value();
            assert!(
                (actual - expected).abs() < 0.000000001,
                "actual: {}, expected: {}",
                actual,
                expected
            );
        };

        assert(1, &[2; 15], 2.0_f64.sqrt());
        assert(1, &[1; 100], 1.6180339887498);
        assert(4, &[2, 1, 3, 1, 2, 8, 2, 1, 3, 1, 2, 8], 19.0_f64.sqrt());
        assert(1, &[], 1.0);
        assert(4, &[], 4.0);
        assert(2, &[1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, 1, 1, 10], E);
        assert(3, &[7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1], PI);
    }

    #[test]
    fn continued_fraction_iter_test() {
        let decimal_approx: Vec<_> = continued_fraction_iter(2, &[1, 2, 1, 1, 4, 1, 1, 6])
            .decimals()
            .collect();
        assert_eq!(
            decimal_approx,
            vec![
                2.0,
                2.1666666666666665,
                2.857142857142857,
                2.5384615384615383,
                2.2203389830508473,
                2.8194444444444446,
                2.549618320610687,
                2.3922155688622753,
                2.718279569892473,
            ]
        );
    }
}
