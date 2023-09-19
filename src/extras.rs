//! Contains some helper functions that can be useful and/or fun.

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

/// Calculate the greatest common divisor of two numbers using [Stein's algorithm](https://en.wikipedia.org/wiki/Binary_GCD_algorithm).
///
/// ## Panics
/// * If the result does not fit in the `i128` primitive type. This only happens in the cases below.
/// ```rust,no_run
///   # use rational::extras::*;
///   // both of these are equal to `i128::MAX + 1`, which does not fit in an `i128`
///   gcd(i128::MIN, 0);
///   gcd(0, i128::MIN);
///   gcd(i128::MIN, i128::MIN);
/// ```
///
/// ## Example
/// ```rust
/// # use rational::extras::*;
/// assert_eq!(gcd(9, 60), 3);
/// assert_eq!(gcd(899, 957), 29);
/// assert_eq!(gcd(-899, 957), 29);
/// ```
pub fn gcd(mut a: i128, mut b: i128) -> i128 {
    if a == 0 || b == 0 {
        return return_gcd(a, b, a | b);
    }

    let factors_of_two = (a | b).trailing_zeros();

    if a == i128::MIN || b == i128::MIN {
        return return_gcd(a, b, 1 << factors_of_two);
    }

    a = a.abs() >> a.trailing_zeros();
    b = b.abs() >> b.trailing_zeros();

    while a != b {
        if a > b {
            a -= b;
            a >>= a.trailing_zeros();
        } else {
            b -= a;
            b >>= b.trailing_zeros();
        }
    }
    a << factors_of_two
}

fn return_gcd(a: i128, b: i128, g: i128) -> i128 {
    if g == i128::MIN {
        panic!("the gcd of {} and {} is equal to i128::MAX+1, which does not fit in the i128 primitive type", a, b)
    } else {
        g.abs()
    }
}

/// Calculate the least common multiple of two numbers.
///
/// ## Panics
/// * If overflow occurred
///
/// ## Example
/// ```rust
/// # use rational::extras::*;
/// assert_eq!(lcm(6, 8), 24);
/// assert_eq!(lcm(-6, 8), 24);
/// ```
pub fn lcm(a: i128, b: i128) -> i128 {
    let g = gcd(a, b);
    a.abs() * (b.abs() / g)
}

/// Calculate the least common multiple of two numbers, raturning `None` if overflow occurred.
///
/// ## Example
/// ```rust
/// # use rational::extras::*;
/// assert_eq!(lcm_checked(6, 8), Some(24));
/// assert_eq!(lcm_checked(-6, 8), Some(24));
/// assert_eq!(lcm_checked(i128::MAX, i128::MAX - 1), None);
/// ```
pub fn lcm_checked(a: i128, b: i128) -> Option<i128> {
    let g = gcd(a, b);
    a.abs().checked_mul(b.abs().checked_div(g)?)
}

/// Checks if `l` and `r` are [coprime](https://en.wikipedia.org/wiki/Coprime_integers). Shorthand for `gcd(l, r) == 1`.
///
/// ## Example
/// ```rust
/// # use rational::extras::*;
/// assert!(is_coprime(8, 9));
/// assert!(is_coprime(7, 9));
/// assert!(!is_coprime(6, 9));
/// assert!(is_coprime(-1, 1));
/// ```
pub fn is_coprime(l: i128, r: i128) -> bool {
    gcd(l, r) == 1
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
        } else if self.idx > self.cont.len() {
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
        eq(-2, -4, 2);
        eq(i128::MIN, 1, 1);
    }

    #[test]
    #[should_panic]
    fn gcd_should_panic_test_1() {
        dbg!(gcd(i128::MIN, 0));
    }

    #[test]
    #[should_panic]
    fn gcd_should_panic_test_2() {
        dbg!(gcd(0, i128::MIN));
    }

    #[test]
    #[should_panic]
    fn gcd_should_panic_test_3() {
        dbg!(gcd(i128::MIN, i128::MIN));
    }

    #[test]
    fn lcm_test() {
        assert_eq!(lcm(2, 6), 6);
        assert_eq!(lcm(1, 6), 6);
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
