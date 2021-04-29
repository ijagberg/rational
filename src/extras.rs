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
}
