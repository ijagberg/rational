/// Contains some helper functions that can be useful.
pub mod extras;

use extras::gcd;
use std::{
    fmt::Display,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

/// A rational number (a fraction of two integers).
#[derive(Copy, Clone, Debug)]
pub struct Rational {
    /// The numerator (number above the fraction line).
    numerator: i128,
    /// The denominator (number below the fraction line).
    denominator: i128,
}

impl Rational {
    /// Construct a new Rational.
    ///
    /// ## Panics
    /// * If the resulting denominator is 0.
    pub fn new<N, D>(numerator: N, denominator: D) -> Self
    where
        Rational: From<N>,
        Rational: From<D>,
    {
        let numerator = Rational::from(numerator);
        let denominator = Rational::from(denominator);

        let num = numerator.numerator * denominator.denominator;
        let den = numerator.denominator * denominator.numerator;

        if den == 0 {
            panic!("denominator cannot be 0");
        }

        let mut this = Self {
            numerator: num,
            denominator: den,
        };
        this.reduce();
        this
    }

    /// Construct a new Rational, returning `None` if the denominator is 0.
    pub fn new_checked<T>(numerator: T, denominator: T) -> Option<Self>
    where
        Rational: From<T>,
    {
        let numerator = Rational::from(numerator);
        let denominator = Rational::from(denominator);

        let num = numerator.numerator * denominator.denominator;
        let den = numerator.denominator * denominator.numerator;

        if den == 0 {
            None
        } else {
            let mut this = Self {
                numerator: num,
                denominator: den,
            };
            this.reduce();
            Some(this)
        }
    }

    /// Get the numerator in this `Rational`.
    pub fn numerator(&self) -> i128 {
        self.numerator
    }

    /// Get the denominator in this `Rational`.
    pub fn denominator(&self) -> i128 {
        self.denominator
    }

    /// Returns the inverse of this `Rational`, or `None` if the denominator of the inverse is 0.
    pub fn inverse_checked(self) -> Option<Self> {
        if self.numerator == 0 {
            None
        } else {
            Some(Self::new(self.denominator, self.numerator))
        }
    }

    /// Returns the inverse of this `Rational`.
    ///
    /// ## Panics
    /// * If the denominator of the inverse is 0.
    pub fn inverse(self) -> Self {
        if self.numerator == 0 {
            panic!("numerator cannot be 0 when inverting");
        }
        Self::new(self.denominator, self.numerator)
    }

    /// Returns the decimal value of this `Rational`.
    /// Equivalent to `f64::from(self)`.
    pub fn decimal_value(self) -> f64 {
        f64::from(self)
    }

    fn reduce(&mut self) {
        let gcd = gcd(self.numerator, self.denominator);
        self.numerator /= gcd;
        self.denominator /= gcd;
    }
}

macro_rules! impl_from {
    ($type:ty) => {
        impl From<$type> for Rational {
            fn from(v: $type) -> Self {
                Rational {
                    numerator: v as i128,
                    denominator: 1 as i128,
                }
            }
        }
    };
}

impl_from!(u8);
impl_from!(u16);
impl_from!(u32);
impl_from!(u64);
impl_from!(i8);
impl_from!(i16);
impl_from!(i32);
impl_from!(i64);
impl_from!(i128);
impl_from!(isize);

impl<T> Div<T> for Rational
where
    Rational: From<T>,
{
    type Output = Self;

    fn div(self, rhs: T) -> Self::Output {
        let rhs = Rational::from(rhs);
        let numerator = self.numerator * rhs.denominator;
        let denominator = self.denominator * rhs.numerator;

        Rational::new::<i128, i128>(numerator, denominator)
    }
}

impl<T> DivAssign<T> for Rational
where
    Rational: From<T>,
{
    fn div_assign(&mut self, rhs: T) {
        let result = *self / rhs;
        *self = result;
    }
}

impl<T> Mul<T> for Rational
where
    Rational: From<T>,
{
    type Output = Self;

    fn mul(self, rhs: T) -> Self::Output {
        let rhs = Rational::from(rhs);
        let numerator = self.numerator * rhs.numerator;
        let denominator = self.denominator * rhs.denominator;

        Rational::new::<i128, i128>(numerator, denominator)
    }
}

impl<T> MulAssign<T> for Rational
where
    Rational: From<T>,
{
    fn mul_assign(&mut self, rhs: T) {
        let result = *self * rhs;
        *self = result;
    }
}

impl<T> Add<T> for Rational
where
    Rational: From<T>,
{
    type Output = Self;

    fn add(self, rhs: T) -> Self::Output {
        let rhs = Rational::from(rhs);
        let denominator = self.denominator * rhs.denominator;

        Rational::new::<i128, i128>(
            self.numerator * rhs.denominator + rhs.numerator * self.denominator,
            denominator,
        )
    }
}

impl<T> AddAssign<T> for Rational
where
    Rational: From<T>,
{
    fn add_assign(&mut self, rhs: T) {
        let result = *self + rhs;
        *self = result;
    }
}

impl<T> Sub<T> for Rational
where
    Rational: From<T>,
{
    type Output = Self;

    fn sub(self, rhs: T) -> Self::Output {
        let rhs = Rational::from(rhs);
        Add::<Rational>::add(self, Neg::neg(rhs))
    }
}

impl<T> SubAssign<T> for Rational
where
    Rational: From<T>,
{
    fn sub_assign(&mut self, rhs: T) {
        let result = *self - rhs;
        *self = result;
    }
}

impl Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self * -1
    }
}

impl PartialEq for Rational {
    fn eq(&self, rhs: &Rational) -> bool {
        self.numerator * rhs.denominator == rhs.numerator * self.denominator
    }
}

impl Eq for Rational {}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let num1 = self.numerator * other.denominator;
        let num2 = self.denominator * other.numerator;
        num1.cmp(&num2)
    }
}

impl From<Rational> for f64 {
    fn from(rat: Rational) -> f64 {
        (rat.numerator as f64) / (rat.denominator as f64)
    }
}

impl Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extras::*;

    #[test]
    fn addition_test() {
        let left = Rational::new(1, 2);

        assert_eq!(left + Rational::new(3, 1), Rational::new(7, 2));
        assert_eq!(left + 10_u8, Rational::new(21, 2));
        assert_eq!(left + 217_u16, Rational::new(435, 2));

        let mut left = r(1, 2);
        left += 5;
        assert_eq!(left, r(11, 2));
        left += r(1, 2);
        assert_eq!(left, r(6, 1));
    }

    #[test]
    fn subtraction_test() {
        let left = Rational::new(4, 3);
        let right = Rational::new(1, 2);
        assert_eq!(left - right, Rational::new(5, 6))
    }

    #[test]
    fn multiplication_test() {
        let left = Rational::new(5, 9);
        let right = Rational::new(10, 31);
        assert_eq!(left * right, Rational::new(50, 279));

        let left = Rational::new(-5, 10);
        let right = Rational::new(100, 10);
        assert_eq!(left * right, Rational::new(-5, 1));
    }

    #[test]
    fn division_test() {
        let left = Rational::new(5, 9);
        let right = Rational::new(10, 31);
        assert_eq!(left / right, Rational::new(31, 18));
    }

    #[test]
    fn negation_test() {
        let rat = r(5, 9);
        assert_eq!(-rat, r(-5, 9));
    }

    #[test]
    fn equality_test() {
        let left = Rational::new(4, 8);
        let right = Rational::new(16, 32);
        assert_eq!(left, right);
    }

    #[test]
    fn ctor_test() {
        let rat = Rational::new(Rational::new(1, 2), Rational::new(2, 4));
        assert_eq!(rat, Rational::new(1, 1));

        let rat = Rational::new(Rational::new(1, 2), 3);
        assert_eq!(rat, Rational::new(1, 6));
    }

    #[test]
    fn inverse_test() {
        let inverse = Rational::new(5, 7).inverse();
        assert_eq!(inverse, Rational::new(7, 5));
    }

    #[test]
    fn ordering_test() {
        let left = Rational::new(127, 298);
        let right = Rational::new(10, 11);
        assert!(left < right);
    }

    #[test]
    fn readme_test() {
        // all rationals are automatically reduced when created, so equality works as following:
        let one_half = Rational::new(1, 2);
        let two_quarters = Rational::new(2, 4);
        assert_eq!(one_half, two_quarters);

        // you can make more complicated rationals:
        let one_half_over_one_quarter = Rational::new(Rational::new(1, 2), Rational::new(1, 4)); // (1/2)/(1/4)
        assert_eq!(one_half_over_one_quarter, Rational::new(2, 1));

        // mathematical ops are implemented:
        let sum = Rational::new(1, 9) + Rational::new(5, 4);
        assert_eq!(sum, Rational::new(49, 36));

        // can get the inverse of a rational:
        let orig = Rational::new(80, 20);
        let inverse = orig.inverse();
        assert_eq!(inverse, Rational::new(20, 80));
        assert_eq!(inverse, Rational::new(1, orig));
    }
}
