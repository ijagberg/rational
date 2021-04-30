/// Contains some helper functions that can be useful.
pub mod extras;

use extras::gcd;
use std::{
    fmt::Display,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

/// A rational number (a fraction of two integers).
#[derive(Copy, Clone, Debug, Hash)]
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
        Self::new_checked(numerator, denominator).expect("denominator can't be 0")
    }

    /// Construct a new Rational, returning `None` if the denominator is 0.
    pub fn new_checked<N, D>(numerator: N, denominator: D) -> Option<Self>
    where
        Rational: From<N>,
        Rational: From<D>,
    {
        let numerator = Rational::from(numerator);
        let denominator = Rational::from(denominator);

        let mut num = numerator.numerator * denominator.denominator;
        let mut den = numerator.denominator * denominator.numerator;

        if den == 0 {
            return None;
        }

        match (num.is_negative(), den.is_negative()) {
            (true, true) => {
                num = -num;
                den = -den;
            }
            (false, true) => {
                num = -num;
                den = -den;
            }
            _ => (),
        }

        let mut this = Self {
            numerator: num,
            denominator: den,
        };
        this.reduce();
        Some(this)
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
        Self::new_checked(1, self)
    }

    /// Returns the inverse of this `Rational`.
    ///
    /// ## Panics
    /// * If the denominator of the inverse is 0.
    pub fn inverse(self) -> Self {
        Self::new(1, self)
    }

    /// Returns the decimal value of this `Rational`.
    /// Equivalent to `f64::from(self)`.
    pub fn decimal_value(self) -> f64 {
        f64::from(self)
    }

    pub fn checked_add<T>(self, other: T) -> Option<Self>
    where
        Self: From<T>,
    {
        let other = Self::from(other);
        let num_den = self.numerator.checked_mul(other.denominator)?;
        let den_num = self.denominator.checked_mul(other.numerator)?;
        let numerator = num_den.checked_add(den_num)?;

        let denominator = self.denominator.checked_mul(other.denominator)?;

        Some(Self::new::<i128, i128>(numerator, denominator))
    }

    pub fn checked_mul<T>(self, other: T) -> Option<Self>
    where
        Self: From<T>,
    {
        let other = Self::from(other);
        let numerator = self.numerator.checked_mul(other.numerator)?;
        let denominator = self.denominator.checked_mul(other.denominator)?;
        Some(Self::new::<i128, i128>(numerator, denominator))
    }

    pub fn checked_sub<T>(self, other: T) -> Option<Self>
    where
        Self: From<T>,
    {
        let other = Self::from(other);
        self.checked_add::<Rational>(-other)
    }

    pub fn checked_div<T>(self, other: T) -> Option<Self>
    where
        Self: From<T>,
    {
        let other = Self::from(other);
        let numerator = self.numerator.checked_mul(other.denominator)?;
        let denominator = self.denominator.checked_mul(other.numerator)?;
        Some(Self::new::<i128, i128>(numerator, denominator))
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
        Rational::new::<Rational, Rational>(self, rhs)
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
        let num_den_gcd = gcd(self.numerator, rhs.denominator);
        let den_num_gcd = gcd(self.denominator, rhs.numerator);
        let numerator = (self.numerator / num_den_gcd) * (rhs.numerator / den_num_gcd);
        let denominator = (self.denominator / den_num_gcd) * (rhs.denominator / num_den_gcd);

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
        match self.cmp(rhs) {
            std::cmp::Ordering::Equal => true,
            _ => false,
        }
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
        let num1 = self.numerator.checked_mul(other.denominator);
        let num2 = self.denominator.checked_mul(other.numerator);
        match (num1, num2) {
            (Some(num1), Some(num2)) => num1.cmp(&num2),
            _ => self
                .decimal_value()
                .partial_cmp(&other.decimal_value())
                .unwrap(),
        }
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
    use rand;
    use std::collections::HashMap;

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

        let invalid = Rational::new_checked(1, 0);
        assert!(invalid.is_none());
    }

    #[test]
    fn inverse_test() {
        let inverse = Rational::new(5, 7).inverse();
        assert_eq!(inverse, Rational::new(7, 5));

        let invalid_inverse = Rational::new(0, 1);
        assert!(invalid_inverse.inverse_checked().is_none());
    }

    #[test]
    fn ordering_test() {
        let left = Rational::new(127, 298);
        let right = Rational::new(10, 11);
        assert!(left < right);
    }

    #[test]
    fn hash_test() {
        let key1 = Rational::new(1, 2);
        let mut map = HashMap::new();

        map.insert(key1, "exists");

        assert_eq!(map.get(&Rational::new(2, 4)).unwrap(), &"exists");
        assert!(map.get(&Rational::new(1, 3)).is_none());
    }

    #[test]
    fn overflow_test() {
        #![allow(arithmetic_overflow)]
        let a = 125_i8 * 64_i8;
        let b = 121_i8 * 121_i8;
        dbg!(a, b);
        assert!(false);
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

    #[test]
    fn fuzz_test() {
        for _ in 0..500_000 {
            let (a, b) = (random_rat(), random_rat());
            assert_eq!(
                a.partial_cmp(&b),
                a.decimal_value().partial_cmp(&b.decimal_value())
            );
        }
    }

    fn random_rat() -> Rational {
        Rational::new(rand::random::<i128>(), rand::random::<i128>())
    }
}
