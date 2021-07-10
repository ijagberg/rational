pub mod extras;
mod ops;

use extras::gcd;
use std::fmt::Display;

/// A rational number (a fraction of two integers).
#[derive(Copy, Clone, Debug, Hash, PartialEq)]
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

        if den.is_negative() {
            // if both are negative, then both should be positive (reduce the -1 factor)
            // if only the denominator is negative, then move the -1 factor to the numerator for aesthetics
            num = -num;
            den = -den;
        }

        let mut this = Self {
            numerator: num,
            denominator: den,
        };
        this.reduce();
        Some(this)
    }

    /// Create a `Rational` from a mixed fraction.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert_eq!(Rational::from_mixed(1, (1, 2)), Rational::new(3, 2));
    /// ```
    pub fn from_mixed<T>(whole: i128, fract: T) -> Rational
    where
        Rational: From<T>,
    {
        let fract = Rational::from(fract);
        if whole.is_negative() {
            Rational::integer(whole) - fract
        } else {
            Rational::integer(whole) + fract
        }
    }

    pub fn integer(n: i128) -> Self {
        Rational::new(n, 1)
    }

    pub fn zero() -> Self {
        Rational::integer(0)
    }

    pub fn one() -> Self {
        Rational::integer(1)
    }

    /// Get the numerator in this `Rational`.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// let r = Rational::new(4, 6);
    /// assert_eq!(r.numerator(), 2); // `r` has been reduced to 2/3
    /// ```
    pub fn numerator(&self) -> i128 {
        self.numerator
    }

    /// Set the numerator of this `Rational`. It is then automatically reduced.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// let mut r = Rational::new(4, 5);
    /// r.set_numerator(10);
    /// assert_eq!(r, Rational::new(2, 1));
    /// ```
    pub fn set_numerator(&mut self, numerator: i128) {
        self.numerator = numerator;
        self.reduce();
    }

    /// Get the denominator in this `Rational`.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// let r = Rational::new(4, 6);
    /// assert_eq!(r.denominator(), 3); // `r` has been reduced to 2/3
    /// ```
    pub fn denominator(&self) -> i128 {
        self.denominator
    }

    /// Set the denominator of this `Rational`. It is then automatically reduced.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// let mut r = Rational::new(4, 5);
    /// r.set_denominator(6);
    /// assert_eq!(r, Rational::new(2, 3));
    /// ```
    pub fn set_denominator(&mut self, denominator: i128) {
        self.denominator = denominator;
        self.reduce();
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

    /// Returns `true` if `self` is an integer.
    /// This is a shorthand for `self.denominator() == 1`.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert!(Rational::new(2, 1).is_integer());
    /// assert!(!Rational::new(1, 2).is_integer());
    /// ```
    pub fn is_integer(&self) -> bool {
        self.denominator() == 1
    }

    /// Returns `true` if `self` is negative.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert!(Rational::new(-1, 2).is_negative());
    /// assert!(Rational::new(1, -2).is_negative());
    /// assert!(!Rational::new(1, 2).is_negative());
    /// ```
    pub fn is_negative(&self) -> bool {
        self.numerator().is_negative()
    }

    /// Returns a tuple representing `self` as a [mixed fraction](https://en.wikipedia.org/wiki/Fraction#Mixed_numbers).
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert_eq!(Rational::new(7, 3).mixed_fraction(), (2, Rational::new(1, 3)));
    /// // the fractional part is always positive:
    /// assert_eq!(Rational::new(-3, 2).mixed_fraction(), (-1, Rational::new(1, 2)));
    /// ```
    pub fn mixed_fraction(self) -> (i128, Rational) {
        let rem = self.numerator() % self.denominator();
        let whole = self.numerator() / self.denominator();
        let mut fract = Rational::new(rem, self.denominator());
        if whole.is_negative() && fract.is_negative() {
            fract = -fract;
        }
        (whole, fract)
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

impl<T, U> From<(T, U)> for Rational
where
    Rational: From<T>,
    Rational: From<U>,
{
    fn from((n, d): (T, U)) -> Self {
        let n = Rational::from(n);
        let d = Rational::from(d);

        Rational::new(n, d)
    }
}

impl Eq for Rational {}

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

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
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
    #![allow(unused)]

    use super::*;
    use crate::extras::*;
    use rand;
    use std::collections::HashMap;

    fn assert_eq_rat<Actual, Expected>(actual: Actual, expected: Expected)
    where
        Rational: From<Actual>,
        Rational: From<Expected>,
    {
        let actual = Rational::from(actual);
        let expected = Rational::from(expected);
        assert_eq!(actual, expected);
    }

    fn assert_ne_rat<Actual, Expected>(actual: Actual, expected: Expected)
    where
        Rational: From<Actual>,
        Rational: From<Expected>,
    {
        let actual = Rational::from(actual);
        let expected = Rational::from(expected);
        assert_ne!(actual, expected);
    }

    #[test]
    fn equality_test() {
        assert_eq_rat((4, 8), (16, 32));
        assert_eq_rat((2, 3), (4, 6));
        assert_ne_rat((-1, 2), (1, 2));
    }

    #[test]
    fn ctor_test() {
        let rat = Rational::new((1, 2), (2, 4));
        assert_eq_rat(rat, (1, 1));

        let rat = Rational::new((1, 2), 3);
        assert_eq_rat(rat, (1, 6));

        let rat = Rational::new((1, 2), (2, 1));
        assert_eq_rat(rat, (1, 4));

        let invalid = Rational::new_checked(1, 0);
        assert!(invalid.is_none());
    }

    #[test]
    fn inverse_test() {
        let inverse = Rational::new(5, 7).inverse();
        assert_eq_rat(inverse, (7, 5));

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
        // for _ in 0..500_000 {
        //     let (a, b) = (random_rat(), random_rat());
        //     assert_eq!(
        //         a.partial_cmp(&b),
        //         a.decimal_value().partial_cmp(&b.decimal_value())
        //     );
        // }
    }

    #[test]
    fn set_denominator_test() {
        let mut rat = Rational::new(1, 6);
        rat.set_numerator(2);

        assert_eq!(rat, Rational::new(1, 3));
    }

    #[test]
    fn set_numerator_test() {
        let mut rat = Rational::new(2, 3);
        rat.set_denominator(4);

        assert_eq!(rat, Rational::new(1, 2));
    }

    #[test]
    fn mixed_fraction_test() {
        let assert = |num: i128, den: i128, whole: i128, (n, d): (i128, i128)| {
            let rat = Rational::new(num, den);
            let actual_mixed_fraction = rat.mixed_fraction();
            let expected_mixed_fraction = (whole, Rational::new(n, d));
            assert_eq!(
                actual_mixed_fraction,
                (whole, Rational::new(n, d)),
                "num: {}, den: {}",
                num,
                den
            );
        };

        assert(4, 3, 1, (1, 3));
        assert(4, 4, 1, (0, 1));
        assert(-3, 2, -1, (1, 2));
        assert(10, 6, 1, (2, 3));
    }

    #[test]
    fn from_mixed_test() {
        assert_eq!(Rational::from_mixed(3, (1, 2)), Rational::new(7, 2));
        assert_eq!(Rational::from_mixed(0, (1, 2)), Rational::new(1, 2));
    }

    fn random_rat() -> Rational {
        let den = loop {
            // generate a random non-zero integer
            let den: i128 = rand::random();
            if den != 0 {
                break den;
            }
        };
        Rational::new(rand::random::<i128>(), den)
    }
}
