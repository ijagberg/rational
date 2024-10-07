//! An implementation of [rational numbers](https://en.wikipedia.org/wiki/Rational_number) and operations.

pub mod extras;
mod ops;

#[cfg(feature = "num-traits")]
mod num;

use extras::gcd;
use std::{
    fmt::{self, Display},
    str::FromStr,
};

/// Error/panic message to return when constructing a `Rational` where the
/// denominator is equal to 0.
const DENOMINATOR_CANT_BE_ZERO: &str = "denominator can't be zero";

/// A rational number (a fraction of two integers).
#[derive(Copy, Clone, Debug, Hash, PartialEq)]
pub struct Rational {
    /// The numerator of this `Rational`.
    numerator: i128,
    /// The denominator of this `Rational`.
    denominator: i128,
}

impl Rational {
    fn construct_and_reduce(mut num: i128, mut den: i128) -> Self {
        if den.is_negative() {
            // if both are negative, then both should be positive (reduce the -1 factor)
            // if only the denominator is negative, then move the -1 factor to the numerator for aesthetics
            num = -num;
            den = -den;
        }

        let mut this = Self::raw(num, den);
        this.reduce();
        this
    }

    /// Create a new Rational without checking that `denominator` is non-zero, or reducing the Rational afterwards.
    fn raw(numerator: i128, denominator: i128) -> Self {
        Self {
            numerator,
            denominator,
        }
    }

    /// Construct a new Rational.
    ///
    /// ## Panics
    /// * If the resulting denominator is 0.
    pub fn new<N, D>(numerator: N, denominator: D) -> Self
    where
        N: Into<Self>,
        D: Into<Self>,
    {
        Self::new_checked(numerator, denominator).expect(DENOMINATOR_CANT_BE_ZERO)
    }

    /// Construct a new Rational, returning `None` if the denominator is 0.
    pub fn new_checked<N, D>(numerator: N, denominator: D) -> Option<Self>
    where
        N: Into<Self>,
        D: Into<Self>,
    {
        let numerator: Self = numerator.into();
        let denominator: Self = denominator.into();

        let num = numerator.numerator() * denominator.denominator();
        let den = numerator.denominator() * denominator.numerator();

        if den == 0 {
            return None;
        }

        let this = Self::construct_and_reduce(num, den);

        Some(this)
    }

    /// Create a `Rational` from a [mixed fraction](https://en.wikipedia.org/wiki/Fraction#Mixed_numbers).
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert_eq!(Rational::from_mixed(1, (1, 2)), Rational::new(3, 2));
    /// assert_eq!(Rational::from_mixed(-1, (-1, 2)), Rational::new(-3, 2));
    /// ```
    pub fn from_mixed<T>(whole: i128, fract: T) -> Self
    where
        T: Into<Self>,
    {
        let fract: Self = fract.into();
        Self::integer(whole) + fract
    }

    /// Shorthand for creating an integer `Rational`, eg. 5/1.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::integer(5), Rational::new(5, 1));
    /// assert_eq!(Rational::integer(-100), Rational::new(-100, 1));
    /// ```
    pub fn integer(n: i128) -> Self {
        // use 'raw' since an integer is always already reduced
        Self::raw(n, 1)
    }

    /// Shorthand for 0/1.
    pub fn zero() -> Self {
        Self::integer(0)
    }

    /// Shorthand for 1/1.
    pub fn one() -> Self {
        Self::integer(1)
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
    /// assert_eq!(r, Rational::new(2, 1)); // 10/5 reduces to 2/1
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
    /// ## Panics
    /// * If `denominator` is 0.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// let mut r = Rational::new(4, 5);
    /// r.set_denominator(6);
    /// assert_eq!(r, Rational::new(2, 3));
    /// ```
    pub fn set_denominator(&mut self, denominator: i128) {
        if denominator == 0 {
            panic!("{}", DENOMINATOR_CANT_BE_ZERO);
        }

        self.denominator = denominator;
        self.reduce();
    }

    /// Returns the inverse of this `Rational`, or `None` if the denominator of the inverse is 0.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// let r = Rational::new(1, 2);
    /// assert_eq!(r.inverse_checked(), Some(Rational::new(2, 1)));
    /// let zero = Rational::new(0, 1);
    /// assert!(zero.inverse_checked().is_none());
    /// ```
    pub fn inverse_checked(self) -> Option<Self> {
        if self.numerator() == 0 {
            None
        } else {
            let (num, den) = if self.numerator().is_negative() {
                (-self.denominator(), -self.numerator())
            } else {
                (self.denominator(), self.numerator())
            };
            // since all rationals are automatically reduced,
            // we can just swap the numerator and denominator
            // without calculating their GCD's again
            Some(Self::construct_and_reduce(num, den))
        }
    }

    /// Returns the inverse of this `Rational`.
    ///
    /// ## Panics
    /// * If the numerator is 0, since then the inverse will be divided by 0.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(1, 2).inverse(), Rational::new(2, 1));
    /// ```
    pub fn inverse(self) -> Self {
        Self::new(1, self)
    }

    /// Returns the decimal value of this `Rational`.
    /// Equivalent to `f64::from(self)`.
    pub fn decimal_value(self) -> f64 {
        f64::from(self)
    }

    /// Checked addition. Computes `self + rhs`, returning `None` if overflow occurred.
    ///
    /// ## Notes
    /// Keep in mind that there are various operations performed in order to add two rational numbers,
    /// which may lead to overflow for rationals with very large numerators or denominators, even though the rational number
    /// itself may be small.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(1, 2).checked_add(Rational::new(2, 3)), Some(Rational::new(7, 6)));
    /// assert_eq!(Rational::new(1, 2).checked_add(2_i32), Some(Rational::new(5, 2)));
    /// assert!(Rational::new(1, 1).checked_add(i128::MAX).is_none());
    /// ```
    pub fn checked_add<T>(self, rhs: T) -> Option<Self>
    where
        T: Into<Self>,
    {
        let rhs: Self = rhs.into();
        let gcd = gcd(self.denominator(), rhs.denominator());
        let lcm = self
            .denominator()
            .abs()
            .checked_mul(rhs.denominator().abs().checked_div(gcd)?)?;

        let num1 = self
            .numerator()
            .checked_mul(lcm.checked_div(self.denominator())?)?;
        let num2 = rhs
            .numerator()
            .checked_mul(lcm.checked_div(rhs.denominator())?)?;

        let num = num1.checked_add(num2)?;
        Some(Rational::new::<i128, i128>(num, lcm))
    }

    /// Checked multiplication. Computes `self * rhs`, returning `None` if overflow occurred.
    ///
    /// ## Notes
    /// Keep in mind that there are various operations performed in order to multiply two rational numbers,
    /// which may lead to overflow for rationals with very large numerators or denominators, even though the rational number
    /// itself may be small.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(1, 2).checked_mul(Rational::new(2, 3)), Some(Rational::new(1, 3)));
    /// assert_eq!(Rational::new(1, 2).checked_mul(2_i32), Some(Rational::new(1, 1)));
    /// assert!(Rational::new(2, 1).checked_mul(i128::MAX).is_none());
    /// ```
    pub fn checked_mul<T>(self, rhs: T) -> Option<Self>
    where
        T: Into<Self>,
    {
        let rhs: Self = rhs.into();
        let (self_num, self_den) = (self.numerator(), self.denominator());
        let (rhs_num, rhs_den) = (rhs.numerator(), rhs.denominator());
        let num_den_gcd = gcd(self_num, rhs_den);
        let den_num_gcd = gcd(self_den, rhs_num);
        let numerator = self_num
            .checked_div(num_den_gcd)?
            .checked_mul(rhs_num.checked_div(den_num_gcd)?)?;
        let denominator = self_den
            .checked_div(den_num_gcd)?
            .checked_mul(rhs_den.checked_div(num_den_gcd)?)?;

        Some(Rational::raw(numerator, denominator))
    }

    /// Checked subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
    ///
    /// ## Notes
    /// Keep in mind that there are various operations performed in order to subtract two rational numbers,
    /// which may lead to overflow for rationals with very large numerators or denominators, even though the rational number
    /// itself may be small.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(1, 2).checked_sub(Rational::new(2, 3)), Some(Rational::new(-1, 6)));
    /// assert_eq!(Rational::new(1, 2).checked_sub(2_i32), Some(Rational::new(-3, 2)));
    /// assert!(Rational::new(-10, 1).checked_sub(i128::MAX).is_none());
    /// ```
    pub fn checked_sub<T>(self, rhs: T) -> Option<Self>
    where
        T: Into<Self>,
    {
        let rhs: Self = rhs.into();
        self.checked_add::<Rational>(-rhs)
    }

    /// Checked division. Computes `self / rhs`, returning `None` if overflow occurred.
    ///
    /// ## Panics
    /// * If `rhs == 0`
    ///
    /// ## Notes
    /// Keep in mind that there are various operations performed in order to divide two rational numbers,
    /// which may lead to overflow for rationals with very large numerators or denominators, even though the rational number
    /// itself may be small.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(1, 2).checked_div(Rational::new(2, 3)), Some(Rational::new(3, 4)));
    /// assert_eq!(Rational::new(1, 2).checked_div(2_i32), Some(Rational::new(1, 4)));
    /// assert!(Rational::new(1, i128::MAX).checked_div(i128::MAX).is_none());
    /// ```
    pub fn checked_div<T>(self, rhs: T) -> Option<Self>
    where
        T: Into<Self>,
    {
        let rhs: Self = rhs.into();
        self.checked_mul::<Rational>(rhs.inverse())
    }

    /// Computes `self^exp`.
    ///
    /// ## Notes
    /// Unlike the `pow` methods in `std`, this supports negative exponents, returning the inverse of the result.
    /// The exponent still needs to be an integer, since a rational number raised to the power of another rational number may be irrational.
    ///
    /// ## Panics
    /// * If the numerator is 0 and `exp` is negative (since a negative exponent will result in an inversed fraction).
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert_eq!(Rational::new(2, 3).pow(2), Rational::new(4, 9));
    /// assert_eq!(Rational::new(1, 4).pow(-2), Rational::new(16, 1));
    /// ```
    pub fn pow(self, exp: i32) -> Rational {
        let abs = exp.unsigned_abs();
        let result =
            Self::construct_and_reduce(self.numerator().pow(abs), self.denominator().pow(abs));
        if exp.is_negative() {
            result.inverse()
        } else {
            result
        }
    }

    /// Checked exponentiation. Computes `self^exp`, returning `None` if overflow occurred.
    ///
    /// ## Notes
    /// Unlike the `pow` methods in `std`, this supports negative exponents, returning the inverse of the result.
    /// The exponent still needs to be an integer, since a rational number raised to the power of another rational number may be irrational.
    ///
    /// ## Panics
    /// * If the numerator is 0 and `exp` is negative (since a negative exponent will result in an inversed fraction).
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert_eq!(Rational::new(2, 3).pow(2), Rational::new(4, 9));
    /// assert_eq!(Rational::new(1, 4).pow(-2), Rational::new(16, 1));
    /// ```
    pub fn checked_pow(self, exp: i32) -> Option<Self> {
        if self == Self::zero() && exp.is_negative() {
            return None;
        }

        let abs = exp.unsigned_abs();
        let num = self.numerator().checked_pow(abs)?;
        let den = self.denominator().checked_pow(abs)?;
        let result = Self::construct_and_reduce(num, den);
        if exp.is_negative() {
            Some(result.inverse())
        } else {
            Some(result)
        }
    }

    /// Checked negation. Computes `-self`, returning `None` if overflow occurred.
    ///
    /// ## Notes
    /// This only returns `None` if `self.numerator() == i128::MIN`.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(1, 2).checked_neg(), Some(Rational::new(-1, 2)));
    /// assert_eq!(Rational::new(-1, 2).checked_neg(), Some(Rational::new(1, 2)));
    /// assert_eq!(Rational::new(i128::MIN, 1).checked_neg(), None);
    /// ```
    pub fn checked_neg(self) -> Option<Self> {
        if self.numerator() == i128::MIN {
            None
        } else {
            Some(-self)
        }
    }

    /// Computes the absolute value of `self`.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert_eq!(Rational::new(-5, 3).abs(), Rational::new(5, 3));
    /// ```
    pub fn abs(self) -> Self {
        // use `raw` since we know neither numerator or denominator will be negative
        Self::raw(self.numerator.abs(), self.denominator)
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

    /// Returns `true` if `self` is positive and `false` if it is zero or negative.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert!(Rational::new(1, 2).is_positive());
    /// assert!(Rational::new(-1, -2).is_positive());
    /// assert!(!Rational::new(-1, 2).is_positive());
    /// assert!(!Rational::zero().is_positive());
    /// ```
    pub fn is_positive(&self) -> bool {
        self.numerator().is_positive()
    }

    /// Returns `true` if `self` is negative and `false` if it is zero or positive.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert!(Rational::new(-1, 2).is_negative());
    /// assert!(Rational::new(1, -2).is_negative());
    /// assert!(!Rational::zero().is_negative());
    /// ```
    pub fn is_negative(&self) -> bool {
        self.numerator().is_negative()
    }

    /// Returns a tuple representing `self` as a [mixed fraction](https://en.wikipedia.org/wiki/Fraction#Mixed_numbers).
    ///
    /// ## Notes
    /// The result is a tuple `(whole: i128, fraction: Rational)`, such that `whole + fraction == self`.
    /// This means that while you might write -7/2 as a mixed fraction: -3½, the result will be a tuple (-3, -1/2).
    ///
    /// ## Example
    /// ```rust
    /// # use rational::*;
    /// assert_eq!(Rational::new(7, 3).mixed_fraction(), (2, Rational::new(1, 3)));
    /// let (mixed, fract) = Rational::new(-7, 2).mixed_fraction();
    /// assert_eq!((mixed, fract), (-3, Rational::new(-1, 2)));
    /// assert_eq!(mixed + fract, Rational::new(-7, 2));
    /// ```
    pub fn mixed_fraction(self) -> (i128, Self) {
        let rem = self.numerator() % self.denominator();
        let whole = self.numerator() / self.denominator();
        let fract = Self::new(rem, self.denominator());
        debug_assert_eq!(whole + fract, self);
        (whole, fract)
    }

    /// Returns the nearest integer to `self`. If a value is half-way between two
    /// integers, round away from `0.0`.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(1, 2).round(), Rational::integer(1));
    /// assert_eq!(Rational::new(-1, 2).round(), Rational::integer(-1));
    /// ```
    pub fn round(self) -> Self {
        if self.is_positive() {
            let left = Self::integer(self.numerator() / self.denominator());
            let right = left + 1;
            let dist_to_left = self - left;
            let dist_to_right = right - self;

            if dist_to_right <= dist_to_left {
                right
            } else {
                left
            }
        } else if self.is_negative() {
            let right = Self::integer(self.numerator() / self.denominator());
            let left = right - 1;
            let dist_to_left = self - left;
            let dist_to_right = right - self;

            if dist_to_left <= dist_to_right {
                left
            } else {
                right
            }
        } else {
            self
        }
    }

    /// Returns the largest integer less than or equal to self.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(4, 3).floor(), Rational::integer(1));
    /// assert_eq!(Rational::new(-3, 2).floor(), Rational::integer(-2));
    /// ```
    pub fn floor(self) -> Self {
        let r = Self::integer(self.numerator() / self.denominator());
        if self.is_negative() && self != r {
            r - 1
        } else {
            r
        }
    }

    /// Returns the smallest integer greater than or equal to self.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    /// assert_eq!(Rational::new(4, 3).ceil(), Rational::integer(2));
    /// assert_eq!(Rational::new(-3, 2).ceil(), Rational::integer(-1));
    /// ```
    pub fn ceil(self) -> Self {
        let r = Self::integer(self.numerator() / self.denominator());
        if self.is_positive() && self != r {
            r + 1
        } else {
            r
        }
    }

    /// Converts a string slice in a given base to a `Rational`.
    ///
    /// The string is expected be in one of the following two forms:
    /// * `"x/y"`, where `x` and `y` follow the format expected by the `from_str_radix` methods in the standard library.
    /// * `"x"`, where `x` follows the format expected by the `from_str_radix` methods in the standard library.
    ///
    /// ## Panics
    /// * If `radix` is not in the range from 2 to 36.
    ///
    /// ## Examples
    /// ```rust
    /// # use rational::Rational;
    /// # use rational::ParseRationalError;
    /// assert_eq!(Rational::from_str_radix("1/2", 10), Ok(Rational::new(1, 2)));
    /// assert_eq!(Rational::from_str_radix("110", 2), Ok(Rational::integer(6)));
    /// assert_eq!(Rational::from_str_radix("-1", 10), Ok(Rational::integer(-1)));
    /// assert_eq!(Rational::from_str_radix("1/-2", 10), Ok(Rational::new(-1, 2)));
    /// assert_eq!(Rational::from_str_radix("1/0", 10), Err(ParseRationalError::DenominatorIsZero));
    /// assert!(matches!(Rational::from_str_radix("1/1a", 10), Err(ParseRationalError::ParseIntError(_))));
    /// ```
    pub fn from_str_radix(s: &str, radix: u32) -> Result<Self, ParseRationalError> {
        match s.split_once('/') {
            Some((num, den)) => {
                let num =
                    i128::from_str_radix(num, radix).map_err(ParseRationalError::ParseIntError)?;
                let den =
                    i128::from_str_radix(den, radix).map_err(ParseRationalError::ParseIntError)?;
                if den == 0 {
                    return Err(ParseRationalError::DenominatorIsZero);
                }
                Ok(Self::new(num, den))
            }
            None => {
                let num =
                    i128::from_str_radix(s, radix).map_err(ParseRationalError::ParseIntError)?;
                Ok(Self::integer(num))
            }
        }
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
                Rational::raw(v as i128, 1)
            }
        }

        impl From<&$type> for Rational {
            fn from(v: &$type) -> Self {
                Rational::raw(*v as i128, 1)
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

impl<T, U> From<(T, U)> for Rational
where
    T: Into<Rational>,
    U: Into<Rational>,
{
    fn from((n, d): (T, U)) -> Self {
        let n: Self = n.into();
        let d: Self = d.into();

        Self::new(n, d)
    }
}

impl From<Rational> for (i128, i128) {
    fn from(r: Rational) -> Self {
        (r.numerator(), r.denominator())
    }
}

impl Eq for Rational {}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        // simple test, if one of the numbers is negative and the other one is positive,
        // no algorithm is needed
        match (self.is_negative(), other.is_negative()) {
            (true, false) => {
                return Ordering::Less;
            }
            (false, true) => return Ordering::Greater,
            _ => (),
        }

        let mut a = *self;
        let mut b = *other;
        loop {
            let (q1, r1) = a.mixed_fraction();
            let (q2, r2) = b.mixed_fraction();
            match q1.cmp(&q2) {
                Ordering::Equal => match (r1.numerator() == 0, r2.numerator() == 0) {
                    (true, true) => {
                        // both remainders are zero, equal
                        return Ordering::Equal;
                    }
                    (true, false) => {
                        // left remainder is 0, so left is smaller than right
                        return Ordering::Less;
                    }
                    (false, true) => {
                        // right remainder is 0, so right is smaller than left
                        return Ordering::Greater;
                    }
                    (false, false) => {
                        a = r2.inverse();
                        b = r1.inverse();
                    }
                },
                other => {
                    return other;
                }
            }
        }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! impl_eq_integer {
    ($type:ty) => {
        impl PartialEq<$type> for Rational {
            fn eq(&self, other: &$type) -> bool {
                *self == Self::integer(*other as i128)
            }
        }

        impl PartialEq<Rational> for $type {
            fn eq(&self, other: &Rational) -> bool {
                Rational::integer(*self as i128) == *other
            }
        }
    };
}

macro_rules! impl_eq_float {
    ($type:ty) => {
        impl PartialEq<$type> for Rational {
            fn eq(&self, other: &$type) -> bool {
                self.decimal_value() == (*other as f64)
            }
        }

        impl PartialEq<Rational> for $type {
            fn eq(&self, other: &Rational) -> bool {
                (*self as f64) == other.decimal_value()
            }
        }
    };
}

impl_eq_integer!(i8);
impl_eq_integer!(i16);
impl_eq_integer!(i32);
impl_eq_integer!(i64);
impl_eq_integer!(i128);
impl_eq_integer!(u8);
impl_eq_integer!(u16);
impl_eq_integer!(u32);
impl_eq_integer!(u64);

impl_eq_float!(f32);
impl_eq_float!(f64);

macro_rules! impl_cmp_integer {
    ($type:ty) => {
        impl PartialOrd<$type> for Rational {
            fn partial_cmp(&self, other: &$type) -> Option<std::cmp::Ordering> {
                Some(self.cmp(&Self::integer(*other as i128)))
            }
        }

        impl PartialOrd<Rational> for $type {
            fn partial_cmp(&self, other: &Rational) -> Option<std::cmp::Ordering> {
                Some(Rational::integer(*self as i128).cmp(other))
            }
        }
    };
}

macro_rules! impl_cmp_float {
    ($type:ty) => {
        impl PartialOrd<$type> for Rational {
            fn partial_cmp(&self, other: &$type) -> Option<std::cmp::Ordering> {
                self.decimal_value().partial_cmp(&(*other as f64))
            }
        }

        impl PartialOrd<Rational> for $type {
            fn partial_cmp(&self, other: &Rational) -> Option<std::cmp::Ordering> {
                (*self as f64).partial_cmp(&other.decimal_value())
            }
        }
    };
}

impl_cmp_integer!(i8);
impl_cmp_integer!(i16);
impl_cmp_integer!(i32);
impl_cmp_integer!(i64);
impl_cmp_integer!(i128);
impl_cmp_integer!(u8);
impl_cmp_integer!(u16);
impl_cmp_integer!(u32);
impl_cmp_integer!(u64);

impl_cmp_float!(f32);
impl_cmp_float!(f64);

impl From<Rational> for f64 {
    fn from(rat: Rational) -> f64 {
        (rat.numerator() as f64) / (rat.denominator() as f64)
    }
}

impl Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

impl FromStr for Rational {
    type Err = ParseRationalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str_radix(s, 10)
    }
}

/// An error which can be returned when parsing a `Rational`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseRationalError {
    /// Denominator in `Rational` is zero.
    DenominatorIsZero,
    /// Failed to parse integer in input.
    ParseIntError(std::num::ParseIntError),
}

impl Display for ParseRationalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseRationalError::DenominatorIsZero => DENOMINATOR_CANT_BE_ZERO.fmt(f),
            ParseRationalError::ParseIntError(err) => err.fmt(f),
        }
    }
}

impl std::error::Error for ParseRationalError {}

#[cfg(test)]
#[allow(unused)]
mod tests {
    use super::*;
    use crate::extras::*;
    use std::{cmp::Ordering, collections::HashMap};

    fn assert_eq_rational<Actual, Expected>(actual: Actual, expected: Expected)
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
    fn cmp_test() {
        assert_eq_rational((4, 8), (16, 32));
        assert_eq_rational((2, 3), (4, 6));
        assert_ne_rat((-1, 2), (1, 2));
        assert_eq!(Rational::zero(), 0);
        assert!(Rational::integer(15) > 14);
        assert_eq!(Rational::new(1, 3), 1.0 / 3.0);
        assert_eq!(Rational::new(1, 2), 0.5);
        assert!(Rational::new(1, 3) < 0.333333334);
        assert!(1 < r(3, 2));
        assert!(r(3, 2) > 1);
    }

    #[test]
    fn ctor_test() {
        let r = Rational::new((1, 2), (2, 4));
        assert_eq_rational(r, (1, 1));

        let r = Rational::new((1, 2), 3);
        assert_eq_rational(r, (1, 6));

        let r = Rational::new((1, 2), (2, 1));
        assert_eq_rational(r, (1, 4));

        let invalid = Rational::new_checked(1, 0);
        assert!(invalid.is_none());

        let r = Rational::new(0, 5);
        assert_eq_rational(r, (0, 1));

        let r = Rational::new(0, -100);
        assert_eq_rational(r, (0, 1));

        let r = Rational::new(5, -2);
        assert_eq!(r.numerator, -5);
        assert_eq!(r.denominator, 2);
    }

    #[test]
    fn inverse_test() {
        let inverse = Rational::new(5, 7).inverse();
        assert_eq_rational(inverse, (7, 5));

        let invalid_inverse = Rational::new(0, 1);
        assert!(invalid_inverse.inverse_checked().is_none());

        let inverse = Rational::new(-5, 7).inverse();
        assert_eq!(inverse.numerator(), -7);
        assert_eq!(inverse.denominator(), 5);
    }

    #[test]
    fn ordering_test() {
        let assert = |(n1, d1): (i128, i128), (n2, d2): (i128, i128), ord: Ordering| {
            let left = Rational::new(n1, d1);
            let right = Rational::new(n2, d2);
            assert_eq!(left.cmp(&right), ord);
        };
        assert((127, 298), (10, 11), Ordering::Less);
        assert((355, 113), (22, 7), Ordering::Less);
        assert((-11, 2), (5, 4), Ordering::Less);
        assert((5, 4), (20, 16), Ordering::Equal);
        assert((7, 4), (14, 11), Ordering::Greater);
        assert((-1, 2), (1, -2), Ordering::Equal);

        for n in 0..100_000 {
            let r1 = random_rat();
            let r2 = random_rat();
            let result1 = r1.cmp(&r2);
            let result2 = r1.decimal_value().partial_cmp(&r2.decimal_value()).unwrap();

            assert_eq!(
                result1, result2,
                "r1: {}, r2: {}, result1: {:?}, result2: {:?}, n: {}",
                r1, r2, result1, result2, n
            );
        }
    }

    #[test]
    fn hash_test() {
        let key1 = Rational::new(1, 2);
        let mut map = HashMap::new();

        map.insert(key1, "exists");

        assert_eq!(map.get(&Rational::new(2, 4)).unwrap(), &"exists");
        assert!(!map.contains_key(&Rational::new(1, 3)));
    }

    #[test]
    fn readme_test() {
        // A minimal library for representing rational numbers.

        // ## Construction

        // Rationals are automatically reduced when created:
        let one_half = Rational::new(1, 2);
        let two_quarters = Rational::new(2, 4);
        assert_eq!(one_half, two_quarters);

        // `From` is implemented for integers and integer tuples:
        assert_eq!(Rational::from(1), Rational::new(1, 1));
        assert_eq!(Rational::from((1, 2)), Rational::new(1, 2));

        // The `new` method takes a numerator and denominator that implement `Into<Rational>`:
        let one_half_over_one_quarter = Rational::new((1, 2), (1, 4));
        assert_eq!(one_half_over_one_quarter, Rational::new(2, 1));

        // ## Mathematical operations

        // Operations and comparisons are implemented for Rationals and integers:
        let one_ninth = Rational::new(1, 9);
        assert_eq!(one_ninth + Rational::new(5, 4), Rational::new(49, 36));
        assert_eq!(one_ninth - 4, Rational::new(-35, 9));
        assert_eq!(one_ninth / Rational::new(21, 6), Rational::new(2, 63));
        assert!(one_ninth < Rational::new(1, 8));
        assert!(one_ninth < 1);

        // ## Other properties

        // Inverse:
        let eight_thirds = Rational::new(8, 3);
        let inverse = eight_thirds.inverse();
        assert_eq!(inverse, Rational::new(3, 8));

        // Mixed fractions:
        let (whole, fractional) = eight_thirds.mixed_fraction();
        assert_eq!(whole, 2);
        assert_eq!(fractional, Rational::new(2, 3));
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
    #[should_panic]
    fn set_denominator_panic_test() {
        let mut rat = Rational::new(1, 2);
        rat.set_denominator(0);
    }

    #[test]
    fn mixed_fraction_test() {
        let assert = |(num, den): (i128, i128), whole: i128, (n, d): (i128, i128)| {
            let rat = Rational::new(num, den);
            let actual_mixed_fraction = rat.mixed_fraction();
            let fract = Rational::new(n, d);
            let expected_mixed_fraction = (whole, fract);
            let sum_of_parts = whole + fract;
            assert_eq!(
                actual_mixed_fraction,
                (whole, Rational::new(n, d)),
                "num: {}, den: {}",
                num,
                den
            );
            assert_eq!(sum_of_parts, rat);
        };

        assert((4, 3), 1, (1, 3));
        assert((4, 4), 1, (0, 1));
        assert((-3, 2), -1, (-1, 2));
        assert((10, 6), 1, (2, 3));
        assert((0, 2), 0, (0, 1));
        assert((-95, 36), -2, (-23, 36));
    }

    #[test]
    fn from_mixed_test() {
        assert_eq!(Rational::from_mixed(3, (1, 2)), Rational::new(7, 2));
        assert_eq!(Rational::from_mixed(0, (1, 2)), Rational::new(1, 2));
    }

    #[test]
    fn tuple_from_rational_test() {
        assert_eq!((1, 5), Rational::new(1, 5).into());
        assert_eq!((1, 5), Rational::new(2, 10).into());
        assert_eq!((-1, 5), Rational::new(2, -10).into());
    }

    #[test]
    fn pow_test() {
        assert_eq!((1, 25), Rational::new(1, 5).pow(2).into());
        assert_eq!((1, 9), Rational::new(2, 6).pow(2).into());
        assert_eq!((1, 1), Rational::new(2, 6).pow(0).into());
        assert_eq!((16, 1), Rational::new(1, 4).pow(-2).into());

        assert!(Rational::new(i128::MAX - 5, 1)
            .checked_pow(i32::MAX)
            .is_none());
    }

    #[should_panic]
    #[test]
    fn pow_panic_test() {
        Rational::zero().pow(-1);
    }

    #[test]
    fn abs_test() {
        assert_eq!(Rational::new(0, 5).abs(), Rational::zero());
        assert_eq!(Rational::new(1, 2).abs(), Rational::new(1, 2));
        assert_eq!(Rational::new(-1, 2).abs(), Rational::new(1, 2));
        assert_eq!(Rational::new(1, -2).abs(), Rational::new(1, 2));
    }

    #[test]
    fn checked_add_test() {
        assert_eq!(r(1, 2).checked_add(r(3, 5)), Some(r(11, 10)));
        assert!(Rational::integer(i128::MAX)
            .checked_add(i128::MAX)
            .is_none());
    }

    #[test]
    fn checked_mul_test() {
        assert_eq!(r(1, 2).checked_mul(r(3, 5)), Some(r(3, 10)));
        assert!(Rational::integer(i128::MAX)
            .checked_mul(i128::MAX)
            .is_none());
    }

    #[test]
    fn round_test() {
        assert_eq!(r(1, 2).round(), r(1, 1));
        assert_eq!(r(-1, 2).round(), r(-1, 1));
        assert_eq!(r(7, 3).round(), r(2, 1));
        assert_eq!(r(111, 4).round(), r(28, 1));
        assert_eq!(r(0, 1).round(), r(0, 1));
        assert_eq!(r(4, 2).round(), r(2, 1));
    }

    #[test]
    fn floor_test() {
        assert_eq!(r(1, 2).floor(), 0);
        assert_eq!(r(0, 1).floor(), 0);
        assert_eq!(r(5, 1).floor(), 5);
        assert_eq!(r(-1, 2).floor(), -1);
    }

    #[test]
    fn ceil_test() {
        assert_eq!(r(1, 2).ceil(), 1);
        assert_eq!(r(0, 1).ceil(), 0);
        assert_eq!(r(-4, 3).ceil(), -1);
    }

    #[test]
    fn parse_rational_test() {
        assert_eq!("1/2".parse(), Ok(r(1, 2)));
        assert_eq!("12".parse(), Ok(r(12, 1)));
        assert!(" 1/2".parse::<Rational>().is_err());
        assert!("1//2".parse::<Rational>().is_err());
        assert!("1/222/".parse::<Rational>().is_err());
        assert!("1/222/3".parse::<Rational>().is_err());
        assert!("/2".parse::<Rational>().is_err());

        assert_eq!(Rational::from_str_radix("110", 2), Ok(Rational::new(6, 1)));
        assert_eq!(
            Rational::from_str_radix("110/111", 2),
            Ok(Rational::new(6, 7))
        );
        assert_eq!(
            Rational::from_str_radix("-1/-2", 10),
            Ok(Rational::new(1, 2))
        );
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
