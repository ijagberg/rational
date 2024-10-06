use crate::{ParseRationalError, Rational};
use num_traits::{
    CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedSub, Float, FromPrimitive, Inv, Num,
    One, Pow, Signed, Zero,
};

impl Rational {
    /// Attempts to construct a `Rational` from the given floating point value.
    ///
    /// Uses the `integer_decode` method from `num_traits`.
    ///
    /// ## Notes
    /// Returns `None` if `f` is not finite, or if integer overflow occurs during construction.
    /// This happens for values with large exponents, where `2^exponent` cannot fit in an `i128`.
    /// In these cases, I would recommend using the `num_rational` crate instead, which is slower but can handle arbitrary values.
    ///
    /// ## Example
    /// ```rust
    /// # use rational::Rational;
    ///
    /// assert_eq!(Rational::from_float(0.5), Some(Rational::new(1, 2)));
    /// assert_eq!(Rational::from_float(f64::INFINITY), None);
    /// assert_eq!(Rational::from_float(f64::MIN_POSITIVE), None); // requires more precision
    /// ```
    pub fn from_float(f: f64) -> Option<Self> {
        if !f.is_finite() {
            return None;
        }

        let (mantissa, exponent, sign) = f.integer_decode();
        if exponent.is_positive() {
            let numerator = i128::from(mantissa.checked_mul(2_u64.checked_pow(exponent as u32)?)?);
            Some(Self::integer(numerator) * sign)
        } else {
            let numerator = mantissa as i128;
            let denominator = 2i128.checked_pow((-exponent) as u32)?;
            Some(Self::new(numerator, denominator) * sign)
        }
    }
}

impl CheckedAdd for Rational {
    fn checked_add(&self, v: &Self) -> Option<Self> {
        (*self).checked_add(*v)
    }
}

impl CheckedDiv for Rational {
    fn checked_div(&self, v: &Self) -> Option<Self> {
        (*self).checked_div(*v)
    }
}

impl CheckedMul for Rational {
    fn checked_mul(&self, v: &Self) -> Option<Self> {
        (*self).checked_mul(*v)
    }
}

impl CheckedNeg for Rational {
    fn checked_neg(&self) -> Option<Self> {
        (*self).checked_neg()
    }
}

impl CheckedSub for Rational {
    fn checked_sub(&self, v: &Self) -> Option<Self> {
        (*self).checked_sub(*v)
    }
}

impl Inv for Rational {
    type Output = Rational;

    fn inv(self) -> Self::Output {
        self.inverse()
    }
}

impl One for Rational {
    fn one() -> Self {
        Self::one()
    }
}

impl Zero for Rational {
    fn zero() -> Self {
        Self::zero()
    }

    fn is_zero(&self) -> bool {
        *self == 0
    }
}

impl Pow<i32> for Rational {
    type Output = Self;

    fn pow(self, rhs: i32) -> Self::Output {
        self.pow(rhs)
    }
}

impl Num for Rational {
    type FromStrRadixErr = ParseRationalError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Self::from_str_radix(str, radix)
    }
}

impl Signed for Rational {
    fn abs(&self) -> Self {
        (*self).abs()
    }

    fn abs_sub(&self, other: &Self) -> Self {
        if self <= other {
            Self::zero()
        } else {
            *self - *other
        }
    }

    fn signum(&self) -> Self {
        if self.is_positive() {
            return Rational::one();
        }
        if self.is_negative() {
            return -Rational::one();
        }
        Rational::zero()
    }

    fn is_positive(&self) -> bool {
        self.is_positive()
    }

    fn is_negative(&self) -> bool {
        self.is_negative()
    }
}

impl FromPrimitive for Rational {
    fn from_i64(n: i64) -> Option<Self> {
        Some(Self::integer(n as i128))
    }

    fn from_u64(n: u64) -> Option<Self> {
        Some(Self::integer(n as i128))
    }

    fn from_i128(n: i128) -> Option<Self> {
        Some(Self::integer(n))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_float_test() {
        assert_eq!(Rational::from_float(0.5).unwrap(), Rational::new(1, 2));
        assert_eq!(Rational::from_float(2.0).unwrap(), Rational::new(2, 1));
        assert_eq!(
            Rational::from_float(-1.141514).unwrap().decimal_value(),
            -1.141514
        );
        assert_eq!(Rational::from_float(f64::NAN), None);
        assert_eq!(Rational::from_float(f64::INFINITY), None);
        assert_eq!(Rational::from_float(f64::NEG_INFINITY), None);
        assert_eq!(Rational::from_float(f64::MIN_POSITIVE), None);
        assert_eq!(Rational::from_float(f64::MIN), None);

        for f in (0..1_000_000).map(|_| rand::random::<f64>()) {
            let r = Rational::from_float(f).unwrap();
            let dec = r.decimal_value();
            assert_eq!(
                dec, f,
                "Rational::from_float({}) = {}, but decimal value is {}",
                f, r, dec
            );
        }
    }
}
