use crate::{ParseRationalError, Rational};
use num_traits::{
    CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedSub, FromPrimitive, Inv, Num, One, Pow,
    Signed, Zero,
};

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
        return Rational::zero();
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
}
