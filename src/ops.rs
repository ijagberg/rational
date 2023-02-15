use crate::{extras::*, Rational};
use std::{
    iter::{Product, Sum},
    ops::*,
};

impl Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        -1 * self
    }
}

impl Product for Rational {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Rational::one(), |a, b| a * b)
    }
}

impl Sum for Rational {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Rational::zero(), |a, b| a + b)
    }
}

mod add {
    use super::*;

    impl Add<Rational> for Rational {
        type Output = Rational;

        fn add(self, rhs: Rational) -> Self::Output {
            let den = self.denominator() * rhs.denominator();

            let num1 = self.numerator() * rhs.denominator();
            let num2 = rhs.numerator() * self.denominator();

            Rational::new(num1 + num2, den)
        }
    }

    impl AddAssign<Rational> for Rational {
        fn add_assign(&mut self, rhs: Rational) {
            let result = *self + rhs;
            *self = result
        }
    }

    macro_rules! impl_add {
        ($type:ty) => {
            impl Add<$type> for Rational {
                type Output = Rational;

                fn add(self, rhs: $type) -> Self {
                    self + Rational::from(rhs)
                }
            }

            impl Add<Rational> for $type {
                type Output = Rational;

                fn add(self, rhs: Rational) -> Rational {
                    rhs + self
                }
            }

            impl AddAssign<$type> for Rational {
                fn add_assign(&mut self, rhs: $type) {
                    let result = Add::<$type>::add(*self, rhs);
                    *self = result;
                }
            }
        };
    }

    impl_add!(u8);
    impl_add!(u16);
    impl_add!(u32);
    impl_add!(u64);
    impl_add!(i8);
    impl_add!(i16);
    impl_add!(i32);
    impl_add!(i64);
    impl_add!(i128);
}

mod mul {
    use super::*;

    impl Mul<Rational> for Rational {
        type Output = Rational;

        fn mul(self, rhs: Rational) -> Self::Output {
            let num_den_gcd = gcd(self.numerator, rhs.denominator);
            let den_num_gcd = gcd(self.denominator, rhs.numerator);
            let numerator = (self.numerator / num_den_gcd) * (rhs.numerator / den_num_gcd);
            let denominator = (self.denominator / den_num_gcd) * (rhs.denominator / num_den_gcd);

            Rational::new::<i128, i128>(numerator, denominator)
        }
    }

    impl MulAssign<Rational> for Rational {
        fn mul_assign(&mut self, rhs: Rational) {
            let result = *self * rhs;
            *self = result;
        }
    }

    macro_rules! impl_mul {
        ($type:ty) => {
            impl Mul<$type> for Rational {
                type Output = Rational;

                fn mul(self, rhs: $type) -> Rational {
                    self * Rational::from(rhs)
                }
            }

            impl Mul<Rational> for $type {
                type Output = Rational;

                fn mul(self, rhs: Rational) -> Rational {
                    rhs * self
                }
            }

            impl MulAssign<$type> for Rational {
                fn mul_assign(&mut self, rhs: $type) {
                    let result = Mul::<$type>::mul(*self, rhs);
                    *self = result;
                }
            }
        };
    }

    impl_mul!(u8);
    impl_mul!(u16);
    impl_mul!(u32);
    impl_mul!(u64);
    impl_mul!(i8);
    impl_mul!(i16);
    impl_mul!(i32);
    impl_mul!(i64);
    impl_mul!(i128);
}

mod sub {
    use super::*;

    impl Sub for Rational {
        type Output = Rational;

        fn sub(self, rhs: Rational) -> Rational {
            Add::<Rational>::add(self, Neg::neg(rhs))
        }
    }

    impl SubAssign for Rational {
        fn sub_assign(&mut self, rhs: Rational) {
            let result = *self - rhs;
            *self = result;
        }
    }

    macro_rules! impl_sub {
        ($type:ty) => {
            impl Sub<$type> for Rational {
                type Output = Rational;

                fn sub(self, rhs: $type) -> Rational {
                    self - Rational::from(rhs)
                }
            }

            impl Sub<Rational> for $type {
                type Output = Rational;

                fn sub(self, rhs: Rational) -> Rational {
                    rhs - self
                }
            }

            impl SubAssign<$type> for Rational {
                fn sub_assign(&mut self, rhs: $type) {
                    let result = Sub::<$type>::sub(*self, rhs);
                    *self = result;
                }
            }
        };
    }

    impl_sub!(u8);
    impl_sub!(u16);
    impl_sub!(u32);
    impl_sub!(u64);
    impl_sub!(i8);
    impl_sub!(i16);
    impl_sub!(i32);
    impl_sub!(i64);
    impl_sub!(i128);
}

mod div {
    use super::*;

    impl Div for Rational {
        type Output = Self;

        fn div(self, rhs: Rational) -> Self::Output {
            Rational::new::<Rational, Rational>(self, rhs)
        }
    }

    impl DivAssign for Rational {
        fn div_assign(&mut self, rhs: Rational) {
            let result = *self / rhs;
            *self = result;
        }
    }

    macro_rules! impl_div {
        ($type:ty) => {
            impl Div<$type> for Rational {
                type Output = Rational;

                fn div(self, rhs: $type) -> Rational {
                    self / Rational::from(rhs)
                }
            }

            impl Div<Rational> for $type {
                type Output = Rational;

                fn div(self, rhs: Rational) -> Rational {
                    rhs / self
                }
            }

            impl DivAssign<$type> for Rational {
                fn div_assign(&mut self, rhs: $type) {
                    let result = Div::<$type>::div(*self, rhs);
                    *self = result;
                }
            }
        };
    }

    impl_div!(u8);
    impl_div!(u16);
    impl_div!(u32);
    impl_div!(u64);
    impl_div!(i8);
    impl_div!(i16);
    impl_div!(i32);
    impl_div!(i64);
    impl_div!(i128);
}

mod rem {
    use super::*;

    impl Rem for Rational {
        type Output = Self;

        fn rem(self, rhs: Rational) -> Self::Output {
            let neg = self.is_negative();
            let a = if neg { self.abs() } else { self };
            let b = rhs.abs();
            let div = Div::<Rational>::div(a, b);
            let (_, mut fract) = div.mixed_fraction();

            if neg {
                fract = -fract;
            }

            Mul::<Rational>::mul(fract, b)
        }
    }

    impl RemAssign for Rational {
        fn rem_assign(&mut self, rhs: Rational) {
            let result = *self % rhs;
            *self = result;
        }
    }

    macro_rules! impl_rem {
        ($type:ty) => {
            impl Rem<$type> for Rational {
                type Output = Rational;

                fn rem(self, rhs: $type) -> Rational {
                    self % Rational::from(rhs)
                }
            }

            impl Rem<Rational> for $type {
                type Output = Rational;

                fn rem(self, rhs: Rational) -> Rational {
                    rhs % self
                }
            }

            impl RemAssign<$type> for Rational {
                fn rem_assign(&mut self, rhs: $type) {
                    let result = Rem::<$type>::rem(*self, rhs);
                    *self = result;
                }
            }
        };
    }

    impl_rem!(u8);
    impl_rem!(u16);
    impl_rem!(u32);
    impl_rem!(u64);
    impl_rem!(i8);
    impl_rem!(i16);
    impl_rem!(i32);
    impl_rem!(i64);
    impl_rem!(i128);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negation_test() {
        assert_eq!(-Rational::new(5, 9), Rational::new(-5, 9));
        assert_eq!(-Rational::new(-1, 2), Rational::new(1, 2));
        assert_eq!(-Rational::integer(100), Rational::integer(-100));
    }

    #[test]
    fn product_test() {
        let product: Rational = vec![r(1, 2), r(1, 4), r(4, 7)].into_iter().product();
        assert_eq!(product, r(1, 14));
        let product: Rational = vec![r(-1, 2), r(1, 4), r(4, 7)].into_iter().product();
        assert_eq!(product, r(-1, 14));
    }

    #[test]
    fn sum_test() {
        let sum: Rational = vec![r(1, 2), r(1, 4), r(4, 7)].into_iter().sum();
        assert_eq!(sum, r(37, 28));
        let sum: Rational = vec![r(-1, 2), r(1, 4), r(4, 7)].into_iter().sum();
        assert_eq!(sum, r(9, 28));
    }

    #[test]
    fn add_test() {
        fn assert<T>((ln, ld): (i128, i128), rhs: T, (dn, dd): (i128, i128))
        where
            Rational: From<T>,
        {
            let rhs = Rational::from(rhs);
            assert_eq!(
                Rational::new::<i128, i128>(ln, ld) + rhs,
                Rational::new::<i128, i128>(dn, dd)
            );
        }

        assert((1, 2), (3, 1), (7, 2));
        assert((1, 2), 10, (21, 2));
        assert((1, 2), 217, (435, 2));
    }

    #[test]
    fn add_assign_test() {
        let mut left = Rational::new(1, 2);
        left += 5;
        assert_eq!(left, Rational::new(11, 2));
        left += r(1, 2);
        assert_eq!(left, Rational::new(6, 1));
    }

    #[test]
    fn sub_test() {
        let assert = |(ln, ld): (i128, i128), (rn, rd): (i128, i128), (dn, dd): (i128, i128)| {
            assert_eq!(
                Rational::new(ln, ld) - Rational::new(rn, rd),
                Rational::new(dn, dd)
            );
        };

        assert((4, 3), (1, 2), (5, 6));
        assert((1, 2), (4, 3), (-5, 6));
    }

    #[test]
    fn sub_assign_test() {
        let mut left = Rational::new(1, 2);
        left -= Rational::new(1, 3);
        assert_eq!(left, Rational::new(1, 6));
        left -= 10;
        assert_eq!(left, Rational::new(-59, 6));
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
    fn rem_test() {
        let assert = |(n1, d1): (i128, i128), (n2, d2): (i128, i128), (num, den): (i128, i128)| {
            let r1 = Rational::new(n1, d1);
            let r2 = Rational::new(n2, d2);
            let actual_rem = r1 % r2;
            let expected_rem = Rational::new(num, den);
            assert_eq!(actual_rem, expected_rem);
        };

        assert((1, 4), (1, 2), (1, 4));
        assert((1, 3), (1, 4), (1, 12));
        assert((6, 1), (2, 1), (0, 1));

        // assert_eq!((-0.5) % (-0.2), 1.0);
        assert_eq!(
            (Rational::new(-1, 5) % Rational::new(1, 4)).decimal_value(),
            (-0.2) % (0.25)
        );
    }
}
