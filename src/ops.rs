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
                    Rational::integer(self as i128) - rhs
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
                    Rational::integer(self as i128) / rhs
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
                    Rational::integer(self as i128) % rhs
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
    fn rational_plus_rational_test() {
        let assign = |r1, r2| {
            let mut r1_copy = r1;
            r1_copy += r2;
            r1_copy
        };
        for (r1, r2, sum) in [(r(1, 2), r(3, 1), r(7, 2))] {
            assert_eq!(r1 + r2, sum);
            assert_eq!(assign(r1, r2), sum);
            assert_eq!(assign(r2, r1), sum);
        }
    }

    #[test]
    fn integer_plus_rational_test() {
        let assign = |int, rat| {
            let mut rat_copy = rat;
            rat_copy += int;
            rat_copy
        };
        for (int, rat, sum) in [(10, r(1, 2), r(21, 2)), (217, r(1, 2), r(435, 2))] {
            assert_eq!(int + rat, sum);
            assert_eq!(assign(int, rat), sum);
        }
    }

    #[test]
    fn rational_minus_rational_test() {
        let assign = |r1, r2| {
            let mut r1_copy = r1;
            r1_copy -= r2;
            r1_copy
        };
        for (r1, r2, diff) in [(r(4, 3), r(1, 2), r(5, 6))] {
            assert_eq!(r1 - r2, diff);
            assert_eq!(assign(r1, r2), diff);

            assert_eq!(r2 - r1, -1 * diff);
            assert_eq!(assign(r2, r1), -1 * diff);
        }
    }

    #[test]
    fn integer_minus_rational_test() {
        let assign = |int, rat| {
            let mut rat_copy = rat;
            rat_copy -= int;
            rat_copy
        };
        for (int, rat, diff) in [(5, r(2, 3), r(13, 3))] {
            assert_eq!(int - rat, diff);

            assert_eq!(rat - int, -1 * diff);
            assert_eq!(assign(int, rat), -1 * diff);
        }
    }

    #[test]
    fn rational_multiplied_by_rational_test() {
        let assign = |r1, r2| {
            let mut r1_copy = r1;
            r1_copy *= r2;
            r1_copy
        };
        for (r1, r2, prod) in [
            (r(5, 9), r(10, 31), r(50, 279)),
            (r(-5, 10), r(100, 10), r(-5, 1)),
        ] {
            assert_eq!(r1 * r2, prod);
            assert_eq!(assign(r1, r2), prod);

            assert_eq!(r2 * r1, prod);
            assert_eq!(assign(r2, r1), prod);

            assert_eq!((-1 * r1) * r2, -1 * prod);
            assert_eq!(assign(-1 * r1, r2), -1 * prod);

            assert_eq!((-1 * r2) * r1, -1 * prod);
            assert_eq!(assign(-1 * r2, r1), -1 * prod);

            assert_eq!((-1 * r1) * (-1 * r2), prod);
            assert_eq!(assign(-1 * r1, -1 * r2), prod);
        }
    }

    #[test]
    fn integer_multiplied_by_rational_test() {
        let assign = |int, rat| {
            let mut rat_copy = rat;
            rat_copy *= int;
            rat_copy
        };
        for (int, rat, prod) in [(2, r(5, 9), r(10, 9)), (-3, r(5, 9), r(-5, 3))] {
            assert_eq!(int * rat, prod);
            assert_eq!(assign(int, rat), prod);

            assert_eq!(rat * int, prod);

            assert_eq!((-1 * int) * rat, -1 * prod);
            assert_eq!(assign(-1 * int, rat), -1 * prod);

            assert_eq!((-1 * rat) * int, -1 * prod);
            assert_eq!(assign(int, -1 * rat), -1 * prod);

            assert_eq!((-1 * int) * (-1 * rat), prod);
            assert_eq!(assign(-1 * int, -1 * rat), prod);
        }
    }

    #[test]
    fn rational_divided_by_rational_test() {
        let assign = |r1, r2| {
            let mut r1_copy = r1;
            r1_copy /= r2;
            r1_copy
        };
        for (r1, r2, ans) in [
            (r(5, 9), r(10, 31), r(31, 18)),
            (r(50, 49), r(11, 12), r(600, 539)),
        ] {
            assert_eq!(r1 / r2, ans);
            assert_eq!(assign(r1, r2), ans);

            assert_eq!(r2 / r1, ans.inverse());
            assert_eq!(assign(r2, r1), ans.inverse());

            assert_eq!((-1 * r1) / r2, -1 * ans);
            assert_eq!(assign(-1 * r1, r2), -1 * ans);

            assert_eq!((-1 * r2) / r1, -1 * ans.inverse());
            assert_eq!(assign(-1 * r2, r1), -1 * ans.inverse());
        }
    }

    #[test]
    fn integer_divided_by_rational_test() {
        let assign = |int, rat| {
            let mut rat_copy = rat;
            rat_copy /= int;
            rat_copy
        };
        for (int, rat, ans) in [
            (6, r(1, 1), r(6, 1)),
            (6, r(3, 4), r(8, 1)),
            (6, r(4, 1), r(6, 4)),
        ] {
            assert_eq!(int / rat, ans);
            assert_eq!(assign(int, rat), ans.inverse());

            assert_eq!((-1 * int) / rat, -1 * ans);
            assert_eq!((-1 * int) / (-1 * rat), ans);
        }
    }

    #[test]
    fn rational_by_rational_remainder_test() {
        let assign = |r1, r2| {
            let mut r1_copy = r1;
            r1_copy %= r2;
            r1_copy
        };

        for (r1, r2, rem) in [
            (r(1, 4), r(1, 2), r(1, 4)),
            (r(1, 3), r(1, 4), r(1, 12)),
            (r(6, 1), r(2, 1), r(0, 1)),
        ] {
            assert_eq!(r1 % r2, rem);
            assert_eq!(assign(r1, r2), rem);
        }
    }

    #[test]
    fn integer_by_rational_remainder_test() {
        let assign = |int, rat| {
            let mut rat_copy = rat;
            rat_copy %= int;
            rat_copy
        };
        for (int, rat, rem) in [(10, r(2, 5), r(0, 1)), (5, r(26, 5), r(1, 5))] {
            dbg!(int, rat, rem);
            if int > rat {
                assert_eq!(int % rat, rem);
                assert_eq!(rat % int, rat);
                assert_eq!(assign(int, rat), rat);
            } else if int < rat {
                assert_eq!(int % rat, int);
                assert_eq!(rat % int, rem);
                assert_eq!(assign(int, rat), rem);
            }
        }
    }
}
