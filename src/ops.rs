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

impl Neg for &Rational {
    type Output = Rational;

    fn neg(self) -> Self::Output {
        (*self) * -1_i32
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
            let gcd = gcd(self.denominator(), rhs.denominator());
            let lcm = self.denominator().abs() * (rhs.denominator().abs() / gcd);

            let num1 = self.numerator() * (lcm / self.denominator());
            let num2 = rhs.numerator() * (lcm / rhs.denominator());

            Rational::new(num1 + num2, lcm)
        }
    }

    impl Add<&Rational> for Rational {
        type Output = Rational;

        fn add(self, rhs: &Rational) -> Self::Output {
            self + *rhs
        }
    }

    impl Add<Rational> for &Rational {
        type Output = Rational;

        fn add(self, rhs: Rational) -> Self::Output {
            *self + rhs
        }
    }

    impl Add<&Rational> for &Rational {
        type Output = Rational;

        fn add(self, rhs: &Rational) -> Self::Output {
            *self + *rhs
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

                fn add(self, rhs: $type) -> Self::Output {
                    self + Rational::from(rhs)
                }
            }

            impl Add<$type> for &Rational {
                type Output = Rational;

                fn add(self, rhs: $type) -> Self::Output {
                    *self + rhs
                }
            }

            impl Add<Rational> for $type {
                type Output = Rational;

                fn add(self, rhs: Rational) -> Self::Output {
                    rhs + self
                }
            }

            impl Add<&Rational> for $type {
                type Output = Rational;

                fn add(self, rhs: &Rational) -> Self::Output {
                    *rhs + self
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
    impl_add!(&u8);
    impl_add!(&u16);
    impl_add!(&u32);
    impl_add!(&u64);
    impl_add!(&i8);
    impl_add!(&i16);
    impl_add!(&i32);
    impl_add!(&i64);
    impl_add!(&i128);

    #[allow(clippy::op_ref)]
    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn rational_rational_addition_test() {
            let assign = |r1, r2| {
                let mut r1_copy = r1;
                r1_copy += r2;
                r1_copy
            };
            for (r1, r2, sum) in [
                (r(1, 2), r(3, 1), r(7, 2)),
                (r(1, 2), r(-3, 2), r(-1, 1)),
                (r(-20, 19), r(-20, 23), r(-840, 437)),
            ] {
                let message = format!("{r1} + {r2} = {sum}");
                assert_eq!(r1 + r2, sum, "{message}");
                assert_eq!(r1 + &r2, sum, "{message}");
                assert_eq!(&r1 + r2, sum, "{message}");
                assert_eq!(&r1 + &r2, sum, "{message}");
                assert_eq!(assign(r1, r2), sum);

                let message = format!("{r2} + {r1} = {sum}");
                assert_eq!(r2 + r1, sum, "{message}");
                assert_eq!(r2 + &r1, sum, "{message}");
                assert_eq!(&r2 + r1, sum, "{message}");
                assert_eq!(&r2 + &r1, sum, "{message}");
                assert_eq!(assign(r2, r1), sum);
            }
        }

        #[test]
        fn rational_integer_addition_test() {
            let assign = |rat, int| {
                let mut rat_copy = rat;
                rat_copy += int;
                rat_copy
            };
            for (rat, int, sum) in [
                (r(1, 2), 10, r(21, 2)),
                (r(1, 2), 217, r(435, 2)),
                (r(-15, 14), 101, r(1399, 14)),
                (r(-15, 14), -101, r(-1429, 14)),
            ] {
                let message = format!("{rat} + {int} = {sum}");
                assert_eq!(rat + int, sum, "{message}");
                assert_eq!(rat + &int, sum, "{message}");
                assert_eq!(&rat + int, sum, "{message}");
                assert_eq!(&rat + &int, sum, "{message}");
                assert_eq!(assign(rat, int), sum);

                let message = format!("{int} + {rat} = {sum}");
                assert_eq!(int + rat, sum, "{message}");
                assert_eq!(int + &rat, sum, "{message}");
                assert_eq!(&int + rat, sum, "{message}");
                assert_eq!(&int + &rat, sum, "{message}");
            }
        }
    }
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

            Rational::raw(numerator, denominator)
        }
    }

    impl Mul<&Rational> for Rational {
        type Output = Rational;

        fn mul(self, rhs: &Rational) -> Self::Output {
            self * *rhs
        }
    }

    impl Mul<Rational> for &Rational {
        type Output = Rational;

        fn mul(self, rhs: Rational) -> Self::Output {
            *self * rhs
        }
    }

    impl Mul<&Rational> for &Rational {
        type Output = Rational;

        fn mul(self, rhs: &Rational) -> Self::Output {
            *self * *rhs
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

                fn mul(self, rhs: $type) -> Self::Output {
                    self * Rational::from(rhs)
                }
            }

            impl Mul<$type> for &Rational {
                type Output = Rational;

                fn mul(self, rhs: $type) -> Self::Output {
                    *self * rhs
                }
            }

            impl Mul<Rational> for $type {
                type Output = Rational;

                fn mul(self, rhs: Rational) -> Self::Output {
                    rhs * self
                }
            }

            impl Mul<&Rational> for $type {
                type Output = Rational;

                fn mul(self, rhs: &Rational) -> Self::Output {
                    *rhs * self
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
    impl_mul!(&u8);
    impl_mul!(&u16);
    impl_mul!(&u32);
    impl_mul!(&u64);
    impl_mul!(&i8);
    impl_mul!(&i16);
    impl_mul!(&i32);
    impl_mul!(&i64);
    impl_mul!(&i128);

    #[allow(clippy::op_ref)]
    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn rational_rational_multiplication_test() {
            let assign = |r1, r2| {
                let mut r1_copy = r1;
                r1_copy *= r2;
                r1_copy
            };
            for (r1, r2, prod) in [
                (r(5, 9), r(10, 31), r(50, 279)),
                (r(-5, 10), r(100, 10), r(-5, 1)),
                (r(-1, 2), r(-2, 3), r(1, 3)),
            ] {
                let message = format!("{r1} * {r2} = {prod}");
                assert_eq!(r1 * r2, prod, "{message}");
                assert_eq!(r1 * &r2, prod, "{message}");
                assert_eq!(&r1 * r2, prod, "{message}");
                assert_eq!(&r1 * &r2, prod, "{message}");
                assert_eq!(assign(r1, r2), prod);

                let message = format!("{r2} * {r1} = {prod}");
                assert_eq!(r2 * r1, prod, "{message}");
                assert_eq!(r2 * &r1, prod, "{message}");
                assert_eq!(&r2 * r1, prod, "{message}");
                assert_eq!(&r2 * &r1, prod, "{message}");
                assert_eq!(assign(r2, r1), prod);
            }
        }

        #[test]
        fn rational_integer_multiplication_test() {
            let assign = |rat, int| {
                let mut rat_copy = rat;
                rat_copy *= int;
                rat_copy
            };
            for (rat, int, prod) in [
                (r(5, 9), 2, r(10, 9)),
                (r(5, 9), -3, r(-5, 3)),
                (r(5, 11), 27, r(135, 11)),
                (r(-13, 5), -9, r(117, 5)),
            ] {
                let message = format!("{rat} * {int} = {prod}");
                assert_eq!(rat * int, prod, "{message}");
                assert_eq!(rat * &int, prod, "{message}");
                assert_eq!(&rat * int, prod, "{message}");
                assert_eq!(&rat * &int, prod, "{message}");
                assert_eq!(assign(rat, int), prod);

                let message = format!("{int} * {rat} = {prod}");
                assert_eq!(int * rat, prod, "{message}");
                assert_eq!(int * &rat, prod, "{message}");
                assert_eq!(&int * rat, prod, "{message}");
                assert_eq!(&int * &rat, prod, "{message}");
            }
        }
    }
}

mod sub {
    use super::*;

    impl Sub for Rational {
        type Output = Rational;

        fn sub(self, rhs: Rational) -> Self::Output {
            Add::<Rational>::add(self, Neg::neg(rhs))
        }
    }

    impl Sub<&Rational> for Rational {
        type Output = Rational;

        fn sub(self, rhs: &Rational) -> Self::Output {
            self - *rhs
        }
    }

    impl Sub<Rational> for &Rational {
        type Output = Rational;

        fn sub(self, rhs: Rational) -> Self::Output {
            *self - rhs
        }
    }

    impl Sub<&Rational> for &Rational {
        type Output = Rational;

        fn sub(self, rhs: &Rational) -> Self::Output {
            *self - *rhs
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

                fn sub(self, rhs: $type) -> Self::Output {
                    self - Rational::from(rhs)
                }
            }

            impl Sub<$type> for &Rational {
                type Output = Rational;

                fn sub(self, rhs: $type) -> Self::Output {
                    *self - rhs
                }
            }

            impl Sub<Rational> for $type {
                type Output = Rational;

                fn sub(self, rhs: Rational) -> Self::Output {
                    Rational::from(self) - rhs
                }
            }

            impl Sub<&Rational> for $type {
                type Output = Rational;

                fn sub(self, rhs: &Rational) -> Self::Output {
                    Rational::from(self) - *rhs
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
    impl_sub!(&u8);
    impl_sub!(&u16);
    impl_sub!(&u32);
    impl_sub!(&u64);
    impl_sub!(&i8);
    impl_sub!(&i16);
    impl_sub!(&i32);
    impl_sub!(&i64);
    impl_sub!(&i128);

    #[allow(clippy::op_ref)]
    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn rational_rational_subtraction_test() {
            let assign = |r1, r2| {
                let mut r1_copy = r1;
                r1_copy -= r2;
                r1_copy
            };
            for (r1, r2, diff) in [
                (r(4, 3), r(1, 2), r(5, 6)),
                (r(4, 3), r(5, 3), r(-1, 3)),
                (r(-1, 3), r(-11, 7), r(26, 21)),
            ] {
                assert_eq!(r1 - r2, diff, "{r1} - {r2} = {diff}");
                assert_eq!(r1 - &r2, diff, "{r1} - {r2} = {diff}");
                assert_eq!(&r1 - r2, diff, "{r1} - {r2} = {diff}");
                assert_eq!(&r1 - &r2, diff, "{r1} - {r2} = {diff}");
                assert_eq!(assign(r1, r2), diff);
            }
        }

        #[test]
        fn rational_integer_subtraction_test() {
            let assign = |rat, int| {
                let mut rat_copy = rat;
                rat_copy -= int;
                rat_copy
            };
            for (rat, int, diff) in [
                (r(2, 3), 5, -r(13, 3)),
                (r(17, 15), -12, r(197, 15)),
                (r(-11, 9), 4, r(-47, 9)),
                (r(-19, 11), -3, r(14, 11)),
            ] {
                let message = format!("{rat} - {int} = {diff}");
                assert_eq!(rat - int, diff, "{message}");
                assert_eq!(rat - &int, diff, "{message}");
                assert_eq!(&rat - int, diff, "{message}");
                assert_eq!(&rat - &int, diff, "{message}");
                assert_eq!(assign(rat, int), diff);

                let message = format!("{int} - {rat} = {diff}");
                assert_eq!(int - rat, -diff, "{message}");
                assert_eq!(int - &rat, -diff, "{message}");
                assert_eq!(&int - rat, -diff, "{message}");
                assert_eq!(&int - &rat, -diff, "{message}");
            }
        }
    }
}

mod div {
    use super::*;

    impl Div<Rational> for Rational {
        type Output = Self;

        fn div(self, rhs: Rational) -> Self::Output {
            Rational::new(self, rhs)
        }
    }

    impl Div<&Rational> for Rational {
        type Output = Rational;

        fn div(self, rhs: &Rational) -> Self::Output {
            self / *rhs
        }
    }

    impl Div<Rational> for &Rational {
        type Output = Rational;

        fn div(self, rhs: Rational) -> Self::Output {
            *self / rhs
        }
    }

    impl Div<&Rational> for &Rational {
        type Output = Rational;

        fn div(self, rhs: &Rational) -> Self::Output {
            *self / *rhs
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

                fn div(self, rhs: $type) -> Self::Output {
                    self / Rational::from(rhs)
                }
            }

            impl Div<$type> for &Rational {
                type Output = Rational;

                fn div(self, rhs: $type) -> Self::Output {
                    self / Rational::from(rhs)
                }
            }

            impl Div<Rational> for $type {
                type Output = Rational;

                fn div(self, rhs: Rational) -> Self::Output {
                    Rational::from(self) / rhs
                }
            }

            impl Div<&Rational> for $type {
                type Output = Rational;

                fn div(self, rhs: &Rational) -> Self::Output {
                    Rational::from(self) / rhs
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
    impl_div!(&u8);
    impl_div!(&u16);
    impl_div!(&u32);
    impl_div!(&u64);
    impl_div!(&i8);
    impl_div!(&i16);
    impl_div!(&i32);
    impl_div!(&i64);
    impl_div!(&i128);

    #[allow(clippy::op_ref)]
    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn rational_rational_division_test() {
            let assign = |r1, r2| {
                let mut r1_copy = r1;
                r1_copy /= r2;
                r1_copy
            };
            for (r1, r2, ans) in [
                (r(5, 9), r(10, 31), r(31, 18)),
                (r(50, 49), r(11, 12), r(600, 539)),
                (r(-11, 9), r(2, 3), r(-11, 6)),
                (r(-19, 11), r(-1, 2), r(38, 11)),
            ] {
                let message = format!("{r1} / {r2} = {ans}");
                assert_eq!(r1 / r2, ans, "{message}");
                assert_eq!(r1 / &r2, ans, "{message}");
                assert_eq!(&r1 / r2, ans, "{message}");
                assert_eq!(&r1 / &r2, ans, "{message}");
                assert_eq!(assign(r1, r2), ans);

                let ans = ans.inverse();
                let message = format!("{r2} / {r1} = {ans}");
                assert_eq!(r2 / r1, ans, "{message}");
                assert_eq!(r2 / &r1, ans, "{message}");
                assert_eq!(&r2 / r1, ans, "{message}");
                assert_eq!(&r2 / &r1, ans, "{message}");
                assert_eq!(assign(r2, r1), ans);
            }
        }

        #[test]
        fn rational_integer_divison_test() {
            let assign = |rat, int| {
                let mut rat_copy = rat;
                rat_copy /= int;
                rat_copy
            };
            for (rat, int, ans) in [
                (r(1, 1), 6, r(1, 6)),
                (r(3, 4), 6, r(1, 8)),
                (r(4, 1), -6, r(-4, 6)),
            ] {
                let message = format!("{rat} / {int} = {ans}");
                assert_eq!(rat / int, ans, "{message}");
                assert_eq!(rat / &int, ans, "{message}");
                assert_eq!(&rat / int, ans, "{message}");
                assert_eq!(&rat / &int, ans, "{message}");
                assert_eq!(assign(rat, int), ans);

                let ans = ans.inverse();
                let message = format!("{int} / {rat} = {ans}");
                assert_eq!(int / rat, ans, "{message}");
                assert_eq!(int / &rat, ans, "{message}");
                assert_eq!(&int / rat, ans, "{message}");
                assert_eq!(&int / &rat, ans, "{message}");
            }
        }
    }
}

mod rem {
    use super::*;

    impl Rem for Rational {
        type Output = Self;

        fn rem(self, rhs: Rational) -> Self::Output {
            let neg = self.is_negative();
            let a = self.abs();
            let b = rhs.abs();
            let div = Div::<Rational>::div(a, b);
            let (_, mut fract) = div.mixed_fraction();

            if neg {
                fract = -fract;
            }

            Mul::<Rational>::mul(fract, b)
        }
    }

    impl Rem<&Rational> for Rational {
        type Output = Rational;

        fn rem(self, rhs: &Rational) -> Self::Output {
            self % *rhs
        }
    }

    impl Rem<Rational> for &Rational {
        type Output = Rational;

        fn rem(self, rhs: Rational) -> Self::Output {
            *self % rhs
        }
    }

    impl Rem<&Rational> for &Rational {
        type Output = Rational;

        fn rem(self, rhs: &Rational) -> Self::Output {
            *self % *rhs
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

                fn rem(self, rhs: $type) -> Self::Output {
                    self % Rational::from(rhs)
                }
            }

            impl Rem<$type> for &Rational {
                type Output = Rational;

                fn rem(self, rhs: $type) -> Self::Output {
                    self % Rational::from(rhs)
                }
            }

            impl Rem<Rational> for $type {
                type Output = Rational;

                fn rem(self, rhs: Rational) -> Self::Output {
                    Rational::from(self) % rhs
                }
            }

            impl Rem<&Rational> for $type {
                type Output = Rational;

                fn rem(self, rhs: &Rational) -> Self::Output {
                    Rational::from(self) % rhs
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
    impl_rem!(&u8);
    impl_rem!(&u16);
    impl_rem!(&u32);
    impl_rem!(&u64);
    impl_rem!(&i8);
    impl_rem!(&i16);
    impl_rem!(&i32);
    impl_rem!(&i64);
    impl_rem!(&i128);

    #[allow(clippy::op_ref)]
    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn rational_rational_remainder_test() {
            let assign = |r1, r2| {
                let mut r1_copy = r1;
                r1_copy %= r2;
                r1_copy
            };

            for (r1, r2, rem_a, rem_b) in [
                (r(1, 4), r(1, 2), r(1, 4), r(0, 1)),
                (r(1, 3), r(1, 4), r(1, 12), r(1, 4)),
                (r(6, 1), r(2, 1), r(0, 1), r(2, 1)),
            ] {
                let message_a = format!("{r1} % {r2} = {rem_a}");
                assert_eq!(r1 % r2, rem_a, "{message_a}");
                assert_eq!(r1 % &r2, rem_a, "{message_a}");
                assert_eq!(&r1 % r2, rem_a, "{message_a}");
                assert_eq!(&r1 % &r2, rem_a, "{message_a}");
                assert_eq!(assign(r1, r2), rem_a);

                let message_b = format!("{r2} % {r1} = {rem_b}");
                assert_eq!(r2 % r1, rem_b, "{message_b}");
                assert_eq!(r2 % &r1, rem_b, "{message_b}");
                assert_eq!(&r2 % r1, rem_b, "{message_b}");
                assert_eq!(&r2 % &r1, rem_b, "{message_b}");
            }
        }

        #[test]
        fn rational_integer_remainder_test() {
            let assign = |rat, int| {
                let mut rat_copy = rat;
                rat_copy %= int;
                rat_copy
            };
            for (rat, int, rem_a, rem_b) in [
                (r(2, 5), 10, r(4, 10), r(0, 1)),
                (r(26, 5), 5, r(1, 5), r(5, 1)),
            ] {
                let message_a = format!("{rat} % {int} = {rem_a}");
                assert_eq!(rat % int, rem_a, "{message_a}");
                assert_eq!(rat % &int, rem_a, "{message_a}");
                assert_eq!(&rat % int, rem_a, "{message_a}");
                assert_eq!(&rat % &int, rem_a, "{message_a}");
                assert_eq!(assign(rat, int), rem_a);

                let message_b = format!("{int} % {rat} = {rem_b}");
                assert_eq!(int % rat, rem_b, "{message_b}");
                assert_eq!(int % &rat, rem_b, "{message_b}");
                assert_eq!(&int % rat, rem_b, "{message_b}");
                assert_eq!(&int % &rat, rem_b, "{message_b}");
            }
        }
    }
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
}
