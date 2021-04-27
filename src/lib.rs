use std::ops::{Add, Div, Mul, Sub};

#[derive(Copy, Clone, Debug)]
pub struct Rational {
    numerator: i128,
    denominator: i128,
}

impl Rational {
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

    pub fn inverse_checked(self) -> Option<Self> {
        if self.numerator == 0 {
            None
        } else {
            Some(Self::new(self.denominator, self.numerator))
        }
    }

    pub fn inverse(self) -> Self {
        if self.numerator == 0 {
            panic!("numerator cannot be 0 when inverting");
        }
        Self::new(self.denominator, self.numerator)
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

impl<T> Sub<T> for Rational
where
    Rational: From<T>,
{
    type Output = Self;

    fn sub(self, rhs: T) -> Self::Output {
        let rhs = Rational::from(rhs);
        let rhs_neg: Rational = Mul::<i128>::mul(rhs, -1_i128);
        Add::<Rational>::add(self, rhs_neg)
    }
}

impl PartialEq for Rational {
    fn eq(&self, rhs: &Rational) -> bool {
        self.numerator * rhs.denominator == rhs.numerator * self.denominator
    }
}

impl Into<f64> for Rational {
    fn into(self) -> f64 {
        (self.numerator as f64) / (self.denominator as f64)
    }
}

pub fn gcd(a: i128, b: i128) -> i128 {
    let mut a = a;
    let mut b = b;
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
    fn addition_test() {
        let left = Rational::new(1, 2);

        assert_eq!(left + Rational::new(3, 1), Rational::new(7, 2));
        assert_eq!(left + 10_u8, Rational::new(21, 2));
        assert_eq!(left + 217_u16, Rational::new(435, 2));
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
}
