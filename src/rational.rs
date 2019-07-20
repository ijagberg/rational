use std::ops::Add;
use std::ops::Mul;
use std::ops::Sub;

#[derive(Copy, Clone, Debug)]
struct Rational {
    numerator: i128,
    denominator: i128,
}

impl Rational {
    pub fn new(numerator: i128, denominator: i128) -> Self {
        if denominator == 0 {
            panic!("Denominator can't be 0");
        }

        let mut this = Rational {
            numerator,
            denominator,
        };
        this.reduce();
        this
    }

    fn reduce(&mut self) {
        let gcd = gcd(self.numerator, self.denominator);
        self.numerator /= gcd;
        self.denominator /= gcd;
    }
}

impl Mul for Rational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let numerator = self.numerator * rhs.numerator;
        let denominator = self.denominator * rhs.denominator;

        Rational::new(numerator, denominator)
    }
}

impl Mul<i128> for Rational {
    type Output = Self;

    fn mul(self, rhs: i128) -> Self {
        Rational::new(self.numerator * rhs, self.denominator)
    }
}

impl Add for Rational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let denominator = self.denominator * rhs.denominator;

        Rational::new(
            self.numerator * rhs.denominator + rhs.numerator * self.denominator,
            denominator,
        )
    }
}

impl Sub for Rational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self + (rhs * -1_i128)
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

fn gcd(a: i128, b: i128) -> i128 {
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
    fn test_addition() {
        let left = Rational::new(1, 2);
        let right = Rational::new(3, 1);
        assert_eq!(left + right, Rational::new(7, 2));
    }

    #[test]
    fn test_subtraction() {
        let left = Rational::new(4, 3);
        let right = Rational::new(1, 2);
        assert_eq!(left - right, Rational::new(5, 6))
    }

    #[test]
    fn test_multiplication() {
        let left = Rational::new(5, 9);
        let right = Rational::new(10, 31);
        assert_eq!(left * right, Rational::new(50, 279));
    }

    #[test]
    fn test_equality() {
        let left = Rational::new(4, 8);
        let right = Rational::new(16, 32);
        assert_eq!(left, right);
    }
}
