use std::ops::Add;
use std::ops::Mul;

struct Rational {
    numerator: u128,
    denominator: u128,
}

impl Rational {
    pub fn new(numerator: u128, denominator: u128) -> Self {
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

    pub fn as_double(&self) -> f64 {
        (self.numerator as f64) / (self.denominator as f64)
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

impl Mul<u128> for Rational {
    type Output = Self;

    fn mul(self, rhs: u128) -> Self {
        self * Rational::new(rhs, 1)
    }
}

impl Add for Rational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let mut right = rhs;
        let mut left = self;
        right = right * self.denominator;
        left = left * rhs.denominator;
        Rational::new(right.numerator + left.numerator, right.denominator)
    }
}

fn gcd(a: u128, b: u128) -> u128 {
    let mut a = a;
    let mut b = b;
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}
