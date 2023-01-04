A minimal library for representing rational numbers (ratios of integers).

# Example

```rust
// all rationals are automatically reduced when created, so equality works as following:
let one_half = Rational::new(1, 2);
let two_quarters = Rational::new(2, 4);
assert_eq!(one_half, two_quarters);

// you can make more complicated rationals:
let one_half_over_one_quarter = Rational::new(Rational::new(1, 2), Rational::new(1, 4)); // (1/2)/(1/4)
assert_eq!(one_half_over_one_quarter, Rational::new(2, 1));

// mathematical operations are implemented for integers and rationals:
let one_ninth = Rational::new(1, 9);
assert_eq!(one_ninth + Rational::new(5, 4), Rational::new(49, 36));
assert_eq!(one_ninth - 4, Rational::new(-35, 9));
assert_eq!(one_ninth / Rational::new(21, 6), Rational::new(2, 63));

// other properties, such as
// inverse
let r = Rational::new(8, 3);
let inverse = r.inverse();
assert_eq!(inverse, Rational::new(3, 8));
assert_eq!(inverse, Rational::new(1, r));
// mixed fraction
let (whole, fractional) = r.mixed_fraction();
assert_eq!(whole, 2);
assert_eq!(fractional, Rational::new(2, 3));
```
