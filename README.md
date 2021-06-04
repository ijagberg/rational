A minimal library for representing rational numbers (ratios of integers).

# Example
```rust
// all rationals are automatically reduced when created, so equality works as following:
let one_half = Rational::new(1, 2);
let two_quarters = Rational::new(2, 4);
assert_eq!(one_half, two_quarters);

// you can make more complicated rationals:
let one_half_over_one_quarter = Rational::new((1, 2), (1, 4)); // (1/2)/(1/4)
assert_eq!(one_half_over_one_quarter, Rational::new(2, 1));

// mathematical ops are implemented:
let sum = Rational::new(1, 9) + Rational::new(5, 4);
assert_eq!(sum, Rational::new(49, 36));

// can get the inverse of a rational:
let orig = Rational::new(80, 20);
let inverse = orig.inverse();
assert_eq!(inverse, Rational::new(20, 80));
assert_eq!(inverse, Rational::new(1, orig));
```