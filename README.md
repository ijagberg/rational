A minimal library for representing rational numbers (ratios of integers).

## Construction

```rust
// Rationals are automatically reduced when created:
let one_half = Rational::new(1, 2);
let two_quarters = Rational::new(2, 4);
assert_eq!(one_half, two_quarters);

// `From` is implemented for integers and integer tuples:
assert_eq!(Rational::from(1), Rational::new(1, 1));
assert_eq!(Rational::from((1, 2)), Rational::new(1, 2));

// The `new` method takes a numerator and denominator that implement `Into<Rational>`:
let one_half_over_one_quarter = Rational::new((1, 2), (1, 4));
assert_eq!(one_half_over_one_quarter, Rational::new(2, 1));
```

## Mathematical operations

```rust
// Operations and comparisons are implemented for Rationals and integers:
let one_ninth = Rational::new(1, 9);
assert_eq!(one_ninth + Rational::new(5, 4), Rational::new(49, 36));
assert_eq!(one_ninth - 4, Rational::new(-35, 9));
assert_eq!(one_ninth / Rational::new(21, 6), Rational::new(2, 63));
assert!(one_ninth < Rational::new(1, 8));
assert!(one_ninth < 1);
```

## Other properties

```rust
// Inverse:
let eight_thirds = Rational::new(8, 3);
let inverse = eight_thirds.inverse();
assert_eq!(inverse, Rational::new(3, 8));

// Mixed fractions:
let (whole, fractional) = eight_thirds.mixed_fraction();
assert_eq!(whole, 2);
assert_eq!(fractional, Rational::new(2, 3));
```

## Features

- Enable the `num-traits` feature to gain access to implementations of many of the traits defined in the `num-traits` crate for `Rationals`
