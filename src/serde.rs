use crate::Rational;
use serde::{
    de::{Deserialize, Deserializer, Error, Visitor},
    ser::{Serialize, Serializer},
};
use std::fmt::{self, Formatter};

struct RationalVisitor;

impl Visitor<'_> for RationalVisitor {
    type Value = Rational;

    fn expecting(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str("a rational number")
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
    where
        E: Error,
    {
        self.visit_i128(v.into())
    }

    fn visit_i128<E>(self, v: i128) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(Rational::integer(v))
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: Error,
    {
        self.visit_i128(v.into())
    }

    fn visit_u128<E>(self, v: u128) -> Result<Self::Value, E>
    where
        E: Error,
    {
        self.visit_i128(v.try_into().map_err(|err| {
            E::custom(format_args!(
                "expected a value that fits a signed i128: {err}"
            ))
        })?)
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        v.parse().map_err(|err| E::custom(err))
    }
}

impl<'de> Deserialize<'de> for Rational {
    fn deserialize<D>(deserializer: D) -> Result<Rational, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(RationalVisitor)
    }
}

impl Serialize for Rational {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

/// Define a test case. Will have a serialize and deserialize test function.
///
/// The test uses `serde_json::Value`. Trying to use the json string representation fails
/// since serde_json is not capable of reliably serializing and deserializing big values
/// that require 128bit precision. Other data formats such as `toml` only support 64bit
/// so this is the best we can do.
macro_rules! test_case {
    ($name:ident, $rational:expr, $value:expr $(, $value_int:expr)?) => {
        #[cfg(test)]
        mod $name {
            use crate::Rational;
            use serde_json::Value;

            #[test]
            fn test_serialize() {
                const ERR: &str = concat!("Error trying to serialize ", stringify!($rational));
                assert_eq!(serde_json::to_value(&$rational).expect(ERR), $value);
            }

            #[test]
            fn test_deserialize() {
                const ERR: &str = concat!("Error trying to deserialize ", stringify!($value));
                assert_eq!(
                    serde_json::from_value::<Rational>($value).expect(ERR),
                    $rational
                );
            }

            $(
                #[test]
                fn test_deserialize_int() {
                    const ERR: &str = concat!("Error trying to deserialize ", stringify!($value_int));
                    assert_eq!(
                        serde_json::from_value::<Rational>($value_int).expect(ERR),
                        $rational
                    );
                }
            )?
        }
    };
}

// integer test cases
test_case!(zero, Rational::zero(), Value::from("0/1"), Value::from(0));
test_case!(one, Rational::one(), Value::from("1/1"), Value::from(1));
test_case!(
    minus_one,
    -Rational::one(),
    Value::from("-1/1"),
    Value::from(-1)
);
test_case!(
    very_big,
    Rational::integer(i128::MAX),
    Value::from("170141183460469231731687303715884105727/1"),
    Value::from(i128::MAX)
);
test_case!(
    very_small,
    Rational::integer(i128::MIN),
    Value::from("-170141183460469231731687303715884105728/1"),
    Value::from(i128::MIN)
);

// non-integer test cases
test_case!(one_half, Rational::new(1, 2), Value::from("1/2"));
test_case!(
    epsilon,
    Rational::new(1, i128::MAX),
    Value::from("1/170141183460469231731687303715884105727")
);
test_case!(
    minus_epsilon,
    Rational::new(-1, i128::MAX),
    Value::from("-1/170141183460469231731687303715884105727")
);
test_case!(
    very_big_half,
    Rational::new(i128::MAX, 2),
    Value::from("170141183460469231731687303715884105727/2")
);
test_case!(
    very_small_third,
    Rational::new(i128::MIN, 3),
    Value::from("-170141183460469231731687303715884105728/3")
);
