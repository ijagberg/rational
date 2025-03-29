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
        if self.is_integer() {
            serializer.serialize_i128(self.numerator)
        } else {
            serializer.serialize_str(&self.to_string())
        }
    }
}
