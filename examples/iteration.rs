use rational::Rational;

//example taken from [https://www.youtube.com/watch?v=N92w4e-hrA4](this Youtube video)
fn main() {
    assert_sequence(
        Rational::new(0, 1),
        2,
        Rational::one(),
        &[
            Rational::integer(0),
            Rational::integer(1),
            Rational::integer(2),
            Rational::integer(5),
            Rational::integer(26),
        ],
    );

    assert_sequence(
        Rational::integer(0),
        2,
        Rational::new(1, 4),
        &[
            Rational::new(0, 1),
            Rational::new(1, 4),
            Rational::new(5, 16),
            Rational::new(89, 256),
        ],
    );

    assert_sequence(
        Rational::new(1, 2),
        2,
        Rational::new(1, 4),
        &[Rational::new(1, 2), Rational::new(1, 2)],
    );

    assert_sequence(
        Rational::new(-7, 4),
        2,
        Rational::new(-29, 16),
        &[
            Rational::new(-7, 4),
            Rational::new(5, 4),
            Rational::new(-1, 4),
            Rational::new(-7, 4),
        ],
    );
}

fn assert_sequence(start: Rational, exp: u32, c: Rational, expected: &[Rational]) {
    let mut current = start;
    let mut actual = Vec::new();
    for _ in 0..expected.len() {
        actual.push(current);
        current = next(current, exp, c);
    }
    assert_eq!(actual, expected);
}

fn next(z: Rational, exp: u32, c: Rational) -> Rational {
    z.pow(exp as i32) + c
}
