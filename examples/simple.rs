use rational::Rational;

fn main() {
    let one_half = Rational::new(1, 2);

    println!("{}", one_half); // prints "1/2"

    println!("{:0b}", -6);
    println!("{}", (-4_i128 | 2_i128).trailing_zeros());
}
