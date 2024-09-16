use rational::Rational;

fn main() {
    let one_half = Rational::new(1, 2);

    println!("{}", one_half); // prints "1/2"
    println!("{}", one_half + 7); // prints "15/2"
    println!("{}", one_half / 2); // prints "1/4"
    println!("{}", one_half * 3); // prints "3/2"
}
