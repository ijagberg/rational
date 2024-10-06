use rational::Rational;
use std::collections::HashMap;

/// An interesting sequence I found.
///
/// ## Description
/// Given an integer `n`, generate a list of all possible rational numbers with the numerator and denominator in the range `1..=n`,
/// keeping count of how many times you have seen each rational number in its reduced form. When done, remove all entries that have occurred
/// more than once. Call this process `f(n)`. The sequence is `f(n)` for `n in 1..`.
///
/// ## Example
/// `n = 4`:
/// 
/// The list of non-reduced rationals that can be constructed with integers in `1..=4`:
/// ```
/// [1/1, 1/2, 1/3, 1/4, 2/1, 2/2, 2/3, 2/4, 3/1, 3/2, 3/3, 3/4, 4/1, 4/2, 4/3, 4/4]
/// ```
/// After reducing each rational, and sorting the list (to make marking duplicates easier):
/// 
/// ```
/// [1/4, 1/3, 1/2, 1/2, 2/3, 3/4, 1/1, 1/1, 1/1, 1/1, 4/3, 3/2, 2/1, 2/1, 3/1, 4/1]
///            --------            ------------------            --------
/// ```
/// So, removing these duplicate values, we are left with 8 unique values, giving `f(4)=8`.
/// 
/// The sequence looks like this for `n in 1..=20`:
/// ```
/// 1, 2, 6, 8, 16, 16, 28, 32, 44, 44, 64, 68, 92, 92, 108, 116, 148, 148, 184, 192
/// ```
fn main() {
    let mut counts = HashMap::new();
    println!("n,k");
    for max in 1..=20 {
        for n in 1..=max {
            let n_over_max = Rational::new(n, max);
            let max_over_n = Rational::new(max, n);
            *counts.entry(n_over_max).or_insert(0) += 1;
            if n_over_max != max_over_n {
                *counts.entry(max_over_n).or_insert(0) += 1;
            }
        }
        let mut uniques: Vec<_> = counts
            .iter()
            .filter_map(|(k, v)| if *v == 1 { Some(k) } else { None })
            .collect();
        uniques.sort();
        println!("{},{}", max, uniques.len());
    }
}
