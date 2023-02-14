// #[cfg(not(feature="hacspec"))]
// extern crate creusot_contracts;
// #[cfg(not(feature="hacspec"))]
// use creusot_contracts::*;

// #[cfg(not(feature = "hacspec"))]
// extern crate hacspec_attributes;
// #[cfg(feature = "hacspec")]
// use hacspec_attributes::*;

use hacspec_lib::*;

// Prove that this function implements the sum of the first n natural numbers.
// Hint: there exists a closed form of this sum
#[ensures(result == n * (n - 1_usize) / 2_usize)]
pub fn sum_first_n(n: usize) -> usize {
    let mut sum = 0;
    for i in 0..n {
        sum = sum + i;
    }
    sum
}
