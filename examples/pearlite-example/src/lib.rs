// // // WHY3PROVE NOSPLIT Z3
// // extern crate creusot_contracts;
// // use creusot_contracts::std::*;
// // use creusot_contracts::*;

// use hacspec_lib::*;
// #[cfg(test)]
// #[cfg(proof)]

// #[requires((@arr).len() <= 18446744073709551615)]
// #[requires(forall<i : usize, j : usize> 0 <= @i && @i < @j && @j < (@arr).len() ==> (@arr)[@i] <= (@arr)[@j])]
// #[ensures(forall<x:usize> result === Result::<usize, usize>::Ok(x) ==> (@arr)[@x] === elem)]
// #[ensures(forall<x:usize> result === Result::<usize, usize>::Err(x) ==> forall<i:usize>  i < x ==> (@arr)[@i] <= elem)]
// #[ensures(forall<x:usize> result === Result::<usize, usize>::Err(x) ==> forall<i:usize> x < i && @i < (@arr).len() ==> elem < (@arr)[@i])]  
// // pub fn binary_search(arr: &Vec<usize>, elem: usize) -> Result<usize, usize> {
// pub fn binary_search(arr: Seq<usize>, elem: usize) -> Result<usize, usize> {
//     if arr.len() == 0_usize {
//         Result::<(), usize>::Err(0_usize)?;
//     }
//     let mut size = arr.len();
//     let mut base = 0_usize;

//     let mut result = Result::<usize, usize>::Err(0_usize);

//     // let mut k = 1;
//     // #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
//     // #[invariant(lower_b, forall<i : usize> i < base ==> (@arr)[@i] <= elem)]
//     // #[invariant(lower_b, forall<i : usize> @base + @size < @i && @i < (@arr).len() ==> elem < (@arr)[@i])]
//     // while k < arr.len() {
//     //     k = k + 1;
//     for k in 1..arr.len() {
//         if size != 1_usize {
//             let half = size / 2_usize;
//             let mid = base + half;

//             base = if arr[mid] > elem { base } else { mid };
//             size = size - half;
//         } else {
//             let cmp = arr[base];
//             if cmp == elem {
//                 result = Result::<usize, usize>::Ok(base)
//             } else {
//                 if cmp < elem {
//                     result = Result::<usize, usize>::Err(base + 1_usize)
//                 } else {
//                     result = Result::<usize, usize>::Err(base)
//                 }
//             }
//         }
//     };

//     result
// }



// extern crate creusot_contracts;
// use creusot_contracts::*;

use hacspec_lib::*;
#[cfg(test)]
#[cfg(proof)]

#[ensures(result == n * (n + 1usize) / 2usize)]
pub fn sum_first_n(n: usize) -> usize {
    let mut sum = 0usize;
    for i in 0..n {
        sum = sum + i;
    }
    
    // let mut i = 0;
    // #[invariant(loop_bound, i < n + 1u32)]
    // #[invariant(sum_value, sum == i * (i + 1u32) / 2u32)]
    // while i <= n {
    //     sum += i;
    //     i += 1;
    // }
    sum
}
