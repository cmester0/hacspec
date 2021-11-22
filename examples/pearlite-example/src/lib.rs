// #![feature(rustc_attrs)]
// #![feature(stmt_expr_attributes)]

// WHY3PROVE NOSPLIT Z3
// #[cfg(test)]
// #[cfg(proof)]
// extern crate creusot_contracts;
// #[cfg(test)]
// #[cfg(proof)]
// use creusot_contracts::std::*;
// #[cfg(test)]
// #[cfg(proof)]
// use creusot_contracts::*;

// extern crate hacspec_lib;
use hacspec_lib::*;

#[cfg(test)]
#[cfg(proof)]
#[requires(arr.len() <= 18446744073709551615)]
#[requires(forall<i : usize, j : usize> 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j])]
#[ensures(forall<x:usize> result === Result::<usize, usize>::Ok(x) ==> arr[x] === elem)]
#[ensures(forall<x:usize> result === Result::<usize, usize>::Err(x) ==> forall<i:usize>  i < x ==> arr[@i] <= elem)]
#[ensures(forall<x:usize> result === Result::<usize, usize>::Err(x) ==> forall<i:usize> x < i && @i < arr.len() ==> elem < arr[@i])]
pub fn binary_search(arr: Seq<usize>, elem: usize) -> Result<usize, usize> {
    if arr.len() == 0_usize {
        Result::<(), usize>::Err(0_usize)?;
    }
    let mut size = arr.len();
    let mut base = 0_usize;

    let mut result = Result::<usize, usize>::Err(0_usize);
    
    for k in 1..arr.len() {
        if size != 1_usize {
            let half = size / 2_usize;
            let mid = base + half;

            base = if arr[mid] > elem { base } else { mid };
            size = size - half;
        } else {
            let cmp = arr[base];
            if cmp == elem {
                result = Result::<usize, usize>::Ok(base)
            } else {
                if cmp < elem {
                    result = Result::<usize, usize>::Err(base + 1_usize)
                } else {
                    result = Result::<usize, usize>::Err(base)
                }
            }
        }
    };

    result

    // #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
    // #[invariant(lower_b, forall<i : usize> i < base ==> (@arr)[@i] <= elem)]
    // #[invariant(lower_b, forall<i : usize> @base + @size < @i && @i < (@arr).len() ==> elem < (@arr)[@i])]
                  
    // while size > 1 {
    //     let half = size / 2;
    //     let mid = base + half;

    //     base = if arr[mid] > elem { base } else { mid };
    //     size -= half;
    // }

    // let cmp = arr[base];
    // if cmp == elem {
    //     Ok(base)
    // } else if cmp < elem {
    //     Err(base + 1)
    // } else {
    //     Err(base)
    // }
}


// #![feature(rustc_attrs)]
// #![feature(stmt_expr_attributes)]

// use hacspec_lib::*;

// extern crate creusot_contracts;
// use creusot_contracts::std::*;
// use creusot_contracts::*;

// // // WHY3PROVE NOSPLIT Z3
// // extern crate creusot_contracts;
// // use creusot_contracts::std::*;
// // use creusot_contracts::*;

// pub type ResultType = Result::<usize, usize>;

// // pub fn lenfun64(arr : Seq<u32>) -> u64 {
// //     arr.len() as u64
// // }

// // // #[logic]
// // pub fn lenfun(arr : Seq<u32>) -> usize {
// //     arr.len()
// // }

// // #[cfg(proof)]
// // #[cfg(test)]
// // #[requires(lenfun64(arr) <= 18446744073709551615_u64)] // u64::MAX = 18446744073709551615
// // #[requires(forall<i : usize, j : usize> 0 <= i && i < j && j < lenfun(arr) ==> arr[i] <= arr[j])]
// #[ensures(forall<x:usize> result === ResultType::Ok(x) ==> arr[x] === elem)]
// // #[ensures(forall<x:usize> result === ResultType::Err(x) ==> forall<i:usize> i < x ==> arr[i] <= elem)]
// // #[ensures(forall<x:u64> result === ResultType::Err(x) ==> forall<i:u64> x < i && i < lenfun64(arr) ==> elem < arr[i])]
// pub fn binary_search(arr: Seq<u32>, elem: u32) -> ResultType {
//     if arr.len() == 0 {
//         // return
//         ResultType::Err(0)?;
//     }
//     let mut size = arr.len();
//     let mut base = 0;

//     let mut result = ResultType::Err(0);

//     // #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
//     // #[invariant(lower_b, forall<i : u64> i < base ==> (@arr)[@i] <= elem)]
//     // #[invariant(lower_b, forall<i : u64> @base + @size < @i && @i < (@arr).len() ==> elem < (@arr)[@i])]
//     for k in 1..arr.len() {
//         if size != 1 {
//             let half = size / 2;
//             let mid = base + half;

//             base = if arr[(mid as usize)] > elem { base } else { mid };
//             size = size - half;
//         } else {
//             let cmp = arr[base as usize];
//             if cmp == elem {
//                 result = ResultType::Ok(base)
//             } else {
//                 if cmp < elem {
//                     result = ResultType::Err(base + 1)
//                 } else {
//                     result = ResultType::Err(base)
//                 }
//             }
//         }
//     };

//     result
// }
