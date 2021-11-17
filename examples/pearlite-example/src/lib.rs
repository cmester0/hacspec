use hacspec_lib::*;

// // WHY3PROVE NOSPLIT Z3
// extern crate creusot_contracts;
// use creusot_contracts::std::*;
// use creusot_contracts::*;

// #[cfg(proof)]
// #[cfg(test)]
// #[predicate]
// fn sorted_range(s: Seq<u32>, l: Int, u: Int) -> bool {
//     pearlite! {

//     }
// }

// #[cfg(proof)]
// #[cfg(test)]
// #[predicate]
// fn sorted(s: Seq<u32>) -> bool {

// }

pub type ResultType = Result::<u64, u64>;

pub fn lenfun64(arr : Seq<u32>) -> u64 {
    arr.len() as u64
}

pub fn lenfun(arr : Seq<u32>) -> usize {
    arr.len()
}

#[cfg(proof)]
#[cfg(test)]
#[requires(lenfun64(arr) <= 18446744073709551615_u64)] // u64::MAX = 18446744073709551615
#[requires(forall<i : usize, j : usize> 0 <= i && i < j && j < lenfun(arr) ==> arr[i] <= arr[j])]
#[ensures(forall<x:u64> result === ResultType::Ok(x) ==> arr[x] === elem)]
#[ensures(forall<x:u64> result === ResultType::Err(x) ==> forall<i:u64> i < x ==> arr[i] <= elem)]
#[ensures(forall<x:u64> result === ResultType::Err(x) ==> forall<i:u64> x < i && i < lenfun64(arr) ==> elem < arr[i])]
fn binary_search(arr: Seq<u32>, elem: u32) -> ResultType {
    if arr.len() == 0 {
        // return
        ResultType::Err(0_u64)?;
    }
    let mut size = (arr.len() as u64);
    let mut base = 0_u64;

    let result = ResultType::Err(0_u64);

    // #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
    // #[invariant(lower_b, forall<i : u64> i < base ==> (@arr)[@i] <= elem)]
    // #[invariant(lower_b, forall<i : u64> @base + @size < @i && @i < (@arr).len() ==> elem < (@arr)[@i])]
    for k in 1..arr.len() {
        if size != 1_u64 {
            let half = size / 2_u64;
            let mid = base + half;

            base = if arr[mid] > elem { base } else { mid };
            size = size - half;
        } else {
            let cmp = arr[base as usize];
            if cmp == elem {
                result = ResultType::Ok((base as u64))
            } else {
                if cmp < elem {
                    result = ResultType::Err((base + 1 as u64))
                } else {
                    result = ResultType::Err((base as u64))
                }
            }
        }
    };

    result
}
