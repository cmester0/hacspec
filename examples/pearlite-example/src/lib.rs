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

pub type ResultType = Result::<usize, usize>;

#[cfg(proof)]
#[cfg(test)]
// #[requires(arr.len() <= usize::MAX)]
// #[requires(forall<i : Int, j : Int> 0 <= i && i < j && j < (@arr).len() ==> (@arr)[i] <= (@arr)[j])]
// #[ensures(forall<x:usize> result === Ok(x) ==> (@arr)[@x] === elem)]
#[ensures(forall<x:usize> result === Err(x) ==> forall<i:usize>  i < x ==> arr[i] <= elem)]
// #[ensures(forall<x:usize> result === Err(x) ==> forall<i:usize> x < i && @i < (@arr).len() ==> elem < (@arr)[@i])]
fn binary_search(arr: Seq<u32>, elem: u32) -> ResultType {
    if arr.len() == 0 {
        // return
        ResultType::Err(0)?;
    }
    let mut size = arr.len();
    let mut base = 0_usize;

    let result = ResultType::Err(0);

    // #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
    // #[invariant(lower_b, forall<i : usize> i < base ==> (@arr)[@i] <= elem)]
    // #[invariant(lower_b, forall<i : usize> @base + @size < @i && @i < (@arr).len() ==> elem < (@arr)[@i])]
    for k in 1..arr.len() {
        if size != 1 {
            let half = size / 2;
            let mid = base + half;

            base = if arr[mid] > elem { base } else { mid };
            size = size - half;
        } else {
            let cmp = arr[base];
            if cmp == elem {
                result = ResultType::Ok(base)
            } else {
                if cmp < elem {
                    result = ResultType::Err(base + 1)
                } else {
                    result = ResultType::Err(base)
                }
            }
        }
    };

    result
}
