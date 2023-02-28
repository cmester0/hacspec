// #[cfg(not(feature = "hacspec"))]
// pub(crate) use std::vec;
// /// Re-export.
// #[cfg(not(feature = "hacspec"))]
// pub use std::{convert, hash, marker, mem, num, string::String, vec::Vec};
// #[cfg(not(feature = "hacspec"))]
// pub use std::collections;
use creusot_contracts::{std::{process::abort as trap, *}, Ghost};

mod concordium_impls;
mod concordium_prims;
mod concordium_traits;
mod concordium_types;
pub mod constants;

pub mod test_infrastructure;

pub use concordium_impls::*;
use concordium_prims::*; // TODO: Does not re-export anything, nothing is public enough (removed pub)
pub use concordium_traits::*;
pub use concordium_types::*;

// TODO: Package into module
// #[cfg(not(feature = "hacspec"))]
// pub mod collections {
//     #[cfg(not(feature = "std"))]
//     use alloc::collections;
//     #[cfg(feature = "std")]
//     use std::collections;

//     pub use collections::*;
//     pub use collections::{BTreeMap, BTreeSet};
//     pub use concordium_contracts_common::{HashMap, HashSet};
// }

#[cfg(not(feature = "hacspec"))]
extern crate concordium_contracts_common;
#[cfg(not(feature = "hacspec"))]
/// Chain constants that impose limits on various aspects of smart contract
/// execution.
pub use concordium_contracts_common::*;

// TODO: Need derive
#[cfg(not(feature = "hacspec"))]
extern crate hacspec_concordium_derive;
#[cfg(not(feature = "hacspec"))]
pub use hacspec_concordium_derive::*;

#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "contracts"))]
extern crate wee_alloc;
// Use `wee_alloc` as the global allocator to reduce code size.
#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "contracts"))]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;
// pub use hacspec_lib::*;

// #[cfg(feature = "hacspec")]
// use hacspec_attributes::*;

// #[cfg(not(feature = "hacspec"))]
// extern crate creusot_contracts;
// #[cfg(not(feature = "hacspec"))]
// use creusot_contracts::*; // {ensures, trusted}; // requires, 
