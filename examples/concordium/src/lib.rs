// #![cfg_attr(not(feature = "std"), no_std, feature(alloc_error_handler, core_intrinsics))]

// #[cfg(not(feature = "std"))]
// pub extern crate alloc;

// #[cfg(not(feature = "std"))]
// #[alloc_error_handler]
// fn on_oom(_layout: alloc::alloc::Layout) -> ! {
//     #[cfg(target_arch = "wasm32")]
//     unsafe {
// 	core::arch::wasm32::unreachable()
//     }
//     #[cfg(not(target_arch = "wasm32"))]
//     loop {}
// }

// /// Terminate execution immediately without panicking.
// /// When the `std` feature is enabled this is just [std::process::abort](https://doc.rust-lang.org/std/process/fn.abort.html).
// /// When `std` is not present and the target architecture is `wasm32` this will
// /// simply emit the [unreachable](https://doc.rust-lang.org/core/arch/wasm32/fn.unreachable.html) instruction.
// #[cfg(feature = "std")]
// pub use std::process::abort as trap;
// #[cfg(all(not(feature = "std"), target_arch = "wasm32"))]
// #[inline(always)]
// pub fn trap() -> ! { unsafe { core::arch::wasm32::unreachable() } }
// #[cfg(all(not(feature = "std"), not(target_arch = "wasm32")))]
// #[inline(always)]
// pub fn trap() -> ! { core::intrinsics::abort() }

// #[cfg(not(feature = "std"))]
// #[panic_handler]
// fn abort_panic(_info: &core::panic::PanicInfo) -> ! {
//     #[cfg(target_arch = "wasm32")]
//     unsafe {
// 	core::arch::wasm32::unreachable()
//     }
//     #[cfg(not(target_arch = "wasm32"))]
//     loop {}
// }

// // Provide some re-exports to make it easier to use the library.
// // This should be expanded in the future.
// /// Re-export.
// #[cfg(not(feature = "std"))]
// pub use alloc::{borrow::ToOwned, string, string::String, string::ToString, vec, vec::Vec};
// /// Re-export.
// #[cfg(not(feature = "std"))]
// pub use core::{convert, hash, marker, mem, num, result::*};
// #[cfg(feature = "std")]
// pub(crate) use std::vec;

// /// Re-export.
// #[cfg(feature = "std")]
// pub use std::{convert, hash, marker, mem, num, string::String, vec::Vec};

// pub mod collections {
//     #[cfg(not(feature = "std"))]
//     use alloc::collections;
//     #[cfg(feature = "std")]
//     use std::collections;

//     pub use collections::*;
//     pub use concordium_contracts_common::{HashMap, HashSet};
// }

#[cfg(not(feature = "hacspec"))]
mod hacspec_concordium_impls;
pub use hacspec_concordium_impls::*;

// /// Chain constants that impose limits on various aspects of smart contract
// /// execution.
// pub mod constants;
// mod impls;
// mod prims;
// mod traits;
// mod types;
// pub use concordium_contracts_common::*;
// pub use concordium_std_derive::*;
// pub use impls::*;
// pub use traits::*;
// pub use types::*;

// extern crate wee_alloc;
// // Use `wee_alloc` as the global allocator to reduce code size.
// #[global_allocator]
// static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

// pub mod test_infrastructure;
