#![cfg_attr(not(feature = "std"), no_std, feature(alloc_error_handler, core_intrinsics))]

#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "std"))]
pub extern crate alloc;

// TODO:
// #[cfg(not(feature = "hacspec"))]
// #[cfg(not(feature = "std"))]
// #[alloc_error_handler]
// fn on_oom(_layout: alloc::alloc::Layout) -> ! {
//     #[cfg(target_arch = "wasm32")]
//     unsafe {
//         core::arch::wasm32::unreachable()
//     }
//     #[cfg(not(target_arch = "wasm32"))]
//     loop {}
// }

/// Terminate execution immediately without panicking.
/// When the `std` feature is enabled this is just [std::process::abort](https://doc.rust-lang.org/std/process/fn.abort.html).
/// When `std` is not present and the target architecture is `wasm32` this will
/// simply emit the [unreachable](https://doc.rust-lang.org/core/arch/wasm32/fn.unreachable.html) instruction.
#[cfg(not(feature = "hacspec"))]
#[cfg(feature = "std")]
pub use std::process::abort as trap;
#[cfg(not(feature = "hacspec"))]
#[cfg(all(not(feature = "std"), target_arch = "wasm32"))]
#[inline(always)]
pub fn trap() -> ! { unsafe { core::arch::wasm32::unreachable() } }
#[cfg(not(feature = "hacspec"))]
#[cfg(all(not(feature = "std"), not(target_arch = "wasm32")))]
#[inline(always)]
pub fn trap() -> ! { core::intrinsics::abort() }

// TODO:
// #[cfg(not(feature = "hacspec"))]
// #[cfg(not(feature = "std"))]
// #[panic_handler]
// fn abort_panic(_info: &core::panic::PanicInfo) -> ! {
//     #[cfg(target_arch = "wasm32")]
//     unsafe {
//         core::arch::wasm32::unreachable()
//     }
//     #[cfg(not(target_arch = "wasm32"))]
//     loop {}
// }

// Provide some re-exports to make it easier to use the library.
// This should be expanded in the future.
/// Re-export.
#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "std"))]
pub use alloc::{borrow::ToOwned, string, string::String, string::ToString, vec, vec::Vec};
/// Re-export.
#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "std"))]
pub use core::{convert, hash, marker, mem, num, result::*};
#[cfg(not(feature = "hacspec"))]
#[cfg(feature = "std")]
pub(crate) use std::vec;

/// Re-export.
#[cfg(not(feature = "hacspec"))]
#[cfg(feature = "std")]
pub use std::{convert, hash, marker, mem, num, string::String, vec::Vec};

#[cfg(not(feature = "hacspec"))]
pub mod collections {
    #[cfg(not(feature = "std"))]
    use alloc::collections;
    #[cfg(feature = "std")]
    use std::collections;

    pub use collections::*;
    pub use concordium_contracts_common::{HashMap, HashSet};
}

#[cfg(not(feature = "hacspec"))]
/// Chain constants that impose limits on various aspects of smart contract
/// execution.
pub use concordium_contracts_common::*;

#[cfg(not(feature = "hacspec"))]
pub use hacspec_concordium_derive::*;

#[cfg(not(feature = "hacspec"))]
extern crate wee_alloc;
// Use `wee_alloc` as the global allocator to reduce code size.
#[cfg(not(feature = "hacspec"))]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[cfg(not(feature = "hacspec"))]
pub mod test_infrastructure;

mod hacspec_concordium_types;
mod hacspec_concordium_traits;
mod hacspec_concordium_prims;
mod hacspec_concordium_impls;

#[cfg(not(feature = "hacspec"))]
pub use hacspec_concordium_types::*;
#[cfg(not(feature = "hacspec"))]
pub use hacspec_concordium_traits::*;
#[cfg(not(feature = "hacspec"))]
pub use hacspec_concordium_prims::*;
#[cfg(not(feature = "hacspec"))]
pub use hacspec_concordium_impls::*;