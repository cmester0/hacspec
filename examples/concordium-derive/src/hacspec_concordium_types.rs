#[cfg(not(feature = "hacspec"))]
use crate::num::NonZeroI32;

#[cfg(not(feature = "hacspec"))]
/// A type representing the constract state bytes.
#[derive(Default)]
pub struct ContractState {
    pub(crate) current_position: u32,
}

#[cfg(not(feature = "hacspec"))]
#[derive(Default)]
/// A type representing the parameter to init and receive methods.
pub struct Parameter {
    pub(crate) current_position: u32,
}

#[cfg(not(feature = "hacspec"))]
/// A type representing the attributes, lazily acquired from the host.
#[derive(Default)]
pub struct AttributesCursor {
    /// Current position of the cursor, starting from 0.
    /// Note that this is only for the variable attributes.
    /// `created_at` and `valid_to` will require.
    pub(crate) current_position: u32,
    /// The number of remaining items in the policy.
    pub(crate) remaining_items:  u16,
}

#[cfg(not(feature = "hacspec"))]
/// A type representing the logger.
#[derive(Default)]
pub struct Logger {
    pub(crate) _private: (),
}

// #[cfg(not(feature = "hacspec"))]
/// Errors that can occur during logging.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum LogError {
    /// The log is full.
    Full,
    /// The message to log was malformed (e.g., too long)
    Malformed,
}

#[cfg(not(feature = "hacspec"))]
/// Actions that can be produced at the end of a contract execution. This
/// type is deliberately not cloneable so that we can enforce that
/// `and_then` and `or_else` can only be used when more than one event is
/// created.
///
/// This type is marked as `must_use` since functions that produce
/// values of the type are effectful.
#[must_use]
pub struct Action {
    pub(crate) _private: u32,
}

#[cfg(not(feature = "hacspec"))]
impl Action {
    pub fn tag(&self) -> u32 { self._private }
}

#[cfg(not(feature = "hacspec"))]
/// An error message, signalling rejection of a smart contract invocation.
/// The client will see the error code as a reject reason; if a schema is
/// provided, the error message corresponding to the error code will be
/// displayed. The valid range for an error code is from i32::MIN to  -1.
#[derive(Eq, PartialEq)] // TODO: Creusot issue re-add "Debug" attribute 
#[repr(transparent)]
pub struct Reject {
    pub error_code: NonZeroI32,
}

#[cfg(not(feature = "hacspec"))]
/// Default error is i32::MIN.
impl Default for Reject {
    #[inline(always)]
    fn default() -> Self {
	Self {
	    error_code: unsafe { NonZeroI32::new_unchecked(i32::MIN) },
	}
    }
}

#[cfg(not(feature = "hacspec"))]
impl Reject {
    /// This returns `None` for all values >= 0 and `Some` otherwise.
    pub fn new(x: i32) -> Option<Self> {
	if x < 0 {
	    let error_code = unsafe { NonZeroI32::new_unchecked(x) };
	    Some(Reject {
		error_code,
	    })
	} else {
	    None
	}
    }
}

// Macros for failing a contract function

#[cfg(not(feature = "hacspec"))]
/// The `bail` macro can be used for cleaner error handling. If the function has
/// result type `Result` invoking `bail` will terminate execution early with an
/// error.
/// If an argument is supplied, this will be used as the error, otherwise it
/// requires the type `E` in `Result<_, E>` to implement the `Default` trait.
#[macro_export]
macro_rules! bail {
    () => {{
	return Err(Default::default());
    }};
    ($arg:expr) => {{
	// format_err!-like formatting
	// logs are only retained in case of rejection when testing.
	return Err($arg);
    }};
}

#[cfg(not(feature = "hacspec"))]
/// The `ensure` macro can be used for cleaner error handling. It is analogous
/// to `assert`, but instead of panicking it uses `bail` to terminate execution
/// of the function early.
#[macro_export]
macro_rules! ensure {
    ($p:expr) => {
	if !$p {
	    $crate::bail!();
	}
    };
    ($p:expr, $arg:expr) => {{
	if !$p {
	    $crate::bail!($arg);
	}
    }};
}

#[cfg(not(feature = "hacspec"))]
/// ## Variants of `ensure` for ease of use in certain contexts.
/// Ensure the first two arguments are equal, using `bail` otherwise.
#[macro_export]
macro_rules! ensure_eq {
    ($l:expr, $r:expr) => {
	$crate::ensure!($l == $r)
    };
    ($l:expr, $r:expr, $arg:expr) => {
	$crate::ensure!($l == $r, $arg)
    };
}

#[cfg(not(feature = "hacspec"))]
#[macro_export]
/// Ensure the first two arguments are __not__ equal, using `bail` otherwise.
macro_rules! ensure_ne {
    ($l:expr, $r:expr) => {
	$crate::ensure!($l != $r)
    };
    ($l:expr, $r:expr, $arg:expr) => {
	$crate::ensure!($l != $r, $arg)
    };
}

// Macros for failing a test

#[cfg(not(feature = "hacspec"))]
/// The `fail` macro is used for testing as a substitute for the panic macro.
/// It reports back error information to the host.
/// Used only in testing.
#[cfg(feature = "std")]
#[macro_export]
macro_rules! fail {
    () => {
	{
	    $crate::test_infrastructure::report_error("", file!(), line!(), column!());
	    panic!()
	}
    };
    ($($arg:tt),+) => {
	{
	    let msg = format!($($arg),+);
	    $crate::test_infrastructure::report_error(&msg, file!(), line!(), column!());
	    panic!("{}", msg)
	}
    };
}

#[cfg(not(feature = "hacspec"))]
/// The `fail` macro is used for testing as a substitute for the panic macro.
/// It reports back error information to the host.
/// Used only in testing.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! fail {
    () => {
	{
	    $crate::test_infrastructure::report_error("", file!(), line!(), column!());
	    panic!()
	}
    };
    ($($arg:tt),+) => {
	{
	    let msg = &$crate::alloc::format!($($arg),+);
	    $crate::test_infrastructure::report_error(&msg, file!(), line!(), column!());
	    panic!("{}", msg)
	}
    };
}

#[cfg(not(feature = "hacspec"))]
/// The `claim` macro is used for testing as a substitute for the assert macro.
/// It checks the condition and if false it reports back an error.
/// Used only in testing.
#[macro_export]
macro_rules! claim {
    ($cond:expr) => {
	if !$cond {
	    $crate::fail!()
	}
    };
    ($cond:expr,) => {
	if !$cond {
	    $crate::fail!()
	}
    };
    ($cond:expr, $($arg:tt),+) => {
	if !$cond {
	    $crate::fail!($($arg),+)
	}
    };
}

#[cfg(not(feature = "hacspec"))]
/// Ensure the first two arguments are equal, just like `assert_eq!`, otherwise
/// reports an error. Used only in testing.
#[macro_export]
macro_rules! claim_eq {
    ($left:expr, $right:expr) => {
	$crate::claim!($left == $right, "left and right are not equal\nleft: {:?}\nright: {:?}", $left, $right)
    };
    ($left:expr, $right:expr,) => {
	$crate::claim_eq!($left, $right)
    };
    ($left:expr, $right:expr, $($arg:tt),+) => {
	$crate::claim!($left == $right, $($arg),+)
    };
}

#[cfg(not(feature = "hacspec"))]
/// Ensure the first two arguments are *not* equal, just like `assert_ne!`,
/// otherwise reports an error.
/// Used only in testing.
#[macro_export]
macro_rules! claim_ne {
    ($left:expr, $right:expr) => {
	$crate::claim!($left != $right)
    };
    ($left:expr, $right:expr,) => {
	$crate::claim!($left != $right)
    };
    ($left:expr, $right:expr, $($arg:tt),+) => {
	$crate::claim!($left != $right, $($arg),+)
    };
}

#[cfg(not(feature = "hacspec"))]
/// The expected return type of the receive method of a smart contract.
///
/// Optionally, to define a custom type for error instead of using
/// Reject, allowing to track the reason for rejection, *but only in unit
/// tests*.
///
/// See also the documentation for [bail!](macro.bail.html) for how to use
/// custom error types.
///
/// # Example
/// Defining a custom error type
/// ```rust
/// enum MyCustomError {
///     SomeError
/// }
///
/// #[receive(contract = "mycontract", name = "receive")]
/// fn contract_receive<R: HasReceiveContext, L: HasLogger, A: HasActions>(
///     ctx: &R,
///     receive_amount: Amount,
///     logger: &mut L,
///     state: &mut State,
/// ) -> Result<A, MyCustomError> { ... }
/// ```
pub type ReceiveResult<A> = Result<A, Reject>;

#[cfg(not(feature = "hacspec"))]
/// The expected return type of the init method of the smart contract,
/// parametrized by the state type of the smart contract.
///
/// Optionally, to define a custom type for error instead of using Reject,
/// allowing the track the reason for rejection, *but only in unit tests*.
///
/// See also the documentation for [bail!](macro.bail.html) for how to use
/// custom error types.
///
/// # Example
/// Defining a custom error type
/// ```rust
/// enum MyCustomError {
///     SomeError
/// }
///
/// #[init(contract = "mycontract")]
/// fn contract_init<R: HasReceiveContext, L: HasLogger, A: HasActions>(
///     ctx: &R,
///     receive_amount: Amount,
///     logger: &mut L,
/// ) -> Result<State, MyCustomError> { ... }
/// ```
pub type InitResult<S> = Result<S, Reject>;


#[cfg(not(feature = "hacspec"))]
/// Context backed by host functions.
#[derive(Default)]
#[doc(hidden)]
pub struct ExternContext<T: sealed::ContextType> {
    marker: crate::marker::PhantomData<T>,
}

#[cfg(not(feature = "hacspec"))]
#[doc(hidden)]
pub struct ChainMetaExtern {}

#[cfg(not(feature = "hacspec"))]
#[derive(Default)]
#[doc(hidden)]
pub struct InitContextExtern;
#[cfg(not(feature = "hacspec"))]
#[derive(Default)]
#[doc(hidden)]
pub struct ReceiveContextExtern;

#[cfg(not(feature = "hacspec"))]
pub(crate) mod sealed {
    use super::*;
    /// Marker trait intended to indicate which context type we have.
    /// This is deliberately a sealed trait, so that it is only implementable
    /// by types in this crate.
    pub trait ContextType {}
    impl ContextType for InitContextExtern {}
    impl ContextType for ReceiveContextExtern {}
}