#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

use hacspec_lib::*;

// #[cfg(feature = "hacspec_attributes")]
#[cfg(feature = "hacspec")]
use hacspec_attributes::*;

// Rust-hacspec Interface
#[cfg(not(feature = "hacspec"))]
extern crate concordium_std;
#[cfg(not(feature = "hacspec"))]
use concordium_std::{
    AccountAddress, Address, Amount, AttributeTag, ContractAddress, HasActions, HasChainMetadata,
    HasCommonData, HasContractState, HasInitContext, HasParameter, HasPolicy, HasReceiveContext,
    IdentityProvider, ParseError, ParseResult, Read, ReceiveName, Seek, SlotTime, Timestamp, Write,
    ACCOUNT_ADDRESS_SIZE,
    Serial,
    Deserial,
};

#[cfg(not(feature = "hacspec"))]
// use ::std::collections::{BTreeMap, BTreeSet};
use std::{ // ::std::
    collections::{BTreeMap, BTreeSet, HashSet, HashMap},
    convert::{self, TryFrom, TryInto},
    hash::Hash,
    mem,
    num, // prims,
    // prims::*,
    // traits::*,
    // types::*,
    vec::Vec,
    // String,
};

// #[cfg(not(feature = "hacspec"))]
// extern crate concordium_contracts_common;
// #[cfg(not(feature = "hacspec"))]
// use concordium_contracts_common::*; // {Serial}

#[cfg(not(feature = "hacspec"))]
use mem::MaybeUninit;

// Creusot
#[cfg(not(feature = "hacspec"))]
extern crate creusot_contracts;
#[cfg(not(feature = "hacspec"))]
use creusot_contracts::{
    ensures,
    requires,
    trusted	  
    };

#[cfg(not(feature = "hacspec"))]
#[derive(Eq, PartialEq, Debug)]
#[repr(transparent)]
pub struct Reject {
    pub error_code: crate::num::NonZeroI32,
}

pub type RejectHacspec = i32;

pub fn reject_impl_deafult() -> RejectHacspec {
    i32::MIN
}

pub fn new_reject_impl(x: i32) -> Option<RejectHacspec> {
    if x < 0i32 {
	Option::<i32>::Some(x)
    } else {
	Option::<i32>::None
    }
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_reject(hacspec_reject: RejectHacspec) -> Reject {
    Reject {
	error_code: unsafe { num::NonZeroI32::new_unchecked(hacspec_reject) },
    }
}

#[cfg(not(feature = "hacspec"))]
/// Default error is i32::MIN.
impl Default for Reject {
    #[inline(always)]
    fn default() -> Self {
	Self {
	    error_code: unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN) },
	}
    }
}

#[cfg(not(feature = "hacspec"))]
impl Reject {
    /// This returns `None` for all values >= 0 and `Some` otherwise.
    pub fn new(x: i32) -> Option<Self> {
	if x < 0 {
	    let error_code = unsafe { crate::num::NonZeroI32::new_unchecked(x) };
	    Some(Reject { error_code })
	} else {
	    None
	}
    }
}

#[ensures(!(result === 0i32))] // !=
pub fn reject_impl_convert_from_unit() -> RejectHacspec {
    i32::MIN + 1i32
}

#[ensures(!(result === 0i32))] // !=
pub fn reject_impl_convert_from_parse_error() -> RejectHacspec {
    i32::MIN + 2i32
}

#[cfg(not(feature = "hacspec"))]
impl convert::From<()> for Reject {
    #[inline(always)]
    fn from(_: ()) -> Self {
	coerce_hacspec_to_rust_reject(reject_impl_convert_from_unit())
    }
}

#[cfg(not(feature = "hacspec"))]
impl convert::From<ParseError> for Reject {
    #[inline(always)]
    fn from(_: ParseError) -> Self {
	coerce_hacspec_to_rust_reject(reject_impl_convert_from_parse_error())
    }
}

/// Errors that can occur during logging.
#[derive(Copy, Clone)] // , Debug, Eq, PartialEq
#[repr(u8)]
pub enum LogError {
    /// The log is full.
    Full,
    /// The message to log was malformed (e.g., too long)
    Malformed,
}

#[ensures(!(result === 0i32))] // !=
pub fn reject_impl_from_log_error(le: LogError) -> RejectHacspec {
    match le {
	LogError::Full => i32::MIN + 3i32,
	LogError::Malformed => i32::MIN + 4i32,
    }
}

#[cfg(not(feature = "hacspec"))]
/// Full is mapped to i32::MIN+3, Malformed is mapped to i32::MIN+4.
impl From<LogError> for Reject {
    #[inline(always)]
    fn from(le: LogError) -> Self {
	coerce_hacspec_to_rust_reject(reject_impl_from_log_error(le))
    }
}

#[derive(Clone)] // , Debug, PartialEq, Eq
pub enum NewContractNameError {
    NewContractNameErrorMissingInitPrefix,
    NewContractNameErrorTooLong,
    NewContractNameErrorContainsDot,
    NewContractNameErrorInvalidCharacters,
}

#[ensures(!(result === 0i32))] // !=
pub fn reject_impl_from_new_contract_name_error(nre: NewContractNameError) -> RejectHacspec {
    match nre {
	NewContractNameError::NewContractNameErrorMissingInitPrefix => i32::MIN + 5i32,
	NewContractNameError::NewContractNameErrorTooLong => i32::MIN + 6i32,
	NewContractNameError::NewContractNameErrorContainsDot => i32::MIN + 9i32,
	NewContractNameError::NewContractNameErrorInvalidCharacters => i32::MIN + 10i32,
    }
}

#[cfg(not(feature = "hacspec"))]
/// MissingInitPrefix is mapped to i32::MIN + 5,
/// TooLong to i32::MIN + 6,
/// ContainsDot to i32::MIN + 9, and
/// InvalidCharacters to i32::MIN + 10.
impl From<NewContractNameError> for Reject {
    fn from(nre: NewContractNameError) -> Self {
	coerce_hacspec_to_rust_reject(reject_impl_from_new_contract_name_error(nre))
    }
}

#[derive(Clone)] // , Debug, PartialEq, Eq
pub enum NewReceiveNameError {
    NewReceiveNameErrorMissingDotSeparator,
    NewReceiveNameErrorTooLong,
    NewReceiveNameErrorInvalidCharacters,
}

#[ensures(!(result === 0i32))] // !=
pub fn reject_impl_from_new_receive_name_error(nre: NewReceiveNameError) -> RejectHacspec {
    match nre {
	NewReceiveNameError::NewReceiveNameErrorMissingDotSeparator => i32::MIN + 7i32,
	NewReceiveNameError::NewReceiveNameErrorTooLong => i32::MIN + 8i32,
	NewReceiveNameError::NewReceiveNameErrorInvalidCharacters => i32::MIN + 11i32,
    }
}

#[cfg(not(feature = "hacspec"))]
/// MissingDotSeparator is mapped to i32::MIN + 7,
/// TooLong to i32::MIN + 8, and
/// InvalidCharacters to i32::MIN + 11.
impl From<NewReceiveNameError> for Reject {
    fn from(nre: NewReceiveNameError) -> Self {
	coerce_hacspec_to_rust_reject(reject_impl_from_new_receive_name_error(nre))
    }
}

#[cfg(not(feature = "hacspec"))]
/// A type representing the constract state bytes.
#[derive(Default)]
pub struct ContractState {
    pub(crate) current_position: u32,
}

pub type ContractStateHacspec = u32;

#[derive(Copy, Clone)] // , Debug, PartialEq, Eq
pub enum SeekFrom {
    /// Sets the offset to the provided number of bytes.
    Start(u64),

    /// Sets the offset to the size of this object plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    End(i64),

    /// Sets the offset to the current position plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    Current(i64),
}

pub type U32Option = Option<u32>;
pub type I64Option = Option<i64>;

// #[requires(forall<delta : i64> pos === SeekFrom::End(delta) ==> exists<b : u32> current_position.checked_add(delta as u32) == U32Option::Some(b))]
pub fn contract_state_impl_seek(current_position: ContractStateHacspec, pos: SeekFrom) -> Result<(ContractStateHacspec, u64), ()> {
    match pos {
	SeekFrom::Start(offset) => Result::<(ContractStateHacspec, u64), ()>::Ok((offset as u32, offset)),
	SeekFrom::End(delta) => {
	    if delta >= 0_i64 {
		match current_position.checked_add(delta as u32) {
		    U32Option::Some(b) => Result::<(ContractStateHacspec, u64), ()>::Ok((b, delta as u64)),
		    U32Option::None => Result::<(ContractStateHacspec, u64), ()>::Err(()),
		}
	    } else {
		match delta.checked_abs() {
		    I64Option::Some(b) =>
		    {
			Result::<(ContractStateHacspec, u64), ()>::Ok(((4_u32 - (b as u32)), (4_u32 - (b as u32)) as u64))
		    }
		    I64Option::None => Result::<(ContractStateHacspec, u64), ()>::Err(()),
		}
	    }
	}
	SeekFrom::Current(delta) => {
	    if delta >= 0_i64 {
		match current_position.checked_add(delta as u32) {
		    U32Option::Some(offset) => Result::<(ContractStateHacspec, u64), ()>::Ok((offset, offset as u64)),
		    U32Option::None => Result::<(ContractStateHacspec, u64), ()>::Err(()),
		}
	    } else {
		match delta.checked_abs() {
		    I64Option::Some(b) => match current_position.checked_sub(b as u32) {
			U32Option::Some(offset) => Result::<(ContractStateHacspec, u64), ()>::Ok((offset, offset as u64)),
			U32Option::None => Result::<(ContractStateHacspec, u64), ()>::Err(()),
		    },
		    I64Option::None => Result::<(ContractStateHacspec, u64), ()>::Err(()),
		}
	    }
	}
    }
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_contract_state(
    rust_contract_state: &mut ContractState,
) -> ContractStateHacspec {
    rust_contract_state.current_position.clone()
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_contract_state(
    rust_contract_state: &mut ContractState,
    hacspec_contract_state: ContractStateHacspec,
) {
    rust_contract_state.current_position = hacspec_contract_state;
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_seek_result(
    rust_contract_state: &mut ContractState,
    hacspec_seek_result: Result<(ContractStateHacspec, u64), ()>,
) -> Result<u64, ()> {
    let (hacspec_result, rust_result) = hacspec_seek_result?;
    coerce_hacspec_to_rust_contract_state(rust_contract_state, hacspec_result);
    Ok(rust_result)
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_seek_from(rust_seek_from: concordium_std::SeekFrom) -> SeekFrom {
    match rust_seek_from {
	concordium_std::SeekFrom::Start(v) => SeekFrom::Start(v),
	concordium_std::SeekFrom::End(v) => SeekFrom::End(v),
	concordium_std::SeekFrom::Current(v) => SeekFrom::Current(v),
    }
}

#[cfg(not(feature = "hacspec"))]
/// # Contract state trait implementations.
impl Seek for ContractState {
    type Err = ();

    fn seek(&mut self, pos: concordium_std::SeekFrom) -> Result<u64, Self::Err> {
	let contract_state = coerce_rust_to_hacspec_contract_state(self);
	coerce_hacspec_to_rust_seek_result(
	    self,
	    contract_state_impl_seek(
		contract_state,
		coerce_rust_to_hacspec_seek_from(pos),
	    ),
	)
    }
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_public_byte_seq(buf: &[u8]) -> PublicByteSeq {
    PublicByteSeq::from_native_slice(buf)
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_public_byte_seq(buf: PublicByteSeq) -> Vec<u8> {
    let mut temp_vec: Vec<u8> = Vec::new();
    for i in 0..buf.len() {
	temp_vec.push(buf.index(i).clone())
    }
    temp_vec
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    pub(crate) fn load_state(start: *mut u8, length: u32, offset: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn load_state_creusot(start: *mut u8, length: u32, offset: u32) -> u32 {
    unsafe { load_state(start, length, offset) }
}

#[cfg(feature = "hacspec")]
fn load_state_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (buf, 1u32)
}

#[cfg(not(feature = "hacspec"))]
fn load_state_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(buf.clone())[..];
    let result = load_state_creusot(temp.as_mut_ptr(), buf.len() as u32, offset);
    (
	coerce_rust_to_hacspec_public_byte_seq(&temp),
	result,
    )
}

pub fn contract_state_impl_read_read(
    current_position: ContractStateHacspec,
    buf : PublicByteSeq,
) -> (ContractStateHacspec, usize) {
    let (buf, num_read) = load_state_hacspec(buf, current_position);
    (current_position + num_read, num_read as usize)
}

/// Read a u32 in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
pub fn contract_state_impl_read_read_u64(
    current_position: ContractStateHacspec,
) -> (ContractStateHacspec, u64) {
    // let mut bytes: MaybeUninit<[u8; 8]> = MaybeUninit::uninit();
    let buf = PublicByteSeq::new(8);
    let (buf, num_read) = load_state_hacspec(buf, current_position);
    (current_position + num_read, u64_from_le_bytes(u64Word::from_seq(&buf))) // num_read as u64
}

/// Read a u32 in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
pub fn contract_state_impl_read_read_u32(
    current_position: ContractStateHacspec,
) -> (ContractStateHacspec, u32) {
    // let mut bytes: MaybeUninit<[u8; 4]> = MaybeUninit::uninit();
    let buf = PublicByteSeq::new(4);
    let (buf, num_read) = load_state_hacspec(buf, current_position);
    (current_position + num_read, u32_from_le_bytes(u32Word::from_seq(&buf))) // num_read as u64
}

/// Read a u8 in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
pub fn contract_state_impl_read_read_u8(
    current_position: ContractStateHacspec,
) -> (ContractStateHacspec, u8) {
    let buf = PublicByteSeq::new(1);
    let (buf, num_read) = load_state_hacspec(buf, current_position);
    (current_position + num_read, buf[0]) // num_read as u64
}

#[cfg(not(feature = "hacspec"))]
impl Read for ContractState {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
	let (cs, nr) = contract_state_impl_read_read(
	    coerce_rust_to_hacspec_contract_state(self),
	    coerce_rust_to_hacspec_public_byte_seq(buf),
	);
	coerce_hacspec_to_rust_contract_state(self, cs);
	Ok(nr)
    }

    // TODO: !! Probably incorrect !!
    /// Read a `u32` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u64(&mut self) -> ParseResult<u64> {
	let (cs, nr) =
	    contract_state_impl_read_read_u64(coerce_rust_to_hacspec_contract_state(self));
	coerce_hacspec_to_rust_contract_state(self, cs);
	Ok(nr)
	// if num_read == 8 {
	//     unsafe { Ok(u64::from_le_bytes(bytes.assume_init())) }
	// } else {
	//     Err(ParseError::default())
	// }
    }

    /// Read a `u32` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u32(&mut self) -> ParseResult<u32> {
	let (cs, nr) =
	    contract_state_impl_read_read_u32(coerce_rust_to_hacspec_contract_state(self));
	coerce_hacspec_to_rust_contract_state(self, cs);
	Ok(nr)

	// let mut bytes: MaybeUninit<[u8; 4]> = MaybeUninit::uninit();
	// let num_read =
	//     unsafe { load_state(bytes.as_mut_ptr() as *mut u8, 4, self.current_position) };
	// self.current_position += num_read;
	// if num_read == 4 {
	//     unsafe { Ok(u32::from_le_bytes(bytes.assume_init())) }
	// } else {
	//     Err(ParseError::default())
	// }
    }

    /// Read a `u8` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u8(&mut self) -> ParseResult<u8> {
	let (cs, nr) =
	    contract_state_impl_read_read_u8(coerce_rust_to_hacspec_contract_state(self));
	coerce_hacspec_to_rust_contract_state(self, cs);
	Ok(nr)
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    pub(crate) fn write_state(start: *mut u8, length: u32, offset: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn write_state_creusot(start: *mut u8, length: u32, offset: u32) -> u32 {
    unsafe { write_state(start, length, offset) }
}

#[cfg(feature = "hacspec")]
fn write_state_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (buf, 1u32)
}

#[cfg(not(feature = "hacspec"))]
fn write_state_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(buf.clone())[..];
    let result = write_state_creusot(temp.as_mut_ptr(), buf.len() as u32, offset);
    (
	coerce_rust_to_hacspec_public_byte_seq(&temp),
	result,
    )
}

pub fn contract_state_impl_write(
    current_position: ContractStateHacspec,
    buf : PublicByteSeq
) -> Result<(ContractStateHacspec, usize), ()> {
    if current_position.checked_add(buf.len() as u32).is_none() {
	Result::<(ContractStateHacspec, usize), ()>::Err(())?;
    }
    let (buf, num_bytes) = write_state_hacspec(buf, current_position);
    Result::<(ContractStateHacspec, usize), ()>::Ok((current_position + num_bytes, num_bytes as usize))
}

#[cfg(not(feature = "hacspec"))]
impl Write for ContractState {
    type Err = ();

    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err> {
	let (cs, nr) = contract_state_impl_write(
	    coerce_rust_to_hacspec_contract_state(self),
	    coerce_rust_to_hacspec_public_byte_seq(buf),
	)?;
	coerce_hacspec_to_rust_contract_state(self, cs);
	Ok(nr)
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    pub(crate) fn state_size() -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn state_size_creusot() -> u32 {
    unsafe { state_size() }
}

#[cfg(feature = "hacspec")]
fn state_size_hacspec() -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
fn state_size_hacspec() -> u32 {
    state_size_creusot()
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    // Resize state to the new value (truncate if new size is smaller). Return 0 if
    // this was unsuccesful (new state too big), or 1 if successful.
    pub(crate) fn resize_state(new_size: u32) -> u32; // returns 0 or 1.
						      // get current state size in bytes.
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn resize_state_creusot(new_size: u32) -> u32 {
    unsafe { resize_state(new_size) }
}

#[cfg(feature = "hacspec")]
fn resize_state_hacspec(new_size: u32) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
fn resize_state_hacspec(new_size: u32) -> u32 {
    resize_state_creusot(new_size)
}

pub fn has_contract_state_impl_for_contract_state_open() -> ContractStateHacspec {
    0_u32
}

// pub fn has_contract_state_impl_for_contract_state_reserve_0(len: u32, cur_size: u32) -> bool {
//     cur_size < len
// }

// pub fn has_contract_state_impl_for_contract_state_reserve_1(res: u32) -> bool {
//     res == 1_u32
// }

pub fn has_contract_state_impl_for_contract_state_reserve(
    contract_state: ContractStateHacspec,
    len: u32,
) -> bool {
    let cur_size = state_size_hacspec();
    if cur_size < len {
	resize_state_hacspec(len) == 1_u32
    } else {
	true
    }
}

pub fn has_contract_state_impl_for_contract_state_truncate(
    current_position : ContractStateHacspec,
    cur_size: u32,
    new_size: u32,
) -> ContractStateHacspec {
    if cur_size > new_size {
	resize_state_hacspec(new_size);
    }
    if new_size < current_position {
	new_size
    }
    else {
	current_position
    }
}

#[cfg(not(feature = "hacspec"))]
impl HasContractState<()> for ContractState {
    type ContractStateData = ();

    #[inline(always)]
    fn open(_: Self::ContractStateData) -> Self {
	ContractState {
	    current_position: has_contract_state_impl_for_contract_state_open(),
	}
    }

    fn reserve(&mut self, len: u32) -> bool {
	has_contract_state_impl_for_contract_state_reserve(
	    coerce_rust_to_hacspec_contract_state(self),
	    len,
	)
    }

    #[inline(always)]
    fn size(&self) -> u32 {
	state_size_hacspec()
    }

    fn truncate(&mut self, new_size: u32) {
	let current_position = coerce_rust_to_hacspec_contract_state(self);
	coerce_hacspec_to_rust_contract_state(
	    self,
	    has_contract_state_impl_for_contract_state_truncate(
		current_position,
		self.size(),
		new_size,
	    ),
	)
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    // Write a section of the parameter to the given location. Return the number
    // of bytes written. The location is assumed to contain enough memory to
    // write the requested length into.
    pub(crate) fn get_parameter_section(param_bytes: *mut u8, length: u32, offset: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_parameter_section_creusot(start: *mut u8, length: u32, offset: u32) -> u32 {
    unsafe { get_parameter_section(start, length, offset) }
}

#[cfg(feature = "hacspec")]
fn get_parameter_section_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (buf, 1u32)
}

#[cfg(not(feature = "hacspec"))]
fn get_parameter_section_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(buf.clone())[..];
    let result = get_parameter_section_creusot(temp.as_mut_ptr(), buf.len() as u32, offset);
    (
	coerce_rust_to_hacspec_public_byte_seq(&temp),
	result,
    )
}

#[cfg(not(feature = "hacspec"))]
#[derive(Default)]
/// A type representing the parameter to init and receive methods.
pub struct Parameter {
    pub(crate) current_position: u32,
}

pub type ParameterHacspec = u32;

pub fn read_impl_for_parameter_read(
    current_position: ParameterHacspec,
    buf: PublicByteSeq,
) -> (ParameterHacspec, usize) {
    let (buf, num_read) = get_parameter_section_hacspec(buf, current_position);
    (current_position + num_read, num_read as usize)
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_parameter(
    rust_parameter: &mut Parameter,
) -> ParameterHacspec {
    rust_parameter.current_position.clone()
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_parameter(
    rust_parameter: &mut Parameter,
    hacspec_parameter: ParameterHacspec,
) {
    rust_parameter.current_position = hacspec_parameter;
}


#[cfg(not(feature = "hacspec"))]
/// # Trait implementations for Parameter
impl Read for Parameter {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
	let (cs, nr) = read_impl_for_parameter_read(
	    coerce_rust_to_hacspec_parameter(self),
	    coerce_rust_to_hacspec_public_byte_seq(buf),
	);
	coerce_hacspec_to_rust_parameter(self, cs);
	Ok(nr)
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    // Get the size of the parameter to the method (either init or receive).
    pub(crate) fn get_parameter_size() -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_parameter_size_creusot() -> u32 {
    unsafe { get_parameter_size() }
}

#[cfg(feature = "hacspec")]
fn get_parameter_size_hacspec() -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
fn get_parameter_size_hacspec() -> u32 {
    get_parameter_size_creusot()
}

#[cfg(not(feature = "hacspec"))]
impl HasParameter for Parameter {
    #[inline(always)]
    fn size(&self) -> u32 {
	get_parameter_size_hacspec()
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Getters for the chain meta data
  /// Slot time (in milliseconds) from chain meta data
  pub(crate) fn get_slot_time() -> u64;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_slot_time_creusot() -> u64 {
    unsafe { get_slot_time() }
}

#[cfg(feature = "hacspec")]
fn get_slot_time_hacspec() -> u64 {
    1u64
}

#[cfg(not(feature = "hacspec"))]
fn get_slot_time_hacspec() -> u64 {
    get_slot_time_creusot()
}

// TODO: Get functionlity into hacspec
#[cfg(not(feature = "hacspec"))]
#[doc(hidden)]
pub struct ChainMetaExtern {}

#[cfg(not(feature = "hacspec"))]
/// # Trait implementations for the chain metadata.
impl HasChainMetadata for ChainMetaExtern {
    #[inline(always)]
    fn slot_time(&self) -> SlotTime {
	Timestamp::from_timestamp_millis(get_slot_time_hacspec() )
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Write a section of the policy to the given location. Return the number
  // of bytes written. The location is assumed to contain enough memory to
  // write the requested length into.
  pub(crate) fn get_policy_section(policy_bytes: *mut u8, length: u32, offset: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_policy_section_creusot(policy_bytes: *mut u8, length: u32, offset: u32) -> u32 {
    unsafe { get_policy_section(policy_bytes, length, offset) }
}

#[cfg(feature = "hacspec")]
fn get_policy_section_hacspec(policy_bytes: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (policy_bytes, 1u32)
}

#[cfg(not(feature = "hacspec"))]
fn get_policy_section_hacspec(policy_bytes: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(policy_bytes.clone())[..];
    let result = get_policy_section_creusot(temp.as_mut_ptr(), policy_bytes.len() as u32, offset);
    (
	coerce_rust_to_hacspec_public_byte_seq(&temp),
	result,
    )
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
    pub(crate) remaining_items: u16,
}

// pub struct AttributeTag(pub u8);
pub type AttributesCursorHacspec = (u32, u16);

// pub fn has_policy_impl_for_policy_attributes_cursor_next_test(
//     policy_attribute_items: AttributesCursorHacspec,
// ) -> bool {
//     let (_, remaining_items) = policy_attribute_items;
//     remaining_items == 0_u16
// }

// pub fn has_policy_impl_for_policy_attributes_cursor_next_tag_invalid(
//     policy_attribute_items: AttributesCursorHacspec,
//     tag_value_len_1: u8,
//     num_read: u32,
// ) -> (AttributesCursorHacspec, bool) {
//     let (current_position, remaining_items) = policy_attribute_items;
//     let policy_attribute_items = (current_position + num_read, remaining_items);
//     (policy_attribute_items, tag_value_len_1 > 31_u8)
// }

pub fn has_policy_impl_for_policy_attributes_cursor_next_item(
    policy_attribute_items: AttributesCursorHacspec,
    buf: PublicByteSeq,
) -> Option<(AttributesCursorHacspec, (u8, u8))> {

    let (mut current_position, mut remaining_items) = policy_attribute_items;

    if remaining_items == 0u16 {
	Option::<(AttributesCursorHacspec, (u8, u8))>::None?;
    }

    let (tag_value_len, num_read) = get_policy_section_hacspec(PublicByteSeq::new(2), current_position);
    current_position = current_position + num_read;

    if tag_value_len[1] > 31u8 {
	// Should not happen because all attributes fit into 31 bytes.
	Option::<(AttributesCursorHacspec, (u8, u8))>::None?;
    }

    let (buf, num_read) = get_policy_section_hacspec(buf, current_position);
    current_position = current_position + num_read;
    remaining_items = remaining_items - 1u16;
    Option::<(AttributesCursorHacspec, (u8, u8))>::Some(((current_position, remaining_items), (tag_value_len[0], tag_value_len[1])))
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_attributes_cursor(
    rust_attributes_cursor: &mut AttributesCursor,
) -> AttributesCursorHacspec {
    (rust_attributes_cursor.current_position.clone(), rust_attributes_cursor.remaining_items.clone())
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_attributes_cursor(
    rust_attributes_cursor: &mut AttributesCursor,
    hacspec_attributes_cursor: AttributesCursorHacspec,
) {
    let (current_position, remaining_items) = hacspec_attributes_cursor;
    rust_attributes_cursor.current_position = current_position;
    rust_attributes_cursor.remaining_items = remaining_items;
}

#[cfg(not(feature = "hacspec"))]
/// Policy on the credential of the account.
///
/// This is one of the key features of the Concordium blockchain. Each account
/// on the chain is backed by an identity. The policy is verified and signed by
/// the identity provider before an account can be created on the chain.
///
/// The type is parameterized by the choice of `Attributes`. These are either
/// borrowed or owned, in the form of an iterator over key-value pairs or a
/// vector of such. This flexibility is needed so that attributes can be
/// accessed efficiently, as well as constructed conveniently for testing.
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
#[derive(Debug, Clone)]
pub struct Policy<Attributes> {
    /// Identity of the identity provider who signed the identity object that
    /// this policy is derived from.
    pub identity_provider: IdentityProvider,
    /// Timestamp at the beginning of the month when the identity object backing
    /// this policy was created. This timestamp has very coarse granularity
    /// in order for the identity provider to not be able to link identities
    /// they have created with accounts that users created on the chain.
    /// as a timestamp (which has millisecond granularity) in order to make it
    /// easier to compare with, e.g., `slot_time`.
    pub created_at: Timestamp,
    /// Beginning of the month where the identity is __no longer valid__.
    pub valid_to: Timestamp,
    /// List of attributes, in ascending order of the tag.
    pub items: Attributes,
}

#[cfg(not(feature = "hacspec"))]
impl HasPolicy for Policy<AttributesCursor> {
    fn identity_provider(&self) -> IdentityProvider {
	self.identity_provider
    }

    fn created_at(&self) -> Timestamp {
	self.created_at
    }

    fn valid_to(&self) -> Timestamp {
	self.valid_to
    }

    fn next_item(&mut self, buf: &mut [u8; 31]) -> Option<(AttributeTag, u8)> {	  
	let (ac, (at, v)) = has_policy_impl_for_policy_attributes_cursor_next_item(
	    coerce_rust_to_hacspec_attributes_cursor(&mut self.items),
	    coerce_rust_to_hacspec_public_byte_seq(buf),
	)?;
	coerce_hacspec_to_rust_attributes_cursor(&mut self.items, ac);
	Some ((AttributeTag(at),v))
    }
}

#[cfg(not(feature = "hacspec"))]
/// An iterator over policies using host functions to supply the data.
/// The main interface to using this type is via the methods of the [Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html)
/// and [ExactSizeIterator](https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html) traits.
pub struct PoliciesIterator {
    /// Position in the policies binary serialization.
    pos: u32,
    /// Number of remaining items in the stream.
    remaining_items: u16,
}

pub type PoliciesIteratorHacspec = (u32, u16);

// TODO: use PolicyAttributesCursorHacspec for implementation above instead of just AttributesCursorHacspec
pub type PolicyAttributesCursorHacspec = (u32, u64, u64, AttributesCursorHacspec); // IdentityProvider, Timestamp, Timestamp, AttributesCursor

fn iterator_impl_for_policies_iterator_next(policies_iterator : PoliciesIteratorHacspec) -> Option<(PoliciesIteratorHacspec, PolicyAttributesCursorHacspec)> {
    let (mut pos, remaining_items) = policies_iterator;
    if remaining_items == 0u16 {
	Option::<(PoliciesIteratorHacspec, PolicyAttributesCursorHacspec)>::None?;
    }

    // 2 for total size of this section, 4 for identity_provider,
    // 8 bytes for created_at, 8 for valid_to, and 2 for
    // the length
    let (buf, _) = get_policy_section_hacspec(PublicByteSeq::new(2 + 4 + 8 + 8 + 2), pos);
    let skip_part: PublicByteSeq = buf.slice_range(0..2);
    let ip_part: PublicByteSeq = buf.slice_range(2..2 + 4);
    let created_at_part: PublicByteSeq = buf.slice_range(2 + 4..2 + 4 + 8);
    let valid_to_part: PublicByteSeq = buf.slice_range(2 + 4 + 8..2 + 4 + 8 + 8);
    let len_part: PublicByteSeq = buf.slice_range(2 + 4 + 8 + 8..2 + 4 + 8 + 8 + 2);
    let identity_provider = u32_from_le_bytes(u32Word::from_seq(&ip_part)); // IdentityProvider = u32 // UnsignedPublicInteger
    let created_at = u64_from_le_bytes(u64Word::from_seq(&created_at_part)); // Timestamp = Timestamp::from_timestamp_millis(u64)
    let valid_to = u64_from_le_bytes(u64Word::from_seq(&valid_to_part)); // Timestamp = u64)
    let mut remaining_items = u16_from_le_bytes(u16Word::from_seq(&len_part));
    let attributes_start = pos + 2u32 + 4u32 + 8u32 + 8u32 + 2u32;
    pos = pos + (u16_from_le_bytes(u16Word::from_seq(&skip_part)) as u32) + 2u32;
    remaining_items = remaining_items - 1u16;
    Option::<(PoliciesIteratorHacspec, PolicyAttributesCursorHacspec)>::Some(((pos, remaining_items),
	  (
	identity_provider,
	created_at,
	valid_to,
	(
	    attributes_start,
	    remaining_items,
	),
    )))
}

#[cfg(not(feature = "hacspec"))]
impl Iterator for PoliciesIterator {
    type Item = Policy<AttributesCursor>;

    fn next(&mut self) -> Option<Self::Item> {
	let ((pos, remaining_items), (identity_provider, created_at, valid_to, (cp,ri))) = iterator_impl_for_policies_iterator_next((self.pos, self.remaining_items))?;

	// TODO: make into coerce function
	self.pos = pos;
	self.remaining_items = remaining_items;

	Some(Policy {
	    identity_provider,
	    created_at: Timestamp::from_timestamp_millis(created_at),
	    valid_to: Timestamp::from_timestamp_millis(valid_to),
	    items: AttributesCursor {
		current_position: cp,
		remaining_items: ri,
	    },
	})
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
	let rem = self.remaining_items as usize;
	(rem, Some(rem))
    }
}

#[cfg(not(feature = "hacspec"))]
impl ExactSizeIterator for PoliciesIterator {
    #[inline(always)]
    fn len(&self) -> usize {
	self.remaining_items as usize
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Getter for the init context.
  /// Address of the sender, 32 bytes
  pub(crate) fn get_init_origin(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_init_origin_creusot(start: *mut u8) {
    unsafe { get_init_origin(start) }
}

#[cfg(feature = "hacspec")]
fn get_init_origin_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
fn get_init_origin_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_init_origin_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Invoker of the top-level transaction, AccountAddress.
  pub(crate) fn get_receive_invoker(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_invoker_creusot(start: *mut u8) {
    unsafe { get_receive_invoker(start) }
}

#[cfg(feature = "hacspec")]
fn get_receive_invoker_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
fn get_receive_invoker_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_receive_invoker_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Address of the contract itself, ContractAddress.
  pub(crate) fn get_receive_self_address(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_self_address_creusot(start: *mut u8) {
    unsafe { get_receive_self_address(start) }
}

#[cfg(feature = "hacspec")]
fn get_receive_self_address_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
fn get_receive_self_address_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_receive_self_address_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Self-balance of the contract, returns the amount
  pub(crate) fn get_receive_self_balance() -> u64;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_self_balance_creusot() -> u64 {
    unsafe { get_receive_self_balance() }
}

#[cfg(feature = "hacspec")]
fn get_receive_self_balance_hacspec() -> u64 {
    1u64
}

#[cfg(not(feature = "hacspec"))]
fn get_receive_self_balance_hacspec() -> u64 {
    get_receive_self_balance_creusot()
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Immediate sender of the message (either contract or account).
  pub(crate) fn get_receive_sender(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_sender_creusot(start: *mut u8) {
    unsafe { get_receive_sender(start) }
}

#[cfg(feature = "hacspec")]
fn get_receive_sender_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
fn get_receive_sender_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_receive_sender_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Owner of the contract, AccountAddress.
  pub(crate) fn get_receive_owner(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_owner_creusot(start: *mut u8) {
    unsafe { get_receive_owner(start) }
}

#[cfg(feature = "hacspec")]
fn get_receive_owner_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
fn get_receive_owner_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_receive_owner_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
/// Context backed by host functions.
#[derive(Default)]
#[doc(hidden)]
pub struct ExternContext<T: sealed::ContextType> {
    marker: concordium_std::marker::PhantomData<T>,
}

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

#[cfg(not(feature = "hacspec"))]
impl<T: sealed::ContextType> HasCommonData for ExternContext<T> {
    type MetadataType = ChainMetaExtern;
    type ParamType = Parameter;
    type PolicyIteratorType = PoliciesIterator;
    type PolicyType = Policy<AttributesCursor>;

    #[inline(always)]
    fn metadata(&self) -> &Self::MetadataType {
	&ChainMetaExtern {}
    }

    fn policies(&self) -> PoliciesIterator {
	let (buf, _) = get_policy_section_hacspec(PublicByteSeq::new(2), 0);
	PoliciesIterator {
	    pos: 2, // 2 because we already read 2 bytes.
	    remaining_items: u16_from_le_bytes(u16Word::from_seq(&buf)),
	}
    }

    #[inline(always)]
    fn parameter_cursor(&self) -> Self::ParamType {
	Parameter {
	    current_position: 0,
	}
    }
}

#[cfg(not(feature = "hacspec"))]
/// # Trait implementations for the init context
impl HasInitContext for ExternContext<InitContextExtern> {
    type InitData = ();

    /// Create a new init context by using an external call.
    fn open(_: Self::InitData) -> Self {
	ExternContext::default()
    }

    #[inline(always)]
    fn init_origin(&self) -> AccountAddress {
	let mut address: [u8; ACCOUNT_ADDRESS_SIZE] = Default::default();
	address.clone_from_slice(
	    &mut coerce_hacspec_to_rust_public_byte_seq(get_init_origin_hacspec(
		PublicByteSeq::new(ACCOUNT_ADDRESS_SIZE),
	    ))[..],
	);
	AccountAddress(address)
    }
}

#[cfg(not(feature = "hacspec"))]
/// # Trait implementations for the receive context
impl HasReceiveContext for ExternContext<ReceiveContextExtern> {
    type ReceiveData = ();

    /// Create a new receive context
    fn open(_: Self::ReceiveData) -> Self {
	ExternContext::default()
    }

    #[inline(always)]
    fn invoker(&self) -> AccountAddress {
	let mut address: [u8; ACCOUNT_ADDRESS_SIZE] = Default::default();
	address.clone_from_slice(
	    &mut coerce_hacspec_to_rust_public_byte_seq(get_receive_invoker_hacspec(
		PublicByteSeq::new(ACCOUNT_ADDRESS_SIZE),
	    ))[..],
	);
	AccountAddress(address)
    }

    #[inline(always)]
    fn self_address(&self) -> ContractAddress {
	let mut address: [u8; ACCOUNT_ADDRESS_SIZE] = Default::default();
	address.clone_from_slice(
	    &mut coerce_hacspec_to_rust_public_byte_seq(get_receive_self_address_hacspec(
		PublicByteSeq::new(ACCOUNT_ADDRESS_SIZE),
	    ))[..],
	);
	match concordium_std::from_bytes(&address) {
	    Ok(v) => v,
	    Err(_) => concordium_std::trap(),
	}
    }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
	Amount::from_micro_gtu(get_receive_self_balance_hacspec())
    }

    // TODO: Remove/replace unsafe code !
    #[inline(always)]
    fn sender(&self) -> Address {
	let ptr : *mut u8 = (&mut coerce_hacspec_to_rust_public_byte_seq(get_receive_sender_hacspec(
	    PublicByteSeq::new(ACCOUNT_ADDRESS_SIZE),
	))[..]).as_mut_ptr();
	let tag = unsafe { *ptr };
	match tag {
	    0u8 => {
		match concordium_std::from_bytes(unsafe { core::slice::from_raw_parts(
		    ptr.add(1),
		    ACCOUNT_ADDRESS_SIZE,
		)} ) {
		    Ok(v) => Address::Account(v),
		    Err(_) => concordium_std::trap(),
		}
	    }
	    1u8 => match concordium_std::from_bytes(unsafe { core::slice::from_raw_parts(ptr.add(1), 16) }) {
		Ok(v) => Address::Contract(v),
		Err(_) => concordium_std::trap(),
	    },
	    _ => concordium_std::trap(), // unreachable!("Host violated precondition."),
	}
    }

    #[inline(always)]
    fn owner(&self) -> AccountAddress {
	let mut address: [u8; ACCOUNT_ADDRESS_SIZE] = Default::default();
	address.clone_from_slice(
	    &mut coerce_hacspec_to_rust_public_byte_seq(get_receive_self_address_hacspec(
		PublicByteSeq::new(ACCOUNT_ADDRESS_SIZE),
	    ))[..],
	);
	AccountAddress(address)
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    // Add a log item. Return values are
    // - -1 if logging failed due to the message being too long
    // - 0 if the log is already full
    // - 1 if data was successfully logged.
    pub(crate) fn log_event(start: *const u8, length: u32) -> i32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn log_event_creusot(start: *const u8, length: u32) -> i32 {
    unsafe { log_event(start, length) }
}

#[cfg(feature = "hacspec")]
fn log_event_hacspec(start: PublicByteSeq) -> (PublicByteSeq, i32) {
    (start, 1i32)
}

#[cfg(not(feature = "hacspec"))]
fn log_event_hacspec(start: PublicByteSeq) -> (PublicByteSeq, i32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    let result = log_event_creusot(temp.as_ptr(), start.len() as u32);
    (coerce_rust_to_hacspec_public_byte_seq(&temp), result)
}

#[cfg(not(feature = "hacspec"))]
/// A type representing the logger.
#[derive(Default)]
pub struct Logger {
    pub(crate) _private: (),
}

#[cfg(not(feature = "hacspec"))]
/// Objects which can serve as loggers.
///
/// Logging functionality can be used by smart contracts to record events that
/// might be of interest to external parties. These events are not used on the
/// chain, and cannot be observed by other contracts, but they are stored by the
/// node, and can be queried to provide information to off-chain actors.
pub trait HasLogger {
    /// Initialize a logger.
    fn init() -> Self;

    /// Log the given slice as-is. If logging is not successful an error will be
    /// returned.
    fn log_raw(&mut self, event: &[u8]) -> Result<(), LogError>;

    #[inline(always)]
    /// Log a serializable event by serializing it with a supplied serializer.
    fn log<S: Serial>(&mut self, event: &S) -> Result<(), LogError> {
	let mut out = Vec::new();
	if event.serial(&mut out).is_err() {
	    concordium_std::trap(); // should not happen
	}
	self.log_raw(&out)
    }
}

#[cfg(not(feature = "hacspec"))]
/// #Implementations of the logger.
impl HasLogger for Logger {
    #[inline(always)]
    fn init() -> Self {
	Self { _private: () }
    }

    fn log_raw(&mut self, event: &[u8]) -> Result<(), LogError> {
	let (_, res) = log_event_hacspec(coerce_rust_to_hacspec_public_byte_seq(event));
	match res {
	    1 => Ok(()),
	    0 => Err(LogError::Full),
	    _ => Err(LogError::Malformed),
	}
    }
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    pub(crate) fn accept() -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn accept_creusot() -> u32 {
    unsafe { accept() }
}

#[cfg(feature = "hacspec")]
fn accept_hacspec() -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
fn accept_hacspec() -> u32 {
    accept_creusot()
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Basic action to send tokens to an account.
  pub(crate) fn simple_transfer(addr_bytes: *const u8, amount: u64) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn simple_transfer_creusot(addr_bytes: *const u8, amount: u64) -> u32 {
    unsafe { simple_transfer(addr_bytes, amount) }
}

#[cfg(feature = "hacspec")]
fn simple_transfer_hacspec(buf: PublicByteSeq, amount: u64) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
fn simple_transfer_hacspec(buf: PublicByteSeq, amount: u64) -> u32 {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(buf.clone())[..];
    simple_transfer_creusot(temp.as_ptr(), amount)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Send a message to a smart contract.
  pub(crate) fn send(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: *const u8,
      receive_name_len: u32,
      amount: u64,
      parameter: *const u8,
      parameter_len: u32,
  ) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn send_creusot(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: *const u8,
      receive_name_len: u32,
      amount: u64,
      parameter: *const u8,
      parameter_len: u32,
  ) -> u32 {
    unsafe { send(addr_index, addr_subindex, receive_name, receive_name_len, amount, parameter, parameter_len) }
}

#[cfg(feature = "hacspec")]
fn send_hacspec(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: PublicByteSeq,
      amount: u64,
      parameter: PublicByteSeq,
  ) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
fn send_hacspec(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: PublicByteSeq,
      amount: u64,
      parameter: PublicByteSeq,
  ) -> u32 {
    let temp_receive_name = &mut coerce_hacspec_to_rust_public_byte_seq(receive_name.clone())[..];
    let temp_parameter = &mut coerce_hacspec_to_rust_public_byte_seq(parameter.clone())[..];
    send_creusot(addr_index, addr_subindex, temp_receive_name.as_ptr(), receive_name.len() as u32, amount, temp_parameter.as_ptr(), parameter.len() as u32)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Combine two actions using normal sequencing. This is using the stack of
  // actions already produced.
  pub(crate) fn combine_and(l: u32, r: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn combine_and_creusot(l: u32, r: u32) -> u32 {
    unsafe { combine_and(l, r) }
}

#[cfg(feature = "hacspec")]
fn combine_and_hacspec(l: u32, r: u32) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
fn combine_and_hacspec(l: u32, r: u32) -> u32 {
    combine_and_creusot(l,r)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Combine two actions using normal sequencing. This is using the stack of
  // actions already produced.
  pub(crate) fn combine_or(l: u32, r: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn combine_or_creusot(l: u32, r: u32) -> u32 {
    unsafe { combine_or(l, r) }
}

#[cfg(feature = "hacspec")]
fn combine_or_hacspec(l: u32, r: u32) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
fn combine_or_hacspec(l: u32, r: u32) -> u32 {
    combine_or_creusot(l,r)
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
/// #Implementation of actions.
/// These actions are implemented by direct calls to host functions.
impl HasActions for Action {
    #[inline(always)]
    fn accept() -> Self {
	Action {
	    _private: accept_hacspec(),
	}
    }

    #[inline(always)]
    fn simple_transfer(acc: &AccountAddress, amount: Amount) -> Self {
	let res = simple_transfer_hacspec(coerce_rust_to_hacspec_public_byte_seq(&acc.0), amount.micro_gtu);
	Action { _private: res }
    }

    #[inline(always)]
    fn send_raw(
	ca: &ContractAddress,
	receive_name: ReceiveName,
	amount: Amount,
	parameter: &[u8],
    ) -> Self {
	let receive_bytes = receive_name.get_chain_name().as_bytes();
	let res = 
	    send_hacspec(
		ca.index,
		ca.subindex,
		coerce_rust_to_hacspec_public_byte_seq(&receive_bytes),
		amount.micro_gtu,
		coerce_rust_to_hacspec_public_byte_seq(&parameter),
	    );
	Action { _private: res }
    }

    #[inline(always)]
    fn and_then(self, then: Self) -> Self {
	let res = combine_and_hacspec(self._private, then._private);
	Action { _private: res }
    }

    #[inline(always)]
    fn or_else(self, el: Self) -> Self {
	let res = combine_or_hacspec(self._private, el._private);
	Action { _private: res }
    }
}

// TODO: Define functionality in hacspec instead!
#[cfg(not(feature = "hacspec"))]
/// Allocates a Vec of bytes prepended with its length as a `u32` into memory,
/// and prevents them from being dropped. Returns the pointer.
/// Used to pass bytes from a Wasm module to its host.
#[doc(hidden)]
pub fn put_in_memory(input: &[u8]) -> *mut u8 {
    let bytes_length = input.len() as u32;
    let mut bytes = concordium_std::to_bytes(&bytes_length);
    bytes.extend_from_slice(input);
    let ptr = bytes.as_mut_ptr();
    #[cfg(feature = "std")]
    ::std::mem::forget(bytes);
    #[cfg(not(feature = "std"))]
    core::mem::forget(bytes);
    ptr
}

// TODO: Name collision
// #[cfg(not(feature = "hacspec"))]
// /// Wrapper for
// /// [HasActions::send_raw](./trait.HasActions.html#tymethod.send_raw), which
// /// automatically serializes the parameter. Note that if the parameter is
// /// already a byte array or convertible to a byte array without allocations it
// /// is preferrable to use [send_raw](./trait.HasActions.html#tymethod.send_raw).
// /// It is more efficient and avoids memory allocations.
// pub fn send<A: HasActions, P: Serial>(
//     ca: &ContractAddress,
//     receive_name: ReceiveName,
//     amount: Amount,
//     parameter: &P,
// ) -> A {
//     let param_bytes = concordium_std::to_bytes(parameter);
//     A::send_raw(ca, receive_name, amount, &param_bytes)
// }

#[cfg(not(feature = "hacspec"))]
/// Add optimized unwrap behaviour that aborts the process instead of
/// panicking.
pub trait UnwrapAbort {
    /// The underlying result type of the unwrap, in case of success.
    type Unwrap;
    /// Unwrap or call [trap](./fn.trap.html). In contrast to
    /// the unwrap methods on [Option::unwrap](https://doc.rust-lang.org/std/option/enum.Option.html#method.unwrap)
    /// this method will tend to produce smaller code, at the cost of the
    /// ability to handle the panic.
    /// This is intended to be used only in `Wasm` code, where panics cannot be
    /// handled anyhow.
    fn unwrap_abort(self) -> Self::Unwrap;
}

#[cfg(not(feature = "hacspec"))]
impl<A, E> UnwrapAbort for Result<A, E> {
    type Unwrap = A;

    #[inline]
    fn unwrap_abort(self) -> Self::Unwrap {
	match self {
	    Ok(x) => x,
	    Err(_) => concordium_std::trap(),
	}
    }
}

#[cfg(not(feature = "hacspec"))]
/// Analogue of the `expect` methods on types such as [Option](https://doc.rust-lang.org/std/option/enum.Option.html),
/// but useful in a Wasm setting.
pub trait ExpectReport {
    type Unwrap;
    /// Like the default `expect` on, e.g., `Result`, but calling
    /// [fail](macro.fail.html) with the given message, instead of `panic`.
    fn expect_report(self, msg: &str) -> Self::Unwrap;
}

// #[cfg(not(feature = "hacspec"))]
// #[cfg(not(feature = "std"))]
// use concordium_std::fmt; // core::fmt;

#[cfg(not(feature = "hacspec"))]
#[cfg(feature = "std")]
use std::fmt;

#[cfg(not(feature = "hacspec"))]
impl<A, E: fmt::Debug> ExpectReport for Result<A, E> {
    type Unwrap = A;

    fn expect_report(self, msg: &str) -> Self::Unwrap {
	match self {
	    Ok(x) => x,
	    Err(e) => concordium_std::fail!("{}: {:?}", msg, e),
	}
    }
}

#[cfg(not(feature = "hacspec"))]  
/// Analogue of the `expect_err` methods on [Result](https://doc.rust-lang.org/std/result/enum.Result.html),
/// but useful in a Wasm setting.
pub trait ExpectErrReport {
    type Unwrap;
    /// Like the default `expect_err` on, e.g., `Result`, but calling
    /// [fail](macro.fail.html) with the given message, instead of `panic`.
    fn expect_err_report(self, msg: &str) -> Self::Unwrap;
}

#[cfg(not(feature = "hacspec"))]
impl<A: fmt::Debug, E> ExpectErrReport for Result<A, E> {
    type Unwrap = E;

    fn expect_err_report(self, msg: &str) -> Self::Unwrap {
	match self {
	    Ok(a) => concordium_std::fail!("{}: {:?}", msg, a),
	    Err(e) => e,
	}
    }
}

#[cfg(not(feature = "hacspec"))]
impl<A> UnwrapAbort for Option<A> {
    type Unwrap = A;

    #[inline(always)]
    fn unwrap_abort(self) -> Self::Unwrap {
	self.unwrap_or_else(|| concordium_std::trap())
    }
}

#[cfg(not(feature = "hacspec"))]
impl<A> ExpectReport for Option<A> {
    type Unwrap = A;

    fn expect_report(self, msg: &str) -> Self::Unwrap {
	match self {
	    Some(v) => v,
	    None => concordium_std::fail!("{}", msg),
	}
    }
}

#[cfg(not(feature = "hacspec"))]
/// Analogue of the `expect_none` methods on [Option](https://doc.rust-lang.org/std/option/enum.Option.html),
/// but useful in a Wasm setting.
pub trait ExpectNoneReport {
    /// Like the default `expect_none_report` on, e.g., `Option`, but calling
    /// [fail](macro.fail.html) with the given message, instead of `panic`.
    fn expect_none_report(self, msg: &str);
}

#[cfg(not(feature = "hacspec"))]
impl<A: fmt::Debug> ExpectNoneReport for Option<A> {
    fn expect_none_report(self, msg: &str) {
	if let Some(x) = self {
	    concordium_std::fail!("{}: {:?}", msg, x)
	}
    }
}

// #[cfg(not(feature = "hacspec"))]
// /// The `Serial` trait provides a means of writing structures into byte-sinks
// /// (`Write`).
// ///
// /// Can be derived using `#[derive(Serial)]` for most cases.
// pub trait Serial {
//     /// Attempt to write the structure into the provided writer, failing if
//     /// only part of the structure could be written.
//     ///
//     /// NB: We use Result instead of Option for better composability with other
//     /// constructs.
//     fn serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err>;
// }

#[cfg(not(feature = "hacspec"))]
/// The `SerialCtx` trait provides a means of writing structures into byte-sinks
/// (`Write`) using contextual information.
/// The contextual information is:
///
///   - `size_length`: The number of bytes used to record the length of the
///     data.
pub trait SerialCtx {
    /// Attempt to write the structure into the provided writer, failing if
    /// if the length cannot be represented in the provided `size_length` or
    /// only part of the structure could be written.
    ///
    /// NB: We use Result instead of Option for better composability with other
    /// constructs.
    fn serial_ctx<W: Write>(
	&self,
	size_length: concordium_std::schema::SizeLength,
	out: &mut W,
    ) -> Result<(), W::Err>;
}

#[cfg(not(feature = "hacspec"))]
/// Write a [BTreeSet](https://doc.rust-lang.org/std/collections/struct.BTreeSet.html) as an ascending list of keys, without the length information.
pub fn serial_set_no_length<W: Write, K: Serial>(
    map: &BTreeSet<K>,
    out: &mut W,
) -> Result<(), W::Err> {
    for k in map.iter() {
	k.serial(out)?;
    }
    Ok(())
}

#[cfg(not(feature = "hacspec"))]
impl<K: Serial + Ord> SerialCtx for BTreeSet<K> {
    fn serial_ctx<W: Write>(
	&self,
	size_len: concordium_std::schema::SizeLength,
	out: &mut W,
    ) -> Result<(), W::Err> {
	concordium_std::schema::serial_length(self.len(), size_len, out)?;
	// concordium_std::
	serial_set_no_length(self, out)
    }
}

#[cfg(not(feature = "hacspec"))]
/// The `DeserialCtx` trait provides a means of reading structures from
/// byte-sources (`Read`) using contextual information.
/// The contextual information is:
///
///   - `size_length`: The expected number of bytes used for the length of the
///     data.
///   - `ensure_ordered`: Whether the ordering should be ensured, for example
///     that keys in `BTreeMap` and `BTreeSet` are in strictly increasing order.
pub trait DeserialCtx: Sized {
    /// Attempt to read a structure from a given source and context, failing if
    /// an error occurs during deserialization or reading.
    fn deserial_ctx<R: Read>(
	size_length: concordium_std::schema::SizeLength,
	ensure_ordered: bool,
	source: &mut R,
    ) -> ParseResult<Self>;
}

/// A more convenient wrapper around `Deserial` that makes it easier to write
/// deserialization code. It has a blanked implementation for any read and
/// serialize pair. The key idea is that the type to deserialize is inferred
/// from the context, enabling one to write, for example,
///
/// ```rust
/// # fn deserial<R: concordium_contracts_common::Read>(source: &mut R) -> concordium_contracts_common::ParseResult<(u8, u8)> {
/// #  use crate::concordium_contracts_common::Get;
///    let x = source.get()?;
///    let y = source.get()?;
/// #   Ok((x,y))
/// # }
/// ```
/// where `source` is any type that implements `Read`.
#[cfg(not(feature = "hacspec"))]
pub trait Get<T> {
    fn get(&mut self) -> ParseResult<T>;
}

#[cfg(not(feature = "hacspec"))]
impl<R: Read, T: Deserial> Get<T> for R {
    #[inline(always)]
    fn get(&mut self) -> ParseResult<T> {
	T::deserial(self)
    }
}

#[cfg(not(feature = "hacspec"))]
/// Read a [BTreeSet](https://doc.rust-lang.org/std/collections/struct.BTreeSet.html) as a list of keys, given some length.
/// NB: This ensures there are no duplicates, hence the specialized type.
/// Moreover this will only succeed if keys are listed in order.
pub fn deserial_set_no_length<R: Read, K: Deserial + Ord + Copy>(
    source: &mut R,
    len: usize,
) -> ParseResult<BTreeSet<K>> {
    let mut out = BTreeSet::new();
    let mut prev = None;
    for _ in 0..len {
	let key = source.get()?;
	let next = Some(key);
	if next <= prev {
	    return Err(ParseError::default());
	}
	out.insert(key);
	prev = next;
    }
    Ok(out)
}

#[cfg(not(feature = "hacspec"))]
/// Read a [BTreeSet](https://doc.rust-lang.org/std/collections/struct.BTreeSet.html) as an list of key-value pairs given some length.
/// Slightly faster version of `deserial_set_no_length` as it is skipping the
/// order checking. The only check that is made to the set is that there are no
/// duplicates.
pub fn deserial_set_no_length_no_order_check<R: Read, K: Deserial + Ord>(
    source: &mut R,
    len: usize,
) -> ParseResult<BTreeSet<K>> {
    let mut out = BTreeSet::new();
    for _ in 0..len {
	let key = source.get()?;
	if !out.insert(key) {
	    return Err(ParseError::default());
	}
    }
    Ok(out)
}

#[cfg(not(feature = "hacspec"))]
impl<K: Deserial + Ord + Copy> DeserialCtx for BTreeSet<K> {
    fn deserial_ctx<R: Read>(
	size_len: concordium_std::schema::SizeLength,
	ensure_ordered: bool,
	source: &mut R,
    ) -> ParseResult<Self> {
	let len = concordium_std::schema::deserial_length(source, size_len)?;
	if ensure_ordered {
	    // concordium_std::
	    deserial_set_no_length(source, len)
	} else {
	    // concordium_std::
	    deserial_set_no_length_no_order_check(source, len)
	}
    }
}

#[cfg(not(feature = "hacspec"))]
/// Write a Map as a list of key-value pairs ordered by the key, without the
/// length information.
pub fn serial_map_no_length<W: Write, K: Serial, V: Serial>(
    map: &BTreeMap<K, V>,
    out: &mut W,
) -> Result<(), W::Err> {
    for (k, v) in map.iter() {
	k.serial(out)?;
	v.serial(out)?;
    }
    Ok(())
}

#[cfg(not(feature = "hacspec"))]
impl<K: Serial + Ord, V: Serial> SerialCtx for BTreeMap<K, V> {
    fn serial_ctx<W: Write>(
	&self,
	size_len: concordium_std::schema::SizeLength,
	out: &mut W,
    ) -> Result<(), W::Err> {
	concordium_std::schema::serial_length(self.len(), size_len, out)?;
	// concordium_std::
	serial_map_no_length(self, out)
    }
}

#[cfg(not(feature = "hacspec"))]
/// Read a [BTreeMap](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html) as a list of key-value pairs given some length.
/// NB: This ensures there are no duplicates, hence the specialized type.
/// Moreover this will only succeed if keys are listed in order.
pub fn deserial_map_no_length<R: Read, K: Deserial + Ord + Copy, V: Deserial>(
    source: &mut R,
    len: usize,
) -> ParseResult<BTreeMap<K, V>> {
    let mut out = BTreeMap::new();
    let mut x = None;
    for _ in 0..len {
	let k = source.get()?;
	let v = source.get()?;
	match x {
	    None => {
		out.insert(k, v);
	    }
	    Some(kk) => {
		if k > kk {
		    out.insert(k, v);
		} else {
		    return Err(ParseError::default());
		}
	    }
	}
	x = Some(k);
    }
    Ok(out)
}

#[cfg(not(feature = "hacspec"))]  
/// Read a [BTreeMap](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html) as a list of key-value pairs given some length.
/// Slightly faster version of `deserial_map_no_length` as it is skipping the
/// order checking
pub fn deserial_map_no_length_no_order_check<R: Read, K: Deserial + Ord, V: Deserial>(
    source: &mut R,
    len: usize,
) -> ParseResult<BTreeMap<K, V>> {
    let mut out = BTreeMap::new();
    for _ in 0..len {
	let k = source.get()?;
	let v = source.get()?;
	if out.insert(k, v).is_some() {
	    return Err(ParseError::default());
	}
    }
    Ok(out)
}

#[cfg(not(feature = "hacspec"))]  
impl<K: Deserial + Ord + Copy, V: Deserial> DeserialCtx for BTreeMap<K, V> {
    fn deserial_ctx<R: Read>(
	size_len: concordium_std::schema::SizeLength,
	ensure_ordered: bool,
	source: &mut R,
    ) -> ParseResult<Self> {
	let len = concordium_std::schema::deserial_length(source, size_len)?;
	if ensure_ordered {
	    // concordium_std::
	    deserial_map_no_length(source, len)
	} else {
	    // concordium_std::
	    deserial_map_no_length_no_order_check(source, len)
	}
    }
}

#[cfg(not(feature = "hacspec"))]
/// Write a [HashSet](https://doc.rust-lang.org/std/collections/struct.HashSet.html) as a list of keys in no particular order, without the length information.
pub fn serial_hashset_no_length<W: Write, K: Serial>(
    map: &HashSet<K>,
    out: &mut W,
) -> Result<(), W::Err> {
    for k in map.iter() {
	k.serial(out)?;
    }
    Ok(())
}

#[cfg(not(feature = "hacspec"))]
/// Serialization for HashSet given a size_len.
/// Values are not serialized in any particular order.
impl<K: Serial> SerialCtx for HashSet<K> {
    fn serial_ctx<W: Write>(
	&self,
	size_len: concordium_std::schema::SizeLength,
	out: &mut W,
    ) -> Result<(), W::Err> {
	concordium_std::schema::serial_length(self.len(), size_len, out)?;
	// concordium_std::
	serial_hashset_no_length(self, out)
    }
}

#[cfg(not(feature = "hacspec"))]
/// Read a [HashSet](https://doc.rust-lang.org/std/collections/struct.HashSet.html) as a list of keys, given some length.
/// NB: This ensures there are no duplicates.
pub fn deserial_hashset_no_length<R: Read, K: Deserial + Eq + Hash>(
    source: &mut R,
    len: usize,
) -> ParseResult<HashSet<K>> {
    let mut out = HashSet::default();
    for _ in 0..len {
	let key = source.get()?;
	if !out.insert(key) {
	    return Err(ParseError::default());
	}
    }
    Ok(out)
}

#[cfg(not(feature = "hacspec"))]  
/// Deserialization for HashSet given a size_len.
/// Values are not verified to be in any particular order and setting
/// ensure_ordering have no effect.
impl<K: Deserial + Eq + Hash> DeserialCtx for HashSet<K> {
    fn deserial_ctx<R: Read>(
	size_len: concordium_std::schema::SizeLength,
	_ensure_ordered: bool,
	source: &mut R,
    ) -> ParseResult<Self> {
	let len = concordium_std::schema::deserial_length(source, size_len)?;
	deserial_hashset_no_length(source, len)
    }
}

#[cfg(not(feature = "hacspec"))]  
/// Write a HashMap as a list of key-value pairs in to particular order, without
/// the length information.
pub fn serial_hashmap_no_length<W: Write, K: Serial, V: Serial>(
    map: &HashMap<K, V>,
    out: &mut W,
) -> Result<(), W::Err> {
    for (k, v) in map.iter() {
	k.serial(out)?;
	v.serial(out)?;
    }
    Ok(())
}

#[cfg(not(feature = "hacspec"))]  
/// Serialization for HashMap given a size_len.
/// Keys are not serialized in any particular order.
impl<K: Serial, V: Serial> SerialCtx for HashMap<K, V> {
    fn serial_ctx<W: Write>(
	&self,
	size_len: concordium_std::schema::SizeLength,
	out: &mut W,
    ) -> Result<(), W::Err> {
	concordium_std::schema::serial_length(self.len(), size_len, out)?;
	serial_hashmap_no_length(self, out)
    }
}

#[cfg(not(feature = "hacspec"))]
/// Read a [HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html) as a list of key-value pairs given some length.
pub fn deserial_hashmap_no_length<R: Read, K: Deserial + Eq + Hash, V: Deserial>(
    source: &mut R,
    len: usize,
) -> ParseResult<HashMap<K, V>> {
    let mut out = HashMap::default();
    for _ in 0..len {
	let k = source.get()?;
	let v = source.get()?;
	if out.insert(k, v).is_some() {
	    return Err(ParseError::default());
	}
    }
    Ok(out)
}

#[cfg(not(feature = "hacspec"))]
/// Deserialization for HashMap given a size_len.
/// Keys are not verified to be in any particular order and setting
/// ensure_ordering have no effect.
impl<K: Deserial + Eq + Hash, V: Deserial> DeserialCtx for HashMap<K, V> {
    fn deserial_ctx<R: Read>(
	size_len: concordium_std::schema::SizeLength,
	_ensure_ordered: bool,
	source: &mut R,
    ) -> ParseResult<Self> {
	let len = concordium_std::schema::deserial_length(source, size_len)?;
	// concordium_std::
	deserial_hashmap_no_length(source, len)
    }
}

#[cfg(not(feature = "hacspec"))]
/// Write a slice of elements, without including length information.
/// This is intended to be used either when the length is statically known,
/// or when the length is serialized independently as part of a bigger
/// structure.
pub fn serial_vector_no_length<W: Write, T: Serial>(xs: &[T], out: &mut W) -> Result<(), W::Err> {
    for x in xs {
	x.serial(out)?;
    }
    Ok(())
}

#[cfg(not(feature = "hacspec"))]
impl<T: Serial> SerialCtx for &[T] {
    fn serial_ctx<W: Write>(
	&self,
	size_len: concordium_std::schema::SizeLength,
	out: &mut W,
    ) -> Result<(), W::Err> {
	concordium_std::schema::serial_length(self.len(), size_len, out)?;
	serial_vector_no_length(self, out)
    }
}

#[cfg(not(feature = "hacspec"))]
pub(crate) static MAX_PREALLOCATED_CAPACITY: usize = 4096;

#[cfg(not(feature = "hacspec"))]
/// Read a vector given a length.
pub fn deserial_vector_no_length<R: Read, T: Deserial>(
    reader: &mut R,
    len: usize,
) -> ParseResult<Vec<T>> {
    let mut vec = Vec::with_capacity(core::cmp::min(len, MAX_PREALLOCATED_CAPACITY));
    for _ in 0..len {
	vec.push(T::deserial(reader)?);
    }
    Ok(vec)
}

#[cfg(not(feature = "hacspec"))]
impl<T: Deserial> DeserialCtx for Vec<T> {
    fn deserial_ctx<R: Read>(
	size_len: concordium_std::schema::SizeLength,
	_ensure_ordered: bool,
	source: &mut R,
    ) -> ParseResult<Self> {
	let len = concordium_std::schema::deserial_length(source, size_len)?;
	deserial_vector_no_length(source, len)
    }
}

#[cfg(not(feature = "hacspec"))]
impl SerialCtx for &str {
    fn serial_ctx<W: Write>(
	&self,
	size_len: concordium_std::schema::SizeLength,
	out: &mut W,
    ) -> Result<(), W::Err> {
	concordium_std::schema::serial_length(self.len(), size_len, out)?;
	serial_vector_no_length(&self.as_bytes().to_vec(), out)
    }
}

#[cfg(not(feature = "hacspec"))]
impl SerialCtx for String {
    fn serial_ctx<W: Write>(
	&self,
	size_len: concordium_std::schema::SizeLength,
	out: &mut W,
    ) -> Result<(), W::Err> {
	self.as_str().serial_ctx(size_len, out)
    }
}

#[cfg(not(feature = "hacspec"))]  
impl DeserialCtx for String {
    fn deserial_ctx<R: Read>(
	size_len: concordium_std::schema::SizeLength,
	_ensure_ordered: bool,
	source: &mut R,
    ) -> ParseResult<Self> {
	let len = concordium_std::schema::deserial_length(source, size_len)?;
	let bytes = deserial_vector_no_length(source, len)?;
	let res = String::from_utf8(bytes).map_err(|_| ParseError::default())?;
	Ok(res)
    }
}



array!(UserAddress, 32, u8); // U8

#[derive(Clone, PartialEq)]
pub enum AuctionState {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction is over and the item has been sold to the indicated address.
    Sold(UserAddress), // winning account's address
}

#[derive(Clone, PartialEq)]
pub struct SeqMap(pub PublicByteSeq, pub PublicByteSeq);

pub type AmountHacspec = u64;
pub type TimestampHacspec = u64;
pub type Itemtyp = PublicByteSeq; // Seq<u8>;

#[derive(Clone, PartialEq)]
pub struct State(
    pub AuctionState,
    pub AmountHacspec,
    pub Itemtyp,
    pub TimestampHacspec,
    pub SeqMap,
);

// #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
// #[cfg_attr(feature = "use_attributes", ensures(true))]
// #[hacspec_unsafe]
// #[cfg(feature = "hacspec_unsafe")]
// #[hacspec_unsafe]
#[ensures(true)]
// #[hacspec_unsafe] // ensures(result.0 === AuctionState::NotSoldYet)
// #[ensures(forall<x : u32> x + x = x * 2)]
pub fn fresh_state(itm: Itemtyp, exp: u64) -> State {
    State(
	AuctionState::NotSoldYet,
	0_u64,
	itm,
	exp,
	SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
    )
}

// #[ensures(true)]
// #[ensures(result === )]
fn seq_map_entry(m: SeqMap, sender_address: UserAddress) -> (u64, SeqMap) {
    let SeqMap(m0, m1) = m;

    let mut res = // MapEntry::Entry
	(
	0_u64,
	SeqMap(
	    m0.clone().concat(&sender_address),
	    m1.clone().concat(&u64_to_be_bytes(0_u64)),
	),
    );

    for x in 0..m0.clone().len() / 32 {
	if UserAddress::from_seq(&m0.clone().slice(x * 32, 32)) == sender_address {
	    res = // MapEntry::Entry
		(
		u64_from_be_bytes(u64Word::from_seq(&m1.clone().slice(x * 8, 8))),
		SeqMap(m0.clone(), m1.clone()),
	    );
	}
    }

    res
}

#[derive(Clone, PartialEq)]
pub enum MapUpdate {
    Update(u64, SeqMap),
}

fn seq_map_update_entry(m: SeqMap, sender_address: UserAddress, amount: u64) -> MapUpdate {
    let SeqMap(m0, m1) = m;

    let mut res = MapUpdate::Update(
	amount,
	SeqMap(
	    m0.clone().concat(&sender_address),
	    m1.clone().concat(&u64_to_be_bytes(amount)),
	),
    );

    // !! Issue in for loop !! (update, updates the reference!)
    for x in 0..m0.clone().len() / 32 {
	if UserAddress::from_seq(&m0.clone().slice(x * 32, 32)) == sender_address {
	    res = MapUpdate::Update(
		amount,
		SeqMap(
		    m0.clone().update(x * 32, &sender_address),
		    m1.clone().update(x * 8, &u64_to_be_bytes(amount)),
		),
	    );
	}
    }

    res
}

#[derive(Clone, PartialEq)]
pub enum BidError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionIsFinalized,                    /* raised if bid is placed after auction has been
					    * finalized */
}

// pub type UserAddressSet = Option<UserAddress>;
#[derive(Clone, PartialEq)]
pub enum UserAddressSet {
    UserAddressSome(UserAddress),
    UserAddressNone,
}
pub type Context = (u64, UserAddressSet);
pub type AuctionBidResult = Result<State, BidError>;

pub fn auction_bid(ctx: Context, amount: u64, state: State) -> AuctionBidResult {
    let State(auction_state, highest_bid, st2, expiry, st4) = state.clone();

    if !(auction_state == AuctionState::NotSoldYet) {
	AuctionBidResult::Err(BidError::AuctionIsFinalized)?;
    }

    let (slot_time, sender) = ctx;
    if !(slot_time <= expiry) {
	AuctionBidResult::Err(BidError::BidsOverWaitingForAuctionFinalization)?;
    }

    if sender == UserAddressSet::UserAddressNone {
	AuctionBidResult::Err(BidError::ContractSender)?;
    }

    let sender_address = match sender {
	UserAddressSet::UserAddressNone => UserAddress([
	    5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8,
	    5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8,
	    5_u8, 5_u8, 5_u8, 5_u8,
	]), // should never happen
	UserAddressSet::UserAddressSome(account_address) => account_address,
    };

    let (bid_to_update, new_map) = // match
	seq_map_entry(st4.clone(), sender_address) // {
    //     MapEntry::Entry(bid_to_update, new_map) => (bid_to_update, new_map),
    // }
    ;

    let (updated_bid, updated_map) =
	match seq_map_update_entry(st4.clone(), sender_address, bid_to_update + amount) {
	    MapUpdate::Update(updated_bid, updated_map) => (updated_bid, updated_map),
	};

    if !(updated_bid > highest_bid) {
	AuctionBidResult::Err(BidError::BidTooLow)?;
    }

    AuctionBidResult::Ok(State(auction_state, updated_bid, st2, expiry, updated_map))
}

pub type FinalizeContext = (u64, UserAddress, u64);

/// For errors in which the `finalize` function can result
#[derive(Clone, PartialEq)]
pub enum FinalizeError {
    BidMapError,
    AuctionStillActive,
    AuctionFinalized,
}

#[derive(Clone, PartialEq)]
pub enum FinalizeAction {
    Accept,
    SimpleTransfer(PublicByteSeq),
}

#[derive(Clone, PartialEq)]
pub enum BidRemain {
    BidNone,
    BidSome(u64),
}

pub type AuctionFinalizeResult = Result<(State, FinalizeAction), FinalizeError>;
// pub type BidRemain = Option<(UserAddress, u64)>;

pub fn auction_finalize(ctx: FinalizeContext, state: State) -> AuctionFinalizeResult {
    let State(mut auction_state, highest_bid, st2, expiry, SeqMap(m0, m1)) = state.clone();

    let mut result = AuctionFinalizeResult::Ok((state.clone(), FinalizeAction::Accept));

    if !(auction_state == AuctionState::NotSoldYet) {
	AuctionFinalizeResult::Err(FinalizeError::AuctionFinalized)?;
    }

    let (slot_time, owner, balance) = ctx;

    if !(slot_time > expiry) {
	AuctionFinalizeResult::Err(FinalizeError::AuctionStillActive)?;
    }

    if balance != 0_u64 {
	let mut return_action = FinalizeAction::SimpleTransfer(
	    PublicByteSeq::new(0_usize)
		.concat(&owner)
		.concat(&u64_to_be_bytes(highest_bid)),
	);
	let mut remaining_bid = BidRemain::BidNone;
	// Return bids that are smaller than highest
	// let x = 0;
	for x in 0..m0.clone().len() / 32 {
	    let addr = UserAddress::from_seq(&m0.clone().slice(x * 32, 32));
	    let amnt = u64_from_be_bytes(u64Word::from_seq(&m1.clone().slice(x * 8, 8)));
	    if amnt < highest_bid {
		return_action = match return_action {
		    FinalizeAction::Accept => FinalizeAction::Accept, // TODO: What error (should never happen)..
		    FinalizeAction::SimpleTransfer(m) => FinalizeAction::SimpleTransfer(
			m.concat(&addr).concat(&u64_to_be_bytes(amnt)),
		    ),
		};
	    } else {
		// ensure!(remaining_bid.is_none(), FinalizeError::BidMapError);
		if ! (remaining_bid == BidRemain::BidNone) {
		    AuctionFinalizeResult::Err(FinalizeError::BidMapError)?;
		}
		auction_state = AuctionState::Sold(addr);
		remaining_bid = BidRemain::BidSome(amnt);
	    }
	}

	// ensure that the only bidder left in the map is the one with the highest bid
	result = match remaining_bid {
	    BidRemain::BidSome(amount) =>
	    // ensure!(amount == state.highest_bid, FinalizeError::BidMapError);
	    {
		if !(amount == highest_bid) {
		    AuctionFinalizeResult::Err(FinalizeError::BidMapError)
		} else {
		    AuctionFinalizeResult::Ok((
			State(auction_state, highest_bid, st2, expiry, SeqMap(m0.clone(), m1.clone())),
			return_action,
		    ))
		}
	    }
	    BidRemain::BidNone => AuctionFinalizeResult::Err(FinalizeError::BidMapError),
	};

	result.clone()?;
    }

    result
}

// #[cfg(test)]
// extern crate quickcheck;
// #[cfg(test)]
// #[macro_use(quickcheck)]
// extern crate quickcheck_macros;

// #[cfg(test)]
// use quickcheck::*;

// #[cfg(proof)]
// #[cfg(test)]
// pub fn auction_item(a : u64, b : u64, c : u64) -> PublicByteSeq {
//     PublicByteSeq::new(0_usize)
// }

#[test]
#[proof]
#[quickcheck]
#[ensures(result === true)]
/// Test that the smart-contract initialization sets the state correctly
/// (no bids, active state, indicated auction-end time and item name).
pub fn auction_test_init(item: PublicByteSeq, time : u64) -> bool {
    fresh_state(item.clone(), time)
	== State(
	    AuctionState::NotSoldYet,
	    0_u64,
	    item.clone(),
	    time,
	    SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
	)
}

#[test]
#[proof]
fn verify_bid(
    item: PublicByteSeq,
    state: State,
    account: UserAddress,
    ctx: Context,
    amount: u64,
    bid_map: SeqMap,
    highest_bid: u64,
    time : u64,
) -> (State, SeqMap, bool, bool) {
    let t = auction_bid(ctx, amount, state.clone());

    let (state, res) = match t {
	AuctionBidResult::Err(e) => (state, false),
	AuctionBidResult::Ok(s) => (s, true),
    };

    let bid_map = match seq_map_update_entry(bid_map.clone(), account, highest_bid) {
	MapUpdate::Update(_, updated_map) => updated_map,
    };

    (
	state.clone(),
	bid_map.clone(),
	res,
	state.clone()
	    == State(
		AuctionState::NotSoldYet,
		highest_bid,
		item.clone(),
		time,
		bid_map.clone(),
	    ),
    )
}

#[test]
#[proof]
fn useraddress_from_u8(i : u8) -> UserAddress {
    UserAddress([
	i, i, i, i, i, i, i, i, i, i, i, i, i, i, i,
	i, i, i, i, i, i, i, i, i, i, i, i, i, i, i,
	i, i,
    ])
}

#[test]
#[proof]
fn new_account(time : u64, i : u8) -> (UserAddress, Context) {
    let addr = useraddress_from_u8(i);
    let ctx = (time, UserAddressSet::UserAddressSome(addr));
    (addr, ctx)
}

#[test]
#[proof]
// #[quickcheck]
// #[test]
/// Test a sequence of bids and finalizations:
/// 0. Auction is initialized.
/// 1. Alice successfully bids 0.1 GTU.
/// 2. Alice successfully bids another 0.1 GTU, highest bid becomes 0.2 GTU
/// (the sum of her two bids). 3. Bob successfully bids 0.3 GTU, highest
/// bid becomes 0.3 GTU. 4. Someone tries to finalize the auction before
/// its end time. Attempt fails. 5. Dave successfully finalizes the
/// auction after its end time.    Alice gets her money back, while
/// Carol (the owner of the contract) collects the highest bid amount.
/// 6. Attempts to subsequently bid or finalize fail.
#[ensures(result === true)]
#[quickcheck]
fn test_auction_bid_and_finalize(item: PublicByteSeq, time : u64, input_amount : u64) -> bool {
    let amount = input_amount + 1_u64;
    let winning_amount = amount * 3_u64; // 300_u64;
    let big_amount = amount * 5_u64; // 500_u64;

    let bid_map = SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize));

    // initializing auction
    let state = fresh_state(item.clone(), time); // mut

    // 1st bid: account1 bids amount1
    let (alice, alice_ctx) = new_account(time, 0_u8);

    let (state, bid_map, res_0, result_0) = verify_bid(
	item.clone(),
	state,
	alice,
	alice_ctx,
	amount,
	bid_map,
	amount,
	time,
    );

    // // 2nd bid: account1 bids `amount` again
    // // should work even though it's the same amount because account1 simply
    // // increases their bid
    let (state, bid_map, res_1, result_1) = verify_bid(
	item.clone(),
	state,
	alice,
	alice_ctx,
	amount,
	bid_map,
	amount + amount,
	time,
    );

    // // 3rd bid: second account
    let (bob, bob_ctx) = new_account(time, 1_u8); // first argument is slot time

    let (state, bid_map, res_2, result_2) = verify_bid(
	item.clone(),
	state,
	bob,
	bob_ctx,
	winning_amount,
	bid_map,
	winning_amount,
	time,
    );

    let owner = useraddress_from_u8(0_u8);

    // let sender = owner;
    let balance = 100_u64;
    let ctx4 = (time, owner, balance);

    let finres = auction_finalize(ctx4, state.clone());
    let (state, result_3) = match finres {
	AuctionFinalizeResult::Err(err) => (
	    state.clone(),
	    err == FinalizeError::AuctionStillActive
	),
	AuctionFinalizeResult::Ok((state, _)) => (state, false),
    };

    // // finalizing auction
    // let carol = new_account();
    let (carol, carol_ctx) = new_account(time, 2_u8);

    let ctx5 = (time + 1_u64, carol, winning_amount);
    let finres2 = auction_finalize(ctx5, state.clone());

    let (state, result_4) = match finres2 {
	AuctionFinalizeResult::Err(_) => (state.clone(), false),
	AuctionFinalizeResult::Ok((state, action)) => (
	    state,
	    action
		== FinalizeAction::SimpleTransfer(
		    PublicByteSeq::new(0_usize)
			.concat(&carol)
			.concat(&u64_to_be_bytes(winning_amount))
			.concat(&alice)
			.concat(&u64_to_be_bytes(amount + amount)),
		),
	),
    };

    let result_5 = state.clone()
	== State(
	    AuctionState::Sold(bob),
	    winning_amount,
	    item.clone(),
	    time,
	    bid_map.clone(),
	);

    // attempting to finalize auction again should fail
    let finres3 = auction_finalize(ctx5, state.clone());

    let (state, result_6) = match finres3 {
	AuctionFinalizeResult::Err(err) => (state, err == FinalizeError::AuctionFinalized),
	AuctionFinalizeResult::Ok((state, action)) => (state, false),
    };

    let t = auction_bid(bob_ctx, big_amount, state.clone());

    // let result_7 = t == AuctionBidResult::Err (BidError::AuctionIsFinalized);
    let result_7 = match t {
	AuctionBidResult::Err(e) => e == BidError::AuctionIsFinalized,
	AuctionBidResult::Ok(_) => false,
    };

    result_0 && result_1 && result_2 && result_3 && result_4 && result_5 && result_6 && result_7
}
