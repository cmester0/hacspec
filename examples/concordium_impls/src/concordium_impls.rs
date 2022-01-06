#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

use hacspec_lib::*;

// #[cfg(feature = "hacspec_attributes")]
#[cfg(feature = "hacspec")]
use hacspec_attributes::*;

#[cfg(not(feature = "hacspec"))]
extern crate creusot_contracts;
#[cfg(not(feature = "hacspec"))]
use creusot_contracts::*;

pub type Reject = i32;

// #[cfg_attr(feature = "creusot", logic)]
pub fn reject_impl_deafult() -> Reject {
    i32::MIN
}

pub type OptionReject = Option<Reject>;

// #[cfg_attr(feature = "creusot", logic)]
pub fn new_reject_impl(x: i32) -> OptionReject {
    if x < 0i32 {
        Option::<i32>::Some(x)
	// OptionReject::Some(x)
    } else {
	Option::<i32>::None // OptionReject
    }
}

// #[cfg_attr(feature = "creusot", logic)]
#[ensures(result != 0i32)]
pub fn reject_impl_convert_from_unit() -> Reject {
    i32::MIN + 1i32
}

// #[cfg_attr(feature = "creusot", logic)]
#[ensures(result != 0i32)]
pub fn reject_impl_convert_from_parse_error() -> Reject {
    i32::MIN + 2i32
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

// #[cfg_attr(feature = "creusot", logic)]
#[ensures(result != 0i32)]
pub fn reject_impl_from_log_error(le: LogError) -> Reject {
    match le {
	LogError::Full => i32::MIN + 3i32,
	LogError::Malformed => i32::MIN + 4i32,
    }
}

#[derive(Clone)] // , Debug, PartialEq, Eq
pub enum NewContractNameError {
    NewContractNameErrorMissingInitPrefix,
    NewContractNameErrorTooLong,
    NewContractNameErrorContainsDot,
    NewContractNameErrorInvalidCharacters,
}

// #[cfg_attr(feature = "creusot", logic)]
#[ensures(result != 0i32)]
pub fn reject_impl_from_new_contract_name_error(nre: NewContractNameError) -> Reject {
    match nre {
	NewContractNameError::NewContractNameErrorMissingInitPrefix => i32::MIN + 5i32,
	NewContractNameError::NewContractNameErrorTooLong => i32::MIN + 6i32,
	NewContractNameError::NewContractNameErrorContainsDot => i32::MIN + 9i32,
	NewContractNameError::NewContractNameErrorInvalidCharacters => i32::MIN + 10i32,
    }
}

#[derive(Clone)] // , Debug, PartialEq, Eq
pub enum NewReceiveNameError {
    NewReceiveNameErrorMissingDotSeparator,
    NewReceiveNameErrorTooLong,
    NewReceiveNameErrorInvalidCharacters,
}

// #[cfg_attr(feature = "creusot", logic)]
#[ensures(result != 0i32)]
pub fn reject_impl_from_new_receive_name_error(nre: NewReceiveNameError) -> Reject {
    match nre {
	NewReceiveNameError::NewReceiveNameErrorMissingDotSeparator => i32::MIN + 7i32,
	NewReceiveNameError::NewReceiveNameErrorTooLong => i32::MIN + 8i32,
	NewReceiveNameError::NewReceiveNameErrorInvalidCharacters => i32::MIN + 11i32,
    }
}

pub type ContractState = u32;

pub type SeekResult = Result<(ContractState, u64), ()>;

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

// #[cfg_attr(feature = "creusot", trusted)]
// #[requires(forall<delta : i64> pos === SeekFrom::End(delta) ==> exists<b : u32> current_position.checked_add(delta as u32) == U32Option::Some(b))]
pub fn contract_state_impl_seek(current_position: ContractState, pos: SeekFrom) -> SeekResult {
    match pos {
        SeekFrom::Start(offset) => Result::<(ContractState, u64), ()>::Ok((offset as u32, offset)),
        SeekFrom::End(delta) => {
            if delta >= 0_i64 {
                match current_position.checked_add(delta as u32) {
                    U32Option::Some(b) => Result::<(ContractState, u64), ()>::Ok((b, delta as u64)),
                    U32Option::None => Result::<(ContractState, u64), ()>::Err(()),
                }
            } else {
                match delta.checked_abs() {
                    I64Option::Some(b) =>
                    // {
                    // let new_pos = 4_u32 - (b as u32);
                    {
                	Result::<(ContractState, u64), ()>::Ok(((4_u32 - (b as u32)), (4_u32 - (b as u32)) as u64))
                    }
                    // }
                    I64Option::None => Result::<(ContractState, u64), ()>::Err(()),
                }
            }
        }
        SeekFrom::Current(delta) => {
            if delta >= 0_i64 {
                match current_position.checked_add(delta as u32) {
                    U32Option::Some(offset) => Result::<(ContractState, u64), ()>::Ok((offset, offset as u64)),
                    U32Option::None => Result::<(ContractState, u64), ()>::Err(()),
                }
            } else {
                match delta.checked_abs() {
                    I64Option::Some(b) => match current_position.checked_sub(b as u32) {
                	U32Option::Some(offset) => Result::<(ContractState, u64), ()>::Ok((offset, offset as u64)),
                	U32Option::None => Result::<(ContractState, u64), ()>::Err(()),
                    },
                    I64Option::None => Result::<(ContractState, u64), ()>::Err(()),
                }
            }
        }
    }
}

#[cfg(not(feature = "hacspec"))]
// extern "C" {
//     pub(crate) fn load_state(start: *mut u8, length: u32, offset: u32) -> u32;
// }
pub(crate) fn load_state(start: *mut u8, length: u32, offset: u32) -> u32 {
    1u32
}

// #[cfg(feature = "hacspec")]
// #[cfg_attr(feature = "creusot", trusted)]
#[cfg(feature = "hacspec")]
// #[ensures(result != (buf, 2u32))]
fn load_state_hacspec(buf : PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (buf, 1u32)
}

#[cfg(not(feature = "hacspec"))]
fn load_state_hacspec(buf : PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let mut temp_vec : Vec<u8> = Vec::new();
    for i in 0..buf.len() {
        temp_vec.push(buf.index(i).clone())
    };
    let temp = &mut temp_vec[..];
    let i = unsafe { load_state(temp.as_mut_ptr(), buf.len() as u32, offset) };
    (PublicByteSeq::from_native_slice(temp), i)
}

// #[cfg_attr(feature = "creusot", trusted)]
pub fn contract_state_impl_read_read(
    current_position: ContractState,
    buf : PublicByteSeq // Seq<u8>
    // num_read: u32,
) -> (ContractState, usize) {
    let (buf, num_read) = load_state_hacspec(buf, current_position);
    (current_position + num_read, num_read as usize)
}

/// Read a u32 in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
// #[cfg_attr(feature = "creusot", logic)]
pub fn contract_state_impl_read_read_u64(
    current_position: ContractState,
    num_read: u32,
) -> (ContractState, bool) {
    (current_position + num_read, num_read == 8_u32)
}

/// Read a u32 in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
// #[cfg_attr(feature = "creusot", logic)]
pub fn contract_state_impl_read_read_u32(
    current_position: ContractState,
    num_read: u32,
) -> (ContractState, bool) {
    (current_position + num_read, num_read == 4_u32)
}

/// Read a u8 in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
// #[cfg_attr(feature = "creusot", logic)]
pub fn contract_state_impl_read_read_u8(
    current_position: ContractState,
    num_read: u32,
) -> (ContractState, bool) {
    (current_position + num_read, num_read == 1_u32)
}

// #[cfg_attr(feature = "creusot", logic)]
pub fn write_impl_for_contract_state_test(current_position: ContractState, len: u32) -> bool {
    current_position.checked_add(len).is_none() // Check for overflow
}

// #[cfg_attr(feature = "creusot", trusted)]
pub fn write_impl_for_contract_state(
    current_position: ContractState,
    num_bytes: u32,
) -> (ContractState, usize) {
    (current_position + num_bytes, num_bytes as usize)
}

// #[cfg_attr(feature = "creusot", logic)]
pub fn has_contract_state_impl_for_contract_state_open() -> ContractState {
    0_u32
}

// #[cfg_attr(feature = "creusot", logic)]
pub fn has_contract_state_impl_for_contract_state_reserve_0(len: u32, cur_size: u32) -> bool {
    cur_size < len
}
// #[cfg_attr(feature = "creusot", logic)]
pub fn has_contract_state_impl_for_contract_state_reserve_1(res: u32) -> bool {
    res == 1_u32
}

// #[cfg_attr(feature = "creusot", logic)]
pub fn has_contract_state_impl_for_contract_state_truncate_0(cur_size: u32, new_size: u32) -> bool {
    cur_size > new_size
}
// #[cfg_attr(feature = "creusot", logic)]
pub fn has_contract_state_impl_for_contract_state_truncate_1(
    current_position: ContractState,
    new_size: u32,
) -> ContractState {
    if new_size < current_position {
	new_size
    } else {
	current_position
    }
}

pub type Parameter = u32;

// #[cfg_attr(feature = "creusot", trusted)]
pub fn read_impl_for_parameter_read(
    current_position: Parameter,
    num_read: u32,
) -> (Parameter, usize) {
    (current_position + num_read, num_read as usize)
}

// pub struct AttributeTag(pub u8);
pub type AttributesCursor = (u32, u16);

// #[cfg_attr(feature = "creusot", trusted)]
pub fn has_policy_impl_for_policy_attributes_cursor_next_test(
    policy_attribute_items: AttributesCursor,
) -> bool {
    let (_, remaining_items) = policy_attribute_items;
    remaining_items == 0_u16
}

// #[cfg_attr(feature = "creusot", trusted)]
pub fn has_policy_impl_for_policy_attributes_cursor_next_tag_invalid(
    policy_attribute_items: AttributesCursor,
    tag_value_len_1: u8,
    num_read: u32,
) -> (AttributesCursor, bool) {
    let (current_position, remaining_items) = policy_attribute_items;
    let policy_attribute_items = (current_position + num_read, remaining_items);
    (policy_attribute_items, tag_value_len_1 > 31_u8)
}

// #[cfg_attr(feature = "creusot", trusted)]
pub fn has_policy_impl_for_policy_attributes_cursor_next(
    policy_attribute_items: AttributesCursor,
    num_read: u32,
) -> AttributesCursor {
    let (current_position, remaining_items) = policy_attribute_items;
    (current_position + num_read, remaining_items - 1_u16)
}


