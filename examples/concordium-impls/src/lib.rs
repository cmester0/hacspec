use hacspec_lib::*;

pub type Reject = i32;

pub const I32MIN : i32 = (!(0_i32)) ^ (((!(0_u32)) >> 1) as i32);

pub fn reject_impl_default() -> Reject {
    I32MIN
}

pub enum OptionReject {
    SomeReject(Reject),
    NoneReject
}

pub fn new_reject_impl(x : i32) -> OptionReject{
    if x < 0_i32 {
	OptionReject::SomeReject (x)
    } else {
	OptionReject::NoneReject
    }
}

pub fn reject_impl_convert_from_unit() -> Reject {
    I32MIN + 1_i32
}

pub fn reject_impl_convert_from_parse_error() -> Reject {
    I32MIN + 2_i32
}

/// Errors that can occur during logging.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum LogError {
    /// The log is full.
    Full,
    /// The message to log was malformed (e.g., too long)
    Malformed,
}

pub fn reject_impl_from_log_error(le: LogError) -> Reject {
    match le {
        LogError::Full => I32MIN + 3_i32,
        LogError::Malformed => I32MIN + 4_i32 ,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NewContractNameError {
    NewContractNameErrorMissingInitPrefix,
    NewContractNameErrorTooLong,
    NewContractNameErrorContainsDot,
    NewContractNameErrorInvalidCharacters,
}

pub fn reject_impl_from_new_contract_name_error(nre: NewContractNameError) -> Reject {
    match nre {
        NewContractNameError::NewContractNameErrorMissingInitPrefix => I32MIN + 5_i32,
        NewContractNameError::NewContractNameErrorTooLong => I32MIN + 6_i32,
        NewContractNameError::NewContractNameErrorContainsDot => I32MIN + 9_i32,
        NewContractNameError::NewContractNameErrorInvalidCharacters => I32MIN + 10_i32,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NewReceiveNameError {
    NewReceiveNameErrorMissingDotSeparator,
    NewReceiveNameErrorTooLong,
    NewReceiveNameErrorInvalidCharacters,
}

pub fn reject_impl_from_new_receive_name_error(nre: NewReceiveNameError) -> Reject {
    match nre {
        NewReceiveNameError::NewReceiveNameErrorMissingDotSeparator => I32MIN + 7_i32,
        NewReceiveNameError::NewReceiveNameErrorTooLong => I32MIN + 8_i32,
        NewReceiveNameError::NewReceiveNameErrorInvalidCharacters => I32MIN + 11_i32,
    }
}

pub type ContractState = u32;

// TODO: Ignore until tuple issue is fixed!
// Ignore until tuple issue is fixed!
// #[cfg(test)]
// mod test {
//     /// A type representing the constract state bytes.
//     // #[derive(Default)]

//     // pub fn try_from_u64_to_u32 (inp : i64) -> Result<u32, std::num::TryFromIntError> {
//     //     std::convert::TryFrom::try_from(inp)
//     // }

//     // pub fn try_from_i64_to_u32 (inp : i64) -> Result<u32, std::num::TryFromIntError> {
//     //     std::convert::TryFrom::try_from(inp)
//     // }

//     pub enum SeekResult {
// 	SeekResultOk (u64),
// 	SeekResultErr,
//     }

//     #[derive(Copy, PartialEq, Eq, Clone, Debug)]
//     pub enum SeekFrom {
// 	/// Sets the offset to the provided number of bytes.
// 	Start(u64),

// 	/// Sets the offset to the size of this object plus the specified number of
// 	/// bytes.
// 	///
// 	/// It is possible to seek beyond the end of an object, but it's an error to
// 	/// seek before byte 0.
// 	End(i64),

// 	/// Sets the offset to the current position plus the specified number of
// 	/// bytes.
// 	///
// 	/// It is possible to seek beyond the end of an object, but it's an error to
// 	/// seek before byte 0.
// 	Current(i64),
//     }

//     pub fn contract_state_impl_seek(current_position : ContractState, pos: SeekFrom) -> (ContractState, SeekResult) { // (ContractState, SeekResult)
// 	match pos {
//             SeekFrom::Start (offset) => (offset as u32, SeekResult::SeekResultOk (offset)),
//             SeekFrom::End(delta) => 
// 		if delta >= 0 {
// 		    match current_position.checked_add(delta as u32) {
// 			Option::Some (b) => (b, SeekResult::SeekResultOk(delta as u64)),
// 			Option::None => (current_position, SeekResult::SeekResultErr),
// 		    }
// 		} else {
// 		    match delta.checked_abs() {
// 			Option::Some (b) => // {
// 			// let new_pos = 4_u32 - (b as u32);
// 			    ((4_u32 - (b as u32)), SeekResult::SeekResultOk((4_u32 - (b as u32)) as u64)),
// 			// }
// 			Option::None => (current_position, SeekResult::SeekResultErr),
// 		    }
// 		},
//             SeekFrom::Current(delta) => 
// 		if delta >= 0 {
// 		    match current_position.checked_add(delta as u32) {
// 			Option::Some(offset) => (offset, SeekResult::SeekResultOk(offset as u64)),
// 			Option::None => (current_position, SeekResult::SeekResultErr),
// 		    }
// 		} else {
// 		    match delta.checked_abs() {
// 			Option::Some (b) => match current_position.checked_sub(b as u32) {
// 			    Option::Some(offset) => (offset, SeekResult::SeekResultOk(offset as u64)),
// 			    Option::None => (current_position, SeekResult::SeekResultErr),
// 			},
// 			Option::None => (current_position, SeekResult::SeekResultErr),
// 		    }
// 		},
// 	}
//     }
// }
    
// /// # Contract state trait implementations.
// impl Seek for ContractState {
//     type Err = ();

//     fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Err> {
//         use SeekFrom::*;
//         match pos {
//             Start(offset) => match u32::try_from(offset) {
//                 Ok(offset_u32) => {
//                     self.current_position = offset_u32;
//                     Ok(offset)
//                 }
//                 _ => Err(()),
//             },
//             End(delta) => {
//                 let end = self.size();
//                 if delta >= 0 {
//                     match u32::try_from(delta)
//                         .ok()
//                         .and_then(|x| self.current_position.checked_add(x))
//                     {
//                         Some(offset_u32) => {
//                             self.current_position = offset_u32;
//                             Ok(u64::from(offset_u32))
//                         }
//                         _ => Err(()),
//                     }
//                 } else {
//                     match delta.checked_abs().and_then(|x| u32::try_from(x).ok()) {
//                         Some(before) if before <= end => {
//                             let new_pos = end - before;
//                             self.current_position = new_pos;
//                             Ok(u64::from(new_pos))
//                         }
//                         _ => Err(()),
//                     }
//                 }
//             }
//             Current(delta) => {
//                 let new_offset = if delta >= 0 {
//                     u32::try_from(delta).ok().and_then(|x| self.current_position.checked_add(x))
//                 } else {
//                     delta
//                         .checked_abs()
//                         .and_then(|x| u32::try_from(x).ok())
//                         .and_then(|x| self.current_position.checked_sub(x))
//                 };
//                 match new_offset {
//                     Some(offset) => {
//                         self.current_position = offset;
//                         Ok(u64::from(offset))
//                     }
//                     _ => Err(()),
//                 }
//             }
//         }
//     }
// }

// , load_state : &dyn Fn(*mut u8, u32, u32) -> ([u8], u32)
pub fn contract_state_impl_read_read(current_position : ContractState, num_read: u32) -> (ContractState, usize) {
    (current_position + num_read, num_read as usize)
}

/// Read a `u32` in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
pub fn contract_state_impl_read_read_u64(current_position : ContractState, num_read : u32) -> (ContractState, bool) {
    (current_position + num_read, num_read == 8_u32)
}

/// Read a `u32` in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
pub fn contract_state_impl_read_read_u32(current_position : ContractState, num_read : u32) -> (ContractState, bool) {    
    (current_position + num_read, num_read == 4_u32)
}

/// Read a `u8` in little-endian format. This is optimized to not
/// initialize a dummy value before calling an external function.
pub fn contract_state_impl_read_read_u8(current_position : ContractState, num_read : u32) -> (ContractState, bool) {
    (current_position + num_read, num_read == 1_u32)
}

pub fn write_impl_for_contract_state_test(current_position : ContractState, len : u32) -> bool {
    current_position.checked_add(len).is_none() // Check for overflow
}
pub fn write_impl_for_contract_state(current_position : ContractState, num_bytes : u32) -> (ContractState, usize) {
    (current_position + num_bytes, num_bytes as usize)
}

pub fn has_contract_state_impl_for_contract_state_open() -> ContractState {
    0_u32
}

pub fn has_contract_state_impl_for_contract_state_reserve_0(len : u32, cur_size : u32) -> bool {
    cur_size < len
}
pub fn has_contract_state_impl_for_contract_state_reserve_1(res : u32) -> bool {
    res == 1_u32
}

pub fn has_contract_state_impl_for_contract_state_truncate_0(cur_size : u32, new_size : u32) -> bool {
    cur_size > new_size
}
pub fn has_contract_state_impl_for_contract_state_truncate_1(current_position : ContractState, new_size : u32) -> ContractState {
    if new_size < current_position {
	new_size
    } else {
	current_position
    }	
}

pub type Parameter = u32;

pub fn read_impl_for_parameter_read(current_position : Parameter, num_read : u32) -> (Parameter, usize) {
    (current_position + num_read, num_read as usize)
}

// pub struct AttributeTag(pub u8);
pub type AttributesCursor = (u32, u16);

pub fn has_policy_impl_for_policy_attributes_cursor_next_test (policy_attribute_items : AttributesCursor) -> bool {
    let (_,remaining_items) = policy_attribute_items;
    remaining_items == 0_u16
}

pub fn has_policy_impl_for_policy_attributes_cursor_next_tag_invalid (policy_attribute_items : AttributesCursor, tag_value_len_1 : u8, num_read : u32) -> (AttributesCursor, bool) {
    let (current_position,remaining_items) = policy_attribute_items;
    let policy_attribute_items = (current_position + num_read, remaining_items);
    (policy_attribute_items, tag_value_len_1 > 31_u8)
}


pub fn has_policy_impl_for_policy_attributes_cursor_next (policy_attribute_items : AttributesCursor, num_read : u32) -> AttributesCursor {
    let (current_position,remaining_items) = policy_attribute_items;
    (current_position + num_read, remaining_items - 1_u16)
}

// /// An iterator over policies using host functions to supply the data.
// /// The main interface to using this type is via the methods of the [Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html)
// /// and [ExactSizeIterator](https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html) traits.
// pub struct PoliciesIterator {
//     /// Position in the policies binary serialization.
//     pos:             u32,
//     /// Number of remaining items in the stream.
//     remaining_items: u16,
// }

// impl Iterator for PoliciesIterator {
//     type Item = Policy<AttributesCursor>;

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.remaining_items == 0 {
//             return None;
//         }
//         // 2 for total size of this section, 4 for identity_provider,
//         // 8 bytes for created_at, 8 for valid_to, and 2 for
//         // the length
//         let mut buf: MaybeUninit<[u8; 2 + 4 + 8 + 8 + 2]> = MaybeUninit::uninit();
//         let buf = unsafe {
//             get_policy_section(buf.as_mut_ptr() as *mut u8, 2 + 4 + 8 + 8 + 2, self.pos);
//             buf.assume_init()
//         };
//         let skip_part: [u8; 2] = buf[0..2].try_into().unwrap_abort();
//         let ip_part: [u8; 4] = buf[2..2 + 4].try_into().unwrap_abort();
//         let created_at_part: [u8; 8] = buf[2 + 4..2 + 4 + 8].try_into().unwrap_abort();
//         let valid_to_part: [u8; 8] = buf[2 + 4 + 8..2 + 4 + 8 + 8].try_into().unwrap_abort();
//         let len_part: [u8; 2] = buf[2 + 4 + 8 + 8..2 + 4 + 8 + 8 + 2].try_into().unwrap_abort();
//         let identity_provider = IdentityProvider::from_le_bytes(ip_part);
//         let created_at = Timestamp::from_timestamp_millis(u64::from_le_bytes(created_at_part));
//         let valid_to = Timestamp::from_timestamp_millis(u64::from_le_bytes(valid_to_part));
//         let remaining_items = u16::from_le_bytes(len_part);
//         let attributes_start = self.pos + 2 + 4 + 8 + 8 + 2;
//         self.pos += u32::from(u16::from_le_bytes(skip_part)) + 2;
//         self.remaining_items -= 1;
//         Some(Policy {
//             identity_provider,
//             created_at,
//             valid_to,
//             items: AttributesCursor {
//                 current_position: attributes_start,
//                 remaining_items,
//             },
//         })
//     }

//     fn size_hint(&self) -> (usize, Option<usize>) {
//         let rem = self.remaining_items as usize;
//         (rem, Some(rem))
//     }
// }

// impl ExactSizeIterator for PoliciesIterator {
//     #[inline(always)]
//     fn len(&self) -> usize { self.remaining_items as usize }
// }

// impl<T: sealed::ContextType> HasCommonData for ExternContext<T> {
//     type MetadataType = ChainMetaExtern;
//     type ParamType = Parameter;
//     type PolicyIteratorType = PoliciesIterator;
//     type PolicyType = Policy<AttributesCursor>;

//     #[inline(always)]
//     fn metadata(&self) -> &Self::MetadataType { &ChainMetaExtern {} }

//     fn policies(&self) -> PoliciesIterator {
//         let mut buf: MaybeUninit<[u8; 2]> = MaybeUninit::uninit();
//         let buf = unsafe {
//             get_policy_section(buf.as_mut_ptr() as *mut u8, 2, 0);
//             buf.assume_init()
//         };
//         PoliciesIterator {
//             pos:             2, // 2 because we already read 2 bytes.
//             remaining_items: u16::from_le_bytes(buf),
//         }
//     }

//     #[inline(always)]
//     fn parameter_cursor(&self) -> Self::ParamType {
//         Parameter {
//             current_position: 0,
//         }
//     }
// }

// /// # Trait implementations for the init context
// impl HasInitContext for ExternContext<crate::types::InitContextExtern> {
//     type InitData = ();

//     /// Create a new init context by using an external call.
//     fn open(_: Self::InitData) -> Self { ExternContext::default() }

//     #[inline(always)]
//     fn init_origin(&self) -> AccountAddress {
//         let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
//         let ptr = bytes.as_mut_ptr();
//         let address = unsafe {
//             get_init_origin(ptr as *mut u8);
//             bytes.assume_init()
//         };
//         AccountAddress(address)
//     }
// }

// /// # Trait implementations for the receive context
// impl HasReceiveContext for ExternContext<crate::types::ReceiveContextExtern> {
//     type ReceiveData = ();

//     /// Create a new receive context
//     fn open(_: Self::ReceiveData) -> Self { ExternContext::default() }

//     #[inline(always)]
//     fn invoker(&self) -> AccountAddress {
//         let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
//         let ptr = bytes.as_mut_ptr();
//         let address = unsafe {
//             get_receive_invoker(ptr as *mut u8);
//             bytes.assume_init()
//         };
//         AccountAddress(address)
//     }

//     #[inline(always)]
//     fn self_address(&self) -> ContractAddress {
//         let mut bytes: MaybeUninit<[u8; 16]> = MaybeUninit::uninit();
//         let ptr = bytes.as_mut_ptr();
//         let address = unsafe {
//             get_receive_self_address(ptr as *mut u8);
//             bytes.assume_init()
//         };
//         match from_bytes(&address) {
//             Ok(v) => v,
//             Err(_) => crate::trap(),
//         }
//     }

//     #[inline(always)]
//     fn self_balance(&self) -> Amount {
//         Amount::from_micro_gtu(unsafe { get_receive_self_balance() })
//     }

//     #[inline(always)]
//     fn sender(&self) -> Address {
//         let mut bytes: MaybeUninit<[u8; 33]> = MaybeUninit::uninit();
//         let ptr = bytes.as_mut_ptr() as *mut u8;
//         unsafe {
//             get_receive_sender(ptr);
//             let tag = *ptr;
//             match tag {
//                 0u8 => {
//                     match from_bytes(core::slice::from_raw_parts(ptr.add(1), ACCOUNT_ADDRESS_SIZE))
//                     {
//                         Ok(v) => Address::Account(v),
//                         Err(_) => crate::trap(),
//                     }
//                 }
//                 1u8 => match from_bytes(core::slice::from_raw_parts(ptr.add(1), 16)) {
//                     Ok(v) => Address::Contract(v),
//                     Err(_) => crate::trap(),
//                 },
//                 _ => crate::trap(), // unreachable!("Host violated precondition."),
//             }
//         }
//     }

//     #[inline(always)]
//     fn owner(&self) -> AccountAddress {
//         let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
//         let ptr = bytes.as_mut_ptr();
//         let address = unsafe {
//             get_receive_owner(ptr as *mut u8);
//             bytes.assume_init()
//         };
//         AccountAddress(address)
//     }
// }

// /// #Implementations of the logger.

// impl HasLogger for Logger {
//     #[inline(always)]
//     fn init() -> Self {
//         Self {
//             _private: (),
//         }
//     }

//     fn log_raw(&mut self, event: &[u8]) -> Result<(), LogError> {
//         let res = unsafe { log_event(event.as_ptr(), event.len() as u32) };
//         match res {
//             1 => Ok(()),
//             0 => Err(LogError::Full),
//             _ => Err(LogError::Malformed),
//         }
//     }
// }

// /// #Implementation of actions.
// /// These actions are implemented by direct calls to host functions.
// impl HasActions for Action {
//     #[inline(always)]
//     fn accept() -> Self {
//         Action {
//             _private: unsafe { accept() },
//         }
//     }

//     #[inline(always)]
//     fn simple_transfer(acc: &AccountAddress, amount: Amount) -> Self {
//         let res = unsafe { simple_transfer(acc.0.as_ptr(), amount.micro_gtu) };
//         Action {
//             _private: res,
//         }
//     }

//     #[inline(always)]
//     fn send_raw(
//         ca: &ContractAddress,
//         receive_name: ReceiveName,
//         amount: Amount,
//         parameter: &[u8],
//     ) -> Self {
//         let receive_bytes = receive_name.get_chain_name().as_bytes();
//         let res = unsafe {
//             prims::send(
//                 ca.index,
//                 ca.subindex,
//                 receive_bytes.as_ptr(),
//                 receive_bytes.len() as u32,
//                 amount.micro_gtu,
//                 parameter.as_ptr(),
//                 parameter.len() as u32,
//             )
//         };
//         Action {
//             _private: res,
//         }
//     }

//     #[inline(always)]
//     fn and_then(self, then: Self) -> Self {
//         let res = unsafe { combine_and(self._private, then._private) };
//         Action {
//             _private: res,
//         }
//     }

//     #[inline(always)]
//     fn or_else(self, el: Self) -> Self {
//         let res = unsafe { combine_or(self._private, el._private) };
//         Action {
//             _private: res,
//         }
//     }
// }

// /// Allocates a Vec of bytes prepended with its length as a `u32` into memory,
// /// and prevents them from being dropped. Returns the pointer.
// /// Used to pass bytes from a Wasm module to its host.
// #[doc(hidden)]
// pub fn put_in_memory(input: &[u8]) -> *mut u8 {
//     let bytes_length = input.len() as u32;
//     let mut bytes = to_bytes(&bytes_length);
//     bytes.extend_from_slice(input);
//     let ptr = bytes.as_mut_ptr();
//     #[cfg(feature = "std")]
//     ::std::mem::forget(bytes);
//     #[cfg(not(feature = "std"))]
//     core::mem::forget(bytes);
//     ptr
// }

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
//     let param_bytes = to_bytes(parameter);
//     A::send_raw(ca, receive_name, amount, &param_bytes)
// }

// impl<A, E> UnwrapAbort for Result<A, E> {
//     type Unwrap = A;

//     #[inline]
//     fn unwrap_abort(self) -> Self::Unwrap {
//         match self {
//             Ok(x) => x,
//             Err(_) => crate::trap(),
//         }
//     }
// }

// #[cfg(not(feature = "std"))]
// use core::fmt;
// #[cfg(feature = "std")]
// use std::fmt;

// impl<A, E: fmt::Debug> ExpectReport for Result<A, E> {
//     type Unwrap = A;

//     fn expect_report(self, msg: &str) -> Self::Unwrap {
//         match self {
//             Ok(x) => x,
//             Err(e) => crate::fail!("{}: {:?}", msg, e),
//         }
//     }
// }

// impl<A: fmt::Debug, E> ExpectErrReport for Result<A, E> {
//     type Unwrap = E;

//     fn expect_err_report(self, msg: &str) -> Self::Unwrap {
//         match self {
//             Ok(a) => crate::fail!("{}: {:?}", msg, a),
//             Err(e) => e,
//         }
//     }
// }

// impl<A> UnwrapAbort for Option<A> {
//     type Unwrap = A;

//     #[inline(always)]
//     fn unwrap_abort(self) -> Self::Unwrap { self.unwrap_or_else(|| crate::trap()) }
// }

// impl<A> ExpectReport for Option<A> {
//     type Unwrap = A;

//     fn expect_report(self, msg: &str) -> Self::Unwrap {
//         match self {
//             Some(v) => v,
//             None => crate::fail!("{}", msg),
//         }
//     }
// }

// impl<A: fmt::Debug> ExpectNoneReport for Option<A> {
//     fn expect_none_report(self, msg: &str) {
//         if let Some(x) = self {
//             crate::fail!("{}: {:?}", msg, x)
//         }
//     }
// }

// impl<K: Serial + Ord> SerialCtx for BTreeSet<K> {
//     fn serial_ctx<W: Write>(
//         &self,
//         size_len: schema::SizeLength,
//         out: &mut W,
//     ) -> Result<(), W::Err> {
//         schema::serial_length(self.len(), size_len, out)?;
//         serial_set_no_length(self, out)
//     }
// }

// impl<K: Deserial + Ord + Copy> DeserialCtx for BTreeSet<K> {
//     fn deserial_ctx<R: Read>(
//         size_len: schema::SizeLength,
//         ensure_ordered: bool,
//         source: &mut R,
//     ) -> ParseResult<Self> {
//         let len = schema::deserial_length(source, size_len)?;
//         if ensure_ordered {
//             deserial_set_no_length(source, len)
//         } else {
//             deserial_set_no_length_no_order_check(source, len)
//         }
//     }
// }

// impl<K: Serial + Ord, V: Serial> SerialCtx for BTreeMap<K, V> {
//     fn serial_ctx<W: Write>(
//         &self,
//         size_len: schema::SizeLength,
//         out: &mut W,
//     ) -> Result<(), W::Err> {
//         schema::serial_length(self.len(), size_len, out)?;
//         serial_map_no_length(self, out)
//     }
// }

// impl<K: Deserial + Ord + Copy, V: Deserial> DeserialCtx for BTreeMap<K, V> {
//     fn deserial_ctx<R: Read>(
//         size_len: schema::SizeLength,
//         ensure_ordered: bool,
//         source: &mut R,
//     ) -> ParseResult<Self> {
//         let len = schema::deserial_length(source, size_len)?;
//         if ensure_ordered {
//             deserial_map_no_length(source, len)
//         } else {
//             deserial_map_no_length_no_order_check(source, len)
//         }
//     }
// }

// /// Serialization for HashSet given a size_len.
// /// Values are not serialized in any particular order.
// impl<K: Serial> SerialCtx for HashSet<K> {
//     fn serial_ctx<W: Write>(
//         &self,
//         size_len: schema::SizeLength,
//         out: &mut W,
//     ) -> Result<(), W::Err> {
//         schema::serial_length(self.len(), size_len, out)?;
//         serial_hashset_no_length(self, out)
//     }
// }

// /// Deserialization for HashSet given a size_len.
// /// Values are not verified to be in any particular order and setting
// /// ensure_ordering have no effect.
// impl<K: Deserial + Eq + Hash> DeserialCtx for HashSet<K> {
//     fn deserial_ctx<R: Read>(
//         size_len: schema::SizeLength,
//         _ensure_ordered: bool,
//         source: &mut R,
//     ) -> ParseResult<Self> {
//         let len = schema::deserial_length(source, size_len)?;
//         deserial_hashset_no_length(source, len)
//     }
// }

// /// Serialization for HashMap given a size_len.
// /// Keys are not serialized in any particular order.
// impl<K: Serial, V: Serial> SerialCtx for HashMap<K, V> {
//     fn serial_ctx<W: Write>(
//         &self,
//         size_len: schema::SizeLength,
//         out: &mut W,
//     ) -> Result<(), W::Err> {
//         schema::serial_length(self.len(), size_len, out)?;
//         serial_hashmap_no_length(self, out)
//     }
// }

// /// Deserialization for HashMap given a size_len.
// /// Keys are not verified to be in any particular order and setting
// /// ensure_ordering have no effect.
// impl<K: Deserial + Eq + Hash, V: Deserial> DeserialCtx for HashMap<K, V> {
//     fn deserial_ctx<R: Read>(
//         size_len: schema::SizeLength,
//         _ensure_ordered: bool,
//         source: &mut R,
//     ) -> ParseResult<Self> {
//         let len = schema::deserial_length(source, size_len)?;
//         deserial_hashmap_no_length(source, len)
//     }
// }

// impl<T: Serial> SerialCtx for &[T] {
//     fn serial_ctx<W: Write>(
//         &self,
//         size_len: schema::SizeLength,
//         out: &mut W,
//     ) -> Result<(), W::Err> {
//         schema::serial_length(self.len(), size_len, out)?;
//         serial_vector_no_length(self, out)
//     }
// }

// impl<T: Deserial> DeserialCtx for Vec<T> {
//     fn deserial_ctx<R: Read>(
//         size_len: schema::SizeLength,
//         _ensure_ordered: bool,
//         source: &mut R,
//     ) -> ParseResult<Self> {
//         let len = schema::deserial_length(source, size_len)?;
//         deserial_vector_no_length(source, len)
//     }
// }

// impl SerialCtx for &str {
//     fn serial_ctx<W: Write>(
//         &self,
//         size_len: schema::SizeLength,
//         out: &mut W,
//     ) -> Result<(), W::Err> {
//         schema::serial_length(self.len(), size_len, out)?;
//         serial_vector_no_length(&self.as_bytes().to_vec(), out)
//     }
// }

// impl SerialCtx for String {
//     fn serial_ctx<W: Write>(
//         &self,
//         size_len: schema::SizeLength,
//         out: &mut W,
//     ) -> Result<(), W::Err> {
//         self.as_str().serial_ctx(size_len, out)
//     }
// }

// impl DeserialCtx for String {
//     fn deserial_ctx<R: Read>(
//         size_len: schema::SizeLength,
//         _ensure_ordered: bool,
//         source: &mut R,
//     ) -> ParseResult<Self> {
//         let len = schema::deserial_length(source, size_len)?;
//         let bytes = deserial_vector_no_length(source, len)?;
//         let res = String::from_utf8(bytes).map_err(|_| ParseError::default())?;
//         Ok(res)
//     }
// }
