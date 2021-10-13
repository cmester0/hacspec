use hacspec_lib::prelude::*;
use concordium_std::*;
use concordium_impls::*;
use std::convert::{self, TryFrom, TryInto};
use std::mem;
use std::num;
use mem::MaybeUninit;

/// An error message, signalling rejection of a smart contract invocation.
/// The client will see the error code as a reject reason; if a schema is
/// provided, the error message corresponding to the error code will be
/// displayed. The valid range for an error code is from i32::MIN to  -1.
#[derive(Eq, PartialEq, Debug)]
#[repr(transparent)]
pub struct Reject {
    pub error_code: num::NonZeroI32,
}

fn my_reject_to_their_reject(inp : concordium_impls::Reject) -> Reject {
    let error_code = unsafe { num::NonZeroI32::new_unchecked(inp) };
    Reject {error_code,}
}

/// Default error is i32::MIN.
impl Default for Reject {
    #[inline(always)]
    fn default() -> Self {
        my_reject_to_their_reject(reject_impl_default())
    }
}

impl Reject {
    /// This returns `None` for all values >= 0 and `Some` otherwise.
    pub fn new(x: i32) -> Option<Self> {
        match new_reject_impl(x) {
            OptionReject::SomeReject (error_code) => Some(my_reject_to_their_reject(error_code)),
            OptionReject::NoneReject => None,
        }
    }
}

impl convert::From<()> for Reject {
    #[inline(always)]
    fn from(_: ()) -> Self {
        my_reject_to_their_reject(reject_impl_convert_from_unit())
    }
}

impl convert::From<ParseError> for Reject {
    #[inline(always)]
    fn from(_: ParseError) -> Self {
        my_reject_to_their_reject(reject_impl_convert_from_parse_error())
    }
}

fn their_logerror_to_my_logerror(inp : concordium_std::LogError) -> concordium_impls::LogError {
    match inp {
        concordium_std::LogError::Full      => concordium_impls::LogError::Full,
        concordium_std::LogError::Malformed => concordium_impls::LogError::Malformed,
    }
}

/// full is mapped to i32::MIN+3, Malformed is mapped to i32::MIN+4.
impl From<concordium_std::LogError> for Reject {
    #[inline(always)]
    fn from(le: concordium_std::LogError) -> Self {
        my_reject_to_their_reject(reject_impl_from_log_error(their_logerror_to_my_logerror(le)))        
    }
}

fn their_new_contract_name_error_to_my_new_contract_name_error(inp : concordium_std::NewContractNameError) -> concordium_impls::NewContractNameError {
    match inp {
        concordium_std::NewContractNameError::MissingInitPrefix => concordium_impls::NewContractNameError::NewContractNameErrorMissingInitPrefix,
        concordium_std::NewContractNameError::TooLong           => concordium_impls::NewContractNameError::NewContractNameErrorTooLong,
        concordium_std::NewContractNameError::ContainsDot => concordium_impls::NewContractNameError::NewContractNameErrorContainsDot,
        concordium_std::NewContractNameError::InvalidCharacters => concordium_impls::NewContractNameError::NewContractNameErrorInvalidCharacters,
    }
}

/// MissingInitPrefix is mapped to i32::MIN + 5,
/// TooLong to i32::MIN + 6,
/// ContainsDot to i32::MIN + 9, and
/// InvalidCharacters to i32::MIN + 10.
impl From<concordium_std::NewContractNameError> for Reject {
    fn from(nre: concordium_std::NewContractNameError) -> Self {
        my_reject_to_their_reject(reject_impl_from_new_contract_name_error(their_new_contract_name_error_to_my_new_contract_name_error(nre)))
    }
}

fn their_new_receive_name_error_to_my_new_receive_name_error(inp : concordium_std::NewReceiveNameError) -> concordium_impls::NewReceiveNameError {
    match inp {
        concordium_std::NewReceiveNameError::MissingDotSeparator => concordium_impls::NewReceiveNameError::NewReceiveNameErrorMissingDotSeparator,
        concordium_std::NewReceiveNameError::TooLong             => concordium_impls::NewReceiveNameError::NewReceiveNameErrorTooLong,
        concordium_std::NewReceiveNameError::InvalidCharacters   => concordium_impls::NewReceiveNameError::NewReceiveNameErrorInvalidCharacters,
    }
}

/// missingdotseparator is mapped to i32::MIN + 7,
/// TooLong to i32::MIN + 8, and
/// InvalidCharacters to i32::MIN + 11.
impl From<concordium_std::NewReceiveNameError> for Reject {
    fn from(nre: concordium_std::NewReceiveNameError) -> Self {
        my_reject_to_their_reject(reject_impl_from_new_receive_name_error(their_new_receive_name_error_to_my_new_receive_name_error(nre)))
    }
}

/// A type representing the constract state bytes.
#[derive(Default)]
pub struct ContractState {
    pub(crate) current_position: u32,
}

fn update_their_contract_state (a : concordium_impls::ContractState, b : &mut ContractState) {
    b.current_position = a;
}

// TODO: Put hacspec implementation into seek
/// # Contract state trait implementations.
impl Seek for ContractState {
    type Err = ();

    fn seek(&mut self, pos: concordium_std::SeekFrom) -> Result<u64, Self::Err> {
        let pos_our = match pos {
            concordium_std::SeekFrom::Start (a) => concordium_impls::SeekFrom::Start (a),
            concordium_std::SeekFrom::End (a) => concordium_impls::SeekFrom::End (a),
            concordium_std::SeekFrom::Current (a) => concordium_impls::SeekFrom::Current (a)
        };
        
        let (offset, res) = contract_state_impl_seek (self.current_position, pos_our);
        self.current_position += offset;
        match res {
            SeekResult::Ok (a) => Ok (a),
            SeekResult::Err (()) => Err (())
        }
    }
}

// Found in concordium-std/srd/prims.rs
extern "C" {
    // returns how many bytes were read.
    pub(crate) fn load_state(start: *mut u8, length: u32, offset: u32) -> u32;
}

impl Read for ContractState {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ParseError> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read = unsafe { load_state(buf.as_mut_ptr(), len, self.current_position) };

        let (new_pos, ret) = contract_state_impl_read_read(self.current_position, num_read);
        update_their_contract_state(new_pos, self);
        Ok(ret)
    }

    /// Read a `u32` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u64(&mut self) -> ParseResult<u64> {
        let mut bytes: MaybeUninit<[u8; 8]> = MaybeUninit::uninit();
        let num_read =
            unsafe { load_state(bytes.as_mut_ptr() as *mut u8, 8, self.current_position) };
        let (new_pos, success) = contract_state_impl_read_read_u64(self.current_position, num_read);
        update_their_contract_state(new_pos, self);
        if success {
            Ok(unsafe { u64::from_le_bytes(bytes.assume_init()) })
        } else {
            Err(ParseError::default())
        }
    }

    /// Read a `u32` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u32(&mut self) -> ParseResult<u32> {
        let mut bytes: MaybeUninit<[u8; 4]> = MaybeUninit::uninit();
        let num_read =
            unsafe { load_state(bytes.as_mut_ptr() as *mut u8, 4, self.current_position) };

        let (new_pos, success) = contract_state_impl_read_read_u32(self.current_position, num_read);
        update_their_contract_state(new_pos, self);
        if success {
            Ok(unsafe { u32::from_le_bytes(bytes.assume_init()) })
        } else {
            Err(ParseError::default())
        }
    }

    /// Read a `u8` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u8(&mut self) -> ParseResult<u8> {
        let mut bytes: MaybeUninit<[u8; 1]> = MaybeUninit::uninit();
        let num_read =
            unsafe { load_state(bytes.as_mut_ptr() as *mut u8, 1, self.current_position) };

        let (new_pos, success) = contract_state_impl_read_read_u8(self.current_position, num_read);
        update_their_contract_state(new_pos, self);
        if success {
            unsafe { Ok(bytes.assume_init()[0]) }
        }
        else {
            Err(ParseError::default())
        }
    }
}

// Found in concordium-std/srd/prims.rs
extern "C" {
    // returns how many bytes were written
    pub(crate) fn write_state(start: *const u8, length: u32, offset: u32) -> u32;
}

impl Write for ContractState {
    type Err = ();

    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(()),
            }
        };
        if write_impl_for_contract_state_test(self.current_position, len) {
            return Err(());
        }
        let num_bytes = unsafe { write_state(buf.as_ptr(), len, self.current_position) };
         let (new_pos, ret) = write_impl_for_contract_state(self.current_position, num_bytes); // safe because of check above that len + pos is small enough
        update_their_contract_state(new_pos, self);
        Ok(ret)
    }
}


// Found in concordium-std/srd/prims.rs
extern "C" {
    // this was unsuccesful (new state too big), or 1 if successful.
    pub(crate) fn resize_state(new_size: u32) -> u32; // returns 0 or 1.
    // get current state size in bytes.
    pub(crate) fn state_size() -> u32;
}

impl HasContractState<()> for ContractState {
    type ContractStateData = ();

    #[inline(always)]
    fn open(_: Self::ContractStateData) -> Self {
        ContractState {
            current_position: has_contract_state_impl_for_contract_state_open(),
        }
    }

    fn reserve(&mut self, len: u32) -> bool {
        let cur_size = unsafe { state_size() };
        if has_contract_state_impl_for_contract_state_reserve_0(cur_size, len) {
            let res = unsafe { resize_state(len) };
            has_contract_state_impl_for_contract_state_reserve_1(res)
        } else {
            true
        }
    }

    #[inline(always)]
    fn size(&self) -> u32 { unsafe { state_size() } }

    fn truncate(&mut self, new_size: u32) {
        let cur_size = self.size();
        if has_contract_state_impl_for_contract_state_truncate_0(cur_size, new_size) {
            unsafe { resize_state(new_size) };
        }
        update_their_contract_state(has_contract_state_impl_for_contract_state_truncate_1(self.current_position, new_size), self)
    }
}

#[derive(Default)]
/// A type representing the parameter to init and receive methods.
pub struct Parameter {
    pub(crate) current_position: u32,
}

fn update_their_parameter_state (a : concordium_impls::Parameter, b : &mut Parameter) {
    b.current_position = a;
}

// Found in concordium-std/srd/prims.rs
extern "C" {
    // Write a section of the parameter to the given location. Return the number
    // of bytes written. The location is assumed to contain enough memory to
    // write the requested length into.
    pub(crate) fn get_parameter_section(param_bytes: *mut u8, length: u32, offset: u32) -> u32;
}
    
/// # Trait implementations for Parameter
impl Read for Parameter {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read =
            unsafe { get_parameter_section(buf.as_mut_ptr(), len, self.current_position) };
        let (new_pos, ret) = read_impl_for_parameter_read(self.current_position, num_read);
        update_their_parameter_state(new_pos, self);
        Ok(ret)
    }
}

// Found in concordium-std/srd/prims.rs
extern "C" {
    // Get the size of the parameter to the method (either init or receive).
    pub(crate) fn get_parameter_size() -> u32;
}

impl HasParameter for Parameter {
    #[inline(always)]
    fn size(&self) -> u32 { unsafe { get_parameter_size() } }
}


// Found in concordium-std/srd/prims.rs
extern "C" {
    // Getters for the chain meta data
    /// Slot time (in milliseconds) from chain meta data
    pub(crate) fn get_slot_time() -> u64;
}

#[doc(hidden)]
pub struct ChainMetaExtern {}

/// # Trait implementations for the chain metadata.
impl HasChainMetadata for ChainMetaExtern {
    #[inline(always)]
    fn slot_time(&self) -> SlotTime { Timestamp::from_timestamp_millis(unsafe { get_slot_time() }) }
}

// Found in concordium-std/srd/prims.rs
extern "C" {
    // Write a section of the policy to the given location. Return the number
    // of bytes written. The location is assumed to contain enough memory to
    // write the requested length into.
    pub(crate) fn get_policy_section(policy_bytes: *mut u8, length: u32, offset: u32) -> u32;
}

/// A type representing the attributes, lazily acquired from the host.
#[derive(Default, Clone)]
pub struct AttributesCursor {
    /// Current position of the cursor, starting from 0.
    /// Note that this is only for the variable attributes.
    /// `created_at` and `valid_to` will require.
    pub(crate) current_position: u32,
    /// The number of remaining items in the policy.
    pub(crate) remaining_items:  u16,
}

fn my_attributes_cursor_to_their_attributes_cursor(inp : concordium_impls::AttributesCursor) -> AttributesCursor {
    let (current_position,remaining_items) = inp;
    AttributesCursor {current_position: current_position, remaining_items: remaining_items}
}

fn their_attributes_cursor_to_my_attributes_cursor(inp : AttributesCursor) -> concordium_impls::AttributesCursor {
    (inp.current_position, inp.remaining_items)
}


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
    pub created_at:        Timestamp,
    /// Beginning of the month where the identity is __no longer valid__.
    pub valid_to:          Timestamp,
    /// List of attributes, in ascending order of the tag.
    pub items:             Attributes,
}


impl HasPolicy for Policy<AttributesCursor> {
    fn identity_provider(&self) -> IdentityProvider { self.identity_provider }

    fn created_at(&self) -> Timestamp { self.created_at }

    fn valid_to(&self) -> Timestamp { self.valid_to }

    fn next_item(&mut self, buf: &mut [u8; 31]) -> Option<(AttributeTag, u8)> {
        if has_policy_impl_for_policy_attributes_cursor_next_test(their_attributes_cursor_to_my_attributes_cursor(self.items.clone())) {
            return None;
        }

        let (tag_value_len, num_read) = unsafe {
            let mut tag_value_len = MaybeUninit::<[u8; 2]>::uninit();
            // Should succeed, otherwise host violated precondition.
            let num_read = get_policy_section(
                tag_value_len.as_mut_ptr() as *mut u8,
                2,
                self.items.current_position,
            );
            (tag_value_len.assume_init(), num_read)
        };

        let (new_self_items, check) = has_policy_impl_for_policy_attributes_cursor_next_tag_invalid(their_attributes_cursor_to_my_attributes_cursor(self.items.clone()), tag_value_len[1], num_read);
        self.items = my_attributes_cursor_to_their_attributes_cursor(new_self_items);
        if check {
            // Should not happen because all attributes fit into 31 bytes.
            return None;
        }

        
        let num_read = unsafe {
            get_policy_section(
                buf.as_mut_ptr(),
                u32::from(tag_value_len[1]),
                self.items.current_position,
            )
        };
        self.items = my_attributes_cursor_to_their_attributes_cursor(has_policy_impl_for_policy_attributes_cursor_next(their_attributes_cursor_to_my_attributes_cursor(self.items.clone()), num_read));
        Some((AttributeTag(tag_value_len[0]), tag_value_len[1]))
    }
}

/// An iterator over policies using host functions to supply the data.
/// The main interface to using this type is via the methods of the [Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html)
/// and [ExactSizeIterator](https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html) traits.
pub struct PoliciesIterator {
    /// Position in the policies binary serialization.
    pos:             u32,
    /// Number of remaining items in the stream.
    remaining_items: u16,
}

impl Iterator for PoliciesIterator {
    type Item = Policy<AttributesCursor>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_items == 0 {
            return None;
        }
        // 2 for total size of this section, 4 for identity_provider,
        // 8 bytes for created_at, 8 for valid_to, and 2 for
        // the length
        let mut buf: MaybeUninit<[u8; 2 + 4 + 8 + 8 + 2]> = MaybeUninit::uninit();
        let buf = unsafe {
            get_policy_section(buf.as_mut_ptr() as *mut u8, 2 + 4 + 8 + 8 + 2, self.pos);
            buf.assume_init()
        };
        let skip_part: [u8; 2] = buf[0..2].try_into().unwrap_abort();
        let ip_part: [u8; 4] = buf[2..2 + 4].try_into().unwrap_abort();
        let created_at_part: [u8; 8] = buf[2 + 4..2 + 4 + 8].try_into().unwrap_abort();
        let valid_to_part: [u8; 8] = buf[2 + 4 + 8..2 + 4 + 8 + 8].try_into().unwrap_abort();
        let len_part: [u8; 2] = buf[2 + 4 + 8 + 8..2 + 4 + 8 + 8 + 2].try_into().unwrap_abort();
        let identity_provider = IdentityProvider::from_le_bytes(ip_part);
        let created_at = Timestamp::from_timestamp_millis(u64::from_le_bytes(created_at_part));
        let valid_to = Timestamp::from_timestamp_millis(u64::from_le_bytes(valid_to_part));
        let remaining_items = u16::from_le_bytes(len_part);
        let attributes_start = self.pos + 2 + 4 + 8 + 8 + 2;
        self.pos += u32::from(u16::from_le_bytes(skip_part)) + 2;
        self.remaining_items -= 1;
        Some(Policy {
            identity_provider,
            created_at,
            valid_to,
            items: AttributesCursor {
                current_position: attributes_start,
                remaining_items,
            },
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.remaining_items as usize;
        (rem, Some(rem))
    }
}

impl ExactSizeIterator for PoliciesIterator {
    #[inline(always)]
    fn len(&self) -> usize { self.remaining_items as usize }
}

/// Context backed by host functions.
#[derive(Default)]
#[doc(hidden)]
pub struct ExternContext<T: // sealed::
                         ContextType> {
    marker: std::marker::PhantomData<T>,
}

#[derive(Default)]
#[doc(hidden)]
pub struct InitContextExtern;
#[derive(Default)]
#[doc(hidden)]
pub struct ReceiveContextExtern;

// pub(crate) mod sealed {
//     use super::*;
//     /// Marker trait intended to indicate which context type we have.
//     /// This is deliberately a sealed trait, so that it is only implementable
//     /// by types in this crate.
    pub trait ContextType {}
    impl ContextType for InitContextExtern {}
    impl ContextType for ReceiveContextExtern {}
// }

impl<T: // sealed::
     ContextType> HasCommonData for ExternContext<T> {
    type MetadataType = ChainMetaExtern;
    type ParamType = Parameter;
    type PolicyIteratorType = PoliciesIterator;
    type PolicyType = Policy<AttributesCursor>;

    #[inline(always)]
    fn metadata(&self) -> &Self::MetadataType { &ChainMetaExtern {} }

    fn policies(&self) -> PoliciesIterator {
        let mut buf: MaybeUninit<[u8; 2]> = MaybeUninit::uninit();
        let buf = unsafe {
            get_policy_section(buf.as_mut_ptr() as *mut u8, 2, 0);
            buf.assume_init()
        };
        PoliciesIterator {
            pos:             2, // 2 because we already read 2 bytes.
            remaining_items: u16::from_le_bytes(buf),
        }
    }

    #[inline(always)]
    fn parameter_cursor(&self) -> Self::ParamType {
        Parameter {
            current_position: 0,
        }
    }
}

// Found in concordium-std/srd/prims.rs
extern "C" {
    // Getter for the init context.
    /// Address of the sender, 32 bytes
    pub(crate) fn get_init_origin(start: *mut u8);
}

/// # Trait implementations for the init context
impl HasInitContext for ExternContext<InitContextExtern> {
    type InitData = ();

    /// Create a new init context by using an external call.
    fn open(_: Self::InitData) -> Self { ExternContext::default() }

    #[inline(always)]
    fn init_origin(&self) -> AccountAddress {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            get_init_origin(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }
}

// Found in concordium-std/srd/prims.rs
extern "C" {
    // Getters for the receive context
    /// Invoker of the top-level transaction, AccountAddress.
    pub(crate) fn get_receive_invoker(start: *mut u8);
    /// Address of the contract itself, ContractAddress.
    pub(crate) fn get_receive_self_address(start: *mut u8);
    /// Self-balance of the contract, returns the amount
    pub(crate) fn get_receive_self_balance() -> u64;
    /// Immediate sender of the message (either contract or account).
    pub(crate) fn get_receive_sender(start: *mut u8);
    /// Owner of the contract, AccountAddress.
    pub(crate) fn get_receive_owner(start: *mut u8);
}

/// # Trait implementations for the receive context
impl HasReceiveContext for ExternContext<ReceiveContextExtern> {
    type ReceiveData = ();

    /// Create a new receive context
    fn open(_: Self::ReceiveData) -> Self { ExternContext::default() }

    #[inline(always)]
    fn invoker(&self) -> AccountAddress {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            get_receive_invoker(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }

    #[inline(always)]
    fn self_address(&self) -> ContractAddress {
        let mut bytes: MaybeUninit<[u8; 16]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            get_receive_self_address(ptr as *mut u8);
            bytes.assume_init()
        };
        match from_bytes(&address) {
            Ok(v) => v,
            Err(_) => trap(),
        }
    }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_gtu(unsafe { get_receive_self_balance() })
    }

    #[inline(always)]
    fn sender(&self) -> Address {
        let mut bytes: MaybeUninit<[u8; 33]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr() as *mut u8;
        unsafe {
            get_receive_sender(ptr);
            let tag = *ptr;
            match tag {
                0u8 => {
                    match from_bytes(core::slice::from_raw_parts(ptr.add(1), ACCOUNT_ADDRESS_SIZE))
                    {
                        Ok(v) => Address::Account(v),
                        Err(_) => trap(),
                    }
                }
                1u8 => match from_bytes(core::slice::from_raw_parts(ptr.add(1), 16)) {
                    Ok(v) => Address::Contract(v),
                    Err(_) => trap(),
                },
                _ => trap(), // unreachable!("Host violated precondition."),
            }
        }
    }

    #[inline(always)]
    fn owner(&self) -> AccountAddress {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            get_receive_owner(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }
}

/// A type representing the logger.
#[derive(Default)]
pub struct Logger {
    pub(crate) _private: (),
}

// Found in concordium-std/srd/prims.rs
extern "C" {
    // Add a log item. Return values are
    // - -1 if logging failed due to the message being too long
    // - 0 if the log is already full
    // - 1 if data was successfully logged.
    pub(crate) fn log_event(start: *const u8, length: u32) -> i32;
}

/// #Implementations of the logger.

impl HasLogger for Logger {
    #[inline(always)]
    fn init() -> Self {
        Self {
            _private: (),
        }
    }

    fn log_raw(&mut self, event: &[u8]) -> Result<(), concordium_std::LogError> {
        let res = unsafe { log_event(event.as_ptr(), event.len() as u32) };
        match res {
            1 => Ok(()),
            0 => Err(concordium_std::LogError::Full),
            _ => Err(concordium_std::LogError::Malformed),
        }
    }
}

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

impl Action {
    pub fn tag(&self) -> u32 { self._private }
}

extern "C" {
    pub(crate) fn accept() -> u32;
    // Basic action to send tokens to an account.
    pub(crate) fn simple_transfer(addr_bytes: *const u8, amount: u64) -> u32;
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
    // Combine two actions using normal sequencing. This is using the stack of
    // actions already produced.
    pub(crate) fn combine_and(l: u32, r: u32) -> u32;
    // Combine two actions using or. This is using the stack of actions already
    // produced.
    pub(crate) fn combine_or(l: u32, r: u32) -> u32;
}

/// #Implementation of actions.
/// These actions are implemented by direct calls to host functions.
impl HasActions for Action {
    #[inline(always)]
    fn accept() -> Self {
        Action {
            _private: unsafe { accept() },
        }
    }

    #[inline(always)]
    fn simple_transfer(acc: &AccountAddress, amount: Amount) -> Self {
        let res = unsafe { simple_transfer(acc.0.as_ptr(), amount.micro_gtu) };
        Action {
            _private: res,
        }
    }

    #[inline(always)]
    fn send_raw(
        ca: &ContractAddress,
        receive_name: ReceiveName,
        amount: Amount,
        parameter: &[u8],
    ) -> Self {
        let receive_bytes = receive_name.get_chain_name().as_bytes();
        let res = unsafe {
            send(
                ca.index,
                ca.subindex,
                receive_bytes.as_ptr(),
                receive_bytes.len() as u32,
                amount.micro_gtu,
                parameter.as_ptr(),
                parameter.len() as u32,
            )
        };
        Action {
            _private: res,
        }
    }

    #[inline(always)]
    fn and_then(self, then: Self) -> Self {
        let res = unsafe { combine_and(self._private, then._private) };
        Action {
            _private: res,
        }
    }

    #[inline(always)]
    fn or_else(self, el: Self) -> Self {
        let res = unsafe { combine_or(self._private, el._private) };
        Action {
            _private: res,
        }
    }
}

/// Allocates a Vec of bytes prepended with its length as a `u32` into memory,
/// and prevents them from being dropped. Returns the pointer.
/// Used to pass bytes from a Wasm module to its host.
#[doc(hidden)]
pub fn put_in_memory(input: &[u8]) -> *mut u8 {
    let bytes_length = input.len() as u32;
    let mut bytes = to_bytes(&bytes_length);
    bytes.extend_from_slice(input);
    let ptr = bytes.as_mut_ptr();
    #[cfg(feature = "std")]
    ::std::mem::forget(bytes);
    #[cfg(not(feature = "std"))]
    core::mem::forget(bytes);
    ptr
}

/// Wrapper for
/// [HasActions::send_raw](./trait.HasActions.html#tymethod.send_raw), which
/// automatically serializes the parameter. Note that if the parameter is
/// already a byte array or convertible to a byte array without allocations it
/// is preferrable to use [send_raw](./trait.HasActions.html#tymethod.send_raw).
/// It is more efficient and avoids memory allocations.
pub fn wrapper_send<A: HasActions, P: Serial>(
    ca: &ContractAddress,
    receive_name: ReceiveName,
    amount: Amount,
    parameter: &P,
) -> A {
    let param_bytes = to_bytes(parameter);
    A::send_raw(ca, receive_name, amount, &param_bytes)
}

// impl<A, E> UnwrapAbort for Result<A, E> {
//     type Unwrap = A;

//     #[inline]
//     fn unwrap_abort(self) -> Self::Unwrap {
//         match self {
//             Ok(x) => x,
//             Err(_) => trap(),
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

