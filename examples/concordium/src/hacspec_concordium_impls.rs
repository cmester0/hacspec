#[cfg(not(feature = "hacspec"))]
use crate::{
    collections::{BTreeMap, BTreeSet},
    convert::{self, TryFrom, TryInto},
    hash::Hash,
    num::NonZeroI32,
    vec::Vec,
    String,
    trap,
};

#[cfg(not(feature = "hacspec"))]
use concordium_contracts_common::*;

#[cfg(not(feature = "hacspec"))]
use crate::*;

#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

use hacspec_lib::*;

// #[cfg(feature = "hacspec_attributes")]
#[cfg(feature = "hacspec")]
use hacspec_attributes::*;

// Creusot
#[cfg(not(feature = "hacspec"))]
extern crate creusot_contracts;
#[cfg(not(feature = "hacspec"))]
use creusot_contracts::{
    ensures,
    requires,
    trusted          
    };

pub type RejectHacspec = i32;

pub fn reject_impl_deafult() -> RejectHacspec {
    i32::MIN
}

pub fn new_reject_impl(x: i32) -> Option::<i32> { // Option<RejectHacspec>
    // TODO: fix 'identifier is not a constant' error (Seems to be fixed by some import?)
    if x < 0i32 {
        Option::<i32>::Some(x)
    } else {
        Option::<i32>::None
    }
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_reject(hacspec_reject: RejectHacspec) -> Reject {
    Reject {
        error_code: unsafe { NonZeroI32::new_unchecked(hacspec_reject) },
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

pub type ContractStateHacspec = u32;

#[derive(Copy, Clone)] // , Debug, PartialEq, Eq
pub enum SeekFromHacspec {
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
pub fn contract_state_impl_seek(current_position: ContractStateHacspec, pos: SeekFromHacspec) -> Result<(ContractStateHacspec, u64), ()> {
    match pos {
        SeekFromHacspec::Start(offset) => Result::<(ContractStateHacspec, u64), ()>::Ok((offset as u32, offset)),
        SeekFromHacspec::End(delta) => {
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
        SeekFromHacspec::Current(delta) => {
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
pub fn coerce_rust_to_hacspec_seek_from(rust_seek_from: SeekFrom) -> SeekFromHacspec {
    match rust_seek_from {
        SeekFrom::Start(v) => SeekFromHacspec::Start(v),
        SeekFrom::End(v) => SeekFromHacspec::End(v),
        SeekFrom::Current(v) => SeekFromHacspec::Current(v),
    }
}

#[cfg(not(feature = "hacspec"))]
/// # Contract state trait implementations.
impl Seek for ContractState {
    type Err = ();

    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Err> {
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

// TODO: Make creusot friendly version
#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_public_byte_seq(buf: PublicByteSeq) -> Vec<u8> {
    // buf.native_slice().iter().collect();
    let mut temp_vec: Vec<u8> = Vec::new();
    for i in 0..buf.len() {
        temp_vec.push(buf.index(i).clone())
    }
    temp_vec
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
/// # Trait implementations for the chain metadata.
impl HasChainMetadata for ChainMetaExtern {
    #[inline(always)]
    fn slot_time(&self) -> SlotTime {
        Timestamp::from_timestamp_millis(get_slot_time_hacspec() )
    }
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
    (
        rust_attributes_cursor.current_position.clone(),
        rust_attributes_cursor.remaining_items.clone(),
    )
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
#[derive(Clone)] // TODO: Creusot issue readd "Debug" attribute
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

// TODO: Creusot issues?
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
            coerce_rust_to_hacspec_public_byte_seq(&mut buf[..]),
        )?;
        coerce_hacspec_to_rust_attributes_cursor(&mut self.items, ac);
        Some((AttributeTag(at), v))
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

// TODO: Fix creusot issues?
fn iterator_impl_for_policies_iterator_next(
    policies_iterator: PoliciesIteratorHacspec,
) -> Option<(PoliciesIteratorHacspec, PolicyAttributesCursorHacspec)> {
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
    Option::<(PoliciesIteratorHacspec, PolicyAttributesCursorHacspec)>::Some((
        (pos, remaining_items),
        (
            identity_provider,
            created_at,
            valid_to,
            (attributes_start, remaining_items),
        ),
    ))
}

// TODO: Fix creusot issues?
#[cfg(not(feature = "hacspec"))]
impl Iterator for PoliciesIterator {
    type Item = Policy<AttributesCursor>;

    fn next(&mut self) -> Option<Self::Item> {
        let ((pos, remaining_items), (identity_provider, created_at, valid_to, (cp, ri))) =
            iterator_impl_for_policies_iterator_next((self.pos, self.remaining_items))?;

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
        self.remaining_items.into() // as usize
    }
}

#[cfg(not(feature = "hacspec"))]
impl<T: sealed::ContextType> HasCommonData for ExternContext<T> {
    type MetadataType = ChainMetaExtern;
    type ParamType = Parameter;
    type PolicyIteratorType = PoliciesIterator;
    type PolicyType = Policy<AttributesCursor>;

    // TODO: fix creusot issue
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
        let mut address : [u8; ACCOUNT_ADDRESS_SIZE] = Default::default();
        let temp = coerce_hacspec_to_rust_public_byte_seq(get_init_origin_hacspec(
            PublicByteSeq::new(ACCOUNT_ADDRESS_SIZE),
        ));
        address.clone_from_slice(temp.as_slice());
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

    // TODO: Make usable by creusot
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

    // TODO: Make usable by creusot
    #[inline(always)]
    fn self_address(&self) -> ContractAddress {
        let mut address: [u8; ACCOUNT_ADDRESS_SIZE] = Default::default();
        address.clone_from_slice(
            &mut coerce_hacspec_to_rust_public_byte_seq(get_receive_self_address_hacspec(
                PublicByteSeq::new(ACCOUNT_ADDRESS_SIZE),
            ))[..],
        );
        match concordium_contracts_common::from_bytes(&address) {
            Ok(v) => v,
            Err(_) => trap(),
        }
    }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_gtu(get_receive_self_balance_hacspec())
    }

    // TODO: Make usable by creusot
    // TODO: Remove/replace unsafe code !
    #[inline(always)]
    fn sender(&self) -> Address {
        let ptr : *mut u8 = (&mut coerce_hacspec_to_rust_public_byte_seq(get_receive_sender_hacspec(
            PublicByteSeq::new(ACCOUNT_ADDRESS_SIZE),
        ))[..]).as_mut_ptr();
        let tag = unsafe { *ptr };
        match tag {
            0u8 => {
                match concordium_contracts_common::from_bytes(unsafe { core::slice::from_raw_parts(
                    ptr.add(1),
                    ACCOUNT_ADDRESS_SIZE,
                )} ) {
                    Ok(v) => Address::Account(v),
                    Err(_) => trap(),
                }
            }
            1u8 => match concordium_contracts_common::from_bytes(unsafe { core::slice::from_raw_parts(ptr.add(1), 16) }) {
                Ok(v) => Address::Contract(v),
                Err(_) => trap(),
            },
            _ => trap(), // unreachable!("Host violated precondition."),
        }
    }

    // TODO: Make usable by creusot
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

// #[cfg(not(feature = "hacspec"))]
// /// A type representing the logger.
// #[derive(Default)]
// pub struct Logger {
//     pub(crate) _private: (),
// }

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
    let mut bytes = concordium_contracts_common::to_bytes(&bytes_length);
    bytes.extend_from_slice(input);
    let ptr = bytes.as_mut_ptr();
    #[cfg(feature = "std")]
    ::std::mem::forget(bytes);
    #[cfg(not(feature = "std"))]
    core::mem::forget(bytes);
    ptr
}

// TODO: Name collision
#[cfg(not(feature = "hacspec"))]
/// Wrapper for
/// [HasActions::send_raw](./trait.HasActions.html#tymethod.send_raw), which
/// automatically serializes the parameter. Note that if the parameter is
/// already a byte array or convertible to a byte array without allocations it
/// is preferrable to use [send_raw](./trait.HasActions.html#tymethod.send_raw).
/// It is more efficient and avoids memory allocations.
pub fn send<A: HasActions, P: Serial>(
    ca: &ContractAddress,
    receive_name: ReceiveName,
    amount: Amount,
    parameter: &P,
) -> A {
    let param_bytes = concordium_contracts_common::to_bytes(parameter);
    A::send_raw(ca, receive_name, amount, &param_bytes)
}

#[cfg(not(feature = "hacspec"))]
impl<A, E> UnwrapAbort for Result<A, E> {
    type Unwrap = A;

    #[inline]
    fn unwrap_abort(self) -> Self::Unwrap {
        match self {
            Ok(x) => x,
            Err(_) => trap(),
        }
    }
}

// TODO:
// #[cfg(not(feature = "hacspec"))]
// #[cfg(not(feature = "std"))]
// use concordium_contracts_common::fmt; // core::fmt;

#[cfg(not(feature = "hacspec"))]
#[cfg(feature = "std")]
use std::fmt;

#[cfg(not(feature = "hacspec"))]
impl<A, E: fmt::Debug> ExpectReport for Result<A, E> {
    type Unwrap = A;

    fn expect_report(self, msg: &str) -> Self::Unwrap {
        match self {
            Ok(x) => x,
            Err(e) => fail!("{}: {:?}", msg, e),
        }
    }
}

// TODO:
#[cfg(not(feature = "hacspec"))]
impl<A: fmt::Debug, E> ExpectErrReport for Result<A, E> {
    type Unwrap = E;

    fn expect_err_report(self, msg: &str) -> Self::Unwrap {
        match self {
            Ok(a) => fail!("{}: {:?}", msg, a),
            Err(e) => e,
        }
    }
}

#[cfg(not(feature = "hacspec"))]
impl<A> UnwrapAbort for Option<A> {
    type Unwrap = A;

    #[inline(always)]
    fn unwrap_abort(self) -> Self::Unwrap {
        self.unwrap_or_else(|| trap())
    }
}

// TODO:
#[cfg(not(feature = "hacspec"))]
impl<A> ExpectReport for Option<A> {
    type Unwrap = A;

    fn expect_report(self, msg: &str) -> Self::Unwrap {
        match self {
            Some(v) => v,
            None => fail!("{}", msg),
        }
    }
}

// TODO:
#[cfg(not(feature = "hacspec"))]
impl<A: fmt::Debug> ExpectNoneReport for Option<A> {
    fn expect_none_report(self, msg: &str) {
        if let Some(x) = self {
            fail!("{}: {:?}", msg, x)
        }
    }
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
        size_len: concordium_contracts_common::schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        concordium_contracts_common::schema::serial_length(self.len(), size_len, out)?;
        // concordium_std::
        serial_set_no_length(self, out)
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
        size_len: concordium_contracts_common::schema::SizeLength,
        ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = concordium_contracts_common::schema::deserial_length(source, size_len)?;
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
        size_len: concordium_contracts_common::schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        concordium_contracts_common::schema::serial_length(self.len(), size_len, out)?;
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
        size_len: concordium_contracts_common::schema::SizeLength,
        ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = concordium_contracts_common::schema::deserial_length(source, size_len)?;
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
        size_len: concordium_contracts_common::schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        concordium_contracts_common::schema::serial_length(self.len(), size_len, out)?;
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
        size_len: concordium_contracts_common::schema::SizeLength,
        _ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = concordium_contracts_common::schema::deserial_length(source, size_len)?;
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
        size_len: concordium_contracts_common::schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        concordium_contracts_common::schema::serial_length(self.len(), size_len, out)?;
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
        size_len: concordium_contracts_common::schema::SizeLength,
        _ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = concordium_contracts_common::schema::deserial_length(source, size_len)?;
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
        size_len: concordium_contracts_common::schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        concordium_contracts_common::schema::serial_length(self.len(), size_len, out)?;
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
        size_len: concordium_contracts_common::schema::SizeLength,
        _ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = concordium_contracts_common::schema::deserial_length(source, size_len)?;
        deserial_vector_no_length(source, len)
    }
}

#[cfg(not(feature = "hacspec"))]
impl SerialCtx for &str {
    fn serial_ctx<W: Write>(
        &self,
        size_len: concordium_contracts_common::schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        concordium_contracts_common::schema::serial_length(self.len(), size_len, out)?;
        serial_vector_no_length(&self.as_bytes().to_vec(), out)
    }
}

#[cfg(not(feature = "hacspec"))]
impl SerialCtx for String {
    fn serial_ctx<W: Write>(
        &self,
        size_len: concordium_contracts_common::schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        self.as_str().serial_ctx(size_len, out)
    }
}

#[cfg(not(feature = "hacspec"))]  
impl DeserialCtx for String {
    fn deserial_ctx<R: Read>(
        size_len: concordium_contracts_common::schema::SizeLength,
        _ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = concordium_contracts_common::schema::deserial_length(source, size_len)?;
        let bytes = deserial_vector_no_length(source, len)?;
        let res = String::from_utf8(bytes).map_err(|_| ParseError::default())?;
        Ok(res)
    }
}


