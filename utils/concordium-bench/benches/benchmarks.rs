#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

use concordium_std::{collections::BTreeMap, *};
// use concordium_provider::provider::*;
use concordium_provider::piggy_provider::*;
use concordium_provider::auction_provider::*;
use std::convert::TryInto;

#[macro_use]
use pearlite_syn::*;

extern crate creusot_contracts;
use creusot_contracts::*;

////////////////////////////////////////////////////////////
 
#[derive(Default, Clone)]
pub struct ChainMetaTest {
    pub(crate) slot_time: Option<SlotTime>,
}

/// Policy type used by init and receive contexts for testing.
/// This type should not be used directly, but rather through
/// its `HasPolicy` interface.
#[derive(Debug, Clone)]
pub struct TestPolicy {
    /// Current position in the vector of policies. Used to implement
    /// `next_item`.
    position: usize,
    policy:   OwnedPolicy,
}

impl TestPolicy {
    fn new(policy: OwnedPolicy) -> Self {
        Self {
            position: 0,
            policy,
        }
    }
}

#[derive(Default, Clone)]
#[doc(hidden)]
pub struct CommonDataTest<'a> {
    pub(crate) metadata:  ChainMetaTest,
    pub(crate) parameter: Option<&'a [u8]>,
    pub(crate) policies:  Option<Vec<TestPolicy>>,
}

#[derive(Default, Clone)]
pub struct ContextTest<'a, C> {
    pub(crate) common: CommonDataTest<'a>,
    pub(crate) custom: C,
}

pub type InitContextTest<'a> = ContextTest<'a, InitOnlyDataTest>;

#[derive(Default)]
#[doc(hidden)]
pub struct InitOnlyDataTest {
    init_origin: Option<AccountAddress>,
}

pub type ReceiveContextTest<'a> = ContextTest<'a, ReceiveOnlyDataTest>;

#[derive(Default)]
#[doc(hidden)]
pub struct ReceiveOnlyDataTest {
    pub(crate) invoker:      Option<AccountAddress>,
    pub(crate) self_address: Option<ContractAddress>,
    pub(crate) self_balance: Option<Amount>,
    pub(crate) sender:       Option<Address>,
    pub(crate) owner:        Option<AccountAddress>,
}

// Setters for testing-context
impl ChainMetaTest {
    /// Create an `ChainMetaTest` where every field is unset, and getting any of
    /// the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    /// Set the block slot time
    pub fn set_slot_time(&mut self, value: SlotTime) -> &mut Self {
        self.slot_time = Some(value);
        self
    }
}

impl<'a, C> ContextTest<'a, C> {
    /// Push a new sender policy to the context.
    /// When the first policy is pushed this will set the policy vector
    /// to 'Some', even if it was undefined previously.
    pub fn push_policy(&mut self, value: OwnedPolicy) -> &mut Self {
        if let Some(policies) = self.common.policies.as_mut() {
            policies.push(TestPolicy::new(value));
        } else {
            self.common.policies = Some(vec![TestPolicy::new(value)])
        }
        self
    }

    /// Set the policies to be defined, but an empty list.
    /// Such a situation can not realistically happen on the chain,
    /// but we provide functionality for it in case smart contract
    /// writers wish to program defensively.
    pub fn empty_policies(&mut self) -> &mut Self {
        self.common.policies = Some(Vec::new());
        self
    }

    pub fn set_parameter(&mut self, value: &'a [u8]) -> &mut Self {
        self.common.parameter = Some(value);
        self
    }

    /// Get a mutable reference to the chain meta data placeholder
    pub fn metadata_mut(&mut self) -> &mut ChainMetaTest { &mut self.common.metadata }

    /// Set the metadata block slot time
    pub fn set_metadata_slot_time(&mut self, value: SlotTime) -> &mut Self {
        self.metadata_mut().set_slot_time(value);
        self
    }
}

impl<'a> InitContextTest<'a> {
    /// Create an `InitContextTest` where every field is unset, and getting any
    /// of the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    /// Set `init_origin` in the `InitContextTest`
    pub fn set_init_origin(&mut self, value: AccountAddress) -> &mut Self {
        self.custom.init_origin = Some(value);
        self
    }
}

impl<'a> ReceiveContextTest<'a> {
    /// Create a `ReceiveContextTest` where every field is unset, and getting
    /// any of the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    pub fn set_invoker(&mut self, value: AccountAddress) -> &mut Self {
        self.custom.invoker = Some(value);
        self
    }

    pub fn set_self_address(&mut self, value: ContractAddress) -> &mut Self {
        self.custom.self_address = Some(value);
        self
    }

    pub fn set_self_balance(&mut self, value: Amount) -> &mut Self {
        self.custom.self_balance = Some(value);
        self
    }

    pub fn set_sender(&mut self, value: Address) -> &mut Self {
        self.custom.sender = Some(value);
        self
    }

    pub fn set_owner(&mut self, value: AccountAddress) -> &mut Self {
        self.custom.owner = Some(value);
        self
    }
}

// Error handling when unwrapping
fn unwrap_ctx_field<A>(opt: Option<A>, name: &str) -> A {
    match opt {
        Some(v) => v,
        None => fail!(
            "Unset field on test context '{}', make sure to set all the field necessary for the \
             contract",
            name
        ),
    }
}

impl<'a> HasReceiveContext for ReceiveContextTest<'a> {
    type ReceiveData = ();

    fn open(_data: Self::ReceiveData) -> Self { ReceiveContextTest::default() }

    fn invoker(&self) -> AccountAddress { unwrap_ctx_field(self.custom.invoker, "invoker") }

    fn self_address(&self) -> ContractAddress {
        unwrap_ctx_field(self.custom.self_address, "self_address")
    }

    fn self_balance(&self) -> Amount { unwrap_ctx_field(self.custom.self_balance, "self_balance") }

    fn sender(&self) -> Address { unwrap_ctx_field(self.custom.sender, "sender") }

    fn owner(&self) -> AccountAddress { unwrap_ctx_field(self.custom.owner, "owner") }
}

/// An actions tree, used to provide a simpler presentation for testing.
#[derive(Eq, PartialEq, Debug)]
pub enum ActionsTree {
    Accept,
    SimpleTransfer {
        to:     AccountAddress,
        amount: Amount,
    },
    Send {
        to:           ContractAddress,
        receive_name: OwnedReceiveName,
        amount:       Amount,
        parameter:    Vec<u8>,
    },
    AndThen {
        left:  Box<ActionsTree>,
        right: Box<ActionsTree>,
    },
    OrElse {
        left:  Box<ActionsTree>,
        right: Box<ActionsTree>,
    },
}

impl<'a, C> HasCommonData for ContextTest<'a, C> {
    type MetadataType = ChainMetaTest;
    type ParamType = Cursor<&'a [u8]>;
    type PolicyIteratorType = std::vec::IntoIter<TestPolicy>;
    type PolicyType = TestPolicy;

    fn parameter_cursor(&self) -> Self::ParamType {
        Cursor::new(unwrap_ctx_field(self.common.parameter, "parameter"))
    }

    fn metadata(&self) -> &Self::MetadataType { &self.common.metadata }

    fn policies(&self) -> Self::PolicyIteratorType {
        unwrap_ctx_field(self.common.policies.clone(), "policies").into_iter()
    }
}

impl HasPolicy for TestPolicy {
    fn identity_provider(&self) -> IdentityProvider { self.policy.identity_provider }

    fn created_at(&self) -> Timestamp { self.policy.created_at }

    fn valid_to(&self) -> Timestamp { self.policy.valid_to }

    fn next_item(&mut self, buf: &mut [u8; 31]) -> Option<(AttributeTag, u8)> {
        if let Some(item) = self.policy.items.get(self.position) {
            let len = item.1.len();
            buf[0..len].copy_from_slice(&item.1);
            self.position += 1;
            Some((item.0, len as u8))
        } else {
            None
        }
    }
}

// Getters for testing-context
impl HasChainMetadata for ChainMetaTest {
    fn slot_time(&self) -> SlotTime { unwrap_ctx_field(self.slot_time, "metadata.slot_time") }
}

impl HasActions for ActionsTree {
    fn accept() -> Self { ActionsTree::Accept }

    fn simple_transfer(acc: &AccountAddress, amount: Amount) -> Self {
        ActionsTree::SimpleTransfer {
            to: *acc,
            amount,
        }
    }

    fn send_raw(
        ca: &ContractAddress,
        receive_name: ReceiveName,
        amount: Amount,
        parameter: &[u8],
    ) -> Self {
        ActionsTree::Send {
            to: *ca,
            receive_name: receive_name.to_owned(),
            amount,
            parameter: parameter.to_vec(),
        }
    }

    fn and_then(self, then: Self) -> Self {
        ActionsTree::AndThen {
            left:  Box::new(self),
            right: Box::new(then),
        }
    }

    fn or_else(self, el: Self) -> Self {
        ActionsTree::OrElse {
            left:  Box::new(self),
            right: Box::new(el),
        }
    }
}

impl<'a> HasInitContext for InitContextTest<'a> {
    type InitData = ();

    fn open(_data: Self::InitData) -> Self { InitContextTest::default() }

    fn init_origin(&self) -> AccountAddress {
        unwrap_ctx_field(self.custom.init_origin, "init_origin")
    }
}

/// Contract state for testing, mimicking the operations the scheduler allows,
/// including the limit on the size of the maximum size of the contract state.
pub struct ContractStateTest<T> {
    pub cursor: Cursor<T>,
}

/// A borrowed instantiation of `ContractStateTest`.
pub type ContractStateTestBorrowed<'a> = ContractStateTest<&'a mut Vec<u8>>;

/// An owned variant that can be more convenient for testing since the type
/// itself owns the data.
pub type ContractStateTestOwned = ContractStateTest<Vec<u8>>;

#[derive(Debug, PartialEq, Eq)]
/// An error that is raised when operating with `Seek`, `Write`, or `Read` trait
/// methods of the `ContractStateTest` type.
pub enum ContractStateError {
    /// The computation of the new offset would result in an overflow.
    Overflow,
    /// An error occurred when writing to the contract state.
    Write,
    /// The new offset would be out of bounds of the state.
    Offset,
    /// Some other error occurred.
    Default,
}

// impl<T: AsRef<[u8]>> Seek for ContractStateTest<T> {
//     type Err = TryFromIntError; // ContractStateError;

//     fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Err> {
//         use ContractStateError::*;
//         match pos {
//             SeekFrom::Start(x) => {
//                 // We can set the position to just after the end of the current length.
//                 let new_offset = x.try_into()?;
//                 if new_offset <= self.cursor.data.as_ref().len() {
//                     self.cursor.offset = new_offset;
//                     Ok(x)
//                 } else {
//                     Err(Offset)
//                 }
//             }
//             SeekFrom::End(x) => {
//                 // cannot seek beyond end, nor before beginning
//                 if x <= 0 {
//                     let end: u32 = self.cursor.data.as_ref().len().try_into()?;
//                     let minus_x = x.checked_abs().ok_or(Overflow)?;
//                     if let Some(new_pos) = end.checked_sub(minus_x.try_into()?) {
//                         self.cursor.offset = new_pos.try_into()?;
//                         Ok(u64::from(new_pos))
//                     } else {
//                         Err(Offset)
//                     }
//                 } else {
//                     Err(Offset)
//                 }
//             }
//             SeekFrom::Current(x) => match x {
//                 0 => Ok(self.cursor.offset.try_into()?),
//                 x if x > 0 => {
//                     let x = x.try_into()?;
//                     let new_pos = self.cursor.offset.checked_add(x).ok_or(Overflow)?;
//                     if new_pos <= self.cursor.data.as_ref().len() {
//                         self.cursor.offset = new_pos;
//                         new_pos.try_into().map_err(Self::Err::from)
//                     } else {
//                         Err(Offset)
//                     }
//                 }
//                 x => {
//                     let x = (-x).try_into()?;
//                     let new_pos = self.cursor.offset.checked_sub(x).ok_or(Overflow)?;
//                     self.cursor.offset = new_pos;
//                     new_pos.try_into().map_err(Self::Err::from)
//                 }
//             },
//         }
//     }
// }



////////////////////////////////////////////////////////////

// #[ensures(result == false)]
fn test_init() -> bool {
    // Setup
    let ctx = InitContextTest::empty();

    // Call the init function
    let state_result = piggy_init(&ctx);

    // Inspect the result
    let state = state_result.expect_report("Contract initialization failed.");

    claim_eq!(
        state,
        PiggyBankState::Intact,
        "Piggy bank state should be intact after initialization."
    );

    state == PiggyBankState::Intact
}
    
fn test_insert_intact() {
    // Setup
    let mut ctx = ReceiveContextTest::empty();

    let owner = AccountAddress([0u8; 32]);
    ctx.set_owner(owner);
    let sender = Address::Account(owner);
    ctx.set_sender(sender);
    let balance = Amount::from_micro_gtu(100);
    ctx.set_self_balance(balance);
    
    let amount = Amount::from_micro_gtu(100);
    let mut state = PiggyBankState::Intact;
    
    // Trigger the insert
    let actions_result: ReceiveResult<ActionsTree> = piggy_insert(&ctx, amount, &mut state);
    
    // Inspect the result
    let actions = actions_result.expect_report("Inserting GTU results in error.");
    
    claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");
    claim_eq!(state, PiggyBankState::Intact, "Piggy bank state should still be intact.");
}

fn test_insert_smashed() {
    // Setup
    let mut ctx = ReceiveContextTest::empty();

    let owner = AccountAddress([0u8; 32]);
    ctx.set_owner(owner);
    let sender = Address::Account(owner);
    ctx.set_sender(sender);
    let balance = Amount::from_micro_gtu(100);
    ctx.set_self_balance(balance);
    
    let amount = Amount::from_micro_gtu(100);
    let mut state = PiggyBankState::Smashed;

    // Trigger the insert
    let actions_result: ReceiveResult<ActionsTree> = piggy_insert(&ctx, amount, &mut state);

    // Inspect the result
    claim!(actions_result.is_err(), "Should failed when piggy bank is smashed.");
}

fn test_smash_intact() {
    // Setup the context

    let mut ctx = ReceiveContextTest::empty();
    let owner = AccountAddress([0u8; 32]);
    ctx.set_owner(owner);
    let sender = Address::Account(owner);
    ctx.set_sender(sender);
    let balance = Amount::from_micro_gtu(100);
    ctx.set_self_balance(balance);

    let mut state = PiggyBankState::Intact;

    // Trigger the smash
    let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

    // Inspect the result
    let actions = actions_result.expect_report("Inserting GTU results in error.");
    claim_eq!(actions, ActionsTree::simple_transfer(&owner, balance));
    claim_eq!(state, PiggyBankState::Smashed);
}

fn test_smash_intact_not_owner() {
    // Setup the context

    let mut ctx = ReceiveContextTest::empty();
    let owner = AccountAddress([0u8; 32]);
    ctx.set_owner(owner);
    let sender = Address::Account(AccountAddress([1u8; 32]));
    ctx.set_sender(sender);
    let balance = Amount::from_micro_gtu(100);
    ctx.set_self_balance(balance);

    let mut state = PiggyBankState::Intact;

    // Trigger the smash
    let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

    let err = actions_result.expect_err_report("Contract is expected to fail.");
    claim_eq!(err, Reject {error_code: unsafe { std::num::NonZeroI32::new_unchecked(4) }}, "Expected to fail with error NotOwner") // SmashError::NotOwner // TODO: ??
}

fn test_smash_smashed() {
    // Setup the context
    let mut ctx = ReceiveContextTest::empty();
    let owner = AccountAddress([0u8; 32]);
    ctx.set_owner(owner);
    let sender = Address::Account(owner);
    ctx.set_sender(sender);
    let balance = Amount::from_micro_gtu(100);
    ctx.set_self_balance(balance);

    let mut state = PiggyBankState::Smashed;

    // Trigger the smash
    let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

    let err = actions_result.expect_err_report("Contract is expected to fail.");
    claim_eq!(err, Reject {error_code: unsafe { std::num::NonZeroI32::new_unchecked(5) }}, "Expected  to fail with error AlreadySmashed") // TODO: ??
}


use std::sync::atomic::{AtomicU8, Ordering};
use core::fmt::Debug;

// // A counter for generating new account addresses
static ADDRESS_COUNTER: AtomicU8 = AtomicU8::new(0);
const AUCTION_END: u64 = 1;
const ITEM: &str = "Starry night by Van Gogh";

// fn dummy_fresh_state() -> State { dummy_active_state(Amount::zero(), BTreeMap::new()) }

// fn dummy_active_state(highest: Amount, bids: BTreeMap<AccountAddress, Amount>) -> State {
//     // State {
//     //     auction_state: my_auction_state_to_their_auction_state(a),
//     //     highest_bid: Amount { micro_gtu: b },
//     //     item: c.native_slice().to_vec(),
//     //     expiry: Timestamp::from_timestamp_millis(d),
//     //     bids: seq_map_to_btree_map(e),
//     // }
    
//     State {
//         auction_state: AuctionState::NotSoldYet,
//         highest_bid: highest,
//         item: ITEM.as_bytes().to_vec(),
//         expiry: Timestamp::from_timestamp_millis(AUCTION_END),
//         bids: bids,
//     }
// }

fn expect_error<E, T>(expr: Result<T, E>, err: E, msg: &str)
where
    E: Eq + Debug,
    T: Debug, {
    let actual = expr.expect_err(msg);
    assert_eq!(actual, err);
}

fn create_parameter_bytes(parameter: &InitParameter) -> Vec<u8> { to_bytes(parameter) }

fn parametrized_init_ctx<'a>(parameter_bytes: &'a Vec<u8>) -> InitContextTest<'a> {
    let mut ctx = InitContextTest::empty();
    ctx.set_parameter(parameter_bytes);
    ctx
}

fn new_account() -> AccountAddress {
    let account = AccountAddress([ADDRESS_COUNTER.load(Ordering::SeqCst); 32]);
    ADDRESS_COUNTER.fetch_add(1, Ordering::SeqCst);
    account
}

fn new_account_ctx<'a>() -> (AccountAddress, ReceiveContextTest<'a>) {
    let account = new_account();
    let ctx = new_ctx(account, account, AUCTION_END);
    (account, ctx)
}

fn new_ctx<'a>(
    owner: AccountAddress,
    sender: AccountAddress,
    slot_time: u64,
) -> ReceiveContextTest<'a> {
    let mut ctx = ReceiveContextTest::empty();
    ctx.set_sender(Address::Account(sender));
    ctx.set_owner(owner);
    ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(slot_time));
    ctx
}

// #[test]
/// Test that the smart-contract initialization sets the state correctly
/// (no bids, active state, indicated auction-end time and item name).
pub fn auction_test_init() {
    let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
    let ctx = parametrized_init_ctx(&parameter_bytes);

    let state_result = auction_init(&ctx);
    let state = state_result.expect("Contract initialization results in error");
    assert_eq!(state, dummy_fresh_state(), "Auction state should be new after initialization");
}


fn verify_bid(
    mut state: &mut State,
    account: AccountAddress,
    ctx: &ContextTest<ReceiveOnlyDataTest>,
    amount: Amount,
    bid_map: &mut BTreeMap<AccountAddress, Amount>,
    highest_bid: Amount,
) {
    let res: Result<ActionsTree, _> = auction_bid(ctx, amount, &mut state);
    res.expect("Bidding should pass");
    bid_map.insert(account, highest_bid);
    assert_eq!(*state, dummy_active_state(highest_bid, bid_map.clone()));
}


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
fn test_auction_bid_and_finalize() {
    let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
    let ctx0 = parametrized_init_ctx(&parameter_bytes);

    let amount = Amount::from_micro_gtu(100);
    let winning_amount = Amount::from_micro_gtu(300);
    let big_amount = Amount::from_micro_gtu(500);

    let mut bid_map = BTreeMap::new();

    // initializing auction
    let mut state = auction_init(&ctx0).expect("Initialization should pass");
    
    // 1st bid: account1 bids amount1
    let (alice, mut alice_ctx) = new_account_ctx();

    let balance = Amount::from_micro_gtu(100);
    alice_ctx.set_self_balance(balance);
    
    verify_bid(&mut state, alice, &alice_ctx, amount, &mut bid_map, amount);
    
    // 2nd bid: account1 bids `amount` again
    // should work even though it's the same amount because account1 simply
    // increases their bid
    verify_bid(&mut state, alice, &alice_ctx, amount, &mut bid_map, amount + amount);
    
    // 3rd bid: second account
    let (bob, mut bob_ctx) = new_account_ctx();

    bob_ctx.set_self_balance(balance);
    
    verify_bid(&mut state, bob, &bob_ctx, winning_amount, &mut bid_map, winning_amount);
    
    // trying to finalize auction that is still active
    // (specifically, the bid is submitted at the last moment, at the AUCTION_END
    // time)
    let mut ctx4 = ReceiveContextTest::empty();

    let owner = AccountAddress([0u8; 32]);
    ctx4.set_owner(owner);
    let sender = Address::Account(owner);
    ctx4.set_sender(sender);
    let balance = Amount::from_micro_gtu(100);
    ctx4.set_self_balance(balance);
    
    ctx4.set_metadata_slot_time(Timestamp::from_timestamp_millis(AUCTION_END));
    let finres: Result<ActionsTree, _> = auction_finalize(&ctx4, &mut state);
    expect_error(
        finres,
        FinalizeError::AuctionStillActive,
        "Finalizing auction should fail when it's before auction-end time",
    );

    // finalizing auction
    let carol = new_account();
    let dave = new_account();
    let mut ctx5 = new_ctx(carol, dave, AUCTION_END + 1);

    ctx5.set_self_balance(winning_amount);
    let finres2: Result<ActionsTree, _> = auction_finalize(&ctx5, &mut state);
    let actions = finres2.expect("Finalizing auction should work");
    assert_eq!(
        actions,
        ActionsTree::simple_transfer(&carol, winning_amount)
            .and_then(ActionsTree::simple_transfer(&alice, amount + amount))
    );
    assert_eq!(state, make_state (
        AuctionState::Sold(bob),
        winning_amount,
        ITEM.as_bytes().to_vec(),
        Timestamp::from_timestamp_millis(AUCTION_END),
        bid_map,
    ));

    // attempting to finalize auction again should fail
    let finres3: Result<ActionsTree, _> = auction_finalize(&ctx5, &mut state);
    expect_error(
        finres3,
        FinalizeError::AuctionFinalized,
        "Finalizing auction a second time should fail",
    );

    // attempting to bid again should fail
    let res4: Result<ActionsTree, _> = auction_bid(&bob_ctx, big_amount, &mut state);
    expect_error(
        res4,
        BidError::AuctionFinalized,
        "Bidding should fail because the auction is finalized",
    );
}

// #[test]
/// Bids for amounts lower or equal to the highest bid should be rejected.
fn test_auction_bid_repeated_bid() {
    let (account1, ctx1) = new_account_ctx();
    let ctx2 = new_account_ctx().1;

    let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
    let ctx0 = parametrized_init_ctx(&parameter_bytes);

    let amount = Amount::from_micro_gtu(100);

    let mut bid_map = BTreeMap::new();

    // initializing auction
    let mut state = auction_init(&ctx0).expect("Init results in error");

    // 1st bid: account1 bids amount1
    verify_bid(&mut state, account1, &ctx1, amount, &mut bid_map, amount);

    // 2nd bid: account2 bids amount1
    // should fail because amount is equal to highest bid
    let res2: Result<ActionsTree, _> = auction_bid(&ctx2, amount, &mut state);
    expect_error(
        res2,
        BidError::BidTooLow, /* { bid: amount, highest_bid: amount } */
        "Bidding 2 should fail because bid amount must be higher than highest bid",
    );
}

// #[test]
/// Bids for 0 GTU should be rejected.
fn test_auction_bid_zero() {
    let ctx1 = new_account_ctx().1;
    let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
    let ctx = parametrized_init_ctx(&parameter_bytes);

    let mut state = auction_init(&ctx).expect("Init results in error");

    let res: Result<ActionsTree, _> = auction_bid(&ctx1, Amount::zero(), &mut state);
    expect_error(
        res,
        BidError::BidTooLow, /* { bid: Amount::zero(), highest_bid: Amount::zero()} */
        "Bidding zero should fail",
    );
}


// use concordium_contracts_common::{Read, Seek, SeekFrom, Write};
// use concordium_contracts_common::{Read, Seek, SeekFrom, Write};

// use crate::{constants, traits::HasContractState};

// // #[test]
// // Perform a number of operations from Seek, Read, Write and HasContractState
// // classes on the ContractStateTest structure and check that they behave as
// // specified.
// fn test_contract_state() {
//     let data = vec![1; 100];
//     let mut state = ContractStateTest::open(data);
//     assert_eq!(state.seek(SeekFrom::Start(100)), Ok(100), "Seeking to the end failed.");
//     assert_eq!(
//         state.seek(SeekFrom::Current(0)),
//         Ok(100),
//         "Seeking from current position with offset 0 failed."
//     );
//     assert!(
//         state.seek(SeekFrom::Current(1)).is_err(),
//         "Seeking from current position with offset 1 succeeded."
//     );
//     assert_eq!(state.cursor.offset, 100, "Cursor position changed on failed seek.");
//     assert_eq!(
//         state.seek(SeekFrom::Current(-1)),
//         Ok(99),
//         "Seeking from current position backwards with offset 1 failed."
//     );
//     assert!(state.seek(SeekFrom::Current(-100)).is_err(), "Seeking beyond beginning succeeds");
//     assert_eq!(state.seek(SeekFrom::Current(-99)), Ok(0), "Seeking to the beginning fails.");
//     assert_eq!(state.seek(SeekFrom::End(0)), Ok(100), "Seeking from end fails.");
//     assert!(
//         state.seek(SeekFrom::End(1)).is_err(),
//         "Seeking beyond the end succeeds but should fail."
//     );
//     assert_eq!(state.cursor.offset, 100, "Cursor position changed on failed seek.");
//     assert_eq!(
//         state.seek(SeekFrom::End(-20)),
//         Ok(80),
//         "Seeking from end leads to incorrect position."
//     );
//     assert_eq!(state.write(&[0; 21]), Ok(21), "Writing writes an incorrect amount of data.");
//     assert_eq!(state.cursor.offset, 101, "After writing the cursor is at the end.");
//     assert_eq!(state.write(&[0; 21]), Ok(21), "Writing again writes incorrect amount of data.");
//     let mut buf = [0; 30];
//     assert_eq!(state.read(&mut buf), Ok(0), "Reading from the end should read 0 bytes.");
//     assert_eq!(state.seek(SeekFrom::End(-20)), Ok(102));
//     assert_eq!(state.read(&mut buf), Ok(20), "Reading from offset 80 should read 20 bytes.");
//     assert_eq!(&buf[0..20], &state.cursor.data[80..100], "Incorrect data was read.");
//     assert_eq!(
//         state.cursor.offset, 122,
//         "After reading the offset is in the correct position."
//     );
//     assert!(state.reserve(222), "Could not increase state to 222.");
//     assert!(
//         !state.reserve(constants::MAX_CONTRACT_STATE_SIZE + 1),
//         "State should not be resizable beyond max limit."
//     );
//     assert_eq!(state.write(&[2; 100]), Ok(100), "Should have written 100 bytes.");
//     assert_eq!(state.cursor.offset, 222, "After writing the offset should be 200.");
//     state.truncate(50);
//     assert_eq!(state.cursor.offset, 50, "After truncation the state should be 50.");
//     assert!(state.reserve(constants::MAX_CONTRACT_STATE_SIZE), "Could not increase state MAX.");
//     assert_eq!(
//         state.seek(SeekFrom::End(0)),
//         Ok(u64::from(constants::MAX_CONTRACT_STATE_SIZE)),
//         "State should be full now."
//     );
//     assert_eq!(
//         state.write(&[1; 1000]),
//         Ok(0),
//         "Writing at the end after truncation should do nothing."
//     );
//     assert_eq!(
//         state.cursor.data.len(),
//         constants::MAX_CONTRACT_STATE_SIZE as usize,
//         "State size should not increase beyond max."
//     )
// }

// #[cfg(proof)]
// #[test]
// fn test_contract_state_write() {
//     let data = [0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8,0u8];
//     let mut state = ContractStateTest::open(data);
//     let test0 = state.write(&1u64.to_le_bytes()) == Ok(8);
//     // , "Incorrect number of bytes written."
    
//     // assert_eq!(
//     //     state.write(&2u64.to_le_bytes()),
//     //     Ok(8),
//     //     "State should be resized automatically."
//     // );
//     // assert_eq!(state.cursor.offset, 16, "Pos should be at the end.");
//     // assert_eq!(
//     //     state.cursor.data,
//     //     vec![1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
//     //     "Correct data was written."
//     // );
// }

fn main () {
    println!("\n\n\tConcordium benchmark tests\n\n");

    println!("\n\n\tTest Piggybank\n\n");

    println!("test_init");
    test_init();
    println!("test_insert_intact");
    test_insert_intact();
    println!("test_insert_smashed");
    test_insert_smashed();
    println!("test_smash_intact");
    test_smash_intact();
    println!("test_smash_intact_not_owner");
    test_smash_intact_not_owner();
    println!("test_smash_smashed");
    test_smash_smashed();
    
    println!("\n\n\tTest Auction\n\n");

    println!("test_init");
    auction_test_init();
    println!("test_auction_bid_and_finalize");
    test_auction_bid_and_finalize();
    println!("test_auction_bid_repeated_bid");
    test_auction_bid_repeated_bid();
    println!("test_auction_bid_zero");
    test_auction_bid_zero();

    // println!("\n\n\tTest Impls\n\n");
    // test_contract_state();
    
    println!("\n\n\tDONE\n\n");
}

