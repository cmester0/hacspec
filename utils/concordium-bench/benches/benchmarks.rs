use concordium_std::*;
// use concordium_provider::provider::*;
use concordium_provider::piggy_provider::*;

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


////////////////////////////////////////////////////////////

fn test_init() {
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


fn main () {
    println!("\n\n\tConcordium benchmark tests\n\n");

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
    
    println!("\n\n\tDONE\n\n");

}

