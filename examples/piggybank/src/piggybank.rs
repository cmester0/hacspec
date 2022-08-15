#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

use hacspec_lib::*;

// #[cfg(feature = "hacspec")]
// use hacspec_attribute::*;

#[cfg(not(feature = "hacspec"))]
extern crate creusot_contracts;
#[cfg(not(feature = "hacspec"))]
use creusot_contracts::{ensures, requires};

use hacspec_concordium::*;

#[cfg(not(feature = "hacspec"))]
/// The state of the piggy bank
#[derive(Debug, Serialize, PartialEq, Eq)]
enum PiggyBankState {
    /// Alive and well, allows for GTU to be inserted.
    Intact,
    /// The piggy bank has been emptied, preventing further GTU to be inserted.
    Smashed,
}

// Record State :=
//     build_state { balance : Amount ;
//                 owner : Address ; 
//                 piggyState : piggy_bank_state_hacspec_t}.
/// The state of the piggy bank
#[derive(Debug, PartialEq, Eq)] // , Serialize
pub enum PiggyBankStateHacspec {
    /// Alive and well, allows for GTU to be inserted.
    Intact,
    /// The piggy bank has been emptied, preventing further GTU to be inserted.
    Smashed,
}

#[cfg(not(feature = "hacspec"))]
fn coerce_hacspec_to_rust_piggybank_state(pbs : PiggyBankStateHacspec) -> PiggyBankState {
    match pbs {
        PiggyBankStateHacspec::Intact  => PiggyBankState::Intact,
        PiggyBankStateHacspec::Smashed => PiggyBankState::Smashed,
    }
}


#[cfg(not(feature = "hacspec"))]
fn coerce_rust_to_hacspec_piggybank_state(pbs : &PiggyBankState) -> PiggyBankStateHacspec {
    match pbs {
        PiggyBankState::Intact  => PiggyBankStateHacspec::Intact,
        PiggyBankState::Smashed => PiggyBankStateHacspec::Smashed,
    }
}

array!(UserAddress, 32, u8);

pub type Context = (UserAddress, UserAddress, u64);
pub type ContextStateHacspec = (Context, PiggyBankStateHacspec);

pub fn piggy_init_hacspec() -> PiggyBankStateHacspec {
    // Always succeeds
    PiggyBankStateHacspec::Intact
}

// Definition piggyBank_init (chain : Chain) (ctx : ContractCallContext) (_ : Setup) : option State :=
// Some {| balance := 0 ;
//         owner := ctx.(ctx_from);
//         piggyState := Intact |}.
#[cfg(feature = "hacspec")]
#[init(contract = "PiggyBank")]
pub fn piggy_init(ctx : Context) -> ContextStateHacspec { // , actions
    // Always succeeds
    (ctx, piggy_init_hacspec())
}

#[cfg(not(feature = "hacspec"))]
/// Setup a new Intact piggy bank.
#[init(contract = "PiggyBank")]
fn piggy_init(ctx: &impl HasInitContext) -> InitResult<PiggyBankState> {
    // let ctx_hacspec = coerce_rust_to_hacspec_context(ctx)?;
    // Always succeeds
    Ok(coerce_hacspec_to_rust_piggybank_state(piggy_init_hacspec()))
}

#[cfg(not(feature = "hacspec"))]
fn coerce_rust_to_hacspec_account_address(aa: &AccountAddress) -> UserAddress {
    UserAddress::from_native_slice(&aa.0)
}

pub type PiggyInsertResult = Result<(), ()>;

pub fn piggy_insert_hacspec(ctx: Context, amount: u64, state: PiggyBankStateHacspec) -> PiggyInsertResult {
    // Ensure the piggy bank has not been smashed already.
    match state {
        PiggyBankStateHacspec::Intact => PiggyInsertResult::Ok(()),
        PiggyBankStateHacspec::Smashed => PiggyInsertResult::Err(()),
    }
}

// Definition insert (n : Amount) (st : State) : State :=
//     {| balance := st.(balance) + n ;
//         owner := st.(owner);
//         piggyState := st.(piggyState) |}.
#[cfg(feature = "hacspec")]
#[receive(contract = "PiggyBank", name = "insert", payable)]
pub fn piggy_insert(ctx: Context, amount: u64, state: PiggyBankStateHacspec) -> ContextStateHacspec {
    let (a, c, balance) = ctx;
    accept_hacspec();
    ((a, c, balance + amount), state)
}

#[cfg(not(feature = "hacspec"))]
/// Insert some GTU into a piggy bank, allowed by anyone.
#[receive(contract = "PiggyBank", name = "insert", payable)]
fn piggy_insert<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    state: &mut PiggyBankState,
) -> ReceiveResult<A> {
    let ctx_hacspec = coerce_rust_to_hacspec_context(ctx)?;
    // Ensure the piggy bank has not been smashed already.
    piggy_insert_hacspec(ctx_hacspec, amount.micro_ccd, coerce_rust_to_hacspec_piggybank_state(state))?;
    // Just accept since the GTU balance is managed by the chain.
    Ok(A::accept())
}

// #[cfg(not(feature = "hacspec"))]
#[derive(Debug, PartialEq, Eq, Reject)]
enum SmashError {
    NotOwner,
    AlreadySmashed,
}

#[cfg(not(feature = "hacspec"))]
fn coerce_rust_to_hacspec_context(ctx: &impl HasReceiveContext) -> Result<Context, SmashError> {
    Ok((
        coerce_rust_to_hacspec_account_address(&ctx.owner()),
        coerce_rust_to_hacspec_account_address(
            &(match ctx.sender() {
                Address::Account(a) => Ok(a),
                _ => Err(SmashError::NotOwner),
            }?),
        ),
        match ctx.self_balance() {
            Amount { micro_ccd } => micro_ccd,
        },
        
    ))
}

// enum PiggySmashErr {
//     OwnerSender,
//     Smashed,
// }

type PiggySmashResult = Result<PiggyBankStateHacspec, SmashError>;

fn piggy_smash_hacspec(ctx: Context, state: PiggyBankStateHacspec) -> PiggySmashResult {
    // Get the contract owner, i.e. the account who initialized the contract.
    let (owner, sender, _balance) = ctx;

    if !(owner == sender) {
        PiggySmashResult::Err(SmashError::NotOwner)?;
    }

    if !(state == PiggyBankStateHacspec::Intact) {
        PiggySmashResult::Err(SmashError::AlreadySmashed)?;
    }

    PiggySmashResult::Ok(PiggyBankStateHacspec::Smashed)
}

// Definition smash (st : State) : State :=
//     {| balance := 0 ;
//         owner := st.(owner);
//         piggyState := Smashed |}.
#[cfg(feature = "hacspec")]
#[receive(contract = "PiggyBank", name = "smash")]
fn piggy_smash(ctx: Context, state: PiggyBankStateHacspec) -> ContextStateHacspec {
    let (a, c, _) = ctx;
    accept_hacspec();
    ((a, c, 0u64), state)
    // piggy_smash_hacspec(ctx, state)
}

#[cfg(not(feature = "hacspec"))]
/// Smash a piggy bank retrieving the GTU, only allowed by the owner.
#[receive(contract = "PiggyBank", name = "smash")]
fn piggy_smash<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut PiggyBankState,
) -> Result<A, SmashError> {
    let ctx_hacspec = coerce_rust_to_hacspec_context(ctx)?;

    *state = coerce_hacspec_to_rust_piggybank_state(
        match piggy_smash_hacspec(ctx_hacspec, coerce_rust_to_hacspec_piggybank_state(state)) {
            Ok(a) => a,
            Err(e) => return Err(e),
        },
    );

    // Get the current balance of the smart contract.
    let balance = ctx.self_balance();
    // Result in a transfer of the whole balance to the contract owner.
    Ok(A::simple_transfer(&ctx.owner(), balance))
}

//Tests - type checker ignores #[cfg(test)] parts
#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

// Running the initialization ensuring nothing fails and the state of the
// piggy bank is intact.
#[cfg(test)]
#[proof]
fn test_init_hacspec() -> bool {
    piggy_init_hacspec() == PiggyBankStateHacspec::Intact
}

#[cfg(test)]
#[proof]
#[quickcheck]
fn test_insert_intact(owner : UserAddress, balance : u64, amount : u64) -> bool {
    // Setup the context
    let sender = owner;
    let ctx = (owner, sender, balance);
    piggy_insert_hacspec(ctx, amount, PiggyBankStateHacspec::Intact) == PiggyInsertResult::Ok()
}

#[cfg(test)]
#[proof]
#[quickcheck]
fn test_insert_smashed(owner : UserAddress, balance : u64, amount : u64) -> bool {
    // Setup the context
    let sender = owner;
    let ctx = (owner, sender, balance);
    piggy_insert_hacspec(ctx, amount, PiggyBankStateHacspec::Smashed) == PiggyInsertResult::Err(())
}

#[cfg(test)]
#[quickcheck]
#[proof]
fn test_smash_intact(owner : UserAddress, balance : u64) -> bool {
    // Setup the context
    let sender = owner;
    let ctx = (owner, sender, balance);

    // Trigger the smash
    piggy_smash_hacspec(ctx, PiggyBankStateHacspec::Intact) == PiggySmashResult::Ok(PiggyBankStateHacspec::Smashed)
}

#[cfg(test)]
#[quickcheck]
#[proof]
fn test_smash_intact_not_owner(owner : UserAddress, sender : UserAddress, balance : u64) -> bool{    
    // Setup the contextt
    let ctx = (owner, sender, balance);

    // Trigger the smash
    // TODO: Generate pair of owner sender not equal (not a big issue)
    owner == sender || piggy_smash_hacspec(ctx, PiggyBankStateHacspec::Intact) == PiggySmashResult::Err(SmashError::NotOwner)
}

#[cfg(test)]
#[quickcheck]
#[proof]
fn test_smash_smashed(owner : UserAddress, balance : u64) -> bool{
    // Setup the context
    let sender = owner;
    let ctx = (owner, sender, balance);

    // Trigger the smash
    piggy_smash_hacspec(ctx, PiggyBankStateHacspec::Smashed) == PiggySmashResult::Err(SmashError::AlreadySmashed)
}

#[cfg(not(feature = "hacspec"))]
// Unit tests for the smart contract "PiggyBank"
#[concordium_cfg_test]
mod tests {
    use super::*;
    // Pulling in the testing utils found in concordium_std.
    use test_infrastructure::*;

    // Running the initialization ensuring nothing fails and the state of the
    // piggy bank is intact.
    #[concordium_test]
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

    #[concordium_test]
    fn test_insert_intact() {
        // Setup
        let ctx = ReceiveContextTest::empty();
        let amount = Amount::from_micro_ccd(100);
        let mut state = PiggyBankState::Intact;

        // Trigger the insert
        let actions_result: ReceiveResult<ActionsTree> = piggy_insert(&ctx, amount, &mut state);

        // Inspect the result
        let actions = actions_result.expect_report("Inserting GTU results in error.");

        claim_eq!(
            actions,
            ActionsTree::accept(),
            "No action should be produced."
        );
        claim_eq!(
            state,
            PiggyBankState::Intact,
            "Piggy bank state should still be intact."
        );
    }

    #[concordium_test]
    fn test_insert_smashed() {
        // Setup
        let ctx = ReceiveContextTest::empty();
        let amount = Amount::from_micro_ccd(100);
        let mut state = PiggyBankState::Smashed;

        // Trigger the insert
        let actions_result: ReceiveResult<ActionsTree> = piggy_insert(&ctx, amount, &mut state);

        // Inspect the result
        claim!(
            actions_result.is_err(),
            "Should failed when piggy bank is smashed."
        );
    }

    #[concordium_test]
    fn test_smash_intact() {
        // Setup the context

        let mut ctx = ReceiveContextTest::empty();
        let owner = AccountAddress([0u8; 32]);
        ctx.set_owner(owner);
        let sender = Address::Account(owner);
        ctx.set_sender(sender);
        let balance = Amount::from_micro_ccd(100);
        ctx.set_self_balance(balance);

        let mut state = PiggyBankState::Intact;

        // Trigger the smash
        let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

        // Inspect the result
        let actions = actions_result.expect_report("Inserting GTU results in error.");
        claim_eq!(actions, ActionsTree::simple_transfer(&owner, balance));
        claim_eq!(state, PiggyBankState::Smashed);
    }

    #[concordium_test]
    fn test_smash_intact_not_owner() {
        // Setup the context

        let mut ctx = ReceiveContextTest::empty();
        let owner = AccountAddress([0u8; 32]);
        ctx.set_owner(owner);
        let sender = Address::Account(AccountAddress([1u8; 32]));
        ctx.set_sender(sender);
        let balance = Amount::from_micro_ccd(100);
        ctx.set_self_balance(balance);

        let mut state = PiggyBankState::Intact;

        // Trigger the smash
        let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

        let err = actions_result.expect_err_report("Contract is expected to fail.");
        claim_eq!(
            err,
            SmashError::NotOwner,
            "Expected to fail with error NotOwner"
        )
    }

    #[concordium_test]
    fn test_smash_smashed() {
        // Setup the context
        let mut ctx = ReceiveContextTest::empty();
        let owner = AccountAddress([0u8; 32]);
        ctx.set_owner(owner);
        let sender = Address::Account(owner);
        ctx.set_sender(sender);
        let balance = Amount::from_micro_ccd(100);
        ctx.set_self_balance(balance);

        let mut state = PiggyBankState::Smashed;

        // Trigger the smash
        let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

        let err = actions_result.expect_err_report("Contract is expected to fail.");
        claim_eq!(
            err,
            SmashError::AlreadySmashed,
            "Expected  to fail with error AlreadySmashed"
        )
    }
}
