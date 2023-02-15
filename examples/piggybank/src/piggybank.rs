#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

use hacspec_lib::*;

#[cfg(not(feature = "hacspec"))]
extern crate hacspec_attributes;
#[cfg(not(feature = "hacspec"))]
use hacspec_attributes::*;

#[cfg(not(feature = "hacspec"))]
extern crate creusot_contracts;
#[cfg(not(feature = "hacspec"))]
use creusot_contracts::{ensures, requires};

use hacspec_concordium::*;

#[cfg(feature = "hacspec")]
use concert_lib::*;

#[cfg(not(feature = "hacspec"))]
/// The state of the piggy bank
#[derive(Debug, Serialize, PartialEq, Eq)]
enum PiggyBankState {
    /// Alive and well, allows for GTU to be inserted.
    Intact,
    /// The piggy bank has been emptied, preventing further GTU to be inserted.
    Smashed,
}


// #[cfg(feature = "hacspec")]
/// The state of the piggy bank
#[derive(Debug, PartialEq, Eq, Serialize)]
#[contract_state(contract = "CIS1-wCCD")]
#[serialize]
pub enum PiggyBankStateHacspec {
    Intact,
    Smashed,
}
// #[cfg(not(feature = "hacspec"))]
// #[derive(Debug, PartialEq, Eq)]
// pub enum PiggyBankStateHacspec {
//     Intact,
//     Smashed,
// }

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

pub fn piggy_init_hacspec() -> PiggyBankStateHacspec {
    // Always succeeds
    PiggyBankStateHacspec::Intact
}

#[cfg(feature = "hacspec")]
#[init(contract = "PiggyBank")]
#[ensures(result == (ctx, PiggyBankStateHacspec::Intact))]
pub fn piggy_init(ctx : Context) -> (Context, PiggyBankStateHacspec) { // , actions
    // Always succeeds
    (ctx, piggy_init_hacspec())
}

#[cfg(not(feature = "hacspec"))]
/// Setup a new Intact piggy bank.
#[init(contract = "PiggyBank")]
fn piggy_init(_ctx: &impl HasInitContext) -> InitResult<PiggyBankState> {
    // Always succeeds
    Ok(coerce_hacspec_to_rust_piggybank_state(piggy_init_hacspec()))
}

pub type PiggyInsertResult = Result<(), ()>;

pub fn piggy_insert_hacspec(ctx: Context, amount: u64, state: PiggyBankStateHacspec) -> PiggyInsertResult {
    // Ensure the piggy bank has not been smashed already.
    match state {
        PiggyBankStateHacspec::Intact => PiggyInsertResult::Ok(()),
        PiggyBankStateHacspec::Smashed => PiggyInsertResult::Err(()),
    }
}

#[cfg(feature = "hacspec")]
#[receive(contract = "PiggyBank", name = "insert", payable)]
pub fn piggy_insert(ctx_state: (Context, PiggyBankStateHacspec), amount: u64) -> Option<((Context, PiggyBankStateHacspec), ListAction)> {
    let (ctx, state) = ctx_state;
    let Context(a, c, balance, d) = ctx;
    accept_hacspec();
    let temp = piggy_insert_hacspec(ctx, amount, state);
    match temp {
        PiggyInsertResult::Ok(_) => Option::<()>::Some(()),
        PiggyInsertResult::Err(_) => Option::<()>::None
    }?;
    let s = Seq::<HasAction>::new(0);
    s[0] = accept_action();
    Option::<((Context, PiggyBankStateHacspec), ListAction)>::Some (((Context(a, c, balance + amount, d), state), s))
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
    Ok(Context(
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
        0u64
    ))
}

type PiggySmashResult = Result<PiggyBankStateHacspec, SmashError>;

#[ensures((!(state == PiggyBankStateHacspec::Intact) ==> result == PiggySmashResult::Err(SmashError::AlreadySmashed)) ||
          (forall<owner : UserAddress>
           forall<sender : UserAddress>
           forall<balance : u64>
           forall<metadata : u64>
           ctx == Context(owner, sender, balance, metadata) ==>
           !(owner == sender) ==>
           result == PiggySmashResult::Err(SmashError::NotOwner)))]
fn piggy_smash_hacspec(ctx: Context, state: PiggyBankStateHacspec) -> PiggySmashResult {
    // Get the contract owner, i.e. the account who initialized the contract.
    let Context(owner, sender, _balance, _metadata) = ctx;

    if !(owner == sender) {
        PiggySmashResult::Err(SmashError::NotOwner)?;
    }

    if !(state == PiggyBankStateHacspec::Intact) {
        PiggySmashResult::Err(SmashError::AlreadySmashed)?;
    }

    PiggySmashResult::Ok(PiggyBankStateHacspec::Smashed)
}

#[cfg(feature = "hacspec")]
#[receive(contract = "PiggyBank", name = "smash")]
fn piggy_smash(ctx_state: (Context, PiggyBankStateHacspec)) -> Option<((Context, PiggyBankStateHacspec), ListAction)> {
    let (ctx, state) = ctx_state;
    let Context(a, c, balance, d) = ctx;
    accept_hacspec();
    let smash = piggy_smash_hacspec(ctx, state);
    let new_state = match smash {
        PiggySmashResult::Ok(a) => Option::<PiggyBankStateHacspec>::Some(a),
        PiggySmashResult::Err(b) => Option::<PiggyBankStateHacspec>::None,
    }?;
    let s = Seq::<HasAction>::new(1);
    // s[0] = HasAction::SIMPLE_TRANSFER( a, balance );
    Option::<((Context, PiggyBankStateHacspec), ListAction)>::Some(((Context(a, c, 0u64, d), new_state), s))
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
#[quickcheck]
#[proof]
fn test_insert_intact(ctx: Context, amount: u64) -> bool {
    piggy_insert_hacspec(ctx, amount, PiggyBankStateHacspec::Intact) == PiggyInsertResult::Ok(())
}

#[cfg(test)]
#[quickcheck]
#[proof]
fn test_insert_smashed(ctx: Context, amount: u64) -> bool {
    piggy_insert_hacspec(ctx, amount, PiggyBankStateHacspec::Smashed) == PiggyInsertResult::Err(())
}

#[cfg(test)]
#[quickcheck]
#[proof]
fn test_smash_intact(owner : UserAddress, balance : u64, metadata: u64) -> bool {
    // Setup the context
    let sender = owner;
    let ctx = Context(owner, sender, balance, metadata);

    // Trigger the smash
    piggy_smash_hacspec(ctx, PiggyBankStateHacspec::Intact) == PiggySmashResult::Ok(PiggyBankStateHacspec::Smashed)
}

#[cfg(test)]
#[quickcheck]
#[proof]
fn test_smash_intact_not_owner(owner : UserAddress, sender : UserAddress, balance : u64, metadata: u64) -> bool{
    // Setup the contextt
    let ctx = Context(owner, sender, balance, metadata);

    // Trigger the smash
    // TODO: Generate pair of owner sender not equal (not a big issue)
    owner == sender || piggy_smash_hacspec(ctx, PiggyBankStateHacspec::Intact) == PiggySmashResult::Err(SmashError::NotOwner)
}

#[cfg(test)]
#[quickcheck]
#[proof]
fn test_smash_smashed(owner : UserAddress, balance : u64, metadata: u64) -> bool{
    // Setup the context
    let sender = owner;
    let ctx = Context(owner, sender, balance, metadata);

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
