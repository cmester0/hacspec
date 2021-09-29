use hacspec_lib::*;

/// The state of the piggy bank
#[derive(Debug, PartialEq, Eq)] // , Serialize
pub enum PiggyBankState {
    /// Alive and well, allows for GTU to be inserted.
    Intact,
    /// The piggy bank has been emptied, preventing further GTU to be inserted.
    Smashed,
}

pub fn piggy_init() -> PiggyBankState {
    // Always succeeds
    PiggyBankState::Intact
}

// type ByteSeqResult = Result<ByteSeq, u8>; assert_bytes_eq!
// bytes!(UserAddress, 32);
array!(UserAddress, 32, u8); // U8
    
// owner, sender, balance, state
pub type Context = (UserAddress, UserAddress, u64, PiggyBankState);

pub enum PiggyInsertResult {
    PiggyInsertResultInl (UserAddress, UserAddress, u64, PiggyBankState),
    PiggyInsertResultInr,
}

pub enum PiggySmashResult {
    PiggySmashResultInl (Context, UserAddress, u64),
    PiggySmashResultInrOwnerSender,
    PiggySmashResultInrSmashed,
}

pub fn piggy_insert(
    ctx : Context,
    amount: u64) -> PiggyInsertResult {
    let (owner, sender, balance, state) = ctx;
    
    // Ensure the piggy bank has not been smashed already.
    // ensure!
    match state {
	PiggyBankState::Intact => PiggyInsertResult::PiggyInsertResultInl (owner, sender, balance + amount, state),
	PiggyBankState::Smashed => PiggyInsertResult::PiggyInsertResultInr,
    }
}

pub fn piggy_smash(ctx : Context) -> PiggySmashResult {
    // Get the contract owner, i.e. the account who initialized the contract.
    let (owner, sender, balance, state) = ctx;

    // Ensure only the owner can smash the piggy bank.
    match state {
	PiggyBankState::Intact =>
	    if !(owner == sender) {
		PiggySmashResult::PiggySmashResultInrOwnerSender
	    } else {
		PiggySmashResult::PiggySmashResultInl ((owner, sender, balance, PiggyBankState::Smashed), owner, balance)
	    },
	PiggyBankState::Smashed => PiggySmashResult::PiggySmashResultInrSmashed,
    }
}

//Tests - type checker ignores #[cfg(test)] parts
#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

#[quickcheck]
#[cfg(test)]
#[cfg(proof)]
fn test_init() -> bool {
    let state = piggy_init();
    
    match state {// "Piggy bank state should be intact after initialization."
        PiggyBankState::Intact => true,
        PiggyBankState::Smashed => false,
    }
}

// fn test_insert_intact() {
//     // Setup
//     let mut ctx = ReceiveContextTest::empty();

//     let owner = AccountAddress([0u8; 32]);
//     ctx.set_owner(owner);
//     let sender = Address::Account(owner);
//     ctx.set_sender(sender);
//     let balance = Amount::from_micro_gtu(100);
//     ctx.set_self_balance(balance);
    
//     let amount = Amount::from_micro_gtu(100);
//     let mut state = PiggyBankState::Intact;
    
//     // Trigger the insert
//     let actions_result: ReceiveResult<ActionsTree> = piggy_insert(&ctx, amount, &mut state);
    
//     // Inspect the result
//     let actions = actions_result.expect_report("Inserting GTU results in error.");
    
//     claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");
//     claim_eq!(state, PiggyBankState::Intact, "Piggy bank state should still be intact.");
// }

// fn test_insert_smashed() {
//     // Setup
//     let mut ctx = ReceiveContextTest::empty();

//     let owner = AccountAddress([0u8; 32]);
//     ctx.set_owner(owner);
//     let sender = Address::Account(owner);
//     ctx.set_sender(sender);
//     let balance = Amount::from_micro_gtu(100);
//     ctx.set_self_balance(balance);
    
//     let amount = Amount::from_micro_gtu(100);
//     let mut state = PiggyBankState::Smashed;

//     // Trigger the insert
//     let actions_result: ReceiveResult<ActionsTree> = piggy_insert(&ctx, amount, &mut state);

//     // Inspect the result
//     claim!(actions_result.is_err(), "Should failed when piggy bank is smashed.");
// }

// fn test_smash_intact() {
//     // Setup the context

//     let mut ctx = ReceiveContextTest::empty();
//     let owner = AccountAddress([0u8; 32]);
//     ctx.set_owner(owner);
//     let sender = Address::Account(owner);
//     ctx.set_sender(sender);
//     let balance = Amount::from_micro_gtu(100);
//     ctx.set_self_balance(balance);

//     let mut state = PiggyBankState::Intact;

//     // Trigger the smash
//     let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

//     // Inspect the result
//     let actions = actions_result.expect_report("Inserting GTU results in error.");
//     claim_eq!(actions, ActionsTree::simple_transfer(&owner, balance));
//     claim_eq!(state, PiggyBankState::Smashed);
// }

// fn test_smash_intact_not_owner() {
//     // Setup the context

//     let mut ctx = ReceiveContextTest::empty();
//     let owner = AccountAddress([0u8; 32]);
//     ctx.set_owner(owner);
//     let sender = Address::Account(AccountAddress([1u8; 32]));
//     ctx.set_sender(sender);
//     let balance = Amount::from_micro_gtu(100);
//     ctx.set_self_balance(balance);

//     let mut state = PiggyBankState::Intact;

//     // Trigger the smash
//     let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

//     let err = actions_result.expect_err_report("Contract is expected to fail.");
//     claim_eq!(err, Reject {error_code: unsafe { std::num::NonZeroI32::new_unchecked(4) }}, "Expected to fail with error NotOwner") // SmashError::NotOwner // TODO: ??
// }

// fn test_smash_smashed() {
//     // Setup the context
//     let mut ctx = ReceiveContextTest::empty();
//     let owner = AccountAddress([0u8; 32]);
//     ctx.set_owner(owner);
//     let sender = Address::Account(owner);
//     ctx.set_sender(sender);
//     let balance = Amount::from_micro_gtu(100);
//     ctx.set_self_balance(balance);

//     let mut state = PiggyBankState::Smashed;

//     // Trigger the smash
//     let actions_result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

//     let err = actions_result.expect_err_report("Contract is expected to fail.");
//     claim_eq!(err, Reject {error_code: unsafe { std::num::NonZeroI32::new_unchecked(5) }}, "Expected  to fail with error AlreadySmashed") // TODO: ??
// }




// #[cfg(test)]
// #[cfg(proof)]
// //Pearlite #[ensures(forall u v, bind (piggy_smash(u,u,v, piggy_init())) (|(_, _, balance)| => balance == v) )]
// fn test_init_smash_zero (user : UserAddress, start_val : u64) -> bool {
//     match piggy_smash((user, user, start_val, piggy_init())) {
// 	PiggySmashResult::PiggySmashResultInl ((_ , _ , balance)) => balance == start_val,
// 	PiggySmashResult::PiggySmashResultInr => false,
//     }
// }

// #[cfg(test)]
// #[cfg(proof)]
// //Pearlite #[ensures(forall u v w, bind (piggy_insert(u,u,v, piggy_init())) (|ctx| bind (piggy_smash ctx) (|(_, _, balance)| => balance == v + w)))]
// fn test_increment_then_smash (user : UserAddress, start_val : u64, increment : u64) -> bool {
//     match piggy_insert((user, user, start_val, piggy_init()), increment) {
// 	PiggyInsertResult::PiggyInsertResultInl ((a,b,c,d)) =>
// 	    match piggy_smash ((a,b,c,d)) {
// 		PiggySmashResult::PiggySmashResultInl ((_ , _ , balance)) => balance == start_val + increment,
// 		PiggySmashResult::PiggySmashResultInr => false,
// 	    }
// 	PiggyInsertResult::PiggyInsertResultInr => false,
//     }
// }

// #[cfg(test)]
// #[cfg(proof)]
// //Pearlite #[ensures(forall u v, bind (piggy_smash(u,u,v, piggy_init())) (|(ctx, _, balance)| => piggy_smash ctx) == fail )]
// fn test_re_smash_fails (user : UserAddress, start_val : u64) -> bool {
//     match piggy_smash((user, user, start_val, piggy_init())) {
// 	PiggySmashResult::PiggySmashResultInl ((ctx , _ , _)) =>
// 	    match piggy_smash (ctx) {
// 		PiggySmashResult::PiggySmashResultInl ((ctx , _ , _)) => false,
// 		PiggySmashResult::PiggySmashResultInr => true,
// 	    },
// 	PiggySmashResult::PiggySmashResultInr => false,
//     }
// }

// #[cfg(test)]
// #[cfg(proof)]
// //Pearlite #[ensures(forall u v, bind (piggy_smash(u,u,v, piggy_init())) (|(ctx, _, _)| => piggy_init ctx) == fail )]
// fn test_transfer_to_smash_fails (user : UserAddress, start_val : u64, increment : u64) -> bool {
//     match piggy_smash((user, user, start_val, piggy_init())) {
// 	PiggySmashResult::PiggySmashResultInl ((ctx , _ , _)) =>
// 	    match piggy_insert (ctx, increment) {
// 		PiggyInsertResult::PiggyInsertResultInl (_) => false,
// 		PiggyInsertResult::PiggyInsertResultInr => true,
// 	    },
// 	PiggySmashResult::PiggySmashResultInr => false,
//     }
// }

// #[cfg(test)]
// #[cfg(proof)]
// fn test_transfer_to_smash_fails_zero (user : UserAddress, sender : UserAddress, start_val : u64, increment : u64) -> bool {
//     !(
//     user != sender &&
//     match piggy_smash((user, sender, start_val, piggy_init())) {
// 	PiggySmashResult::PiggySmashResultInl ((ctx , _ , _)) =>
// 	    match piggy_insert (ctx, increment) {
// 		PiggyInsertResult::PiggyInsertResultInl (_) => true,
// 		PiggyInsertResult::PiggyInsertResultInr => false,
// 	    },
// 	PiggySmashResult::PiggySmashResultInr => false,
//     })
// }

// Cannot smash and lose money
// Cannot smash others piggy bank
// Cannot transfer negative money to piggy bank
// Cannot resmash piggy bank
// Cannot transfer to smashed piggy bank
// ...

// Ok (ctx) => helper ctx
