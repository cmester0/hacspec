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

#[quickcheck]
#[cfg(test)]
#[cfg(proof)]
fn test_insert_intact() -> bool {
    // Setup
    let ctx =
        (UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         100_u64,
         PiggyBankState::Intact);

    // Trigger the insert
    let result: PiggyInsertResult = piggy_insert(ctx, 100_u64);

    match result {
        PiggyInsertResult::PiggyInsertResultInl (owner, sender, balance, state) => match state {
            PiggyBankState::Intact => true,
            PiggyBankState::Smashed => false,
        },
        PiggyInsertResult::PiggyInsertResultInr => false,
    }
}

#[quickcheck]
#[cfg(test)]
#[cfg(proof)]
fn test_insert_smashed() -> bool {
    // Setup
    let ctx =
        (UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         100_u64,
         PiggyBankState::Smashed);

    let result = piggy_insert(ctx, 100_u64);
    match result {
        PiggyInsertResult::PiggyInsertResultInl (_, _, _, _) => false,
        PiggyInsertResult::PiggyInsertResultInr => true,
    }
}

#[quickcheck]
#[cfg(test)]
#[cfg(proof)]
fn test_smash_intact() -> bool {
    // Setup
    let ctx =
        (UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         100_u64,
         PiggyBankState::Intact);

    let result = piggy_smash(ctx);

    match result {
        PiggySmashResult::PiggySmashResultInl ((_,_,_,state), _, balance) => match state {
            PiggyBankState::Intact => false,
            PiggyBankState::Smashed => balance == 100_u64,
        },
        PiggySmashResult::PiggySmashResultInrSmashed => false,
        PiggySmashResult::PiggySmashResultInrOwnerSender => false,
    }
}

#[quickcheck]
#[cfg(test)]
#[cfg(proof)]
fn test_smash_intact_not_owner() -> bool {
    // Setup
    let ctx =
        (UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         UserAddress ([1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,1_u8,]),
         100_u64,
         PiggyBankState::Intact);
    // Setup the context

    let result = piggy_smash(ctx);
    match result {
        PiggySmashResult::PiggySmashResultInl (_, _, _) => false,
        PiggySmashResult::PiggySmashResultInrSmashed => false,
        PiggySmashResult::PiggySmashResultInrOwnerSender => true,
    }
}

#[quickcheck]
#[cfg(test)]
#[cfg(proof)]
fn test_smash_smashed()  -> bool {
    // Setup
    let ctx =
        (UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         UserAddress ([0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,0_u8,]),
         100_u64,
         PiggyBankState::Smashed);

    let result = piggy_smash(ctx);
    match result {
        PiggySmashResult::PiggySmashResultInl (_, _, _) => false,
        PiggySmashResult::PiggySmashResultInrSmashed => true,
        PiggySmashResult::PiggySmashResultInrOwnerSender => false,
    }
}




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
