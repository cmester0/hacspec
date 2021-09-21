/// The state of the piggy bank
#[derive(Debug, PartialEq, Eq)] // , Serialize
pub enum PiggyBankState {
    /// Alive and well, allows for GTU to be inserted.
    Intact,
    /// The piggy bank has been emptied, preventing further GTU to be inserted.
    Smashed,
}

// TODO: Monad notation?

pub fn piggy_init() -> PiggyBankState {
    // Always succeeds
    PiggyBankState::Intact // Ok()
}

// owner, sender, balance, state
pub type Context = (usize, usize, usize, PiggyBankState);

pub enum PiggyInsertResult {
    PiggyInsertResultInl (usize, usize, usize, PiggyBankState),
    PiggyInsertResultInr,
}

pub enum PiggySmashResult {
    PiggySmashResultInl (Context, usize, usize),
    PiggySmashResultInr,
}

pub fn piggy_insert(
    ctx : Context,
    amount: usize) -> PiggyInsertResult {
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
	PiggyBankState::Intact => if !(owner == sender) {
	    PiggySmashResult::PiggySmashResultInr
	}
	else {
	    PiggySmashResult::PiggySmashResultInl ((owner, sender, balance, PiggyBankState::Smashed), owner, balance)
	},
	PiggyBankState::Smashed => PiggySmashResult::PiggySmashResultInr,
    }
}

#[cfg(test)]
#[cfg(proof)]
//Pearlite #[ensures(forall u v, bind (piggy_smash(u,u,v, piggy_init())) (|(_, _, balance)| => balance == v) )]
fn test_init_smash_zero (user : usize, start_val : usize) -> bool {
    match piggy_smash((user, user, start_val, piggy_init())) {
	PiggySmashResult::PiggySmashResultInl ((_ , _ , balance)) => balance == start_val,
	PiggySmashResult::PiggySmashResultInr => false,
    }
}

#[cfg(test)]
#[cfg(proof)]
//Pearlite #[ensures(forall u v w, bind (piggy_insert(u,u,v, piggy_init())) (|ctx| bind (piggy_smash ctx) (|(_, _, balance)| => balance == v + w)))]
fn test_increment_then_smash (user : usize, start_val : usize, increment : usize) -> bool {
    match piggy_insert((user, user, start_val, piggy_init()), increment) {
	PiggyInsertResult::PiggyInsertResultInl ((a,b,c,d)) =>
	    match piggy_smash ((a,b,c,d)) {
		PiggySmashResult::PiggySmashResultInl ((_ , _ , balance)) => balance == start_val + increment,
		PiggySmashResult::PiggySmashResultInr => false,
	    }
	PiggyInsertResult::PiggyInsertResultInr => false,
    }
}

#[cfg(test)]
#[cfg(proof)]
//Pearlite #[ensures(forall u v, bind (piggy_smash(u,u,v, piggy_init())) (|(ctx, _, balance)| => piggy_smash ctx) == fail )]
fn test_re_smash_fails (user : usize, start_val : usize) -> bool {
    match piggy_smash((user, user, start_val, piggy_init())) {
	PiggySmashResult::PiggySmashResultInl ((ctx , _ , _)) =>
	    match piggy_smash (ctx) {
		PiggySmashResult::PiggySmashResultInl ((ctx , _ , _)) => false,
		PiggySmashResult::PiggySmashResultInr => true,
	    },
	PiggySmashResult::PiggySmashResultInr => false,
    }
}

#[cfg(test)]
#[cfg(proof)]
//Pearlite #[ensures(forall u v, bind (piggy_smash(u,u,v, piggy_init())) (|(ctx, _, _)| => piggy_init ctx) == fail )]
fn test_transfer_to_smash_fails (user : usize, start_val : usize, increment : usize) -> bool {
    match piggy_smash((user, user, start_val, piggy_init())) {
	PiggySmashResult::PiggySmashResultInl ((ctx , _ , _)) =>
	    match piggy_insert (ctx, increment) {
		PiggyInsertResult::PiggyInsertResultInl (_) => false,
		PiggyInsertResult::PiggyInsertResultInr => true,
	    },
	PiggySmashResult::PiggySmashResultInr => false,
    }
}

// Cannot smash and lose money
// Cannot smash others piggy bank
// Cannot transfer negative money to piggy bank
// Cannot resmash piggy bank
// Cannot transfer to smashed piggy bank
// ...

// Ok (ctx) => helper ctx
