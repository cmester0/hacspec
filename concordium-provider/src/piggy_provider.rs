use hacspec_lib::prelude::*;
use concordium_std::*;
use piggybank::*;

/// The state of the piggy bank
#[derive(Debug, Serialize, PartialEq, Eq)]
enum PiggyBankState {
    /// Alive and well, allows for GTU to be inserted.
    Intact,
    /// The piggy bank has been emptied, preventing further GTU to be inserted.
    Smashed,
}


#[init(contract = "PiggyBank")]
fn piggy_init(_ctx: &impl HasInitContext) -> InitResult<PiggyBankState> {
    piggybank::piggy_init();
    Ok (PiggyBankState::Intact)
    // Always succeeds
    // Ok(PiggyBankState::Intact)
}

fn u8x32_to_user_address (acc : [u8;32]) -> UserAddress {
    UserAddress ([acc[0],
		  acc[1],
		  acc[2],
		  acc[3],
		  acc[4],
		  acc[5],
		  acc[6],
		  acc[7],
		  acc[8],
		  acc[9],
		  acc[10],
		  acc[11],
		  acc[12],
		  acc[13],
		  acc[14],
		  acc[15],
		  acc[16],
		  acc[17],
		  acc[18],
		  acc[19],
		  acc[20],
		  acc[21],
		  acc[22],
		  acc[23],
		  acc[24],
		  acc[25],
		  acc[26],
		  acc[27],
		  acc[28],
		  acc[29],
		  acc[30],
		  acc[31],])
}

/// Insert some GTU into a piggy bank, allowed by anyone.
#[receive(contract = "PiggyBank", name = "insert", payable)]
fn piggy_insert<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    state: &mut PiggyBankState,
) -> ReceiveResult<A> {

    // bytes!()
    let owner = u8x32_to_user_address(ctx.owner().0);
    let sender = match ctx.sender() {
	Address::Account (acd) => u8x32_to_user_address(acd.0),
	_ => u8x32_to_user_address([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
    };
    let balance = ctx.self_balance().micro_gtu;
    let addition = amount.micro_gtu;
    let piggybank_state = match *state {
	PiggyBankState::Intact => piggybank::PiggyBankState::Intact,
	PiggyBankState::Smashed => piggybank::PiggyBankState::Smashed,
    };
    
    match piggybank::piggy_insert((owner, sender, balance, piggybank_state), addition) {
	PiggyInsertResult::PiggyInsertResultInl (_, _, _, _) => (),
	    _ => panic!(),
    };
    
    Ok(A::accept())
}

/// Smash a piggy bank retrieving the GTU, only allowed by the owner.
#[receive(contract = "PiggyBank", name = "smash")]
fn piggy_smash<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut PiggyBankState,
) -> ReceiveResult<A> {

    let owner = u8x32_to_user_address(ctx.owner().0);
    let sender = match ctx.sender() {
	Address::Account (acd) => u8x32_to_user_address(acd.0),
	_ => u8x32_to_user_address([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
    };
    let balance = ctx.self_balance().micro_gtu;
    let piggybank_state = match *state {
	PiggyBankState::Intact => piggybank::PiggyBankState::Intact,
	PiggyBankState::Smashed => piggybank::PiggyBankState::Smashed,
    };
    
    match piggybank::piggy_smash((owner, sender, balance, piggybank_state)) {
	PiggySmashResult::PiggySmashResultInl (_, _, balance_result) =>
	    Ok(A::simple_transfer(&ctx.owner(), Amount {micro_gtu : balance_result,})),
	_ => panic!(),
    }
}
