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

fn u8x32ToUserAddress (acc : [u8;32]) -> UserAddress {
    UserAddress ([U8(acc[0]),
		  U8(acc[1]),
		  U8(acc[2]),
		  U8(acc[3]),
		  U8(acc[4]),
		  U8(acc[5]),
		  U8(acc[6]),
		  U8(acc[7]),
		  U8(acc[8]),
		  U8(acc[9]),
		  U8(acc[10]),
		  U8(acc[11]),
		  U8(acc[12]),
		  U8(acc[13]),
		  U8(acc[14]),
		  U8(acc[15]),
		  U8(acc[16]),
		  U8(acc[17]),
		  U8(acc[18]),
		  U8(acc[19]),
		  U8(acc[20]),
		  U8(acc[21]),
		  U8(acc[22]),
		  U8(acc[23]),
		  U8(acc[24]),
		  U8(acc[25]),
		  U8(acc[26]),
		  U8(acc[27]),
		  U8(acc[28]),
		  U8(acc[29]),
		  U8(acc[30]),
		  U8(acc[31]),])
}

/// Insert some GTU into a piggy bank, allowed by anyone.
#[receive(contract = "PiggyBank", name = "insert", payable)]
fn piggy_insert<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    state: &mut PiggyBankState,
) -> ReceiveResult<A> {

    // bytes!()
    let owner = u8x32ToUserAddress(ctx.owner().0);
    let sender = match ctx.sender() {
	Address::Account (acd) => u8x32ToUserAddress(acd.0),
	_ => u8x32ToUserAddress([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
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

    let owner = u8x32ToUserAddress(ctx.owner().0);
    let sender = match ctx.sender() {
	Address::Account (acd) => u8x32ToUserAddress(acd.0),
	_ => u8x32ToUserAddress([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
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
