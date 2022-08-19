#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

use hacspec_lib::*;

// #[cfg(not(feature = "hacspec"))]
// extern crate creusot_contracts;
#[cfg(test)]
#[cfg(not(feature = "hacspec"))]
use creusot_contracts::{ensures, requires};

// // Rust-hacspec Interface
#[cfg(not(feature = "hacspec"))]
use hacspec_concordium::{collections::BTreeMap, *};

#[cfg(feature = "hacspec")]
use concert_lib::*;

array!(UserAddress, 32, u8); // U8

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_account_address(ua: UserAddress) -> AccountAddress {
    AccountAddress([
	ua[0], ua[1], ua[2], ua[3], ua[4], ua[5], ua[6], ua[7], ua[8], ua[9], ua[10], ua[11],
	ua[12], ua[13], ua[14], ua[15], ua[16], ua[17], ua[18], ua[19], ua[20], ua[21], ua[22],
	ua[23], ua[24], ua[25], ua[26], ua[27], ua[28], ua[29], ua[30], ua[31],
    ])
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_account_address(aa: &AccountAddress) -> UserAddress {
    UserAddress::from_native_slice(&aa.0)
}

#[cfg(not(feature = "hacspec"))]
/// The state in which an auction can be.
#[derive(Debug, Eq, PartialEq, PartialOrd, Serialize, SchemaType)] // TODO: Debug with creusot 
pub enum AuctionState {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction is over and the item has been sold to the indicated address.
    Sold(AccountAddress), // winning account's address
}

/// The state in which an auction can be.
#[derive(Clone, PartialEq)]
pub enum AuctionStateHacspec {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction is over and the item has been sold to the indicated address.
    Sold(UserAddress), // winning account's address
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_auction_state(s : AuctionStateHacspec) -> AuctionState {
    match s {
	AuctionStateHacspec::NotSoldYet => AuctionState::NotSoldYet,
	AuctionStateHacspec::Sold(ua) => AuctionState::Sold(coerce_hacspec_to_rust_account_address(ua))
    }
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_auction_state(s : &AuctionState) -> AuctionStateHacspec {
    match s {
	AuctionState::NotSoldYet => AuctionStateHacspec::NotSoldYet,
	AuctionState::Sold(aa) => AuctionStateHacspec::Sold(coerce_rust_to_hacspec_account_address(aa))
    }
}

#[derive(Clone, PartialEq)]
pub struct SeqMap(pub PublicByteSeq, pub PublicByteSeq);

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_b_tree_map(m: SeqMap) -> BTreeMap<AccountAddress, Amount> {
    let m1prime =
	(0..m.0.len() / 32).map(|x| UserAddress::from_seq(&m.0.clone().slice(x * 32, 32)));
    let m2prime =
	(0..m.1.len() / 8).map(|x| u64_from_be_bytes(u64Word::from_seq(&m.1.slice(x * 8, 8))));

    (m1prime.zip(m2prime)).fold(BTreeMap::new(), |mut t, (x, y)| {
	t.insert(
	    coerce_hacspec_to_rust_account_address(x),
	    Amount { micro_ccd: y },
	);
	t
    })
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_b_tree_map(m: &BTreeMap<AccountAddress, Amount>) -> SeqMap {
    SeqMap(
	m.keys()
	    .map(|x| coerce_rust_to_hacspec_account_address(x))
	    .fold(PublicByteSeq::new(0_usize), |v, x| v.concat(&x)),
	m.values()
	    .map(|x| x.micro_ccd)
	    .fold(PublicSeq::new(0_usize), |v, x| {
		v.concat(&u64_to_be_bytes(x))
	    }),
    )
}

#[cfg(not(feature = "hacspec"))]
/// The state of the smart contract.
/// This is the state that will be shown when the contract is queried using
/// `concordium-client contract show`.
#[contract_state(contract = "auction")]
#[derive(Debug, Eq, PartialEq, Serialize, SchemaType)] // TODO: Debug, 
pub struct State {
    /// Has the item been sold?
    auction_state: AuctionState,
    /// The highest bid so far (stored explicitly so that bidders can quickly
    /// see it)
    highest_bid:   Amount,
    /// The sold item (to be displayed to the auction participants), encoded in
    /// ASCII
    item:          Vec<u8>,
    /// Expiration time of the auction at which bids will be closed (to be
    /// displayed to the auction participants)
    expiry:        Timestamp,
    /// Keeping track of which account bid how much money
    // #[concordium(size_length = 2)] // TODO
    bids:          BTreeMap<AccountAddress, Amount>,
}

#[derive(Clone, PartialEq)]
pub struct StateHacspec(
    pub AuctionStateHacspec,
    pub u64, // amount
    pub PublicByteSeq,
    pub u64, // timestamp
    pub SeqMap,
);

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_state(s : StateHacspec) -> State {
    let StateHacspec(auction_state_hacspec, amount, item_seq, time, bid_map) = s;
    let auction_state = coerce_hacspec_to_rust_auction_state(auction_state_hacspec);
    let highest_bid = Amount { micro_ccd: amount };
    let item = item_seq.native_slice().to_vec();
    let expiry = Timestamp::from_timestamp_millis(time);
    let bids = coerce_hacspec_to_rust_b_tree_map(bid_map);

    State {
	auction_state,
	highest_bid,
	item,
	expiry,
	bids,
    }
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_state(s : &State) -> StateHacspec {
    let auction_state = coerce_rust_to_hacspec_auction_state(&s.auction_state);
    let highest_bid = s.highest_bid.micro_ccd;
    let item = PublicByteSeq::from_native_slice(&s.item);
    let expiry = s.expiry.timestamp_millis();
    let bids = coerce_rust_to_hacspec_b_tree_map(&s.bids);

    StateHacspec (
	auction_state,
	highest_bid,
	item,
	expiry,
	bids,
    )
}

pub fn fresh_state_hacspec(itm: PublicByteSeq, exp: u64) -> StateHacspec {
    StateHacspec(
	AuctionStateHacspec::NotSoldYet,
	0_u64,
	itm,
	exp,
	SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
    )
}

#[cfg(not(feature = "hacspec"))]
/// A helper function to create a state for a new auction.
fn fresh_state(itm: Vec<u8>, exp: Timestamp) -> State {
    coerce_hacspec_to_rust_state(fresh_state_hacspec(
	PublicByteSeq::from_vec(itm),
	exp.timestamp_millis(),
    ))
}

#[cfg(not(feature = "hacspec"))]
/// Type of the parameter to the `init` function.
#[derive(Serialize, SchemaType)]
struct InitParameter {
    /// The item to be sold, as a sequence of ASCII codes.
    item: Vec<u8>,
    /// Time of the auction end in the RFC 3339 format (https://tools.ietf.org/html/rfc3339)
    expiry: Timestamp,
}

#[cfg(feature = "hacspec")]
struct InitParameter(
    /// The item to be sold, as a sequence of ASCII codes.
    PublicByteSeq,
    /// Time of the auction end in the RFC 3339 format (https://tools.ietf.org/html/rfc3339)
    u64,
);

pub struct Context(UserAddress, UserAddress, u64, u64);
pub type ContextStateHacspec = (Context, StateHacspec);

#[cfg(feature = "hacspec")]
#[init(contract = "auction", parameter = "InitParameter")]
pub fn auction_init(ctx : Context, init_parameter: InitParameter) -> ContextStateHacspec {
    // Always succeeds
    (ctx, fresh_state_hacspec(PublicByteSeq::new(0), 0u64))
}

#[cfg(not(feature = "hacspec"))]
/// Init function that creates a new auction
#[init(contract = "auction", parameter = "InitParameter")]
fn auction_init(ctx: &impl HasInitContext) -> InitResult<State> {
    let parameter: InitParameter = ctx.parameter_cursor().get()?;
    Ok(fresh_state(parameter.item, parameter.expiry))
}

fn seq_map_entry(m: SeqMap, sender_address: UserAddress) -> (u64, SeqMap) {
    let SeqMap(m0, m1) = m;

    let mut res = // MapEntry::Entry
	(
	0_u64,
	SeqMap(
	    m0.clone().concat(&sender_address),
	    m1.clone().concat(&u64_to_be_bytes(0_u64)),
	),
    );

    // TODO: use chunks instead of doing the math yourself
    for x in 0..m0.clone().len() / 32 {
	if UserAddress::from_seq(&m0.clone().slice(x * 32, 32)) == sender_address {
	    res = // MapEntry::Entry
		(
		u64_from_be_bytes(u64Word::from_seq(&m1.clone().slice(x * 8, 8))),
		SeqMap(m0.clone(), m1.clone()),
	    );
	}
    }

    res
}

#[derive(Clone, PartialEq)]
pub enum MapUpdate {
    Update(u64, SeqMap),
}

fn seq_map_update_entry(m: SeqMap, sender_address: UserAddress, amount: u64) -> MapUpdate {
    let SeqMap(m0, m1) = m;

    let mut res = MapUpdate::Update(
	amount,
	SeqMap(
	    m0.clone().concat(&sender_address),
	    m1.clone().concat(&u64_to_be_bytes(amount)),
	),
    );

    // TODO: use chunks instead of doing the math yourself
    // !! Issue in for loop !! (update, updates the reference!)
    for x in 0..m0.clone().len() / 32 {
	if UserAddress::from_seq(&m0.clone().slice(x * 32, 32)) == sender_address {
	    res = MapUpdate::Update(
		amount,
		SeqMap(
		    m0.clone().update(x * 32, &sender_address),
		    m1.clone().update(x * 8, &u64_to_be_bytes(amount)),
		),
	    );
	}
    }

    res
}

#[cfg(not(feature = "hacspec"))]
/// For errors in which the `bid` function can result
#[derive(Debug, PartialEq, Eq, Clone, Reject)]
enum BidError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionFinalized,                      /* raised if bid is placed after auction has been
					    * finalized */
}

#[derive(Clone, PartialEq)]
pub enum BidErrorHacspec {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionIsFinalized,                    /* raised if bid is placed after auction has been
					    * finalized */
}

// TODO: Never used?
// #[cfg(not(feature = "hacspec"))]
// fn coerce_rust_to_hacspec_bid_error(b: BidError) -> BidErrorHacspec {
//     match b {
// 	BidError::ContractSender => BidErrorHacspec::ContractSender,
// 	BidError::BidTooLow => BidErrorHacspec::BidTooLow,
// 	BidError::BidsOverWaitingForAuctionFinalization => {
// 	    BidErrorHacspec::BidsOverWaitingForAuctionFinalization
// 	}
// 	BidError::AuctionFinalized => BidErrorHacspec::AuctionIsFinalized,
//     }
// }

#[cfg(not(feature = "hacspec"))]
fn coerce_hacspec_to_rust_bid_error(b: BidErrorHacspec) -> BidError {
    match b {
	BidErrorHacspec::ContractSender => BidError::ContractSender,
	BidErrorHacspec::BidTooLow => BidError::BidTooLow,
	BidErrorHacspec::BidsOverWaitingForAuctionFinalization => {
	    BidError::BidsOverWaitingForAuctionFinalization
	}
	BidErrorHacspec::AuctionIsFinalized => BidError::AuctionFinalized,
    }
}

pub type AuctionBidResult = Result<StateHacspec, BidErrorHacspec>;

pub fn auction_bid_hacspec(ctx: Context, amount: u64, state: StateHacspec) -> AuctionBidResult {
    let StateHacspec(auction_state, highest_bid, st2, expiry, st4) = state.clone();

    if !(auction_state == AuctionStateHacspec::NotSoldYet) {
	AuctionBidResult::Err(BidErrorHacspec::AuctionIsFinalized)?;
    }

    let Context(owner, sender, balance, slot_time) = ctx;
    if !(slot_time <= expiry) {
	AuctionBidResult::Err(BidErrorHacspec::BidsOverWaitingForAuctionFinalization)?;
    }

    let (bid_to_update, _new_map) = // match
	  seq_map_entry(st4.clone(), sender) // {
      //     MapEntry::Entry(bid_to_update, new_map) => (bid_to_update, new_map),
      // }
      ;

    let (updated_bid, updated_map) =
	match seq_map_update_entry(st4.clone(), sender, bid_to_update + amount) {
	    MapUpdate::Update(updated_bid, updated_map) => (updated_bid, updated_map),
	};

    if !(updated_bid > highest_bid) {
	AuctionBidResult::Err(BidErrorHacspec::BidTooLow)?;
    }

    AuctionBidResult::Ok(StateHacspec(
	auction_state,
	updated_bid,
	st2,
	expiry,
	updated_map,
    ))
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_context(ctx: &impl HasReceiveContext) -> Context {
    Context(
        coerce_rust_to_hacspec_account_address(&ctx.owner()),
	match ctx.sender() {
	    Address::Contract(_) => panic!(),
	    Address::Account(account_address) => coerce_rust_to_hacspec_account_address(&account_address),
	},
        match ctx.self_balance() {
            Amount { micro_ccd } => micro_ccd,
        },
        ctx.metadata().slot_time().timestamp_millis(),	
    )
}

#[cfg(feature = "hacspec")]
/// Receive function in which accounts can bid before the auction end time
#[receive(contract = "auction", name = "bid", payable)]
fn auction_bid(
    ctx: ContextStateHacspec,
    amount: u64,
) -> Option<(ContextStateHacspec, ListAction)> {
    let s = Seq::<HasAction>::new(0);
    Option::<(ContextStateHacspec, ListAction)>::Some((ctx, s))
}

#[cfg(not(feature = "hacspec"))]
/// Receive function in which accounts can bid before the auction end time
#[receive(contract = "auction", name = "bid", payable)]
fn auction_bid<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    state: &mut State,
) -> Result<A, BidError> {
    let hacspec_state = coerce_rust_to_hacspec_state(state);

    let new_state = match auction_bid_hacspec(
	coerce_rust_to_hacspec_context(ctx),
	amount.micro_ccd,
	hacspec_state,
    ) {
	Ok (a) => a,
	Err (e) => return Err (coerce_hacspec_to_rust_bid_error(e)),
    };

    *state = coerce_hacspec_to_rust_state(new_state);

    Ok (A::accept())
}

#[cfg(not(feature = "hacspec"))]
/// For errors in which the `finalize` function can result
#[derive(Debug, PartialEq, Eq, Clone, Reject)]
enum FinalizeError {
    BidMapError,        /* raised if there is a mistake in the bid map that keeps track of all
			 * accounts' bids */
    AuctionStillActive, // raised if there is an attempt to finalize the auction before its expiry
    AuctionFinalized,   // raised if there is an attempt to finalize an already finalized auction
}

/// For errors in which the `finalize` function can result
#[derive(Clone, PartialEq)]
pub enum FinalizeErrorHacspec {
    BidMapError,
    AuctionStillActive,
    AuctionFinalized,
}

// TODO: never used
// #[cfg(not(feature = "hacspec"))]
// fn coerce_rust_to_hacspec_finalize_error(fe: FinalizeError) -> FinalizeErrorHacspec {
//     match fe {
// 	FinalizeError::BidMapError => FinalizeErrorHacspec::BidMapError,
// 	FinalizeError::AuctionStillActive => FinalizeErrorHacspec::AuctionStillActive,
// 	FinalizeError::AuctionFinalized => FinalizeErrorHacspec::AuctionFinalized,
//     }
// }

#[cfg(not(feature = "hacspec"))]
fn coerce_hacspec_to_rust_finalize_error(fe: FinalizeErrorHacspec) -> FinalizeError {
    match fe {
	FinalizeErrorHacspec::BidMapError => FinalizeError::BidMapError,
	FinalizeErrorHacspec::AuctionStillActive => FinalizeError::AuctionStillActive,
	FinalizeErrorHacspec::AuctionFinalized => FinalizeError::AuctionFinalized,
    }
}

pub type FinalizeContext = (u64, UserAddress, u64);

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_finalize_context(ctx: &impl HasReceiveContext) -> FinalizeContext {
  (
      ctx.metadata().slot_time().timestamp_millis(),
      coerce_rust_to_hacspec_account_address(&ctx.owner()),
      ctx.self_balance().micro_ccd,
  )
}

  // let slot_time = ctx.metadata().slot_time();
  // ensure!(slot_time > state.expiry, FinalizeError::AuctionStillActive);

  // let owner = ctx.owner();

  // let balance = ctx.self_balance();

#[derive(Clone, PartialEq)]
pub enum FinalizeAction {
    Accept,
    SimpleTransfer(PublicByteSeq),
}

#[derive(Clone, PartialEq)]
pub enum BidRemain {
    BidNone,
    BidSome(u64),
}

pub type AuctionFinalizeResult = Result<(StateHacspec, FinalizeAction), FinalizeErrorHacspec>;
// pub type BidRemain = Option<(UserAddress, u64)>;

pub fn auction_finalize_hacspec(
    ctx: FinalizeContext,
    state: StateHacspec,
) -> AuctionFinalizeResult {
    let StateHacspec(mut auction_state, highest_bid, st2, expiry, SeqMap(m0, m1)) = state.clone();

    let mut result = AuctionFinalizeResult::Ok((state.clone(), FinalizeAction::Accept));

    if !(auction_state == AuctionStateHacspec::NotSoldYet) {
        AuctionFinalizeResult::Err(FinalizeErrorHacspec::AuctionFinalized)?;
    }

    let (slot_time, owner, balance) = ctx;

    if !(slot_time > expiry) {
        AuctionFinalizeResult::Err(FinalizeErrorHacspec::AuctionStillActive)?;
    }

    if balance != 0_u64 {
        let mut return_action = FinalizeAction::SimpleTransfer(
            PublicByteSeq::new(0_usize)
                .concat(&owner)
                .concat(&u64_to_be_bytes(highest_bid)),
        );
        let mut remaining_bid = BidRemain::BidNone;
        // Return bids that are smaller than highest
        // let x = 0;
        for x in 0..m0.clone().len() / 32 {
            let addr = UserAddress::from_seq(&m0.clone().slice(x * 32, 32));
            let amnt = u64_from_be_bytes(u64Word::from_seq(&m1.clone().slice(x * 8, 8)));
            if amnt < highest_bid {
                return_action = match return_action {
                    FinalizeAction::Accept => FinalizeAction::Accept, // TODO: What error (should never happen)..
                    FinalizeAction::SimpleTransfer(m) => FinalizeAction::SimpleTransfer(
                        m.concat(&addr).concat(&u64_to_be_bytes(amnt)),
                    ),
                };
            } else {
                // ensure!(remaining_bid.is_none(), FinalizeErrorHacspec::BidMapError);
                if !(remaining_bid == BidRemain::BidNone) {
                    AuctionFinalizeResult::Err(FinalizeErrorHacspec::BidMapError)?;
                }
                auction_state = AuctionStateHacspec::Sold(addr);
                remaining_bid = BidRemain::BidSome(amnt);
            }
        }

        // ensure that the only bidder left in the map is the one with the highest bid
        result = match remaining_bid {
            BidRemain::BidSome(amount) =>
            // ensure!(amount == state.highest_bid, FinalizeErrorHacspec::BidMapError);
            {
                if !(amount == highest_bid) {
                    AuctionFinalizeResult::Err(FinalizeErrorHacspec::BidMapError)
                } else {
                    AuctionFinalizeResult::Ok((
                        StateHacspec(
                            auction_state,
                            highest_bid,
                            st2,
                            expiry,
                            SeqMap(m0.clone(), m1.clone()),
                        ),
                        return_action,
                    ))
                }
            }
            BidRemain::BidNone => AuctionFinalizeResult::Err(FinalizeErrorHacspec::BidMapError),
        };

        result.clone()?;
    }

    result
}

#[cfg(not(feature = "hacspec"))]
fn simple_transfer_from_index_and_seq<A: HasActions>(x: usize, s: PublicByteSeq) -> A {
    A::simple_transfer(
        &coerce_hacspec_to_rust_account_address(UserAddress::from_seq(
            &s.slice(x * (32 + 8), 32), // TODO: use chunks instead of doing the math yourself
        )),
        Amount {
            micro_ccd: u64_from_be_bytes(u64Word::from_seq(&s.slice(x * (32 + 8) + 32, 8))),
        },
    )
}

#[cfg(feature = "hacspec")]
/// Receive function in which accounts can bid before the auction end time
#[receive(contract = "auction", name = "finalize")]
fn auction_finalize(
    ctx: ContextStateHacspec,
) -> Option<(ContextStateHacspec, ListAction)> {
    let s = Seq::<HasAction>::new(0);
    Option::<(ContextStateHacspec, ListAction)>::Some((ctx, s))
}

#[cfg(not(feature = "hacspec"))]
/// Receive function used to finalize the auction, returning all bids to their
/// senders, except for the winning bid
#[receive(contract = "auction", name = "finalize")]
fn auction_finalize<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> Result<A, FinalizeError> {
    let hacspec_state = coerce_rust_to_hacspec_state(state);

    let (new_state, fa) =
        match auction_finalize_hacspec(coerce_rust_to_hacspec_finalize_context(ctx), hacspec_state)
        {
            Ok(a) => a,
            Err(e) => return Err(coerce_hacspec_to_rust_finalize_error(e)),
        };

    *state = coerce_hacspec_to_rust_state(new_state);

    match fa {
        FinalizeAction::Accept => Ok(A::accept()),
        FinalizeAction::SimpleTransfer(s) => Ok((1..s.len() / (32 + 8))
            .fold(simple_transfer_from_index_and_seq(0, s.clone()), |t, x| {
                t.and_then(simple_transfer_from_index_and_seq(x, s.clone()))
            })),
    }
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

#[ensures(result == true)]
#[cfg(test)]
#[proof]
#[quickcheck]
/// Test that the smart-contract initialization sets the state correctly
/// (no bids, active state, indicated auction-end time and item name).
pub fn auction_test_init(item: PublicByteSeq, time : u64) -> bool {
    fresh_state_hacspec(item.clone(), time)
	== StateHacspec(
	    AuctionStateHacspec::NotSoldYet,
	    0_u64,
	    item.clone(),
	    time,
	    SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
	)
}


#[cfg(test)]
#[proof]
fn verify_bid(
    item: PublicByteSeq,
    state: StateHacspec,
    account: UserAddress,
    ctx: Context,
    amount: u64,
    bid_map: SeqMap,
    highest_bid: u64,
    time : u64,
) -> (StateHacspec, SeqMap, bool, bool) {
    let t = auction_bid_hacspec(ctx, amount, state.clone());

    let (state, res) = match t {
	AuctionBidResult::Err(_e) => (state, false),
	AuctionBidResult::Ok(s) => (s, true),
    };

    let bid_map = match seq_map_update_entry(bid_map.clone(), account, highest_bid) {
	MapUpdate::Update(_, updated_map) => updated_map,
    };

    (
	state.clone(),
	bid_map.clone(),
	res,
	state.clone()
	    == StateHacspec(
		AuctionStateHacspec::NotSoldYet,
		highest_bid,
		item.clone(),
		time,
		bid_map.clone(),
	    ),
    )
}


#[cfg(test)]
#[proof]
fn useraddress_from_u8(i : u8) -> UserAddress {
    UserAddress([
	i, i, i, i, i, i, i, i, i, i, i, i, i, i, i,
	i, i, i, i, i, i, i, i, i, i, i, i, i, i, i,
	i, i,
    ])
}

#[cfg(test)]
#[proof]
fn new_account(time : u64, i : u8) -> (UserAddress, Context) {
    let addr = useraddress_from_u8(i);
    let ctx = Context(addr, addr, 0u64, time);
    (addr, ctx)
}

#[cfg(test)]
#[proof]
// #[quickcheck]
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
// TODO: Requires
// #[requires(18446744073709551615u64 > time)]
// #[requires(18446744073709551615u64 / 5u64 - 1u64 > input_amount)]
#[ensures(result == true)]
#[quickcheck]
fn test_auction_bid_and_finalize(item: PublicByteSeq, time : u64, input_amount : u64) -> bool {
    let time = if time == 18446744073709551615u64 { 18446744073709551614u64 } else { time }; // Can overflow !
    let input_amount : u64 = if input_amount > 18446744073709551615u64 / 5u64 - 1u64 { 100u64 } else { input_amount };

    let amount = input_amount + 1_u64;
    let winning_amount = amount * 3_u64; // 300_u64;
    let big_amount = amount * 5_u64; // 500_u64;

    let bid_map = SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize));

    // initializing auction
    let state = fresh_state_hacspec(item.clone(), time); // mut

    // 1st bid: account1 bids amount1
    let (alice, alice_ctx) = new_account(time, 0_u8);

    let Context(_, ac0, _, ac1) = alice_ctx;

    let (state, bid_map, _res_0, result_0) = verify_bid(
	item.clone(),
	state,
	alice,
	alice_ctx,
	amount,
	bid_map,
	amount,
	time,
    );

    // // 2nd bid: account1 bids `amount` again
    // // should work even though it's the same amount because account1 simply
    // // increases their bid
    let (state, bid_map, _res_1, result_1) = verify_bid(
	item.clone(),
	state,
	alice,
	alice_ctx,
	amount,
	bid_map,
	amount + amount,
	time,
    );

    // // 3rd bid: second account
    let (bob, bob_ctx) = new_account(time, 1_u8); // first argument is slot time
    let Context(_, bc1, _, bc2) = bob_ctx;

    let (state, bid_map, _res_2, result_2) = verify_bid(
	item.clone(),
	state,
	bob,
	bob_ctx,
	winning_amount,
	bid_map,
	winning_amount,
	time,
    );

    let owner = useraddress_from_u8(0_u8);

    // let sender = owner;
    let balance = 100_u64;
    let ctx4 = (time, owner, balance);

    let finres = auction_finalize_hacspec(ctx4, state.clone());
    let (state, result_3) = match finres {
	AuctionFinalizeResult::Err(err) => (
	    state.clone(),
	    err == FinalizeErrorHacspec::AuctionStillActive
	),
	AuctionFinalizeResult::Ok((state, _)) => (state, false),
    };

    // // finalizing auction
    // let carol = new_account();
    let (carol, _carol_ctx) = new_account(time, 2_u8);

    let ctx5 = (time + 1_u64, carol, winning_amount);
    let finres2 = auction_finalize_hacspec(ctx5, state.clone());

    let (state, result_4) = match finres2 {
	AuctionFinalizeResult::Err(_) => (state.clone(), false),
	AuctionFinalizeResult::Ok((state, action)) => (
	    state,
	    action
		== FinalizeAction::SimpleTransfer(
		    PublicByteSeq::new(0_usize)
			.concat(&carol)
			.concat(&u64_to_be_bytes(winning_amount))
			.concat(&alice)
			.concat(&u64_to_be_bytes(amount + amount)),
		),
	),
    };

    let result_5 = state.clone()
	== StateHacspec(
	    AuctionStateHacspec::Sold(bob),
	    winning_amount,
	    item.clone(),
	    time,
	    bid_map.clone(),
	);

    // attempting to finalize auction again should fail
    let finres3 = auction_finalize_hacspec(ctx5, state.clone());

    let (state, result_6) = match finres3 {
	AuctionFinalizeResult::Err(err) => (state, err == FinalizeErrorHacspec::AuctionFinalized),
	AuctionFinalizeResult::Ok((state, _action)) => (state, false),
    };

    let t = auction_bid_hacspec(bob_ctx, big_amount, state.clone());

    // let result_7 = t == AuctionBidResult::Err (BidErrorHacspec::AuctionIsFinalized);
    let result_7 = match t {
	AuctionBidResult::Err(e) => e == BidErrorHacspec::AuctionIsFinalized,
	AuctionBidResult::Ok(_) => false,
    };

    result_0 && result_1 && result_2 && result_3 && result_4 && result_5 && result_6 && result_7
}

#[cfg(not(feature = "hacspec"))]
#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU8, Ordering};
    use test_infrastructure::*;

    // A counter for generating new account addresses
    static ADDRESS_COUNTER: AtomicU8 = AtomicU8::new(0);
    const AUCTION_END: u64 = 1;
    const ITEM: &str = "Starry night by Van Gogh";

    fn dummy_fresh_state() -> State {
	dummy_active_state(Amount::zero(), BTreeMap::new())
    }

    fn dummy_active_state(highest: Amount, bids: BTreeMap<AccountAddress, Amount>) -> State {
	State {
	    auction_state: AuctionState::NotSoldYet,
	    highest_bid: highest,
	    item: ITEM.as_bytes().to_vec(),
	    expiry: Timestamp::from_timestamp_millis(AUCTION_END),
	    bids,
	}
    }

    fn expect_error<E, T>(expr: Result<T, E>, err: E, msg: &str)
    where
	E: Eq + Debug,
	T: Debug,
    {
	let actual = expr.expect_err(msg);
	assert_eq!(actual, err);
    }

    fn item_expiry_parameter() -> InitParameter {
	InitParameter {
	    item: ITEM.as_bytes().to_vec(),
	    expiry: Timestamp::from_timestamp_millis(AUCTION_END),
	}
    }

    fn create_parameter_bytes(parameter: &InitParameter) -> Vec<u8> {
	to_bytes(parameter)
    }

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

    #[test]
    /// Test that the smart-contract initialization sets the state correctly
    /// (no bids, active state, indicated auction-end time and item name).
    fn test_init() {
	let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
	let ctx = parametrized_init_ctx(&parameter_bytes);

	let state_result = auction_init(&ctx);
	let state = state_result.expect("Contract initialization results in error");
	assert_eq!(
	    state,
	    dummy_fresh_state(),
	    "Auction state should be new after initialization"
	);
    }

    #[test]
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

	let amount = Amount::from_micro_ccd(100);
	let winning_amount = Amount::from_micro_ccd(300);
	let big_amount = Amount::from_micro_ccd(500);

	let mut bid_map = BTreeMap::new();

	// initializing auction
	let mut state = auction_init(&ctx0).expect("Initialization should pass");

	// 1st bid: account1 bids amount1
	let (alice, alice_ctx) = new_account_ctx();
	verify_bid(&mut state, alice, &alice_ctx, amount, &mut bid_map, amount);

	// 2nd bid: account1 bids `amount` again
	// should work even though it's the same amount because account1 simply
	// increases their bid
	verify_bid(
	    &mut state,
	    alice,
	    &alice_ctx,
	    amount,
	    &mut bid_map,
	    amount + amount,
	);


	// 3rd bid: second account
	let (bob, bob_ctx) = new_account_ctx();
	verify_bid(
	    &mut state,
	    bob,
	    &bob_ctx,
	    winning_amount,
	    &mut bid_map,
	    winning_amount,
	);

	// trying to finalize auction that is still active
	// (specifically, the bid is submitted at the last moment, at the AUCTION_END
	// time)
	let mut ctx4 = ReceiveContextTest::empty();
	ctx4.set_metadata_slot_time(Timestamp::from_timestamp_millis(AUCTION_END));
	ctx4.set_owner(bob); // TODO: If not set fails in coercion value never used because it fails early. Is this a bug in the implementation or a feature that needs to be mimiced in hacspec.
	ctx4.set_self_balance(winning_amount); // TODO: If not set fails in coercion value never used because it fails early. Is this a bug in the implementation or a feature that needs to be mimiced in hacspec.
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

	assert_eq!(
	    state,
	    State {
		auction_state: AuctionState::Sold(bob),
		highest_bid: winning_amount,
		item: ITEM.as_bytes().to_vec(),
		expiry: Timestamp::from_timestamp_millis(AUCTION_END),
		bids: bid_map,
	    }
	);


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

    #[test]
    /// Bids for amounts lower or equal to the highest bid should be rejected.
    fn test_auction_bid_repeated_bid() {
	let (account1, ctx1) = new_account_ctx();
	let ctx2 = new_account_ctx().1;

	let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
	let ctx0 = parametrized_init_ctx(&parameter_bytes);

	let amount = Amount::from_micro_ccd(100);

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

    #[test]
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
}
