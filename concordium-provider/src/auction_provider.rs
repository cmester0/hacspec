use concordium_std::{collections::BTreeMap, *};
use core::fmt::Debug;
use crate::provider::Action;
use auction::*;
use hacspec_lib::*;

/// # Implementation of an auction smart contract
///
/// To bid, participants send GTU using the bid function.
/// The participant with the highest bid wins the auction.
/// Bids are to be placed before the auction end. After that, bids are refused.
/// Only bids that exceed the highest bid are accepted.
/// Bids are placed incrementally, i.e., an account's bid is considered
/// to be the **sum** of all bids.
///
/// Example: if Alice first bid 1 GTU and then bid 2 GTU, her total
/// bid is 3 GTU. The bidding will only go through if 3 GTU is higher than
/// the currently highest bid.
///
/// After the auction end, any account can finalize the auction.
/// The auction can be finalized only once.
/// When the auction is finalized, every participant except the
/// winner gets their money back.

/// The state in which an auction can be.
#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub enum AuctionState {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction is over and the item has been sold to the indicated address.
    Sold(AccountAddress), // winning account's address
}

/// The state of the smart contract.
/// This is the state that will be shown when the contract is queried using
/// `concordium-client contract show`.
#[contract_state(contract = "auction")]
#[derive(Debug, Serialize, SchemaType, Eq, PartialEq)]
pub struct State {
    /// Has the item been sold?
    auction_state: AuctionState,
    /// The highest bid so far (stored explicitly so that bidders can quickly
    /// see it)
    highest_bid:   concordium_std::Amount,
    /// The sold item (to be displayed to the auction participants), encoded in
    /// ASCII
    item:          Vec<u8>,
    /// Expiration time of the auction at which bids will be closed (to be
    /// displayed to the auction participants)
    expiry:        concordium_std::Timestamp,
    /// Keeping track of which account bid how much money
    #[concordium(size_length = 2)]
    bids:          BTreeMap<AccountAddress, concordium_std::Amount>,
}

fn user_address_to_accout_address (acc : UserAddress) -> AccountAddress {
    AccountAddress (
        [acc[0],
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

fn my_auction_state_to_their_auction_state(s : auction::AuctionState) -> AuctionState {
    match s {
        auction::AuctionState::NotSoldYet => AuctionState::NotSoldYet,
        auction::AuctionState::Sold (a) => AuctionState::Sold (user_address_to_accout_address(a)),
    }
}


fn seq_map_to_btree_map (m : SeqMap) -> BTreeMap<AccountAddress, concordium_std::Amount> {
    let (m1,m2) = m;

    let m1prime = (0..m1.len() / 32).map(|x| UserAddress::from_seq(&m1.clone().slice(x * 32,32)));
    let m2prime = (0..m2.len() / 8).map(|x| u64_from_be_bytes(u64Word::from_seq(&m2.slice(x * 8, 8))));

    (m1prime.zip(m2prime)).fold(BTreeMap::new(), |mut t, (x, y)| { t.insert(user_address_to_accout_address (x), concordium_std::Amount { micro_gtu: y }); t } )
}


fn my_state_to_their_state (s : auction::State) -> State {
    let (a,b,c,d,e) = s;
    State {
        auction_state: my_auction_state_to_their_auction_state(a),
        highest_bid: concordium_std::Amount { micro_gtu: b },
        item: c.native_slice().to_vec(),
        expiry: concordium_std::Timestamp::from_timestamp_millis(d),
        bids: seq_map_to_btree_map(e),
    }
}

/// A helper function to create a state for a new auction.
fn fresh_state(itm: Vec<u8>, exp: concordium_std::Timestamp) -> State {
    my_state_to_their_state(auction::fresh_state(Seq::from_vec(itm), exp.timestamp_millis()))
}

/// Type of the parameter to the `init` function.
#[derive(Serialize, SchemaType)]
pub struct InitParameter {
    /// The item to be sold, as a sequence of ASCII codes.
    item:   Vec<u8>,
    /// Time of the auction end in the RFC 3339 format (https://tools.ietf.org/html/rfc3339)
    expiry: concordium_std::Timestamp,
}

/// For errors in which the `bid` function can result
#[derive(Debug, PartialEq, Eq, Clone, Reject)]
pub enum BidError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionFinalized,                      /* raised if bid is placed after auction has been
                                            * finalized */
}

/// For errors in which the `finalize` function can result
#[derive(Debug, PartialEq, Eq, Clone, Reject)]
pub enum FinalizeError {
    BidMapError,        /* raised if there is a mistake in the bid map that keeps track of all
                         * accounts' bids */
    AuctionStillActive, // raised if there is an attempt to finalize the auction before its expiry
    AuctionFinalized,   // raised if there is an attempt to finalize an already finalized auction
}

/// Init function that creates a new auction
#[init(contract = "auction", parameter = "InitParameter")]
pub fn auction_init(ctx: &impl HasInitContext) -> InitResult<State> {
    let parameter: InitParameter = ctx.parameter_cursor().get()?;
    Ok(fresh_state(parameter.item, parameter.expiry))
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

fn their_auction_state_to_my_auction_state (s : AuctionState) -> auction::AuctionState {
    match s {
        AuctionState::NotSoldYet => auction::AuctionState::NotSoldYet,
        AuctionState::Sold (a) => auction::AuctionState::Sold (u8x32_to_user_address(a.0)),
    }
}

fn btree_map_to_seq_map (m : BTreeMap<AccountAddress, concordium_std::Amount>) -> SeqMap {
    (m.keys().map(|x| u8x32_to_user_address(x.0)).fold(PublicByteSeq::new(0_usize), |v,x| v.concat(&x)),
     m.values().map(|x| x.micro_gtu).fold(PublicSeq::new(0_usize), |v, x| v.concat(&u64_to_be_bytes(x))))

    // Seq::from_vec(m.keys().map(|x| u8x32_to_user_address(x.0)).zip(m.values().map(|(x)| x.micro_gtu)).collect())
}

fn their_state_to_my_state (s : &mut State) -> auction::State {
(their_auction_state_to_my_auction_state(s.auction_state.clone()),s.highest_bid.micro_gtu,Seq::from_vec(s.item.clone()),s.expiry.timestamp_millis(),btree_map_to_seq_map(s.bids.clone()))
}

fn their_context_to_my_context (ctx: &impl HasReceiveContext) -> auction::Context {
    (ctx.metadata().slot_time().timestamp_millis(),
     match ctx.sender() {
         Address::Contract(_) => UserAddressSet::UserAddressNone,
         Address::Account(account_address) => UserAddressSet::UserAddressSome (u8x32_to_user_address(account_address.0), ()),
     })
}

fn their_context_to_my_finalize_context (ctx: &impl HasReceiveContext) -> auction::FinalizeContext {
    (ctx.metadata().slot_time().timestamp_millis(),
     u8x32_to_user_address(ctx.owner().0),
     ctx.self_balance().micro_gtu)
}

/// Receive function in which accounts can bid before the auction end time
#[receive(contract = "auction", name = "bid", payable)]
pub fn auction_bid<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: concordium_std::Amount,
    state: &mut State,
) -> Result<A, BidError> {
    let (new_state, res) = auction::auction_bid(their_context_to_my_context(ctx), amount.micro_gtu, their_state_to_my_state(state));
    *state = my_state_to_their_state(new_state);
    
    match res {
        Ok(_) => Ok(A::accept()),
        Err(auction::BidError::ContractSender) =>                        Err(BidError::ContractSender),
        Err(auction::BidError::BidTooLow) =>                             Err(BidError::BidTooLow),
        Err(auction::BidError::BidsOverWaitingForAuctionFinalization) => Err(BidError::BidsOverWaitingForAuctionFinalization),
        Err(auction::BidError::AuctionIsFinalized) =>                    Err(BidError::AuctionFinalized),
    }
}

/// Receive function used to finalize the auction, returning all bids to their
/// senders, except for the winning bid
#[receive(contract = "auction", name = "finalize")]
pub fn auction_finalize<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> Result<A, FinalizeError> {
    let (new_state, res) = auction::auction_finalize(their_context_to_my_finalize_context(ctx), their_state_to_my_state(state));
    *state = my_state_to_their_state(new_state);
    
    match res {
        Ok(FinalizeAction::Accept) => {println!("ACCEPT"); Ok(A::accept())},
        Ok(FinalizeAction::SimpleTransfer(owner, b, s)) =>
            {println!("Simple Transfer"); 
            Ok((0..s.len() / (32+8))
               .fold(A::simple_transfer(&user_address_to_accout_address(owner), concordium_std::Amount { micro_gtu: b }),
                     |t,x| t.and_then(A::simple_transfer(
                         &user_address_to_accout_address(UserAddress::from_seq(&s.slice(x * (32+8), 32))),
                         concordium_std::Amount { micro_gtu: u64_from_be_bytes(u64Word::from_seq(&s.slice(x * (32+8) + 32,8))) })
                     )))},
        Err(auction::FinalizeError::BidMapError) => {println!("Bid map error"); Err(FinalizeError::BidMapError)},
        Err(auction::FinalizeError::AuctionStillActive) => {println!("Auction still alive"); Err(FinalizeError::AuctionStillActive)},
        Err(auction::FinalizeError::AuctionFinalized) => {println!("Auction finalized"); Err(FinalizeError::AuctionFinalized)},
    }
}

/// functions used for testing

const AUCTION_END: u64 = 1;
const ITEM: &str = "Starry night by Van Gogh";

pub fn dummy_fresh_state() -> State { dummy_active_state(concordium_std::Amount::zero(), BTreeMap::new()) }

pub fn dummy_active_state(highest: concordium_std::Amount, bids: BTreeMap<AccountAddress, concordium_std::Amount>) -> State {
    // State {
    //     auction_state: my_auction_state_to_their_auction_state(a),
    //     highest_bid: Amount { micro_gtu: b },
    //     item: c.native_slice().to_vec(),
    //     expiry: Timestamp::from_timestamp_millis(d),
    //     bids: seq_map_to_btree_map(e),
    // }
    
    State {
        auction_state: AuctionState::NotSoldYet,
        highest_bid: highest,
        item: ITEM.as_bytes().to_vec(),
        expiry: concordium_std::Timestamp::from_timestamp_millis(AUCTION_END),
        bids: bids,
    }
}

pub fn make_state (
    auction_state: AuctionState,
    highest_bid:   concordium_std::Amount,
    item:          Vec<u8>,
    expiry:        concordium_std::Timestamp,
    bids:          BTreeMap<AccountAddress, concordium_std::Amount>) -> State {
    State {
        auction_state: auction_state,
        highest_bid: highest_bid,
        item: item,
        expiry: expiry,
        bids: bids,
    }
}

// pub fn instantiate_state () {
//     auction_state: AuctionState::Sold(bob),
//     highest_bid:   winning_amount,
//     item:          ITEM.as_bytes().to_vec(),
//     expiry:        Timestamp::from_timestamp_millis(AUCTION_END),
//     bids:          bid_map,    
// }

pub fn item_expiry_parameter() -> InitParameter {
    InitParameter {
        item:   ITEM.as_bytes().to_vec(),
        expiry: concordium_std::Timestamp::from_timestamp_millis(AUCTION_END),
    }
}
