use hacspec_lib::*;

array!(UserAddress, 32, u8); // U8

pub enum AuctionState {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction is over and the item has been sold to the indicated address.
    Sold(UserAddress), // winning account's address
}
// #[repr(transparent)]
// #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// #[cfg_attr(feature = "fuzz", derive(Arbitrary))]
// pub struct Timestamp {
//     /// Milliseconds since unix epoch.
//     pub(crate) milliseconds: u64,
// }

// pub type SeqMap = Seq<(UserAddress, u64)>;
// pub type SeqMap = (Seq<u8>, Seq<u64>);
pub type SeqMap = (PublicByteSeq, PublicByteSeq);

// auction_state, highest_bid, item, expiry, bids
pub type State = (AuctionState, u64, Seq<u8>, u64, SeqMap);

pub fn fresh_state (itm: Seq<u8>, exp: u64) -> State {
    (AuctionState::NotSoldYet, 0_u64, itm, exp, (PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)))
}

pub enum BidError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionFinalized,                      /* raised if bid is placed after auction has been
                                            * finalized */
}

pub type UserAddressSet = Option<UserAddress>;
pub type Context = (u64, UserAddressSet);
pub type FinalizeContext = (u64, UserAddress, u64);

pub enum MapEntry {
    Entry (u64,SeqMap),
}

// .entry(sender_address).or_insert_with(Amount::zero)
fn seq_map_entry(m : SeqMap, sender_address : UserAddress) -> MapEntry {
    let (m1, m2) = m.clone();
    let mut res = MapEntry::Entry (0_u64, (m1.clone().concat(&sender_address), m2.clone().concat(&u64_to_be_bytes(0_u64))));

    for x in 0..m1.clone().len() / 32 {
        if UserAddress::from_seq(&m1.clone().slice(x * 32,32)) == sender_address {
            res = MapEntry::Entry (u64_from_be_bytes(u64Word::from_seq(&m2.slice(x * 8, 8))), m.clone());
        }
    }

    res
}

pub enum MapUpdate {
    Update (u64,SeqMap),
}

fn seq_map_update_entry(m : SeqMap, sender_address : UserAddress, amount : u64) -> MapUpdate {
    let (m1, m2) = m;
    // let (m1, m2) = (m1.reserve(32), m2.reserve(8));

    let mut res = MapUpdate::Update(amount, (m1.concat(&sender_address), m2.concat(&u64_to_be_bytes(amount))));

    for x in 0..m1.clone().len() / 32 {        
        if UserAddress::from_seq(&m1.clone().slice(x * 32,32)) == sender_address {
            res = MapUpdate::Update(amount, (m1.clone().update(x * 32, &sender_address), m2.clone().update(x * 8, &u64_to_be_bytes(amount))));
        }
    }

    res
}

pub type AuctionBidResult = Result<(), BidError>;

pub fn auction_bid(
    ctx: Context,
    amount: u64,
    state: State,
) -> (State, AuctionBidResult)
{
    // ensure!(state.auction_state == AuctionState::NotSoldYet, BidError::AuctionFinalized);
    let (auction_state, b, c, expiry, e) = state;
    let (slot_time, sender) = ctx;

    let ((acs, upb, ce, expirye, (updated1_mape, updated2_mape)), rese) = match auction_state {
        AuctionState::NotSoldYet =>
            if slot_time <= expiry {
                match sender {
                    UserAddressSet::None => ((auction_state,b,c,expiry,e), AuctionBidResult::Err(BidError::ContractSender)),
                    UserAddressSet::Some (sender_address) =>
                        match seq_map_entry(e.clone(), sender_address) {
                            MapEntry::Entry (bid_to_update, new_map) =>
                                match seq_map_update_entry(new_map.clone(), sender_address, bid_to_update + amount) {
                                    MapUpdate::Update (updated_bid, updated_map) =>
                                        if updated_bid > b {
                                            ((auction_state, updated_bid, c, expiry, updated_map), AuctionBidResult::Ok(()))
                                        } else {
                                            ((auction_state, b, c, expiry, updated_map), AuctionBidResult::Err(BidError::BidTooLow))
                                        },
                                },
                        },
                }
            }
        else {
            ((auction_state,b,c,expiry,e), AuctionBidResult::Err(BidError::BidsOverWaitingForAuctionFinalization))
        },
        AuctionState::Sold (_) => ((auction_state,b,c,expiry,e), AuctionBidResult::Err(BidError::AuctionFinalized))
    };


    ((acs, upb, ce, expirye, (updated1_mape, updated2_mape)), rese)
}

/// For errors in which the `finalize` function can result
pub enum FinalizeError {
    BidMapError,        /* raised if there is a mistake in the bid map that keeps track of all
                         * accounts' bids */
    AuctionStillActive, // raised if there is an attempt to finalize the auction before its expiry
    AuctionFinalized,   // raised if there is an attempt to finalize an already finalized auction
}

pub enum FinalizeAction {
    Accept,
    SimpleTransfer(UserAddress, u64, PublicByteSeq),
}

pub enum BidRemain {
    None,
    Some(u64),
}

pub fn auction_finalize(
    ctx: FinalizeContext,
    state: State,
) -> (State, Result<FinalizeAction, FinalizeError>) {
    let (mut auction_state, b, c, expiry, (m1,m2)) = state;
    let (slot_time, owner, balance) = ctx;

    println!("SXEP {} {}", slot_time , expiry);
    
    let (continues, mut return_action) = match auction_state {
        AuctionState::NotSoldYet =>
            if slot_time > expiry {
                if balance == 0 {
                    (false, Ok(FinalizeAction::Accept))
                }
                else {
                    (true, Ok(FinalizeAction::SimpleTransfer(owner, b, PublicByteSeq::new(0_usize))))
                }
            } else {
                (false, Err(FinalizeError::AuctionStillActive))
            },
        AuctionState::Sold (_) => (false, Err(FinalizeError::AuctionFinalized)),
    };

    let result = if continues {
        let mut remaining_bid = BidRemain::None;
        // Return bids that are smaller than highest
        // let aucstate = auction_state;
        for x in 0..m1.clone().len() / 32 {
            let amnt = u64_from_be_bytes(u64Word::from_seq(&m2.slice(x * 8, 8)));
            let addr = UserAddress::from_seq(&m1.clone().slice(x * 32,32));
            if amnt < b {
                return_action = match return_action {
                    Ok(FinalizeAction::SimpleTransfer(o,b,a)) => Ok(FinalizeAction::SimpleTransfer(o,b,a.concat(&addr).concat(&u64_to_be_bytes(amnt)))),
                    Ok(FinalizeAction::Accept) => Ok(FinalizeAction::Accept),
                    Err(e) => Err(e),
                };
            }
            else {
                match remaining_bid {
                    BidRemain::None => {auction_state = AuctionState::Sold(addr); remaining_bid = BidRemain::Some(amnt)},
                    BidRemain::Some (_) => return_action = Err(FinalizeError::BidMapError),
                };
            }
        }

        // Ensure that the only bidder left in the map is the one with the highest bid
        let res =
            match return_action {
                Ok (_) =>
                    match remaining_bid {
                        BidRemain::Some(amount) => {
                            if amount == b {
                                return_action
                            }
                            else {
                                Err(FinalizeError::BidMapError)
                            }
                        }
                        BidRemain::None => Err(FinalizeError::BidMapError),
                    },
                Err (e) => Err (e)
            };

        ((auction_state, b, c, expiry, (m1,m2)), res)

    } else {
        ((auction_state, b, c, expiry, (m1,m2)), return_action)
    };

    result
}
