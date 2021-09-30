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

pub type SeqMap = Seq<(UserAddress, u64)>;

// auction_state, highest_bid, item, expiry, bids
pub type State = (AuctionState, u64, Seq<u8>, u64, SeqMap);

pub fn fresh_state (itm: Seq<u8>, exp: u64) -> State {
    (AuctionState::NotSoldYet, 0_u64, itm, exp, Seq::new(0))    
}

pub enum BidError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionFinalized,                      /* raised if bid is placed after auction has been
                                            * finalized */
}

pub type Context = (u64, Option<UserAddress>);

// .entry(sender_address).or_insert_with(Amount::zero)
fn seq_map_entry(m : SeqMap, sender_address : UserAddress) -> (u64,SeqMap) {
    match m.iter().find(|&&x| x.0 == sender_address) {
        None => (0_u64, m.concat(&Seq::from_native_slice(&[(sender_address, 0_u64)]))),
        Some ((a,b)) => (*b, m),
    }
}

fn seq_map_update_entry(m : SeqMap, sender_address : UserAddress, amount : u64) -> SeqMap {
    m.concat(&Seq::from_native_slice(&[(sender_address, amount)]))
}

pub fn auction_bid(
    ctx: Context,
    amount: u64,
    state: State,
) -> (State, Result<(), BidError>) {
    // ensure!(state.auction_state == AuctionState::NotSoldYet, BidError::AuctionFinalized);
    let (auction_state, b, c, expiry, e) = state;
    match auction_state {
        AuctionState::NotSoldYet => {
            let (slot_time, sender) = ctx; // .metadata().slot_time()
            // ensure!(slot_time <= state.expiry, BidError::BidsOverWaitingForAuctionFinalization);
            if (slot_time <= expiry) {
                match sender {
                    None => ((auction_state,b,c,expiry,e), Err(BidError::ContractSender)),
                    Some (sender_address) => {
                        // let sender_address = match ctx.sender() {
                        //     Address::Contract(_) => bail!(BidError::ContractSender),
                        //     Address::Account(account_address) => account_address,
                        // };

                        let (bid_to_update, new_map) = seq_map_entry(e.clone(), sender_address);
                        let updated_bid = bid_to_update + amount;
                        let updated_map = seq_map_update_entry(new_map.clone(), sender_address, updated_bid);

                        // *bid_to_update += amount;
                        // // Ensure that the new bid exceeds the highest bid so far

                        if (updated_bid > b) {
                        
                        // ensure!(
                        //     *bid_to_update > state.highest_bid,
                        //     BidError::BidTooLow /* { bid: amount, highest_bid: state.highest_bid } */
                            // );
                            
                            // state.highest_bid = *bid_to_update;
                            
                            ((auction_state,updated_bid,c,expiry,updated_map), Ok(()))
                        }
                        else {
                            ((auction_state,b,c,expiry,updated_map), Err(BidError::BidTooLow))
                        }
                    }
                }
                
            } else {
                ((auction_state,b,c,expiry,e), Err(BidError::BidsOverWaitingForAuctionFinalization))
            }
        }
        _ => ((auction_state,b,c,expiry,e), Err(BidError::AuctionFinalized))
    }
}
