use hacspec_lib::*;

array!(UserAddress, 32, u8); // U8

#[derive(Clone, PartialEq)]
pub enum AuctionState {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction is over and the item has been sold to the indicated address.
    Sold(UserAddress), // winning account's address
}

#[derive(Clone, PartialEq)]
pub struct SeqMap(pub PublicByteSeq, pub PublicByteSeq);

pub type Amount = u64;
pub type Timestamp = u64;

pub type Itemtyp = PublicByteSeq; // Seq<u8>;

#[derive(Clone, PartialEq)]
pub struct State(
    pub AuctionState,
    pub Amount,
    pub Itemtyp,
    pub Timestamp,
    pub SeqMap,
);

pub fn fresh_state(itm: Itemtyp, exp: u64) -> State {
    State(
        AuctionState::NotSoldYet,
        0_u64,
        itm,
        exp,
        SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
    )
}

#[derive(Clone, PartialEq)]
pub enum MapEntry {
    Entry(u64, SeqMap),
}

fn seq_map_entry(m: SeqMap, sender_address: UserAddress) -> MapEntry {
    let SeqMap(m0, m1) = m;

    let mut res = MapEntry::Entry(
        0_u64,
        SeqMap(
            m0.clone().concat(&sender_address),
            m1.clone().concat(&u64_to_be_bytes(0_u64)),
        ),
    );

    for x in 0..m0.clone().len() / 32 {
        if UserAddress::from_seq(&m0.clone().slice(x * 32, 32)) == sender_address {
            res = MapEntry::Entry(
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

#[derive(Clone, PartialEq)]
pub enum BidError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionIsFinalized,                    /* raised if bid is placed after auction has been
                                            * finalized */
}

// pub type UserAddressSet = Option<UserAddress>;
#[derive(Clone, PartialEq)]
pub enum UserAddressSet {
    UserAddressSome(UserAddress),
    UserAddressNone,
}
pub type Context = (u64, UserAddressSet);
pub type AuctionBidResult = Result<State, BidError>;

pub fn auction_bid(ctx: Context, amount: u64, state: State) -> AuctionBidResult {
    let State(auction_state, highest_bid, st2, expiry, st4) = state.clone();

    if !(auction_state == AuctionState::NotSoldYet) {
        AuctionBidResult::Err(BidError::AuctionIsFinalized)?;
    }

    let (slot_time, sender) = ctx;
    if !(slot_time <= expiry) {
        AuctionBidResult::Err(BidError::BidsOverWaitingForAuctionFinalization)?;
    }

    if sender == UserAddressSet::UserAddressNone {
        AuctionBidResult::Err(BidError::ContractSender)?;
    }

    let sender_address = match sender {
        UserAddressSet::UserAddressNone => UserAddress([
            5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8,
            5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8, 5_u8,
            5_u8, 5_u8, 5_u8, 5_u8,
        ]), // should never happen
        UserAddressSet::UserAddressSome(account_address) => account_address,
    };

    let (bid_to_update, new_map) = match seq_map_entry(st4.clone(), sender_address) {
        MapEntry::Entry(bid_to_update, new_map) => (bid_to_update, new_map),
    };

    let (updated_bid, updated_map) =
        match seq_map_update_entry(st4.clone(), sender_address, bid_to_update + amount) {
            MapUpdate::Update(updated_bid, updated_map) => (updated_bid, updated_map),
        };

    if !(updated_bid > highest_bid) {
        AuctionBidResult::Err(BidError::BidTooLow)?;
    }

    AuctionBidResult::Ok(State(auction_state, updated_bid, st2, expiry, updated_map))
}

pub type FinalizeContext = (u64, UserAddress, u64);

/// For errors in which the `finalize` function can result
#[derive(Clone, PartialEq)]
pub enum FinalizeError {
    BidMapError,
    AuctionStillActive,
    AuctionFinalized,
}

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

pub type AuctionFinalizeResult = Result<(State, FinalizeAction), FinalizeError>;
// pub type BidRemain = Option<(UserAddress, u64)>;

pub fn auction_finalize(ctx: FinalizeContext, state: State) -> AuctionFinalizeResult {
    let State(mut auction_state, highest_bid, st2, expiry, SeqMap(m0, m1)) = state.clone();

    let mut result = AuctionFinalizeResult::Ok((state.clone(), FinalizeAction::Accept));

    if !(auction_state == AuctionState::NotSoldYet) {
        AuctionFinalizeResult::Err(FinalizeError::AuctionFinalized)?;
    }

    let (slot_time, owner, balance) = ctx;

    if !(slot_time > expiry) {
        AuctionFinalizeResult::Err(FinalizeError::AuctionStillActive)?;
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
                // ensure!(remaining_bid.is_none(), FinalizeError::BidMapError);
                if ! (remaining_bid == BidRemain::BidNone) {
                    AuctionFinalizeResult::Err(FinalizeError::BidMapError)?;
                }
                auction_state = AuctionState::Sold(addr);
                remaining_bid = BidRemain::BidSome(amnt);
            }
        }

        // ensure that the only bidder left in the map is the one with the highest bid
        result = match remaining_bid {
            BidRemain::BidSome(amount) =>
            // ensure!(amount == state.highest_bid, FinalizeError::BidMapError);
            {
                if !(amount == highest_bid) {
                    AuctionFinalizeResult::Err(FinalizeError::BidMapError)
                } else {
                    AuctionFinalizeResult::Ok((
                        State(auction_state, highest_bid, st2, expiry, SeqMap(m0.clone(), m1.clone())),
                        return_action,
                    ))
                }
            }
            BidRemain::BidNone => AuctionFinalizeResult::Err(FinalizeError::BidMapError),
        };

        result.clone()?;
    }

    result
}

// #[cfg(test)]
// extern crate quickcheck;
// #[cfg(test)]
// #[macro_use(quickcheck)]
// extern crate quickcheck_macros;

// #[cfg(test)]
// use quickcheck::*;

#[cfg(proof)]
#[cfg(test)]
pub fn auction_item(a : u64, b : u64, c : u64) -> PublicByteSeq {
    PublicByteSeq::new(0_usize)
}

#[cfg(proof)]
#[cfg(test)]
// #[quickcheck]
// #[requires("item === PublicByteSeq::new(0_usize)")]
// #[ensures("result === true")]
#[requires(item === auction_item(0_u64,1_u64,2_u64))]
#[requires(time === 1_u64)]
#[ensures(result === true)] // TODO: Macros unfolding! (PublicByteSeq::new(0_usize))
/// Test that the smart-contract initialization sets the state correctly
/// (no bids, active state, indicated auction-end time and item name).
pub fn auction_test_init(item: PublicByteSeq, time : u64) -> bool {
    fresh_state(item.clone(), time)
        == State(
            AuctionState::NotSoldYet,
            0_u64,
            item.clone(),
            time,
            SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
        )
}

#[cfg(test)]
#[cfg(proof)]
fn verify_bid(
    item: PublicByteSeq,
    state: State,
    account: UserAddress,
    ctx: Context,
    amount: u64,
    bid_map: SeqMap,
    highest_bid: u64,
    time : u64,
) -> (State, SeqMap, bool, bool) {
    let t = auction_bid(ctx, amount, state.clone());

    let (state, res) = match t {
        AuctionBidResult::Err(e) => (state, false),
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
            == State(
                AuctionState::NotSoldYet,
                highest_bid,
                item.clone(),
                time,
                bid_map.clone(),
            ),
    )
}

#[cfg(proof)]
#[cfg(test)]
fn useraddress_from_u8(i : u8) -> UserAddress {
    UserAddress([
        i, i, i, i, i, i, i, i, i, i, i, i, i, i, i,
        i, i, i, i, i, i, i, i, i, i, i, i, i, i, i,
        i, i,
    ])
}

#[cfg(proof)]
#[cfg(test)]
fn new_account(time : u64, i : u8) -> (UserAddress, Context) {
    let addr = useraddress_from_u8(i);
    let ctx = (time, UserAddressSet::UserAddressSome(addr));
    (addr, ctx)
}

#[cfg(proof)]
#[cfg(test)]
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
// #[ensures("result === true && exists <k : usize> item.len() === k")]
// #[requires(forall<i:Int> 0 <= len(item) && i < len(*item) ==> get(^item, i) === Some(0u32))]
#[requires(item === auction_item(0_u64,1_u64,5_u64))]
#[requires(time === 1_u64)]
// #[ensures(@result === (a, b))]
#[ensures(result === true)]
// #[ensures(exists<b : bool> (result === b) && (3 + 4 === 7))]
fn test_auction_bid_and_finalize(item: PublicByteSeq, time : u64) -> bool { // item: PublicByteSeq, time : u64
    // let item = PublicByteSeq::new(0_usize);
    // let time = 1_u64; //  100

    let amount = 100_u64;
    let winning_amount = 300_u64;
    let big_amount = 500_u64;

    let bid_map = SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize));

    // initializing auction
    let state = fresh_state(item.clone(), time); // mut

    // 1st bid: account1 bids amount1
    let (alice, alice_ctx) = new_account(time, 0_u8);

    let (state, bid_map, res_0, result_0) = verify_bid(
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
    let (state, bid_map, res_1, result_1) = verify_bid(
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

    let (state, bid_map, res_2, result_2) = verify_bid(
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
    let ctx4 = (1_u64, owner, balance);

    let finres = auction_finalize(ctx4, state.clone());
    let (state, result_3) = match finres {
        AuctionFinalizeResult::Err(err) => (
            state.clone(),
            err == FinalizeError::AuctionStillActive
        ),
        AuctionFinalizeResult::Ok((state, _)) => (state, false),
    };

    // // finalizing auction
    // let carol = new_account();
    let (carol, carol_ctx) = new_account(time, 2_u8);

    let ctx5 = (time + 1_u64, carol, winning_amount);
    let finres2 = auction_finalize(ctx5, state.clone());

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
        == State(
            AuctionState::Sold(bob),
            winning_amount,
            item.clone(),
            1_u64,
            bid_map.clone(),
        );

    // attempting to finalize auction again should fail
    let finres3 = auction_finalize(ctx5, state.clone());

    let (state, result_6) = match finres3 {
        AuctionFinalizeResult::Err(err) => (state, err == FinalizeError::AuctionFinalized),
        AuctionFinalizeResult::Ok((state, action)) => (state, false),
    };

    let t = auction_bid(bob_ctx, big_amount, state.clone());

    // let result_7 = t == AuctionBidResult::Err (BidError::AuctionIsFinalized);
    let result_7 = match t {
        AuctionBidResult::Err(e) => e == BidError::AuctionIsFinalized,
        AuctionBidResult::Ok(_) => false,
    };
    
    result_0 && result_1 && result_2 && result_3 && result_4 && result_5 && result_6 && result_7
}
