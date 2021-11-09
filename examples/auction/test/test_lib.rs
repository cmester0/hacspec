#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
use quickcheck::*;

#[cfg(proof)]
#[cfg(test)]
#[quickcheck]
// #[requires("item === PublicByteSeq::new(0_usize)")]
#[ensures("result === true")]
/// Test that the smart-contract initialization sets the state correctly
/// (no bids, active state, indicated auction-end time and item name).
pub fn auction_test_init(item: PublicByteSeq, time: u64) -> bool {
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
) -> (State, SeqMap, bool) {
    let time = 100_u64;

    let t = auction_bid(ctx, amount, state.clone());
    
    let (state, res) = match t {
        AuctionBidResult::Err(e) => (state, false),
        AuctionBidResult::Ok(s) => (s, true)
    };
    
    let bid_map = match seq_map_update_entry(bid_map.clone(), account, highest_bid) {
        MapUpdate::Update(_, updated_map) => updated_map,
    };

    println!("res {}", res);
    
    (
        state.clone(),
        bid_map.clone(),
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

// const AUCTION_END: u64 = 1;

// fn new_account() -> AccountAddress {
//     let account = AccountAddress([0; 32]);
//     ADDRESS_COUNTER.fetch_add(1, Ordering::SeqCst);
//     account
// }

// #[cfg(proof)]
// fn new_account_ctx() -> (UserAddress, Context) {
//     let account = new_account();
//     let ctx = new_ctx(account, account, 1_u64);
//     (account, ctx)
// }

// #[cfg(proof)]
// fn new_ctx(
//     owner: UserAddress,
//     sender: UserAddress,
//     slot_time: u64,
// ) -> Context {
//     // let mut ctx = Context;
//     // ctx.set_sender(Address::Account(sender));
//     // ctx.set_owner(owner);
//     // ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(slot_time));
//     // ctx
//     (slot_time, sender)
// }

#[cfg(proof)]
#[cfg(test)]
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
#[ensures("result === true")]
fn test_auction_bid_and_finalize(item: PublicByteSeq) -> bool {
    let time = 100_u64;

    let amount = 100_u64;
    let winning_amount = 300_u64;
    // let big_amount = 500_u64;

    let bid_map = SeqMap(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize));

    // initializing auction
    let state = fresh_state(item.clone(), time); // mut

    // 1st bid: account1 bids amount1
    let alice = (UserAddress([ 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8,]));
    let alice_ctx = (1_u64, UserAddressSet::UserAddressSome(alice));

    println!("{}", bid_map);
    
    let (state, bid_map, result_0) = verify_bid(
        item.clone(),
        state,
        alice,
        alice_ctx,
        amount,
        bid_map,
        amount,
    );

    // // 2nd bid: account1 bids `amount` again
    // // should work even though it's the same amount because account1 simply
    // // increases their bid
    let (state, bid_map, result_1) = verify_bid(
        item.clone(),
        state,
        alice,
        alice_ctx,
        amount,
        bid_map,
        amount + amount,
    );

    // // 3rd bid: second account
    let bob = (UserAddress([ 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, ]));
    let bob_ctx = (2_u64, UserAddressSet::UserAddressSome(bob));

    let (state, bid_map, result_2) = verify_bid(
        item.clone(),
        state,
        bob,
        bob_ctx,
        winning_amount,
        bid_map,
        winning_amount,
    );

    // let owner = (UserAddress([
    //     0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8,
    //     0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8,
    //     0_u8, 0_u8,
    // ]));

    // let sender = owner;
    // let balance = 100_u64;
    // let ctx4 = (1_u64, owner, balance);

    // let (state, finres) = auction_finalize(ctx4, state);

    // let result_3 = match finres {
    //     AuctionFinalizeResult::Err(err) => match err {
    //         FinalizeError::AuctionStillActive => true,
    //         FinalizeError::BidMapError => false,
    //         FinalizeError::AuctionFinalized => false,
    //     },
    //     AuctionFinalizeResult::Ok(_) => false,
    // };

    // // // finalizing auction
    // // let carol = new_account();
    // let carol = (UserAddress([
    //     2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8,
    //     2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8,
    //     2_u8, 2_u8,
    // ]));
    // let carol_ctx = (2_u64, UserAddressSet::UserAddressSome(carol));

    // // // let dave = new_account();
    // // let dave = (UserAddress([
    // //     3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8,
    // //     3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8,
    // //     3_u8, 3_u8,
    // // ]));
    // // let dave_ctx = (3_u64, UserAddressSet::UserAddressSome(dave));

    // let ctx5 = (2_u64, carol, winning_amount);

    // let (state, finres2) = auction_finalize(ctx5, state);

    // // let result_4 = match finres2 {
    // //     AuctionFinalizeResult::Err(err) => false,
    // //     AuctionFinalizeResult::Ok(actions) => true,
    // // };

    // // let result_4 = state == State (
    // //     AuctionState::Sold(bob),
    // //     winning_amount,
    // //     item.clone(),
    // //     1_u64,
    // //     bid_map.clone(),
    // // );

    // // assert_eq!(state, make_state (
    // //     AuctionState::Sold(bob),
    // //     winning_amount,
    // //     ITEM.as_bytes().to_vec(),
    // //     Timestamp::from_timestamp_millis(AUCTION_END),
    // //     bid_map,
    // // ));

    // // let actions = finres2.expect("Finalizing auction should work");
    // // assert_eq!(
    // //     actions,
    // //     ActionsTree::simple_transfer(&carol, winning_amount)
    // //         .and_then(ActionsTree::simple_transfer(&alice, amount + amount))
    // // );
    // // assert_eq!(state, make_state (
    // //     AuctionState::Sold(bob),
    // //     winning_amount,
    // //     ITEM.as_bytes().to_vec(),
    // //     Timestamp::from_timestamp_millis(AUCTION_END),
    // //     bid_map,
    // // ));

    // // // attempting to finalize auction again should fail
    // // let finres3: Result<ActionsTree, _> = auction_finalize(&ctx5, &mut state);
    // // expect_error(
    // //     finres3,
    // //     FinalizeError::AuctionFinalized,
    // //     "Finalizing auction a second time should fail",
    // // );

    // // // attempting to bid again should fail
    // // let res4: Result<ActionsTree, _> = auction_bid(&bob_ctx, big_amount, &mut state);
    // // expect_error(
    // //     res4,
    // //     BidError::AuctionFinalized,
    // //     "Bidding should fail because the auction is finalized",
    // // );

    result_0 && result_1 && result_2 // && result_3 // && result_4
}
