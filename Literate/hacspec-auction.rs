use hacspec_lib::*;

array!(UserAddress, 32, u8);

pub enum AuctionState {
    NotSoldYet,
    Sold(UserAddress),
}

pub type SeqMap = (PublicByteSeq, PublicByteSeq);

pub enum MapEntry {
    Entry(u64, SeqMap),
}

fn seq_map_entry(m: SeqMap, sender_address: UserAddress) -> MapEntry {
    let (m1, m2) = m.clone();
    let mut res = MapEntry::Entry(
	0_u64,
	(
	    m1.clone().concat(&sender_address),
	    m2.clone().concat(&u64_to_be_bytes(0_u64)),
	),
    );

    for x in 0..m1.clone().len() / 32 {
	if UserAddress::from_seq(&m1.clone().slice(x * 32, 32)) == sender_address {
	    res = MapEntry::Entry(
		u64_from_be_bytes(u64Word::from_seq(&m2.slice(x * 8, 8))),
		m.clone(),
	    );
	}
    }

    res
}

pub enum MapUpdate {
    Update(u64, SeqMap),
}

fn seq_map_update_entry(m: SeqMap, sender_address: UserAddress, amount: u64) -> MapUpdate {
    let (m1, m2) = m;

    let mut res = MapUpdate::Update(
	amount,
	(
	    m1.concat(&sender_address),
	    m2.concat(&u64_to_be_bytes(amount)),
	),
    );

    for x in 0..m1.clone().len() / 32 {
	if UserAddress::from_seq(&m1.clone().slice(x * 32, 32)) == sender_address {
	    res = MapUpdate::Update(
		amount,
		(
		    m1.clone().update(x * 32, &sender_address),
		    m2.clone().update(x * 8, &u64_to_be_bytes(amount)),
		),
	    );
	}
    }

    res
}

pub fn fresh_state(itm: Seq<u8>, exp: u64) -> State {
    (
	AuctionState::NotSoldYet,
	0_u64,
	itm,
	exp,
	(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
    )
}

pub type Context = (u64, UserAddressSet);

fn their_context_to_my_context(ctx: &impl HasReceiveContext) -> auction::Context {
    (
	ctx.metadata().slot_time().timestamp_millis(),
	match ctx.sender() {
	    Address::Contract(_) => UserAddressSet::UserAddressNone,
	    Address::Account(account_address) => {
		UserAddressSet::UserAddressSome(u8x32_to_user_address(account_address.0), ())
	    }
	},
    )
}

pub enum BidError {
    ContractSender,
    BidTooLow,
    BidsOverWaitingForAuctionFinalization,
    AuctionIsFinalized,
}

pub enum Boolean {
    True,
    False,
}

pub fn auction_bid(ctx: Context, amount: u64, state: State) -> (State, AuctionBidResult) {
    // ensure!(state.auction_state == AuctionState::NotSoldYet, BidError::AuctionFinalized);
    let (auction_state, b, c, expiry, e) = state;
    let (slot_time, sender) = ctx;

    let ((acs, upb, ce, expirye, (updated1_mape, updated2_mape)), rese) = match auction_state {
	AuctionState::NotSoldYet => match if slot_time <= expiry {
	    Boolean::True
	} else {
	    Boolean::False
	} {
	    Boolean::True => match sender {
		UserAddressSet::UserAddressNone => (
		    (auction_state, b, c, expiry, e),
		    AuctionBidResult::Err(BidError::ContractSender),
		),
		UserAddressSet::UserAddressSome(sender_address, _) => {
		    match seq_map_entry(e.clone(), sender_address) {
			MapEntry::Entry(bid_to_update, new_map) => match seq_map_update_entry(
			    new_map.clone(),
			    sender_address,
			    bid_to_update + amount,
			) {
			    MapUpdate::Update(updated_bid, updated_map) => match if updated_bid > b
			    {
				Boolean::True
			    } else {
				Boolean::False
			    } {
				Boolean::True => (
				    (auction_state, updated_bid, c, expiry, updated_map),
				    AuctionBidResult::Ok(()),
				),
				Boolean::False => (
				    (auction_state, b, c, expiry, updated_map),
				    AuctionBidResult::Err(BidError::BidTooLow),
				),
			    },
			},
		    }
		}
	    },
	    Boolean::False => (
		(auction_state, b, c, expiry, e),
		AuctionBidResult::Err(BidError::BidsOverWaitingForAuctionFinalization),
	    ),
	},
	AuctionState::Sold(_) => (
	    (auction_state, b, c, expiry, e),
	    AuctionBidResult::Err(BidError::AuctionIsFinalized),
	),
    };

    (
	(acs, upb, ce, expirye, (updated1_mape, updated2_mape)),
	rese,
    )
}

pub type FinalizeContext = (u64, UserAddress, u64);

pub enum FinalizeError {
    BidMapError,
    AuctionStillActive,
    AuctionFinalized,
}

pub enum BidRemain {
    None,
    Some(u64, ()),
}

pub enum FinalizeAction {
    Accept,
    SimpleTransfer(UserAddress, u64, PublicByteSeq),
}

pub type AuctionFinalizeResult = Result<FinalizeAction, FinalizeError>;

pub fn auction_finalize(ctx: FinalizeContext, state: State) -> (State, AuctionFinalizeResult) {
    let (mut auction_state, b, c, expiry, (m1, m2)) = state;
    let (slot_time, owner, balance) = ctx;

    let (continues, mut return_action) = match auction_state {
	AuctionState::NotSoldYet => {
	    if slot_time > expiry {
		if balance == 0_u64 {
		    (false, AuctionFinalizeResult::Ok(FinalizeAction::Accept))
		} else {
		    (
			true,
			AuctionFinalizeResult::Ok(FinalizeAction::SimpleTransfer(
			    owner,
			    b,
			    PublicByteSeq::new(0_usize),
			)),
		    )
		}
	    } else {
		(
		    false,
		    AuctionFinalizeResult::Err(FinalizeError::AuctionStillActive),
		)
	    }
	}
	AuctionState::Sold(_) => (
	    false,
	    AuctionFinalizeResult::Err(FinalizeError::AuctionFinalized),
	),
    };

    let mut remaining_bid = BidRemain::None;

    if continues {
	for x in 0..m1.clone().len() / 32 {
	    let amnt = u64_from_be_bytes(u64Word::from_seq(&m2.slice(x * 8, 8)));
	    let addr = UserAddress::from_seq(&m1.clone().slice(x * 32, 32));
	    if amnt < b {
		return_action = match return_action {
		    AuctionFinalizeResult::Ok(a) => match a {
			FinalizeAction::SimpleTransfer(o, b, a) => {
			    AuctionFinalizeResult::Ok(FinalizeAction::SimpleTransfer(
				o,
				b,
				a.concat(&addr).concat(&u64_to_be_bytes(amnt)),
			    ))
			}
			FinalizeAction::Accept => AuctionFinalizeResult::Ok(FinalizeAction::Accept),
		    },
		    AuctionFinalizeResult::Err(e) => AuctionFinalizeResult::Err(e),
		};
	    } else {
		if match remaining_bid {
		    BidRemain::None => true,
		    BidRemain::Some(_, _) => false,
		} {
		    auction_state = AuctionState::Sold(addr);
		    remaining_bid = BidRemain::Some(amnt, ());
		} else {
		    return_action = AuctionFinalizeResult::Err(FinalizeError::BidMapError);
		}
	    }
	}
    };

    if continues {
	return_action = match remaining_bid {
	    BidRemain::Some(amount, _) => match if amount == b {
		Boolean::True
	    } else {
		Boolean::False
	    } {
		Boolean::True => return_action,
		Boolean::False => AuctionFinalizeResult::Err(FinalizeError::BidMapError),
	    },
	    BidRemain::None => AuctionFinalizeResult::Err(FinalizeError::BidMapError),
	};
    };

    ((auction_state, b, c, expiry, (m1, m2)), return_action)
}
