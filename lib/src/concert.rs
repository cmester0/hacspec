use crate::prelude::*;

// Concordium library types
array!(UserAddress, 32, u8);

// pub type Context = (u64, UserAddressSet);

// ActionBody
pub enum ActionBody {
    ACT_TRANSFER (UserAddress , u64),
}
pub type ListAction = Seq<ActionBody>;
// {
//     act_transfer (to : Address) (amount : Amount);
//     act_call (to : Address) (amount : Amount) (msg : SerializedValue);
//     act_deploy (amount : Amount) (c : WeakContract) (setup : SerializedValue);
// }
