#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

use hacspec_lib::*;

// #[cfg(feature = "hacspec_attributes")]
#[cfg(feature = "hacspec")]
use hacspec_attributes::*;
// #[cfg(not(feature = "hacspec"))]
#[cfg(test)]
use hacspec_attributes::proof;

#[cfg(test)]
#[cfg(not(feature = "hacspec"))]
use creusot_contracts::{ensures, requires};

use hacspec_concordium::*;

#[cfg(not(feature = "hacspec"))]
#[derive(Serialize, SchemaType)]
pub struct State {
    result: u64,
}

pub type StateHacspec = u64;

#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_state(st: StateHacspec) -> State {
    State { result: st }
}

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_state(st: State) -> StateHacspec {
    st.result
}

fn contract_init_hacspec() -> StateHacspec {
    0u64
}

#[cfg(not(feature = "hacspec"))]
#[init(contract = "fib")]
#[inline(always)]
fn contract_init(_ctx: &impl HasInitContext) -> InitResult<((), State)> {
    let state = coerce_hacspec_to_rust_state(contract_init_hacspec());
    Ok(((), state))
}

// pub enum Action {
//     Value(u64),
//     Continuation0(u64, u64),
//     Continuation1(u64, u64),
//     Start(u64),
// }

// fn contract_receive_hacspec(
//     action : Action,
// ) -> Action {
//     match action {
//         Action::Start(n) =>
//             if n <= 1u64 {
//                 Action::Value(1u64)
//             } else {
//                 Action::Continuation0(n, n-2u64)
//             },
//         Action::Continuation0(n, p) => Action::Continuation1(p, n-1u64),
//         Action::Continuation1(p, q) => Action::Value(p + q),
//         Action::Value(v) => Action::Value(v) // TODO: Should never happen ! (happens because return / call statement in strange recursive )
//     }
// }

// #[cfg(not(feature = "hacspec"))]
// fn contract_receive_creusot(
//     ctx: &impl HasReceiveContext,
//     host: &mut impl HasHost<State>,
//     action : Action,
// ) -> u64 {
//     match contract_receive_hacspec(action) {
//         Action::Start(n) => panic!(), // Should never happen
//         Action::Continuation0(n, nsub2) => {
//             let cv2 = contract_receive_call(ctx, host, nsub2);
//             contract_receive_creusot(ctx, host, Action::Continuation0(n, cv2))
//         }
//         Action::Continuation1(p, nsub1) => {
//             let cv2 = contract_receive_call(ctx, host, nsub1);
//             contract_receive_creusot(ctx, host, Action::Continuation0(p, cv2))
//         }
//         Action::Value(v) => v
//     }
// }

// #[cfg(not(feature = "hacspec"))]
// // Add the the nth Fibonacci number F(n) to this contract's state.
// // This is achieved by recursively calling the contract itself.
// #[inline(always)]
// #[receive(contract = "fib", name = "receive", parameter = "u64", return_value = "u64")]
// fn contract_receive(
//     ctx: &impl HasReceiveContext,
//     host: &mut impl HasHost<State>,
// ) -> ReceiveResult<u64> {
//     // Try to get the parameter (64bit unsigned integer).
//     let n: u64 = ctx.parameter_cursor().get()?;
//     let result = contract_receive_creusot(ctx, host, Action::Start(n));
//     host.state().result = result;
//     Ok(result)
// }

pub enum Action {
    Value(u64),
    Continuation0(u64, u64),
    Continuation1(u64, u64),
    Start(u64),
}

fn contract_receive_hacspec(action: Action) -> Action {
    match action {
        Action::Start(n) => {
            if n <= 1u64 {
                Action::Value(1u64)
            } else {
                Action::Continuation0(n, n - 2u64)
            }
        }
        Action::Continuation0(n, p) => Action::Continuation1(p, n - 1u64),
        Action::Continuation1(p, q) => Action::Value(p + q),
        Action::Value(v) => Action::Value(v), // TODO: Should never happen ! (happens because return / call statement in strange recursive )
    }
}

#[cfg(not(feature = "hacspec"))]
fn contract_receive_call(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State>,
    n: u64,
) -> u64 {
    let self_address = ctx.self_address();
    let p2 = n.to_le_bytes();
    let mut n2 = host
        .invoke_contract(
            &self_address,
            Parameter(&p2),
            EntrypointName::new_unchecked("receive"),
            Amount::zero(),
        )
        .unwrap_abort()
        .1
        .unwrap_abort();
    let cv2 = host.state().result;
    let n2: u64 = n2.get().unwrap_abort();
    // ensure_eq!(cv2, n2);
    cv2
}

#[cfg(not(feature = "hacspec"))]
// Add the the nth Fibonacci number F(n) to this contract's state.
// This is achieved by recursively calling the contract itself.
#[inline(always)]
#[receive(
    contract = "fib",
    name = "receive",
    parameter = "u64",
    return_value = "u64"
)]
fn contract_receive(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State>,
) -> ReceiveResult<u64> {
    // Try to get the parameter (64bit unsigned integer).
    let n: u64 = ctx.parameter_cursor().get()?;

    match contract_receive_hacspec(Action::Start(n)) {
        Action::Value(v) => {
            host.state().result = v;
            Ok(v)
        }
        Action::Continuation0(_, p) => {
            let p = contract_receive_call(ctx, host, p); // p = n-1
            match contract_receive_hacspec(Action::Continuation0(n, p)) {
                Action::Continuation1(p, q) => {
                    let q = contract_receive_call(ctx, host, q);
                    match contract_receive_hacspec(Action::Continuation1(p, q)) {
                        Action::Value(v) => {
                            host.state().result = v;
                            Ok(v)
                        }

                        _ => Err(Reject {
                            error_code: unsafe {
                                core::num::NonZeroI32::new_unchecked(i32::MIN + 5i32)
                            },
                        }),
                    }
                }
                _ => Err(Reject {
                    error_code: unsafe { core::num::NonZeroI32::new_unchecked(i32::MIN + 5i32) },
                }),
            }
        }

        _ => {
            Err(Reject {
                error_code: unsafe { core::num::NonZeroI32::new_unchecked(i32::MIN + 5i32) },
            })
            // host.state().result = 89;
            // Ok(89)
        }
    }

    // if n <= 1 {
    //     host.state().result = 1;
    //     Ok(1)
    // } else {
    //     let cv2 = contract_receive_call(ctx, host, n-2);
    //     let cv1 = contract_receive_call(ctx, host, n-1);
    //     host.state().result = cv1 + cv2;
    //     Ok(cv1 + cv2)
    // }
}

#[cfg(not(feature = "hacspec"))]
/// Retrieve the value of the state.
#[inline(always)]
#[receive(contract = "fib", name = "view", return_value = "u64")]
fn contract_view(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State>,
) -> ReceiveResult<u64> {
    Ok(host.state().result)
}

#[cfg(not(feature = "hacspec"))]
#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    // Compute the n-th fibonacci number.
    fn fib(n: u64) -> u64 {
        let mut n1 = 1;
        let mut n2 = 1;
        for _ in 2..=n {
            let t = n1;
            n1 = n2;
            n2 += t;
        }
        n2
    }

    #[concordium_test]
    fn receive_works() {
        let mut ctx = ReceiveContextTest::empty();
        let parameter_bytes = to_bytes(&10u64);
        let contract_address = ContractAddress {
            index: 0,
            subindex: 0,
        };
        ctx.set_parameter(&parameter_bytes);
        ctx.set_self_address(contract_address.clone());

        let mut host = HostTest::new(State { result: 0 });

        host.setup_mock_invocation(
            contract_address,
            OwnedEntrypointName::new_unchecked("receive".into()),
            Handler::new(MockFn::new(|parameter, _amount, state| {
                let n: u64 = match from_bytes(parameter.0) {
                    Ok(n) => n,
                    Err(_) => return Err(InvokeError::Trap),
                };
                state.result = fib(n);
                Ok((true, state.result))
            })),
        );
        let res = contract_receive(&ctx, &mut host).expect_report("Calling receive failed.");
        assert_eq!(res, fib(10));
        assert_eq!(host.state().result, fib(10));
    }
}
