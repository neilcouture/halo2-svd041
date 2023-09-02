#![allow(unused_imports)]

use clap::Parser;
use halo2_base::gates::{GateChip, RangeChip, RangeInstructions};
use halo2_base::safe_types::GateInstructions;
use halo2_base::utils::{fe_to_biguint, ScalarField};
use halo2_base::AssignedValue;
#[allow(unused_imports)]
use halo2_base::{
    Context,
    QuantumCell::{Constant, Existing, Witness},
};
use halo2_scaffold::scaffold::cmd::Cli;
use halo2_scaffold::scaffold::run;
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use std::env::var;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CircuitInput {
    pub x: String, // field element, but easier to deserialize as a string
}

// public inputs:
// * An array `arr` of length 1000
// * `start`, an index guaranteed to be in `[0, 1000)`
// * `end`, an index guaranteed to be in `[0, 1000)`
// * It is also known that `start <= end`

// public outputs:
// * An array `out` of length 1000 such that
//   * the first `end - start` entries of `out` are the subarray `arr[start:end]`
//   * all other entries of `out` are 0.

fn some_algorithm_in_zk<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    let x = F::from_str_vartime(&input.x).expect("deserialize field element should not fail");
    let x = ctx.load_witness(x);
    // input
    make_public.push(x);

    // create a Gate chip that contains methods for basic arithmetic operations
    let gate = GateChip::<F>::default();

    const N: usize = 10;
    let mut arr: Vec<F> = Vec::new();
    for i in 0..N {
        arr.push(F::from_u128(i as u128));
    }
    let mut temp_arr: Vec<AssignedValue<F>> = Vec::new();
    for x in &arr {
        temp_arr.push(ctx.load_witness(*x));
    }
    // temp_arr moved here
    let arr = temp_arr;

    let start = F::from_u128(5);
    let start = ctx.load_witness(start);

    let sel: F = F::one();
    let sel = ctx.load_witness(sel);
    let shifted_arr = shift_by_const::<F>(ctx, gate, &arr, sel, 3);
    for a in &shifted_arr {
        println!("{:?}", a.value());
    }
}

/// this function shifts array [arr] by [k] is [sel]=1
/// sel is assumed to be binary
fn shift_by_const<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: GateChip<F>,
    arr: &Vec<AssignedValue<F>>,
    sel: AssignedValue<F>,
    k: usize,
) -> Vec<AssignedValue<F>> {
    let n = arr.len();
    let k = k % n;
    let mut shifted_arr_val: Vec<F> = vec![F::zero(); n];
    let mut shifted_arr: Vec<AssignedValue<F>> = Vec::new();
    for i in 0..n {
        // ensure the unsigned ints don't become negative
        shifted_arr_val[i] = arr[(i + k) % n].value().clone();
        shifted_arr.push(ctx.load_witness(shifted_arr_val[i]));
    }
    for i in 0..n {
        gate.is_equal(ctx, arr[(i + k) % n], shifted_arr[i]);
    }
    let mut diff: Vec<AssignedValue<F>> = Vec::new();
    for i in 0..n {
        diff.push(gate.sub(ctx, shifted_arr[i], arr[i]));
    }
    let mut output: Vec<AssignedValue<F>> = Vec::new();
    for i in 0..n {
        output.push(gate.mul_add(ctx, sel, diff[i], arr[i]));
    }
    // this moves the value into the calling function
    return output;
}

fn main() {
    env_logger::init();

    let args = Cli::parse();

    // run different zk commands based on the command line arguments
    run(some_algorithm_in_zk, args);
}

// Halo2 docs at
// https://axiom-crypto.github.io/halo2-lib/halo2_base/all.html
// tutorial at
// https://docs.axiom.xyz/zero-knowledge-proofs/getting-started-with-halo2
// exercises at
// https://hackmd.io/@axiom/Hyy0zw6j2
// exercise solutions at
// https://github.com/axiom-crypto/halo2-scaffold/compare/main...os/exercises

// cargo run --example barrel_shift -- --name barrel_shift -k 8 mock
