use clap::Parser;
use halo2_base::gates::{RangeChip, RangeInstructions};
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
// * A non-negative integer x, which is guaranteed to be at most 16-bits

// public outputs:
// * The non-negative integer (x / 32), where "/" represents integer division.

fn divide_using_builin<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    let x = F::from_str_vartime(&input.x).expect("deserialize field element should not fail");

    let x = ctx.load_witness(x);
    println!("x:{:?}", x.value());

    make_public.push(x);

    // need to run: export LOOKUP_BITS=5 before
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();

    // create a Range chip that contains methods for basic arithmetic operations
    let range: RangeChip<F> = RangeChip::default(lookup_bits);

    // q should be the required output
    // need to specify 32u32 for it to convert to BigUint
    let b: u32 = 32;
    let (q, r) = range.div_mod(ctx, x, b, 16);
    make_public.push(q);

    // 233 = 32*7 +9
    println!("q:{:?}", q.value());
    println!("r:{:?}", r.value());
}

fn some_algorithm_in_zk<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    // println!("Hello {}", input.x);
    const DIV: u32 = 32;
    const NUM_BITS_INPUT: u32 = 16;
    let x: u32 = input.x.parse().unwrap();
    let q: u32 = x / DIV;
    let r: u32 = x % DIV;
    // println!("x:{x}, q:{q}, r:{r}");

    let x = F::from_str_vartime(&input.x).expect("deserialize field element should not fail");
    let q: F = F::from_u128(q as u128);
    let r: F = F::from_u128(r as u128);
    // let x_bigint = fe_to_biguint(&x);
    // // let div_bigint: BigUint = BigUint::from(div);
    // let q = x_bigint / div;
    // println!("{}", q);
    // // let r: BigUint = x_bigint % div_bigint;

    let x = ctx.load_witness(x);
    let q = ctx.load_witness(q);
    let r = ctx.load_witness(r);

    println!("x:{:?}", x.value());
    println!("q:{:?}", q.value());
    println!("r:{:?}", r.value());

    // input
    make_public.push(x);
    // output
    make_public.push(q);

    // need to run: export LOOKUP_BITS=5 before
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();

    // create a Range chip that contains methods for basic arithmetic operations
    let range: RangeChip<F> = RangeChip::default(lookup_bits);

    // contrain x = q*DIV + r;
    let y = range.gate.mul_add(ctx, q, Constant(F::from_u128(DIV as u128)), r);
    range.gate.is_equal(ctx, x, y);

    // constrain q
    range.check_less_than_safe(ctx, q, (1 << (NUM_BITS_INPUT + 1)) / DIV as u64);
    // constrain r < DIV
    range.check_less_than_safe(ctx, r, DIV as u64);
}

fn main() {
    env_logger::init();

    let args = Cli::parse();

    // run different zk commands based on the command line arguments
    run(some_algorithm_in_zk, args);
}

// to run:
// export LOOKUP_BITS=5
// cargo run --example divide_by_32 -- --name divide_by_32 -k 8 mock

// Halo2 docs at
// https://axiom-crypto.github.io/halo2-lib/halo2_base/all.html
// tutorial at
// https://docs.axiom.xyz/zero-knowledge-proofs/getting-started-with-halo2
// exercises at
// https://hackmd.io/@axiom/Hyy0zw6j2
// exercise solutions at
// https://github.com/axiom-crypto/halo2-scaffold/compare/main...os/exercises

// halo2-scaffold-
// https://github.com/axiom-crypto/halo2-scaffold
// Halo2 challenge API
// https://hackmd.io/@axiom/SJw3p-qX3
