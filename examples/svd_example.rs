// #![allow(warnings)]
#![allow(dead_code)]
#![allow(unused_imports)]
use clap::Parser;

use halo2_base::gates::{GateChip, GateInstructions, RangeChip, RangeInstructions};
use halo2_base::utils::{BigPrimeField, ScalarField};
use halo2_base::AssignedValue;
use halo2_base::{
    halo2_proofs::{
        dev::MockProver,
        halo2curves::bn256::{Bn256, Fr, G1Affine},
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Error},
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    },
    Context,
    QuantumCell::{Constant, Existing, Witness},
};
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::env;
use std::env::{set_var, var};
use std::fs;
use zk_fixed_point_chip::gadget::fixed_point::{FixedPointChip, FixedPointInstructions};
use chrono;
use axiom_eth::rlc::{
    circuit::instructions::RlcCircuitInstructions,
    circuit::builder::{RlcCircuitBuilder},
    circuit::RlcCircuitParams,
    chip::RlcChip,
    *,
};
use halo2_svd::matrix::*;
use halo2_svd::svd::*;
use rand::{rngs::StdRng, SeedableRng};
use std::cmp;
use halo2_base::gates::circuit::builder::BaseCircuitBuilder;
use halo2_base::gates::circuit::{BaseCircuitParams, CircuitBuilderStage};
use halo2_base::utils::testing::{check_proof, gen_proof};
use halo2_proofs::plonk::Fixed;
use zk_fixed_point_chip::scaffold::cmd::{Cli, SnarkCmd};

//pub mod halo2_svd::utils;
use halo2_svd::utils::executor::{RlcCircuit, RlcExecutor};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CircuitInput {
    pub d: Vec<f64>,
    pub m: Vec<Vec<f64>>,
    pub u: Vec<Vec<f64>>,
    pub v: Vec<Vec<f64>>,
}
const PRECISION_BITS: u32 = 42;
struct SVDExample<'a, F: ScalarField> where F: BigPrimeField {
    ctx : &'a mut Context<F>,
    fpchip: &'a FixedPointChip<F, PRECISION_BITS>,
    m: &'a ZkMatrix<F, PRECISION_BITS>,
    u: &'a ZkMatrix<F, PRECISION_BITS>,
    v: &'a ZkMatrix<F, PRECISION_BITS>,
    d: &'a ZkVector<F, PRECISION_BITS>,
    err_svd: f64,
    err_u: f64,
}
struct SVDPayload<'a, F: ScalarField> where F: BigPrimeField {
    fpchip : &'a FixedPointChip<F, 42>,
    u_t: ZkMatrix<F, PRECISION_BITS>,
    v_t:  ZkMatrix<F, PRECISION_BITS>,
    m: &'a ZkMatrix<F, PRECISION_BITS>,
    u: &'a ZkMatrix<F, PRECISION_BITS>,
    v: &'a ZkMatrix<F, PRECISION_BITS>,
    m_times_vt: Vec<Vec<AssignedValue<F>>>,
    u_times_ut: Vec<Vec<AssignedValue<F>>>,
    v_times_vt: Vec<Vec<AssignedValue<F>>>,
}
impl<'a, F: ScalarField> RlcCircuitInstructions<F> for SVDExample<'a, F> where F: BigPrimeField {
    type FirstPhasePayload = SVDPayload<'a, F>;
    fn virtual_assign_phase0(
        &self,
        builder: &mut RlcCircuitBuilder<F>,
        _: &RangeChip<F>,
    ) -> Self::FirstPhasePayload {

        let mut ctx2 = self.ctx.clone();
        let (u_t, v_t, m_times_vt, u_times_ut, v_times_vt) =
            check_svd_phase0(&mut ctx2, &self.fpchip, &self.m, &self.u, &self.v, &self.d, self.err_svd, self.err_u, 30);

        let fc = self.fpchip;
        let m = &self.m;
        let u = &self.u;
        let v = &self.v;

        SVDPayload{fpchip:fc, u_t, v_t, m, u, v, m_times_vt, u_times_ut, v_times_vt}

        // let ctx = builder.base.main(0);
        // let true_input = self.padded_input[..self.len].to_vec();
        // let inputs = ctx.assign_witnesses(self.padded_input.clone());
        // let len = ctx.load_witness(F::from(self.len as u64));
        // TestPayload { true_input, inputs, len }
    }

    fn virtual_assign_phase1(
        builder: &mut RlcCircuitBuilder<F>,
        range: &RangeChip<F>,
        rlc: &RlcChip<F>,
        payload: Self::FirstPhasePayload,
    ) {
        // old fpchip being moved
        let fpchip2 = payload.fpchip;

        // let range = fpchip2.range_gate();
        //let chip = RlpChip::new(&range, Some(rlc));

        // closure captures `witness` variable
        println!("phase 1 synthesize begin");
        let (ctx_gate, ctx_rlc) = builder.rlc_ctx_pair();

        rlc.load_rlc_cache((ctx_gate, ctx_rlc), &range.gate, 1);
        let init_rand = rlc.gamma_pow_cached()[0];
        println!("The init rand = {:?}", init_rand.value());

        check_svd_phase1(
            ctx_gate,
            &fpchip2,
            &payload.m,
            &payload.u,
            &payload.v,
            &payload.u_t,
            &payload.v_t,
            &payload.m_times_vt,
            &payload.u_times_ut,
            &payload.v_times_vt,
            &init_rand,
        );
    }
}

/// simple tests to make sure zkvector is okay; can also be randomized
/*
fn test_zkvector<F: ScalarField>(ctx: &mut Context<F>)
where
    F: BigPrimeField,
{
    // lookup bits must agree with the size of the lookup table, which is specified by an environmental variable
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();
    const PRECISION_BITS: u32 = 32;
    // fixed-point exp arithmetic
    let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(lookup_bits);

    const N: usize = 5;
    const M: usize = 4;
    let mut matrix: Vec<Vec<f64>> = Vec::new();
    for i in 0..N {
        matrix.push(Vec::<f64>::new());
        for j in 0..M {
            matrix[i].push((i as f64) + (j as f64) / 10.0);
        }
    }
    println!("matrix = {:?}", matrix);

    let zkmatrix: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &matrix);

    println!("zkmatrix = ");
    zkmatrix.print(&fpchip);

    let mut v1: Vec<f64> = Vec::new();
    for i in 0..M {
        if i % 2 == 0 {
            v1.push((i as f64) + ((i * i + 1) as f64) / 10.0);
        } else {
            v1.push(-(i as f64) + ((i * i + 1) as f64) / 10.0);
        }
    }
    // don't mutate now
    let v1 = v1;
    println!("v1 = {:?}", v1);

    let zkvec1 = ZkVector::new(ctx, &fpchip, &v1);
    println!("zkvec1 = ");
    zkvec1.print(&fpchip);

    let mut v2: Vec<f64> = Vec::new();
    for i in 0..M {
        if i % 2 == 0 {
            v2.push((1.0 + i.pow(3) as f64) / 10.0);
        } else {
            v2.push(-(1.0 + i.pow(3) as f64) / 10.0);
        }
    }
    // don't mutate now
    let v2 = v2;
    println!("v2 = {:?}", v2);

    let zkvec2 = ZkVector::new(ctx, &fpchip, &v2);
    println!("zkvec2 = ");
    zkvec2.print(&fpchip);

    println!("Inner product:");
    let mut ip = 0.0;
    for i in 0..v1.len() {
        ip += v1[i] * v2[i];
    }
    println!("f64 non-zk: {:?}", ip);

    let ip = zkvec1.inner_product(ctx, &fpchip, &zkvec2.v);
    let ip = fpchip.dequantization(*ip.value());
    println!("zk ckt: {:?}", ip);

    println!("** The errors for Norm and dist are pretty big **");
    println!("Norm:");
    let mut norm1 = 0.0;
    let mut norm2 = 0.0;
    for i in 0..v1.len() {
        norm1 += v1[i] * v1[i];
        norm2 += v2[i] * v2[i];
    }
    let norm_sq_1 = norm1;
    let norm_sq_2 = norm2;

    norm1 = norm1.powf(0.5);
    norm2 = norm2.powf(0.5);

    println!("f64 non-zk: ");
    println!("  for v1: {:?}", norm1);
    println!("  for v2: {:?}", norm2);

    let norm1: AssignedValue<F> = zkvec1.norm(ctx, &fpchip);
    let norm2: AssignedValue<F> = zkvec2.norm(ctx, &fpchip);

    let norm1 = fpchip.dequantization(*norm1.value());
    let norm2 = fpchip.dequantization(*norm2.value());
    println!("zk ckt: ");
    println!("  for v1: {:?}", norm1);
    println!("  for v2: {:?}", norm2);

    println!("dist:");
    let mut diff: Vec<f64> = Vec::new();

    for i in 0..M {
        diff.push(v1[i] - v2[i]);
    }
    let mut dist = 0.0;
    for i in 0..diff.len() {
        dist += diff[i] * diff[i];
    }
    let dist_sq = dist;
    dist = dist.powf(0.5);
    println!("for non-zk: {:?}", dist);
    let dist = zkvec1.dist(ctx, &fpchip, &zkvec2.v);
    let dist = fpchip.dequantization(*dist.value());
    println!("for zk: {:?}", dist);

    println!("Norm-squared:");
    println!("f64 non-zk: ");
    println!("  for v1: {:?}", norm_sq_1);
    println!("  for v2: {:?}", norm_sq_2);

    let norm_sq_1: AssignedValue<F> = zkvec1._norm_square(ctx, &fpchip);
    let norm_sq_2: AssignedValue<F> = zkvec2._norm_square(ctx, &fpchip);

    let norm_sq_1 = fpchip.dequantization(*norm_sq_1.value());
    let norm_sq_2 = fpchip.dequantization(*norm_sq_2.value());
    println!("zk ckt: ");
    println!("  for v1: {:?}", norm_sq_1);
    println!("  for v2: {:?}", norm_sq_2);

    println!("dist-squared:");
    println!("for non-zk: {:?}", dist_sq);
    let dist_sq = zkvec1._dist_square(ctx, &fpchip, &zkvec2.v);
    let dist_sq = fpchip.dequantization(*dist_sq.value());
    println!("for zk: {:?}", dist_sq);

    println!("Matrix transform:");
    let mut u1: Vec<f64> = Vec::new();
    let mut u2: Vec<f64> = Vec::new();

    for i in 0..N {
        u1.push(0.0);
        u2.push(0.0);
        for j in 0..M {
            u1[i] += matrix[i][j] * v1[j];
            u2[i] += matrix[i][j] * v2[j];
        }
    }
    println!("f64 non-zk: ");
    println!("  for v1: {:?}", u1);
    println!("  for v2: {:?}", u2);

    let zku1 = zkvec1.mul(ctx, &fpchip, &zkmatrix);
    let zku2 = zkvec2.mul(ctx, &fpchip, &zkmatrix);

    println!("zk ckt: ");
    println!("zku1 = ");
    zku1.print(&fpchip);
    println!("zku2 = ");
    zku2.print(&fpchip);
} */

/*
/// useful for optimising cost and testing
fn test_field_mat_times_vec<F: ScalarField>(ctx: &mut Context<F>)
where
    F: BigPrimeField,
{
    // lookup bits must agree with the size of the lookup table, which is specified by an environmental variable
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();
    const PRECISION_BITS: u32 = 32;
    // fixed-point exp arithmetic
    let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(lookup_bits);

    const N: usize = 5;
    const M: usize = 5;
    let mut rng = rand::thread_rng();

    let mut matrix: Vec<Vec<f64>> = Vec::new();
    for _i in 0..N {
        let mut row: Vec<f64> = Vec::new();
        for _j in 0..M {
            row.push(rng.gen_range(-100.0..100.0));
        }
        matrix.push(row);
    }

    let zkmatrix: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &matrix);

    println!("zkmatrix = ");
    zkmatrix.print(&fpchip);

    let mut v1: Vec<f64> = Vec::new();
    for _i in 0..M {
        v1.push(rng.gen_range(-100.0..100.0));
    }
    // don't mutate now
    let v1 = v1;
    // println!("v1 = {:?}", v1);

    let zkvec1 = ZkVector::new(ctx, &fpchip, &v1);
    println!("zkvec1 = ");
    zkvec1.print(&fpchip);

    println!("Matrix transform:");
    let mut u1: Vec<f64> = Vec::new();

    for i in 0..N {
        u1.push(0.0);
        for j in 0..M {
            u1[i] += matrix[i][j] * v1[j];
        }
    }
    println!("f64 non-zk: ");
    println!("  for v1: {:?}", u1);

    let zku1_s = field_mat_vec_mul(ctx, fpchip.gate(), &zkmatrix.matrix, &zkvec1.v);
    let mut zku1: Vec<AssignedValue<F>> = Vec::new();

    println!("zk ckt: ");
    for x in zku1_s {
        let (elem, _) = fpchip.signed_div_scale(ctx, x);
        zku1.push(elem);
    }
    let zku1 = ZkVector::<F, PRECISION_BITS> { v: zku1 };
    println!("zku1 = ");
    zku1.print(&fpchip);
}
*/

fn test_params() -> RlcCircuitParams {
    RlcCircuitParams {
        base: BaseCircuitParams {
            k: K,
            num_advice_per_phase: vec![1, 1],
            num_fixed: 1,
            num_lookup_advice_per_phase: vec![],
            lookup_bits: Some(19),
            num_instance_columns: 0,
        },
        num_rlc_columns: 1,
    }
}
fn rlc_svd_circuit(
    stage: CircuitBuilderStage,
    svde: SVDExample<Fr>,
) -> RlcCircuit<Fr, SVDExample<Fr>> {
    let params = test_params();
    let mut builder = RlcCircuitBuilder::from_stage(stage, 0).use_params(params);
    builder.base.set_lookup_bits(19);// not used, just to create range chip
    builder.base.set_k(20);
    RlcExecutor::new(builder, svde)
}

const K: usize = 20;

pub fn do_zk_svd(
    mut builder: RlcCircuitBuilder<Fr>,
    input: CircuitInput,
) -> Result<(), Error> {

    let degree: usize = var("DEGREE").unwrap_or_else(|_| panic!("DEGREE not set")).parse().unwrap();
    let lookup_bits: usize =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();

    let fpchip = FixedPointChip::<Fr, PRECISION_BITS>::default(
        lookup_bits, &builder.base);
    //let prover = builder.witness_gen_only();
    let ctx : &mut Context<Fr> = builder.base.main(0);

    println!("{:?} do_zk_svd::1.", chrono::offset::Local::now());
    // see [Error Analysis for SVD.pdf] for how the following parameters should be chosen
    // NOTE: 2^-32 = 2.3e-10
    // 1e-12 error estimated for matrices with operator norm <= 100 and size <= 1000 (using svd_error.py)
    // multiplying this by 100 to be on the safer side
    const EPS_SVD: f64 = 1e-10;
    // theoretical analysis indicates this can be as small as 1e-13
    const EPS_U: f64 = 1e-10;
    const MAX_NORM: f64 = 100.0;
    // for PRECISION_BITS = 42, size*MAX_NORM*2^-(P+1) and MAX_NORM*EPS_U are both almost 1e-8
    // NOTE: if you decrease PRECISION_BITS, you should also increase the error value in line 46 of input-creator.py
    const PRECISION_BITS: u32 = 42;

    assert!(degree > lookup_bits, "DEGREE should be more than LOOKUP_BITS");

    println!("{:?} do_zk_svd::2 ", chrono::offset::Local::now());
    let range = fpchip.range_gate();

    // Import from the imput file the matrices of the svd, should satisfy m = u d v, the diagonal matrix is given as a vector
    let m = input.m;
    let u = input.u;
    let v = input.v;
    let d = input.d;

    // load in the circuit
    // m can be rectangular, say N X M matrix
    let m: ZkMatrix<Fr, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &m);
    // u will be N X N matrix
    let u: ZkMatrix<Fr, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &u);
    // v will be M X M matrix
    let v: ZkMatrix<Fr, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &v);
    // numpy gives d of length = min{N, M}
    let d: ZkVector<Fr, PRECISION_BITS> = ZkVector::new(ctx, &fpchip, &d);

    println!("{:?} do_zk_svd::3, m, u, v, d ZkMatrix created...", chrono::offset::Local::now());
    let max_dim = cmp::max(m.num_rows, m.num_col);

    let (err_svd, err_u) = err_calc(PRECISION_BITS, max_dim, MAX_NORM, EPS_SVD, EPS_U);
    println!("{:?} do_zk_svd::4, error calculated err_svd:{:?} err_u:{:?}",
             chrono::offset::Local::now(), err_svd, err_u);
    let fship = &fpchip;

    let svde: SVDExample<Fr> = SVDExample{ctx, fpchip:fship, m:&m, u:&u, v:&v, d:&d, err_svd, err_u};
    println!("{:?} do_zk_svd::5, SVDExample  created... ", chrono::offset::Local::now());
    let mut rng = StdRng::from_seed([0u8; 32]);
    let k = K as u32;
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);

    println!("{:?} do_zk_svd::6, ParamsKZG  created...", chrono::offset::Local::now());

    println!("{:?} do_zk_svd::Will invoke rlc_svd_circuit...", chrono::offset::Local::now());

    let  circuit = rlc_svd_circuit(CircuitBuilderStage::Keygen, svde);

    println!("{:?} vk gen started...", chrono::offset::Local::now());
    let vk = keygen_vk(&params, &circuit)?;

    println!("{:?} vk gen done", chrono::offset::Local::now());
    let pk = keygen_pk(&params, vk, &circuit)?;
    println!("{:?} pk gen done", chrono::offset::Local::now());

    let break_points = circuit.0.builder.borrow().break_points();
    drop(circuit);
    println!();
    println!("{:?} ==============STARTING PROOF GEN===================", chrono::offset::Local::now());
    let svde2 = SVDExample{ctx, fpchip:fship, m:&m, u:&u, v:&v, d:&d, err_svd, err_u};
    let circuit = rlc_svd_circuit(CircuitBuilderStage::Prover, svde2);
    circuit.0.builder.borrow_mut().set_break_points(break_points);
    let proof = gen_proof(&params, &pk, circuit);
    println!("{:?} proof gen done", chrono::offset::Local::now());

    check_proof(&params, pk.get_vk(), &proof, true);
    println!("{:?} verify done", chrono::offset::Local::now());

    Ok(())
}

fn main() {
    println!("svd_example started...");
    let args: Vec<String> = env::args().collect();

    // Check if at least one argument is provided (the program name is the first argument)
    if args.len() < 2 {
        eprintln!("Incorrect usage; use: cargo run --example svd_example_nh -- <filename>");
        std::process::exit(1);
    }
    // The file name is the second argument (index 1)
    let file_path = "./data/".to_string() + &args[1] + ".in";

    let k: usize = 20;
    let lb: usize = 19;

    set_var("DEGREE", k.to_string());
    set_var("LOOKUP_BITS", lb.to_string());
    //let k: u32 = var("DEGREE").unwrap_or_else(|_| panic!("DEGREE not set")).parse().unwrap();
    println!("environment variables set");
    // This is the correct SVD
    let data = fs::read_to_string(file_path).expect("Unable to read file");
    // Use this file for an SVD that is incorrect at one position
    // let data = fs::read_to_string("./data/matrix-wrong.in").expect("Unable to read file");

    let input: CircuitInput = serde_json::from_str(&data).expect("JSON was not well-formatted");
    println!("data loaded...");

    let mut rbcb :RlcCircuitBuilder<Fr> = RlcCircuitBuilder::new(true, 15);

    rbcb.set_k(k);
    rbcb.set_lookup_bits(lb);

    println!("will invoke do_zk_svd");
    let res = do_zk_svd(rbcb, input);

    println!("Test done");
}

// to create input file use
// python3.9 input-creator.py <SIZE> <SIZE>
// to run use:
// cargo run --example svd_example -- matrix
