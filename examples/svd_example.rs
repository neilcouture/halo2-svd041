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
use halo2_svd::matrix::test_matrix::{test_zkvector, test_field_mat_times_vec};

use rand::{rngs::StdRng, SeedableRng};
use std::cmp;
use std::fs::File;
use std::io::{BufReader, BufWriter, Seek, Write};
use axiom_eth::halo2_proofs::poly::commitment::Params;
use halo2_base::gates::circuit::builder::BaseCircuitBuilder;
use halo2_base::gates::circuit::{BaseCircuitParams, CircuitBuilderStage};
use halo2_base::utils::testing::{check_proof, gen_proof};
use halo2_proofs::plonk::Fixed;
use zk_fixed_point_chip::scaffold::cmd::{Cli, SnarkCmd};

//pub mod halo2_svd::utils;
use halo2_svd::utils::executor::{RlcCircuit, RlcExecutor};

use core::marker::PhantomData;
use axiom_eth::rlp::RlpChip;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CircuitInput {
    pub d: Vec<f64>,
    pub m: Vec<Vec<f64>>,
    pub u: Vec<Vec<f64>>,
    pub v: Vec<Vec<f64>>,
}
const K: usize = 20;
const PRECISION_BITS: u32 = 42;
struct SVDExample<'a, F: ScalarField> where F: BigPrimeField {
    pub d: &'a Vec<f64>,
    pub m: &'a Vec<Vec<f64>>,
    pub u: &'a Vec<Vec<f64>>,
    pub v: &'a Vec<Vec<f64>>,
    marker : PhantomData<F>,
}
struct SVDPayload<F: ScalarField> where F: BigPrimeField {
    fpchip : FixedPointChip<F, 42>,
    u_t: ZkMatrix<F, PRECISION_BITS>,
    v_t: ZkMatrix<F, PRECISION_BITS>,
    m: ZkMatrix<F, PRECISION_BITS>,
    u: ZkMatrix<F, PRECISION_BITS>,
    v: ZkMatrix<F, PRECISION_BITS>,
    m_times_vt: Vec<Vec<AssignedValue<F>>>,
    u_times_ut: Vec<Vec<AssignedValue<F>>>,
    v_times_vt: Vec<Vec<AssignedValue<F>>>,
}
impl<'a, F: ScalarField> RlcCircuitInstructions<F> for SVDExample<'a, F> where F: BigPrimeField {
    type FirstPhasePayload = SVDPayload<F>;
    fn virtual_assign_phase0(
        &self,
        builder: &mut RlcCircuitBuilder<F>,
        _: &RangeChip<F>,
    ) -> Self::FirstPhasePayload {

        let degree: usize = var("DEGREE").unwrap_or_else(|_| panic!("DEGREE not set")).parse().unwrap();
        let lookup_bits: usize =
            var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();

        let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(
            lookup_bits, &builder.base);

        let ctx : &mut Context<F> = builder.base.main(0);

        println!("{:?} phase0::1.", chrono::offset::Local::now());
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
        let m = self.m.clone();
        let u = self.u.clone();
        let v = self.v.clone();
        let d = self.d.clone();

        // load in the circuit
        // m can be rectangular, say N X M matrix
        let m: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &m);
        // u will be N X N matrix
        let u: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &u);
        // v will be M X M matrix
        let v: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &v);
        // numpy gives d of length = min{N, M}
        let d: ZkVector<F, PRECISION_BITS> = ZkVector::new(ctx, &fpchip, &d);

        println!("{:?} do_zk_svd::3, m, u,v, d ZkMatrix created...", chrono::offset::Local::now());
        let max_dim = cmp::max(m.num_rows, m.num_col);

        let (err_svd, err_u) = err_calc(PRECISION_BITS, max_dim, MAX_NORM, EPS_SVD, EPS_U);
        println!("{:?} do_zk_svd::4, m, u,v, d error calculated err_svd:{:?} err_u:{:?}",
                 chrono::offset::Local::now(), err_svd, err_u);
        let fship = &fpchip;

        let mut ctx2 = ctx.clone();
        let (u_t, v_t, m_times_vt, u_times_ut, v_times_vt) =
            check_svd_phase0(&mut ctx2, &fpchip, &m, &u, &v, &d, err_svd, err_u, 30);


        SVDPayload{fpchip, u_t, v_t, m, u, v, m_times_vt, u_times_ut, v_times_vt}
    }

    fn virtual_assign_phase1(
        builder: &mut RlcCircuitBuilder<F>,
        range: &RangeChip<F>,
        rlc: &RlcChip<F>,
        payload: Self::FirstPhasePayload,
    ) {
        // old fpchip being moved
        let fpchip2 = payload.fpchip;

        //let range2 = fpchip2.range_gate();
        let chip = RlpChip::new(&range, Some(rlc));

        // closure captures `witness` variable
        println!("phase 1 synthesize begin");
        let (ctx_gate, ctx_rlc) = builder.rlc_ctx_pair();

        rlc.load_rlc_cache((ctx_gate, ctx_rlc), &chip.range().gate, 1);
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

// */

fn test_params() -> RlcCircuitParams {
    RlcCircuitParams {
        base: BaseCircuitParams {
            k: K,
            num_advice_per_phase: vec![2, 2],
            num_fixed: 1,
            num_lookup_advice_per_phase: vec![],
            lookup_bits: Some(K - 1),
            num_instance_columns: 1,
        },
        num_rlc_columns: 1,
    }
}
fn rlc_svd_circuit(
    stage: CircuitBuilderStage,
    svde: SVDExample<Fr>,
) -> RlcCircuit<Fr, SVDExample<Fr>> {
    let params = test_params();
    let mut builder = RlcCircuitBuilder::from_stage(stage, 1).use_params(params);
    //builder.
    // builder.base.set_lookup_bits(K-1);// not used, just to create range chip
    // builder.base.set_k(K);

    //builder.calculate_params(Some(20));

    RlcExecutor::new(builder, svde)
}



pub fn do_zk_svd(
    input: CircuitInput,
) -> Result<(), Error> {

    let pd = PhantomData::<Fr>::default();
    let svde: SVDExample<Fr> = SVDExample{m:&input.m, u:&input.u, v:&input.v, d:&input.d, marker:pd};
    println!("{:?} do_zk_svd::5, SVDExample  created... ", chrono::offset::Local::now());
    let mut rng = StdRng::from_seed([0u8; 32]);
    let k = K as u32;

    // FIXME
    //      ONE MIGHT NEED TO GENERATE THE KZG PARAMETER BEFORE RUNNING THIS CODE
    //      THIS IS VERY SLOW
    //
    //let pp = ParamsKZG::<Bn256>::setup(k, &mut rng);

    //use std::fs::File;
    //use std::io::Write;

    // let mut file = File::create("/datasets/kzg_params.txt")?;
    // let mut writer = BufWriter::new(file);
    // let res = pp.write(&mut writer);
    // writer.flush();



    let file = File::options()
        .read(true)
        .write(false)
        .open("/datasets/kzg_params.txt")?;
    // let ll = file.l();
    // println!("do_zk_svd:: ll, ParamsKZG  created... len {:?}", ll);
    let mut reader = BufReader::new(file);
    let rres = ParamsKZG::<Bn256>::read(&mut reader); //.unwrap();

    let params = rres.unwrap();

    println!("{:?} do_zk_svd::6, ParamsKZG  created...", chrono::offset::Local::now());

    println!("{:?} do_zk_svd::Will invoke rlc_svd_circuit...", chrono::offset::Local::now());

    let vv : Vec<Vec<Fr>> = vec![vec![]];
    let  circuitm = rlc_svd_circuit(CircuitBuilderStage::Mock, svde);
    let r = MockProver::run(K as u32, &circuitm, vv);

    let svde: SVDExample<Fr> = SVDExample{m:&input.m, u:&input.u, v:&input.v, d:&input.d, marker:pd};
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
    let pd = PhantomData::<Fr>::default();
    let svde2 = SVDExample{m:&input.m, u:&input.u, v:&input.v, d:&input.d, marker:pd};
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

    let k: usize = K;
    let lb: usize = K - 1;

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

    let task = 3;
    // run test_zkvector
    if task == 1 {
        test_zkvector(rbcb);
        println!("test_zkvector done");
    } else if task == 2 {
        test_field_mat_times_vec(rbcb);
        println!("test_field_mat_times_vec done");
    } else if task == 3 {
        println!("will invoke do_zk_svd");
        let _res = do_zk_svd(input);
    }
    println!("Test done");
}

// to create input file use
// python3.9 input-creator.py <SIZE> <SIZE>
// to run use:
// cargo run --example svd_example -- matrix
