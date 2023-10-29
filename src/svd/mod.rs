// #![allow(warnings)]
#![allow(dead_code)]
// #[allow(unused_imports)]
use halo2_base::gates::{GateChip, RangeChip};
use halo2_base::utils::BigPrimeField;
use halo2_base::AssignedValue;
use halo2_base::Context;
use num_bigint::BigUint;
use zk_fixed_point_chip::gadget::fixed_point::{FixedPointChip, FixedPointInstructions};

use super::matrix::*;
use std::cmp;

/// Given matrices `m` (`N X M` dimension), `u` (`N X N` dimension), `v` (`M X M` dimension) and a vector `d` (`min{N, M}` dimension) in fixed point representation with `fpchip`, performs the first part of checks that the SVD of `m = u*d*v` where the vector `d` is viewed as a diagonal matrix;
/// `u` and `v` are unitraries and `d` is a positive decreasing vector of singular values;
///
/// Also takes as input a tolerance level `tol` given as a floating point number
///
/// Must call `check_svd_phase1` function following this function in the second phase to complete the SVD check
///
/// Might silently fail if `m` is not correctly encoded according to the fixed representation of `fpchip`
///
/// The outputs are simply witnesses to be used for the corresponding variables in `check_svd_phase1`
pub fn check_svd_phase0<F: BigPrimeField, const PRECISION_BITS: u32>(
    ctx: &mut Context<F>,
    fpchip: &FixedPointChip<F, PRECISION_BITS>,
    m: &ZkMatrix<F, PRECISION_BITS>,
    u: &ZkMatrix<F, PRECISION_BITS>,
    v: &ZkMatrix<F, PRECISION_BITS>,
    d: &ZkVector<F, PRECISION_BITS>,
    tol: f64,
    max_bits_d: u32,
) -> (
    ZkMatrix<F, PRECISION_BITS>,
    ZkMatrix<F, PRECISION_BITS>,
    Vec<Vec<AssignedValue<F>>>,
    Vec<Vec<AssignedValue<F>>>,
    Vec<Vec<AssignedValue<F>>>,
) {
    #![allow(non_snake_case)]
    assert_eq!(m.num_rows, u.num_rows);
    assert_eq!(m.num_col, v.num_rows);

    let N = m.num_rows;
    // #[allow(non_snake_case)]
    let M = m.num_col;
    // #[allow(non_snake_case)]
    let minNM = cmp::min(N, M);
    // unitaries are square
    assert_eq!(u.num_rows, u.num_col);
    assert_eq!(v.num_rows, v.num_col);
    assert_eq!(minNM, d.v.len());

    let range: &RangeChip<F> = fpchip.range_gate();
    let gate: &GateChip<F> = fpchip.gate();

    // check the entries of d have at most max_bits_d + precision_bits
    let max_bits = (max_bits_d + PRECISION_BITS) as usize;
    d.entries_less_than(ctx, &fpchip, max_bits);
    // make sure d is in decreasing order
    d.entries_in_desc_order(ctx, &fpchip, max_bits);

    // check that the entries of u, v correspond to real numbers in the interval (-1.0,1.0) upto an error of 2^-PRECISION_BITS
    // unit_bnd_q = quantization of 1+2^-PRECISION_BITS
    let unit_bnd_q = BigUint::from(2u64.pow(PRECISION_BITS) + 1);
    check_mat_entries_bounded(ctx, &range, &u.matrix, &unit_bnd_q);
    check_mat_entries_bounded(ctx, &range, &v.matrix, &unit_bnd_q);

    // Lets define the transpose matrix of u and v
    let u_t: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::transpose_matrix(&u);
    let v_t: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::transpose_matrix(&v);

    // if-else to make sure this matrix is N X M
    let u_times_d: Vec<Vec<AssignedValue<F>>> = if minNM == M {
        mat_times_diag_mat(ctx, gate, &u.matrix, &d.v)
    } else {
        // if N < M, then you need to pad by zeroes and u_times_d should be [UD; 0] where 0 is N X (M-N) matrix of zeroes
        let zero = ctx.load_constant(F::zero());
        let mut u_times_d = mat_times_diag_mat(ctx, gate, &u.matrix, &d.v);
        for row in &mut u_times_d {
            for _ in N..M {
                row.push(zero);
            }
        }
        u_times_d
    };
    let m_times_vt: Vec<Vec<AssignedValue<F>>> = honest_prover_mat_mul(ctx, &m.matrix, &v_t.matrix);

    // define the doubly scaled tolerance
    let tol_scale = BigUint::from((tol * (2u128.pow(2 * PRECISION_BITS) as f64)).round() as u128);

    check_mat_diff(ctx, &range, &u_times_d, &m_times_vt, &tol_scale);

    let quant = F::from(2u64.pow(PRECISION_BITS));
    let quant_square = ctx.load_constant(quant * quant);

    let u_times_ut = honest_prover_mat_mul(ctx, &u.matrix, &u_t.matrix);
    check_mat_id(ctx, &range, &u_times_ut, &quant_square, &tol_scale);

    let v_times_vt = honest_prover_mat_mul(ctx, &v.matrix, &v_t.matrix);
    check_mat_id(ctx, &range, &v_times_vt, &quant_square, &tol_scale);

    return (u_t, v_t, m_times_vt, u_times_ut, v_times_vt);
}

/// Second phase function for checking SVD;
///
/// `check_svd_phase0` should be run in the first phase, so that its outputs are commited to in the first phase;
///
/// Inputs correspond to the `m`, `u`, `v` as used in `check_svd_phase0` and other inputs correspond to the outputs of `check_svd_phase0`
///
/// `init_rand` is the random challenge created after the first phase; must be a commitment of all the inputs to this function
///
/// First phase might silently fail if `m` is not correctly encoded according to the fixed representation of `fpchip`
pub fn check_svd_phase1<F: BigPrimeField, const PRECISION_BITS: u32>(
    ctx: &mut Context<F>,
    fpchip: &FixedPointChip<F, PRECISION_BITS>,
    m: &ZkMatrix<F, PRECISION_BITS>,
    u: &ZkMatrix<F, PRECISION_BITS>,
    v: &ZkMatrix<F, PRECISION_BITS>,
    u_t: &ZkMatrix<F, PRECISION_BITS>,
    v_t: &ZkMatrix<F, PRECISION_BITS>,
    m_times_vt: &Vec<Vec<AssignedValue<F>>>,
    u_times_ut: &Vec<Vec<AssignedValue<F>>>,
    v_times_vt: &Vec<Vec<AssignedValue<F>>>,
    init_rand: &AssignedValue<F>,
) {
    ZkMatrix::verify_mul(ctx, &fpchip, &m, &v_t, &m_times_vt, &init_rand);
    ZkMatrix::verify_mul(ctx, &fpchip, &u, &u_t, &u_times_ut, &init_rand);
    ZkMatrix::verify_mul(ctx, &fpchip, &v, &v_t, &v_times_vt, &init_rand);
    // println!("Phase1 success");
}
