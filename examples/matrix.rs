#![allow(dead_code)]
#[allow(unused_imports)]
use clap::Parser;
use halo2_base::gates::{GateChip, GateInstructions, RangeChip, RangeInstructions};
use halo2_base::utils::{BigPrimeField, ScalarField};
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
use halo2_base::{AssignedValue, QuantumCell};
use halo2_scaffold::gadget::fixed_point::{FixedPointChip, FixedPointInstructions};
use halo2_scaffold::scaffold::cmd::Cli;
use halo2_scaffold::scaffold::run;
use poseidon::PoseidonChip;
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::env::{set_var, var};
use std::fs;

use axiom_eth::rlp::{
    builder::{FnSynthesize, RlcThreadBuilder, RlpCircuitBuilder},
    rlc::RlcChip,
    *,
};
use rand::{rngs::StdRng, SeedableRng};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CircuitInput {
    pub d: Vec<f64>,
    pub m: Vec<Vec<f64>>,
    pub u: Vec<Vec<f64>>,
    pub v: Vec<Vec<f64>>,
    // field element, but easier to deserialize as a string
}

#[derive(Clone)]
/// ZKVector is always associated to a fixed point chip for which we need [PRECISION_BITS]
pub struct ZkVector<F: BigPrimeField, const PRECISION_BITS: u32> {
    v: Vec<AssignedValue<F>>,
    // TODO: can fix dimension
    // can also add fpchip to this itself
}

impl<F: BigPrimeField, const PRECISION_BITS: u32> ZkVector<F, PRECISION_BITS> {
    /// Creates a ZkVector from `v` using the quantization of the `fpchip`;
    ///
    /// Does not constrain the output in anyway
    pub fn new(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        v: &Vec<f64>,
    ) -> Self {
        let mut zk_v: Vec<AssignedValue<F>> = Vec::new();
        for elem in v {
            let elem = fpchip.quantization(*elem);
            zk_v.push(ctx.load_witness(elem));
        }
        return Self { v: zk_v };
    }

    /// Returns the length of the vector
    pub fn size(&self) -> usize {
        return self.v.len();
    }

    /// Dequantizes the vector and returns it;
    ///
    /// Action is not constrained in anyway
    pub fn dequantize(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) -> Vec<f64> {
        let mut dq_v: Vec<f64> = Vec::new();
        for elem in &self.v {
            dq_v.push(fpchip.dequantization(*elem.value()));
        }
        return dq_v;
    }

    /// Prints the dequantized version of the vector and returns it;
    ///
    /// Action is not constrained in anyway
    pub fn print(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) {
        let dq_v = self.dequantize(fpchip);
        println!("[");
        for elem in dq_v {
            println!("{:?}, ", elem);
        }
        println!("]");
    }

    /// With zk constraints calculates the inner product of this vector with vector x
    ///
    /// Outputs the inner product
    ///
    /// Order doesn't matter because we are only dealing with real numbers
    ///
    /// Low level function; uses the fact that FixedPointChip.{add, mul} just call GateChip.{add, mul}
    ///
    /// Leads to about [self.size()] + 90 constraints
    pub fn inner_product(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        x: &Vec<AssignedValue<F>>,
    ) -> AssignedValue<F> {
        // couldn't figure out how to use inner_product of fpchip because we use x: &Vec and I didn't want to move
        assert!(self.size() == x.len());

        let mut v: Vec<QuantumCell<F>> = Vec::new();
        for elem in &self.v {
            v.push(Existing(*elem));
        }
        let v = v;

        let mut u: Vec<QuantumCell<F>> = Vec::new();
        for elem in x {
            u.push(Existing(*elem));
        }
        let u = u;

        let res_s = fpchip.gate().inner_product(ctx, u, v);

        // #CONSTRAINTS = 90
        // Implementing this way allows us to amortize the cost of calling this expensive rescaling- will also lead to more accuracy
        let (res, _) = fpchip.signed_div_scale(ctx, res_s);
        return res;
    }

    /// With zk constraints calculates the square of the norm of the vector;
    ///
    /// Outputs the square of the norm
    pub fn _norm_square(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
    ) -> AssignedValue<F> {
        return self.inner_product(ctx, fpchip, &self.v);
    }

    /// With zk constraints calculates the norm of the vector;
    ///
    /// Outputs the norm;
    ///
    /// Square root function is expensive and adds a lot error; Avoid using whenever possible
    pub fn norm(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
    ) -> AssignedValue<F> {
        let norm_sq = self._norm_square(ctx, fpchip);
        return fpchip.qsqrt(ctx, norm_sq);
    }

    /// With zk constraints calculates the distance squared of the vector from vector `x`;
    ///
    /// Outputs the distance squared
    pub fn _dist_square(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        x: &Vec<AssignedValue<F>>,
    ) -> AssignedValue<F> {
        assert_eq!(self.size(), x.len());
        let mut diff: Vec<AssignedValue<F>> = Vec::new();
        for (r, s) in self.v.iter().zip(x.iter()) {
            diff.push(fpchip.qsub(ctx, *r, *s));
        }
        let diff = Self { v: diff };
        return diff._norm_square(ctx, fpchip);
    }

    /// With zk constraints calculates the dist of the vector from vector `x`
    ///
    /// Outputs the norm;
    ///
    /// Square root function adds a lot error and is very expensive; Avoid using whenever possible
    pub fn dist(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        x: &Vec<AssignedValue<F>>,
    ) -> AssignedValue<F> {
        let dist_sq = self._dist_square(ctx, fpchip, x);
        return fpchip.qsqrt(ctx, dist_sq);
    }

    /// Multiplies this vector by matrix `a` in the zk-circuit and returns the constrained output `a.v`
    ///
    /// Adds about N^2+90*N constraints
    pub fn mul(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &ZkMatrix<F, PRECISION_BITS>,
    ) -> Self {
        assert_eq!(a.num_col, self.size());
        let mut y: Vec<AssignedValue<F>> = Vec::new();
        // #CONSTRAINTS = N^2+90*N
        for row in &a.matrix {
            y.push(self.inner_product(ctx, fpchip, row));
        }
        return Self { v: y };
    }

    /// constraints all the entries of the vector to be in between 0 and 2^max_bits and its entries must be in decreasing order
    pub fn entries_less_than(
        &self,
        max_bits: u32,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
    ) {
        let bound = 2u64.pow(max_bits);
        //let bound_field = ctx.load_witness(F::from(bound));

        for i in 0..self.v.len() {
            fpchip.gate.check_less_than_safe(ctx, self.v[i], bound);
        }

        let mut vec_inc: Vec<AssignedValue<F>> = Vec::new();

        for i in 0..(self.v.len() - 1) {
            let ele = fpchip.qsub(ctx, self.v[i], self.v[i + 1]);
            vec_inc.push(ele);
        }

        for i in 0..vec_inc.len() {
            fpchip.gate.check_less_than_safe(ctx, vec_inc[i], bound);
        }
    }
}

#[derive(Clone)]
pub struct ZkMatrix<F: BigPrimeField, const PRECISION_BITS: u32> {
    matrix: Vec<Vec<AssignedValue<F>>>,
    num_rows: usize,
    num_col: usize,
    // TODO: can fix dimension
    // can also add fpchip to this itself
}
impl<F: BigPrimeField, const PRECISION_BITS: u32> ZkMatrix<F, PRECISION_BITS> {
    // create a ZkMatrix from a f64 matrix
    // leads to num_rows*num_col new cells
    pub fn new(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        matrix: &Vec<Vec<f64>>,
    ) -> Self {
        let mut zkmatrix: Vec<Vec<AssignedValue<F>>> = Vec::new();
        let num_rows = matrix.len();
        let num_col = matrix[0].len();
        for row in matrix {
            assert!(row.len() == num_col);
        }
        for i in 0..num_rows {
            let mut new_row: Vec<AssignedValue<F>> = Vec::new();
            for j in 0..num_col {
                let elem = matrix[i][j];
                let elem = fpchip.quantization(elem);
                new_row.push(ctx.load_witness(elem));
            }
            zkmatrix.push(new_row);
        }
        return Self { matrix: zkmatrix, num_rows: num_rows, num_col: num_col };
    }

    pub fn dequantize(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) -> Vec<Vec<f64>> {
        let mut dq_matrix: Vec<Vec<f64>> = Vec::new();
        for i in 0..self.num_rows {
            dq_matrix.push(Vec::<f64>::new());
            for j in 0..self.num_col {
                let elem = self.matrix[i][j];
                dq_matrix[i].push(fpchip.dequantization(*elem.value()));
            }
        }
        return dq_matrix;
    }
    pub fn print(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) {
        print!("[\n");
        for i in 0..self.num_rows {
            print!("[\n");
            for j in 0..self.num_col {
                let elem = self.matrix[i][j];
                let elem = fpchip.dequantization(*elem.value());
                print!("{:?}, ", elem);
            }
            print!("], \n");
        }
        println!("]");
    }

    /// Takes quantised matrices `a` and `b`, their unscaled product `c_s`
    /// and a commitment (hash) to *at least* all of these matrices `init_rand`
    /// and checks if `a*b = c_s` in field multiplication.
    ///
    /// `c_s`: unscaled product of `a` and `b`(produced by simply multiplying `a` and `b` as field elements);
    ///  producing this is the costly part of matrix multiplication
    ///
    /// `init_rand`:  is the starting randomness/ challenge value; should commit to
    /// *at least* the matrices `a, b, c_s`
    pub fn verify_mul(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &Self,
        b: &Self,
        c_s: &Vec<Vec<AssignedValue<F>>>,
        init_rand: &AssignedValue<F>,
    ) {
        assert_eq!(a.num_col, b.num_rows);
        assert_eq!(c_s.len(), a.num_rows);
        assert_eq!(c_s[0].len(), b.num_col);
        assert!(c_s[0].len() >= 1);

        let d = c_s[0].len();
        let gate = fpchip.gate();

        // v = (1, r, r^2, ..., r^(d-1)) where r = init_rand is the random challenge value
        let mut v: Vec<AssignedValue<F>> = Vec::new();

        let one = ctx.load_witness(F::one());
        gate.assert_is_const(ctx, &one, &F::one());
        v.push(one);

        for i in 1..d {
            let prev = &v[i - 1];
            let r_to_i = fpchip.gate().mul(ctx, *prev, *init_rand);
            v.push(r_to_i);
        }
        let v = v;

        // println!("Random vector, v = [");
        // for x in &v {
        //     println!("{:?}", *x.value());
        // }
        // println!("]");

        let cs_times_v = field_mat_vec_mul(ctx, gate, c_s, &v);
        let b_times_v = field_mat_vec_mul(ctx, gate, &b.matrix, &v);
        let ab_times_v = field_mat_vec_mul(ctx, gate, &a.matrix, &b_times_v);

        for i in 0..cs_times_v.len() {
            gate.is_equal(ctx, cs_times_v[i], ab_times_v[i]);
        }
    }

    /// Takes `c_s` and divides it by the quantization factor to scale it;
    /// Useful after matrix multiplication
    pub fn rescale_matrix(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        c_s: &Vec<Vec<AssignedValue<F>>>,
    ) -> Self {
        // #CONSTRAINTS = 94*N^2
        // now rescale c_s
        let mut c: Vec<Vec<AssignedValue<F>>> = Vec::new();
        let num_rows = c_s.len();
        let num_col = c_s[0].len();
        for i in 0..num_rows {
            let mut new_row: Vec<AssignedValue<F>> = Vec::new();
            for j in 0..num_col {
                // use fpchip to rescale c_s[i][j]
                // implemented in circuit, so we know c produced is correct
                let (elem, _) = fpchip.signed_div_scale(ctx, c_s[i][j]);
                new_row.push(elem);
            }
            c.push(new_row);
        }
        return Self { matrix: c, num_rows: num_rows, num_col: num_col };
    }
    /// hash all the matrices in the given list
    fn hash_matrix_list(
        ctx: &mut Context<F>,
        gate: &GateChip<F>,
        matrix_list: Vec<&Self>,
    ) -> AssignedValue<F> {
        // T, R_F, R_P values correspond to POSEIDON-128 values given in Table 2 of the Poseidon hash paper
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        // MODE OF USE: we will update the poseidon chip with all the values and then extract one value
        let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
        for mat in matrix_list {
            for row in &mat.matrix {
                poseidon.update(row);
            }
        }
        let init_rand = poseidon.squeeze(ctx, gate).unwrap();
        // dbg!(init_rand.value());
        return init_rand;
    }

    /// takes as input two quantized matrices 'a', 'b' and check that the difference of each coefficient is smaller than tol,
    /// in the sense that the field elements of 'a' and 'b' represent real numbers throught the fixed point chip
    /// here "a" and "b" are defined as Vec<Vec<AssignedValue<F>>> rather than &Self for more flexibility when calling the function

    pub fn check_mat_diff(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &Vec<Vec<AssignedValue<F>>>,
        b: &Vec<Vec<AssignedValue<F>>>,
        tol: f64,
    ) {
        assert_eq!(a.len(), b.len());
        assert_eq!(a[0].len(), b[0].len());

        let quant_tol = (tol * (2u64.pow(PRECISION_BITS) as f64)) as u64;

        let quant_tol_field = ctx.load_witness(F::from(quant_tol));

        for i in 0..a.len() {
            for j in 0..a[0].len() {
                let ele = fpchip.qsub(ctx, a[i][j], b[i][j]);
                let ele_add = fpchip.qadd(ctx, ele, quant_tol_field);
                fpchip.gate.check_less_than_safe(ctx, ele_add, 2 * quant_tol);
            }
        }
    }

    /// given a matrix of field elements 'a' and a field element 'scalar_id', checks that 'a' is close to the identity matrix times 'scalar_id',
    /// in the sense that the absolute value of the difference of each coefficient must be less than (tol*scaling of the fixed point chip)

    pub fn check_mat_id(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &Vec<Vec<AssignedValue<F>>>,
        scalar_id: AssignedValue<F>,
        tol: f64,
    ) {
        let quant_tol = (tol * (2u64.pow(PRECISION_BITS) as f64)) as u64;

        let quant_tol_field = ctx.load_witness(F::from(quant_tol));

        for i in 0..a.len() {
            for j in 0..a[0].len() {
                if i == j {
                    let ele = fpchip.qsub(ctx, a[i][i], scalar_id);
                    let ele_add = fpchip.qadd(ctx, ele, quant_tol_field);
                    fpchip.gate.check_less_than_safe(ctx, ele_add, 2 * quant_tol);
                } else {
                    let ele_add = fpchip.qadd(ctx, a[i][j], quant_tol_field);
                    fpchip.gate.check_less_than_safe(ctx, ele_add, 2 * quant_tol);
                }
            }
        }
    }

    // Given a matrix 'a' in the fixed point representation, checks that all of its entries are less in absolute value than a tolerance tol

    pub fn check_mat_entries_bounded(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &Vec<Vec<AssignedValue<F>>>,
        tol: f64,
    ) {
        let quant_tol = (tol * (2u64.pow(PRECISION_BITS) as f64)) as u64;

        let quant_tol_field = ctx.load_witness(F::from(quant_tol));

        for i in 0..a.len() {
            for j in 0..a[0].len() {
                let ele_add = fpchip.qadd(ctx, a[i][j], quant_tol_field);
                fpchip.gate.check_less_than_safe(ctx, ele_add, 2 * quant_tol);
            }
        }
    }

    /// function that outputs the transpose matrix of a matrix `a`
    pub fn transpose_matrix(ctx: &mut Context<F>, a: &Self) -> Self {
        let mut a_trans: Vec<Vec<AssignedValue<F>>> = Vec::new();

        for i in 0..a.num_col {
            let mut new_row: Vec<AssignedValue<F>> = Vec::new();
            for j in 0..a.num_rows {
                new_row.push(a.matrix[j][i].clone());
            }
            a_trans.push(new_row);
        }
        return Self { matrix: a_trans, num_rows: a.num_col, num_col: a.num_rows };
    }
}

/// Takes matrices `a` and `b` (viewed simply as field elements), calculates and outputs matrix product `c = a*b` outside of the zk circuit
///
/// Assumes matrix `a` and `b` are well defined matrices (all rows have the same size) and asserts (outside of circuit) that they can be multiplied
///
/// Uses trivial O(N^3) matrix multiplication algorithm
///
/// Doesn't contrain output in any way
pub fn field_mat_mul<F: BigPrimeField>(
    a: &Vec<Vec<AssignedValue<F>>>,
    b: &Vec<Vec<AssignedValue<F>>>,
) -> Vec<Vec<F>> {
    // a.num_col == b.num_rows
    assert_eq!(a[0].len(), b.len());

    let mut c: Vec<Vec<F>> = Vec::new();
    let N = a.len();
    let K = a[0].len();
    let M = b[0].len();

    for i in 0..N {
        let mut row: Vec<F> = Vec::new();
        for j in 0..M {
            let mut elem = F::zero();
            for k in 0..K {
                elem += a[i][k].value().clone() * b[k][j].value().clone();
            }
            row.push(elem);
        }
        c.push(row);
    }
    return c;
}

/// Takes matrices `a` and `b` (viewed simply as field elements), calculates matrix product `c_s = a*b` outside of the zk circuit, loads `c_s` into the context `ctx` and outputs the loaded matrix
///
/// Assumes matrix `a` and `b` are well defined matrices (all rows have the same size) and asserts (outside of circuit) that they can be multiplied
///
/// Uses trivial O(N^3) matrix multiplication algorithm
///
/// Doesn't contrain output matrix in any way
pub fn honest_prover_mat_mul<F: BigPrimeField>(
    ctx: &mut Context<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    b: &Vec<Vec<AssignedValue<F>>>,
) -> Vec<Vec<AssignedValue<F>>> {
    // field multiply matrices a and b
    // for honest prover creates the correct product multiplied by the quantization_scale (S) when a and b are field point quantized
    let c_s = field_mat_mul(a, b);
    let mut assigned_c_s: Vec<Vec<AssignedValue<F>>> = Vec::new();

    let num_rows = c_s.len();
    let num_col = c_s[0].len();
    for i in 0..num_rows {
        let mut new_row: Vec<AssignedValue<F>> = Vec::new();
        for j in 0..num_col {
            let elem = c_s[i][j];
            new_row.push(ctx.load_witness(elem));
        }
        assigned_c_s.push(new_row);
    }
    return assigned_c_s;
}

/// Multiplies matrix `a` to vector `v` in the zk-circuit and returns the constrained output `a.v`
/// -- all assuming `a` and `v` are field elements (and not fixed point encoded)
/// Assumes matrix `a` is well defined (rows are equal size) and asserts (outside circuit) `a` can be multiplied to `v`
///
/// #CONSTRAINTS = N^2
pub fn field_mat_vec_mul<F: BigPrimeField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    v: &Vec<AssignedValue<F>>,
) -> Vec<AssignedValue<F>> {
    assert_eq!(a[0].len(), v.len());
    let mut y: Vec<AssignedValue<F>> = Vec::new();
    // #CONSTRAINTS = N^2
    for row in a {
        let mut w: Vec<QuantumCell<F>> = Vec::new();
        for x in v {
            w.push(Existing(*x));
        }
        let w = w;

        let mut u: Vec<QuantumCell<F>> = Vec::new();
        for x in row {
            u.push(Existing(*x));
        }
        let u = u;

        y.push(gate.inner_product(ctx, u, w));
    }

    return y;
}

/// Multiplies matrix `a` by a diag matrix represented as a vector `v` in the zk-circuit and returns the constrained output `a*v`
/// -- all assuming `a` and `v` are field elements, (and not fixed point encoded)
///
/// Assumes matrix `a` is well defined (rows are equal size) and asserts (outside circuit) `a` can be multiplied to `v`
///
/// #CONSTRAINTS = N^2
pub fn field_mat_diagmat_mul<F: BigPrimeField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    v: &Vec<AssignedValue<F>>,
) -> Vec<Vec<AssignedValue<F>>> {
    assert_eq!(a[0].len(), v.len());
    let mut m: Vec<Vec<AssignedValue<F>>> = Vec::new();
    // #CONSTRAINTS = N^2
    for i in 0..a.len() {
        let mut new_row: Vec<AssignedValue<F>> = Vec::new();
        for j in 0..a[0].len() {
            let prod = gate.mul(ctx, a[i][j], v[j]);
            new_row.push(prod);
        }
        m.push(new_row);
    }
    return m;
}

/// given matrices 'm', 'u', 'v' and a vector 'd' in floating point, checks the svd m = u*d*v where the vector 'd' is viewed as a diagonal matrix
/// also takes as input a tolerance level tol given as a floating point number
/// init_rand is an assigned value used as a the random challenge
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
    let gate = fpchip.gate();

    // check the entries of d have at most max_bits_d + precision_bits
    let max_bits = max_bits_d + PRECISION_BITS;
    ZkVector::entries_less_than(&d, max_bits, ctx, &fpchip);

    // check that the entries of u, v correspond to real numbers in the interval (-1.01,1.01)
    ZkMatrix::check_mat_entries_bounded(ctx, &fpchip, &u.matrix, 1.01);
    ZkMatrix::check_mat_entries_bounded(ctx, &fpchip, &v.matrix, 1.01);

    // Lets define the transpose matrix of and v
    let u_t: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::transpose_matrix(ctx, &u);
    let v_t: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::transpose_matrix(ctx, &v);

    // define the scaled tolerance level
    let tol_scale = tol * (2u64.pow(PRECISION_BITS) as f64);

    let u_times_d: Vec<Vec<AssignedValue<F>>> = field_mat_diagmat_mul(ctx, gate, &u.matrix, &d.v);
    let m_times_vt: Vec<Vec<AssignedValue<F>>> = honest_prover_mat_mul(ctx, &m.matrix, &v_t.matrix);

    ZkMatrix::check_mat_diff(ctx, &fpchip, &u_times_d, &m_times_vt, tol_scale);

    let quant = F::from(2u64.pow(PRECISION_BITS));
    let quant_square = ctx.load_constant(quant * quant);

    let u_times_ut = honest_prover_mat_mul(ctx, &u.matrix, &u_t.matrix);
    ZkMatrix::check_mat_id(ctx, &fpchip, &u_times_ut, quant_square, tol_scale);

    let v_times_vt = honest_prover_mat_mul(ctx, &v.matrix, &v_t.matrix);
    ZkMatrix::check_mat_id(ctx, &fpchip, &v_times_vt, quant_square, tol_scale);

    return (u_t, v_t, m_times_vt, u_times_ut, v_times_vt);
}

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
    println!("Phase1 success");
}

/// simple tests to make sure zkvector is okay; can also be randomized
fn test_zkvector<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) where
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
}

/// useful for optimising cost and testing
fn test_field_mat_times_vec<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) where
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
    for i in 0..N {
        let mut row: Vec<f64> = Vec::new();
        for j in 0..M {
            row.push(rng.gen_range(-100.0..100.0));
        }
        matrix.push(row);
    }

    let zkmatrix: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &matrix);

    println!("zkmatrix = ");
    zkmatrix.print(&fpchip);

    let mut v1: Vec<f64> = Vec::new();
    for i in 0..M {
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

fn two_phase_svd_verif<F: ScalarField>(
    mut builder: RlcThreadBuilder<F>,
    input: CircuitInput,
) -> RlpCircuitBuilder<F, impl FnSynthesize<F>> {
    let prover = builder.witness_gen_only();
    let ctx = builder.gate_builder.main(0);

    const PRECISION_BITS: u32 = 32;
    let degree: usize = var("DEGREE").unwrap_or_else(|_| panic!("DEGREE not set")).parse().unwrap();
    let lookup_bits: usize =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();

    assert!(degree > lookup_bits, "DEGREE should be more than LOOKUP_BITS");
    let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(lookup_bits);
    let gate = fpchip.gate();
    let range = fpchip.range_gate();

    // Import from the imput file the matrices of the svd, should satisfy m = u d v, the diagonal matrix is given as a vector
    let m = input.m;
    let u = input.u;
    let v = input.v;
    let d = input.d;

    // load in the circuit
    let m: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &m);
    let u: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &u);
    let v: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &v);
    let d: ZkVector<F, PRECISION_BITS> = ZkVector::new(ctx, &fpchip, &d);

    let tol = 1e-5;

    let chip = RlpChip::new(&range, None);
    // let witness = chip.decompose_rlp_field_phase0(ctx, inputs, max_len);

    let (u_t, v_t, m_times_vt, u_times_ut, v_times_vt) =
        check_svd_phase0(ctx, &fpchip, &m, &u, &v, &d, tol, 30);

    // copied from rlp_string_circuit in axiom-eth> src> rlp> tests
    let synthesize_phase1 = move |b: &mut RlcThreadBuilder<F>, rlc: &RlcChip<F>| {
        // old fpchip being moved
        let fpchip2 = fpchip;
        let range = fpchip2.range_gate();
        let chip = RlpChip::new(&range, Some(rlc));

        // closure captures `witness` variable
        println!("phase 1 synthesize begin");
        let (ctx_gate, ctx_rlc) = b.rlc_ctx_pair();

        rlc.load_rlc_cache((ctx_gate, ctx_rlc), &chip.range().gate, 1);
        let init_rand = rlc.gamma_pow_cached()[0];
        println!("The init rand = {:?}", init_rand.value());

        check_svd_phase1(
            ctx_gate,
            &fpchip2,
            &m,
            &u,
            &v,
            &u_t,
            &v_t,
            &m_times_vt,
            &u_times_ut,
            &v_times_vt,
            &init_rand,
        );
    };
    let circuit = RlpCircuitBuilder::new(builder, None, synthesize_phase1);
    // auto-configure circuit if not in prover mode for convenience
    if !prover {
        circuit.config(degree as usize, Some(6));
    }
    return circuit;
}

fn main() {
    let data = fs::read_to_string("./data/matrix.in").expect("Unable to read file");
    let input: CircuitInput = serde_json::from_str(&data).expect("JSON was not well-formatted");
    set_var("DEGREE", 20.to_string());
    set_var("LOOKUP_BITS", 19.to_string());
    let k: u32 = var("DEGREE").unwrap_or_else(|_| panic!("DEGREE not set")).parse().unwrap();
    // // run different zk commands based on the command line arguments
    // run(zk_random_verif_algo, args);

    let circuit = two_phase_svd_verif(RlcThreadBuilder::<Fr>::mock(), input);
    MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();
}

// to create input file use
// python3.9 input-creator.py <SIZE>
// to run use:
// cargo run --example matrix
