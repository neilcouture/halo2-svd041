#![allow(dead_code)]
#[allow(unused_imports)]
use clap::Parser;
use halo2_base::gates::{GateChip, GateInstructions, RangeChip, RangeInstructions};
use halo2_base::utils::{BigPrimeField, ScalarField};
use halo2_base::{AssignedValue, QuantumCell};
use halo2_base::{
    Context,
    QuantumCell::{Constant, Existing, Witness},
};
use halo2_scaffold::gadget::fixed_point::{FixedPointChip, FixedPointInstructions};
use halo2_scaffold::scaffold::cmd::Cli;
use halo2_scaffold::scaffold::run;
use serde::{Deserialize, Serialize};
use std::env::{set_var, var};

use poseidon::PoseidonChip;
use rand::Rng;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CircuitInput {
    pub x: String, // field element, but easier to deserialize as a string
}

/// ZKVector is always associated to a fixed point chip for which we need [PRECISION_BITS]
pub struct ZkVector<F: BigPrimeField, const PRECISION_BITS: u32> {
    v: Vec<AssignedValue<F>>,
    // TODO: can fix dimension
    // can also add fpchip to this itself
}

impl<F: BigPrimeField, const PRECISION_BITS: u32> ZkVector<F, PRECISION_BITS> {
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
    /// Action is not constrained in anyway
    pub fn dequantize(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) -> Vec<f64> {
        let mut dq_v: Vec<f64> = Vec::new();
        for elem in &self.v {
            dq_v.push(fpchip.dequantization(*elem.value()));
        }
        return dq_v;
    }

    /// Prints the dequantized version of the vector and returns it;
    /// Action is not constrained in anyway
    pub fn print(&self, fpchip: &FixedPointChip<F, PRECISION_BITS>) {
        let dq_v = self.dequantize(fpchip);
        println!("[");
        for elem in dq_v {
            println!("{:?}", elem);
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

    /// With zk constraints calculates the square of the norm of the vector
    /// Outputs the square of the norm
    pub fn _norm_square(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
    ) -> AssignedValue<F> {
        return self.inner_product(ctx, fpchip, &self.v);
    }

    /// With zk constraints calculates the norm of the vector
    /// Outputs the norm
    /// Square root function adds a lot error; Avoid using
    pub fn norm(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
    ) -> AssignedValue<F> {
        let norm_sq = self._norm_square(ctx, fpchip);
        return fpchip.qsqrt(ctx, norm_sq);
    }

    /// With zk constraints calculates the distance squared of the vector from vector [x]
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

    /// With zk constraints calculates the dist of the vector from vector [x]
    /// Outputs the norm
    /// Square root function adds a lot error; Avoid using
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
}

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
            for j in 0..self.num_col {
                let elem = self.matrix[i][j];
                let elem = fpchip.dequantization(*elem.value());
                print!("{}, ", elem);
            }
            print!("\n");
        }
        println!("]");
    }

    // /// Verifies that matrices [a], [b], and [c] satisfy [c = a*b]
    // ///
    // /// [init_rand] is the starting randomness/ challenge value
    // pub fn verify_mul(
    //     ctx: &mut Context<F>,
    //     fpchip: &FixedPointChip<F, PRECISION_BITS>,
    //     a: &Self,
    //     b: &Self,
    //     c: &Self,
    //     init_rand: AssignedValue<F>,
    //     tol: f64,
    // ) {
    //     assert!(tol > 0.0);
    //     assert_eq!(a.num_col, b.num_rows);
    //     assert_eq!(c.num_rows, a.num_rows);
    //     assert_eq!(c.num_col, b.num_col);
    //     assert!(c.num_col >= 1);

    //     let d = c.num_col;

    //     // random bits in 1 hash
    //     const RAND_PER_HASH: usize = 254;
    //     // need to hash these many times to produce enough randomness for one random vector check
    //     let num_hash_per_rnd = (d - 1) / RAND_PER_HASH + 1; // -1 because we want just M hashes at d= M*RAND_PER_HASH

    //     // this will determine probability of error for the randomized algorithm
    //     // currently set to 2^-30 ~ 1e-9
    //     const NUM_RNDS: usize = 30;

    //     let gate: &GateChip<F> = &fpchip.gate();
    //     // declare norm_est_sum and contrain it
    //     // #CONSTRAINTS = 1
    //     let mut norm_sq_est_sum = ctx.load_witness(fpchip.quantization(0.0));
    //     gate.assert_is_const(ctx, &norm_sq_est_sum, &fpchip.quantization(0.0));

    //     // T, R_F, R_P values correspond to POSEIDON-128 values given in Table 2 of the Poseidon hash paper
    //     const T: usize = 3;
    //     const RATE: usize = 2;
    //     const R_F: usize = 8;
    //     const R_P: usize = 57;

    //     // list of hashes used in a round
    //     let mut hash_list: Vec<AssignedValue<F>> = vec![init_rand];

    //     // #CONSTRAINTS = 3000*N/254 = 12N
    //     // 1 random element already in the list
    //     for i in 1..num_hash_per_rnd {
    //         // there is a difference between using a single chip and using multiple chips
    //         // TODO: I think the right way is to use multiple chips
    //         let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
    //         poseidon.update(&[hash_list[i - 1]]);
    //         hash_list.push(poseidon.squeeze(ctx, gate).unwrap());
    //     }
    //     // no more mutable
    //     let hash_list = hash_list;

    //     // for h in &hash_list {
    //     //     dbg!(h.value());
    //     // }

    //     // #CONSTRAINTS = 254*N/254 = N
    //     let mut rand_bin_vec: Vec<AssignedValue<F>> = vec![];
    //     for i in 0..num_hash_per_rnd {
    //         let mut new_rand = gate.num_to_bits(ctx, hash_list[i], RAND_PER_HASH);
    //         rand_bin_vec.append(&mut new_rand);
    //     }

    //     // Do not need to explicitly calculate the conversion of this vector to {-1, 1} vector- but we call this converted vector v

    //     // #CONSTRAINTS = 4*N^2 + 2N
    //     let c_times_v = _matrix_times_bin_vec(ctx, &fpchip.gate(), &c, &rand_bin_vec);
    //     let b_times_v = _matrix_times_bin_vec(ctx, &fpchip.gate(), &b, &rand_bin_vec);
    //     // #CONSTRAINTS = N^2 + 90*N
    //     let ab_times_v = b_times_v.mul(ctx, fpchip, a);

    //     // println!("c_times_v is: ");
    //     // c_times_v.print(&fpchip);
    //     // println!("b_times_v is: ");
    //     // b_times_v.print(&fpchip);
    //     // println!("ab_times_v is: ");
    //     // ab_times_v.print(&fpchip);

    //     // #CONSTRAINTS = N
    //     let dist_sq = c_times_v._dist_square(ctx, fpchip, &ab_times_v.v);

    //     let dist_sq_dq = fpchip.dequantization(*dist_sq.value());
    //     // println!("The dist is= {dist_sq_dq}");

    //     // println!("Est sum error= {:?}", fpchip.dequantization(*norm_sq_est_sum.value()));

    //     norm_sq_est_sum = fpchip.qadd(ctx, norm_sq_est_sum, dist_sq);

    //     // println!("Est sum error= {:?}", fpchip.dequantization(*norm_sq_est_sum.value()));

    //     // the commitment for all randomness so far
    //     let mut prev_rand = hash_list[hash_list.len() - 1];

    //     for _ in 1..NUM_RNDS {
    //         // Need to repeat this code in the loop because we do not need this first part for the first iteration

    //         // println!("start rand = {:?}", prev_rand.value());
    //         let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
    //         // use old hash and the results of previous computation to compute next hash
    //         poseidon.update(&[prev_rand, norm_sq_est_sum]);
    //         let init_rand = poseidon.squeeze(ctx, gate).unwrap();

    //         // list of hashes used in a round
    //         let mut hash_list: Vec<AssignedValue<F>> = vec![init_rand];

    //         // 1 random element already in the list
    //         for i in 1..num_hash_per_rnd {
    //             let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
    //             poseidon.update(&[hash_list[i - 1]]);
    //             hash_list.push(poseidon.squeeze(ctx, gate).unwrap());
    //         }
    //         let hash_list = hash_list;

    //         let mut rand_bin_vec: Vec<AssignedValue<F>> = vec![];
    //         for i in 0..num_hash_per_rnd {
    //             let mut new_rand = gate.num_to_bits(ctx, hash_list[i], RAND_PER_HASH);
    //             rand_bin_vec.append(&mut new_rand);
    //         }
    //         // let v = convert_vec(ctx, &fpchip, &rand_bin_vec, Some(d));

    //         let c_times_v = _matrix_times_bin_vec(ctx, &fpchip.gate(), &c, &rand_bin_vec);
    //         let b_times_v = _matrix_times_bin_vec(ctx, &fpchip.gate(), &b, &rand_bin_vec);
    //         let ab_times_v = b_times_v.mul(ctx, fpchip, a);

    //         let dist_sq = c_times_v._dist_square(ctx, fpchip, &ab_times_v.v);

    //         norm_sq_est_sum = fpchip.qadd(ctx, norm_sq_est_sum, dist_sq);
    //         // println!("Est sum error= {:?}", fpchip.dequantization(*norm_sq_est_sum.value()));
    //         prev_rand = hash_list[hash_list.len() - 1];
    //     }

    //     let norm_sq_est =
    //         fpchip.qdiv(ctx, norm_sq_est_sum, Constant(fpchip.quantization(NUM_RNDS as f64)));
    //     println!("Est error= {:?}", fpchip.dequantization(*norm_sq_est.value()));
    //     // ensure dist is smaller than tolerance
    //     // should depend on size of matrix; make sizes constant
    //     // have to explicitly use quantization here
    //     let quant_tol = (tol * (2u64.pow(PRECISION_BITS) as f64)) as u64;
    //     // TODO: uncomment this
    //     // fpchip.gate.check_less_than_safe(ctx, norm_sq_est, quant_tol);
    // }

    /// Takes quantised matrices [a] and [b], calculates matrix [c = a*b] outside of circuit. Verifies [c] is correct in circuit then outputs it
    ///
    /// [init_rand] is the starting randomness/ challenge value
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

        println!("Random vector, v = [");
        for x in &v {
            println!("{:?}", *x.value());
        }
        println!("]");

        let cs_times_v = field_mat_vec_mul(ctx, gate, c_s, &v);
        let b_times_v = field_mat_vec_mul(ctx, gate, &b.matrix, &v);
        let ab_times_v = field_mat_vec_mul(ctx, gate, &a.matrix, &b_times_v);

        for i in 0..d {
            gate.is_equal(ctx, cs_times_v[i], ab_times_v[i]);
        }

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

        // *** c should also be committed and hashed***
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

    /// Computes the product of matrices [a] and [b] using O(N^3) trivial algorithm
    /// Outputs [c] = [a][b]
    pub fn trivial_mul(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &Self,
        b: &Self,
    ) -> Self {
        assert_eq!(a.num_col, b.num_rows);

        let mut c: Vec<Vec<AssignedValue<F>>> = Vec::new();

        for i in 0..a.num_rows {
            let mut new_row: Vec<AssignedValue<F>> = Vec::new();
            for j in 0..b.num_col {
                let mut new_ele = ctx.load_witness(F::from(0));
                fpchip.gate().assert_is_const(ctx, &new_ele, &F::zero());
                for k in 0..a.num_col {
                    // this step will call qmul N times!!
                    let prod = fpchip.qmul(ctx, a.matrix[i][k], b.matrix[k][j]);
                    new_ele = fpchip.qadd(ctx, new_ele, prod);
                }
                new_row.push(new_ele);
            }
            c.push(new_row);
        }
        return Self { matrix: c, num_rows: a.num_rows, num_col: b.num_col };
    }
}

/// Takes matrices [a] and [b] (viewed simply as field elements), calculates and outputs matrix product [c = a*b] outside of the zk circuit
///
/// Assumes matrix [a] and [b] are well defined matrices (all rows have the same size)
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

/// Takes matrices [a] and [b] (viewed simply as field elements), calculates and outputs matrix product [c = a*b] outside of the zk circuit and loads [c] into the context [ctx]
///
/// Assumes matrix [a] and [b] are well defined matrices (all rows have the same size)
///
/// Uses trivial O(N^3) matrix multiplication algorithm
///
/// Doesn't contrain output in any way
pub fn honest_prover_mat_mul<F: BigPrimeField>(
    ctx: &mut Context<F>,
    a: &Vec<Vec<AssignedValue<F>>>,
    b: &Vec<Vec<AssignedValue<F>>>,
) -> Vec<Vec<AssignedValue<F>>> {
    // field multiply matrices a and b
    // for honest prover creates the correct product multiplied by the quantization_scale (S)
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

/// Multiplies this vector by matrix `a` in the zk-circuit and returns the constrained output [a.u] -- all assuming [a] and [u] are field elements, not fixed point elements
///
/// Assumes matrix [a] is well defined (rows are equal size)
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

/// Constructs a quantised ZKVector in {-1, 1}^[length] given [bin_vec] in {0,1}^D where D is greater than equal to length.
/// Assumes [bin_vec] to be a binary vector (NOT encoded using quantisation scheme).
/// If [length] is left None then assumes [length] = [bin_vec.len()].
fn convert_vec<F: BigPrimeField, const PRECISION_BITS: u32>(
    ctx: &mut Context<F>,
    fpchip: &FixedPointChip<F, PRECISION_BITS>,
    bin_vec: &Vec<AssignedValue<F>>,
    length: Option<usize>,
) -> ZkVector<F, PRECISION_BITS> {
    let mut rv: Vec<AssignedValue<F>> = vec![];
    let qnt_2: F = fpchip.quantization(2.0);
    let qnt_neg_1: F = fpchip.quantization(-1.0);
    let gate = &fpchip.gate.gate;

    let l = length.unwrap_or(bin_vec.len());

    assert!(bin_vec.len() >= l);
    for i in 0..l {
        // x --> -1 + 2*x transforms x in {0,1} to x in {-1,1}
        let out = gate.mul_add(ctx, bin_vec[i], Constant(qnt_2), Constant(qnt_neg_1));
        rv.push(out);
    }
    return ZkVector { v: rv };
}

/// Returns [sum] + [matrix_elem] * [2*[b]-1]
///
/// Low level helper function which relies on the inner workings of the current FixedPointChip
///
/// Specifically uses the fact that FixedPointChip.{add, sub} simply calls GateChip.{add, sub}
///
/// Leads to 2 constraints
fn _matrix_times_bin_vec_helper<F: BigPrimeField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    sum: &AssignedValue<F>,
    matrix_elem: &AssignedValue<F>,
    b: &AssignedValue<F>,
) -> AssignedValue<F> {
    // transform bit b to {-1,1} using x -> 2x-1
    let t = gate.mul_add(ctx, Constant(F::from(2)), *b, Constant(-F::one()));
    return gate.mul_add(ctx, *matrix_elem, t, *sum);
}

/// Low level FixedPointChip implementation based method to efficiently convert a random binary vector [bin_vec] to {-1, 1} vector and then multiply that with matrix [m]
///
/// Calls `_matrix_times_bin_vec_helper`
///
/// Leads to about 2*[m.num_rows]*[m.num_col]+ [m.num_rows] contraints
fn _matrix_times_bin_vec<F: BigPrimeField, const PRECISION_BITS: u32>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    m: &ZkMatrix<F, PRECISION_BITS>,
    bin_vec: &Vec<AssignedValue<F>>,
) -> ZkVector<F, PRECISION_BITS> {
    assert!(m.num_col <= bin_vec.len());

    let mut res: Vec<AssignedValue<F>> = Vec::new();
    // #CONSTRAINTS = 2*N^2 + N
    for i in 0..m.num_rows {
        let mut elem = ctx.load_witness(F::zero());
        gate.assert_is_const(ctx, &elem, &F::zero());
        for j in 0..m.num_col {
            elem = _matrix_times_bin_vec_helper(ctx, &gate, &elem, &m.matrix[i][j], &bin_vec[j]);
        }
        res.push(elem);
    }
    return ZkVector { v: res };
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
fn test_zkvector_times_matrix<F: ScalarField>(
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
            row.push(rng.gen_range(-1.0..1.0));
        }
        matrix.push(row);
    }

    let zkmatrix: ZkMatrix<F, PRECISION_BITS> = ZkMatrix::new(ctx, &fpchip, &matrix);

    println!("zkmatrix = ");
    zkmatrix.print(&fpchip);

    let mut v1: Vec<f64> = Vec::new();
    for i in 0..M {
        v1.push(rng.gen_range(-1.0..1.0));
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

    let zku1 = zkvec1.mul(ctx, &fpchip, &zkmatrix);

    println!("zk ckt: ");
    println!("zku1 = ");
    zku1.print(&fpchip);
}

fn zk_random_verif_algo<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    // lookup bits must agree with the size of the lookup table, which is specified by an environmental variable
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();
    const PRECISION_BITS: u32 = 32;
    // fixed-point exp arithmetic
    let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(lookup_bits);
    let gate = &fpchip.gate.gate;
    const N: usize = 100;
    const M: usize = 100;
    const K: usize = 100;

    let mut rng = rand::thread_rng();
    let mut a: Vec<Vec<f64>> = Vec::new();
    let mut b: Vec<Vec<f64>> = Vec::new();
    let mut c: Vec<Vec<f64>> = Vec::new();

    for i in 0..N {
        let mut row: Vec<f64> = Vec::new();
        for j in 0..K {
            row.push(rng.gen_range(-1.0..1.0));
        }
        a.push(row);
    }
    let a = a;
    for i in 0..K {
        let mut row: Vec<f64> = Vec::new();
        for j in 0..M {
            row.push(rng.gen_range(-1.0..1.0));
        }
        b.push(row);
    }
    let b = b;

    for i in 0..N {
        let mut row: Vec<f64> = Vec::new();
        for j in 0..M {
            let mut elem = 0.0;
            for k in 0..K {
                elem += a[i][k] * b[k][j];
            }
            row.push(elem);
        }
        c.push(row);
    }
    let c = c;

    // println!("a = ");
    // print!("[");
    // for i in 0..N {
    //     print!("[");
    //     for j in 0..K {
    //         print!("{:.2}, ", a[i][j]);
    //     }
    //     print!("],\n");
    // }
    // print!("]\n");

    // println!("b = ");
    // print!("[");
    // for i in 0..K {
    //     print!("[");
    //     for j in 0..M {
    //         print!("{:.2}, ", b[i][j]);
    //     }
    //     print!("],\n");
    // }
    // print!("]\n");

    // println!("c = ");
    // print!("[");
    // for i in 0..N {
    //     print!("[");
    //     for j in 0..M {
    //         print!("{:.2}, ", c[i][j]);
    //     }
    //     print!("],\n");
    // }
    // print!("]\n");

    // #CONSTRAINTS = these lead to 3*N^2 constraints
    let a = ZkMatrix::new(ctx, &fpchip, &a);
    let b = ZkMatrix::new(ctx, &fpchip, &b);
    let c = ZkMatrix::new(ctx, &fpchip, &c);

    // TODO: initial hashing
    // manual hash of all matrix elements
    // hashing requires ~1000 cells per element
    // let init_rand = ZkMatrix::hash_matrix_list(ctx, gate, vec![&a, &b, &c]);
    // dbg!(init_rand.value());

    // #CONSTRAINTS = 3000= O(1)
    // init_rand = hash(a[0][0])
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 8;
    const R_P: usize = 57;
    let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
    let elem = a.matrix[0][0].clone();
    poseidon.update(&[elem]);
    let init_rand = poseidon.squeeze(ctx, gate).unwrap();
    // ZkMatrix::verify_mul(ctx, &fpchip, &a, &b, &c, init_rand, 1e-3);

    // ORIGINAL MULTIPICATION
    // at git commit - a07444642cd61c4bd9732bb96f9762a3aa645fa1
    // Multiplication cost 250 per mul
    // Total cost = 26000*dim^2 with 30 hashes
    // 3000 would just be from init_hash
    // Hashing [NUM_RNDS] times = 2000 per hash- only 30*2000 overall- small
    // 250 for a single vector multiplication per element
    // This 250 cost is coming from the rescaling required in qmul (signed_div_scale)

    // NEW MULTIPICATION
    // at git commit - 367bee6a27a606e006fdfac60927d22fed996399
    // costs 94 per mul- will also depend on lookup table

    // With efficient {-1, 1} vector multiplication
    // at git commit - 61a961ab927a078cd4161d7153edd0a6298b3087
    // cells for
    // N=M=K=20 are 1571094
    // N=M=K=50 are 8600994
    // N=M=K=100 are 33529494
    // Number of cells grows as 3440*N^2 = 1150*3N^2
    // 94*30 = 2820

    // With amortized rescaling
    // at git commit - f6c0bc6d145af60e2da3fcc1b1e76a6f00daebe4
    // cells for
    // N=M=K=20 are 539784
    // N=M=K=50 are 2148984
    // N=M=K=100 are 7722984
    // Number of cells grows as N^2 + 94*N
    // 723*N^2 + 3030*N + 189984
    // (mul cost)*(num iter) = 94*30 = 2820 --> this contributes to the coeff of N
    // (hashing cost)*(num iter) = 3000*30 --> contributes to the constant factor
    // 723/30 = 24

    // Minor improvement to inner_product
    // at git commit - 994f4ac4d870d97aedf7ea7fa8095914028d33ed
    // cells for
    // N=M=K=20 are 489384
    // N=M=K=50 are 1842984
    // N=M=K=100 are 6510984
    // At this point if you count visible constraints, they are = 5K*N^2 +106*K*N + 3000*K
    // - this very nicely accounts for all the N order constraint growth
    // - smaller than observed for N^2 coeff by a factor of ~4.3
    // -- because of copying stuff??
    // -- because 4 cells per gate??

    // Another minor improvement to inner_product- to use optimised gate.inner_product
    // cells for
    // N=M=K=50 are 1766484
    // N=M=K=100 are 6207984
}

fn zk_trivial_mat_mul<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    // lookup bits must agree with the size of the lookup table, which is specified by an environmental variable
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();
    const PRECISION_BITS: u32 = 32;
    // fixed-point exp arithmetic
    let fpchip = FixedPointChip::<F, PRECISION_BITS>::default(lookup_bits);
    let gate = &fpchip.gate.gate;
    const N: usize = 5;
    const M: usize = 5;
    const K: usize = 5;

    let mut rng = rand::thread_rng();
    let mut a: Vec<Vec<f64>> = Vec::new();
    let mut b: Vec<Vec<f64>> = Vec::new();
    let mut c: Vec<Vec<f64>> = Vec::new();

    for i in 0..N {
        let mut row: Vec<f64> = Vec::new();
        for j in 0..K {
            row.push(rng.gen_range(-1.0..1.0));
        }
        a.push(row);
    }
    let a = a;
    for i in 0..K {
        let mut row: Vec<f64> = Vec::new();
        for j in 0..M {
            row.push(rng.gen_range(-1.0..1.0));
        }
        b.push(row);
    }
    let b = b;

    for i in 0..N {
        let mut row: Vec<f64> = Vec::new();
        for j in 0..M {
            let mut elem = 0.0;
            for k in 0..K {
                elem += a[i][k] * b[k][j];
            }
            row.push(elem);
        }
        c.push(row);
    }
    let c = c;

    // println!("a = ");
    // print!("[");
    // for i in 0..N {
    //     print!("[");
    //     for j in 0..K {
    //         print!("{:.2}, ", a[i][j]);
    //     }
    //     print!("],\n");
    // }
    // print!("]\n");

    // println!("b = ");
    // print!("[");
    // for i in 0..K {
    //     print!("[");
    //     for j in 0..M {
    //         print!("{:.2}, ", b[i][j]);
    //     }
    //     print!("],\n");
    // }
    // print!("]\n");

    // println!("c = ");
    // print!("[");
    // for i in 0..N {
    //     print!("[");
    //     for j in 0..M {
    //         print!("{:.2}, ", c[i][j]);
    //     }
    //     print!("],\n");
    // }
    // print!("]\n");

    let a = ZkMatrix::new(ctx, &fpchip, &a);
    let b = ZkMatrix::new(ctx, &fpchip, &b);
    let c = ZkMatrix::trivial_mul(ctx, &fpchip, &a, &b);

    println!("ZKMatrices:");

    println!("a = ");
    a.print(&fpchip);

    println!("b = ");
    b.print(&fpchip);

    println!("c = ");
    c.print(&fpchip);

    println!("~~~~~Ckt over~~~~~");

    // Comparison

    // ORIGINAL MULTIPICATION
    // at git commit - a07444642cd61c4bd9732bb96f9762a3aa645fa1
    // cells for
    // N=M=K=20 are 2049200
    // N=M=K=50 are 32007500
    // Number of cells grows as 250*N^3

    // NEW MULTIPICATION
    // at git commit - 367bee6a27a606e006fdfac60927d22fed996399
    // cells for
    // N=M=K=20 are 753200
    // N=M=K=50 are 11757500
    // Number of cells grows as 94*N^3
}

fn main() {
    set_var("LOOKUP_BITS", 12.to_string());

    env_logger::init();

    let args = Cli::parse();

    // run different zk commands based on the command line arguments
    run(zk_random_verif_algo, args);
}

// TODO:
// select good value of LOOKUP_BITS

// to run:
// export LOOKUP_BITS=12
// cargo run --example matrix -- --name divide_by_32 -k 16 mock
