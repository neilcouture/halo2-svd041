use clap::Parser;
use halo2_base::gates::{GateChip, GateInstructions, RangeChip, RangeInstructions};
use halo2_base::utils::{BigPrimeField, ScalarField};
use halo2_base::AssignedValue;
#[allow(unused_imports)]
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
    /// Outputs the inner product
    /// Order doesn't matter because we are only dealing with real numbers
    pub fn inner_product(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        x: &Vec<AssignedValue<F>>,
    ) -> AssignedValue<F> {
        // couldn't figure out how to use inner_product of fpchip because we use x: &Vec I didn't want to move
        assert!(self.size() == x.len());
        // TODO!: following seems unecessary
        let mut res = fpchip.qadd(ctx, Constant(F::zero()), Constant(F::zero()));
        for i in 0..self.size() {
            let ai_bi = fpchip.qmul(ctx, self.v[i], x[i]);
            res = fpchip.qadd(ctx, res, ai_bi);
        }

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
    pub fn mul(
        &self,
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &ZkMatrix<F, PRECISION_BITS>,
    ) -> Self {
        assert_eq!(a.num_col, self.size());
        let mut y: Vec<AssignedValue<F>> = Vec::new();
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

    /// Verifies that matrices [a], [b], and [c] satisfy [c = a*b]
    pub fn verify_mul(
        ctx: &mut Context<F>,
        fpchip: &FixedPointChip<F, PRECISION_BITS>,
        a: &Self,
        b: &Self,
        c: &Self,
        init_rand: AssignedValue<F>,
        tol: f64,
    ) {
        assert!(tol > 0.0);
        assert_eq!(a.num_col, b.num_rows);
        assert_eq!(c.num_rows, a.num_rows);
        assert_eq!(c.num_col, b.num_col);
        assert!(c.num_col >= 1);

        let d = c.num_col;

        // need to hash these many times to produce enough randomness for one random vector check
        const RAND_PER_HASH: usize = 254;
        let num_hash_per_rnd = (d - 1) / RAND_PER_HASH + 1; // -1 because we want just M hashes at d= M*RAND_PER_HASH

        // this will determine probability of error for the randomized algorithm
        // currently set to 2^-30 ~ 1e-9
        const NUM_RNDS: usize = 1;

        let gate: &GateChip<F> = &fpchip.gate.gate;
        // declare norm_est_sum and contrain it
        let mut norm_sq_est_sum = ctx.load_witness(fpchip.quantization(0.0));
        gate.assert_is_const(ctx, &norm_sq_est_sum, &fpchip.quantization(0.0));

        // T, R_F, R_P values correspond to POSEIDON-128 values given in Table 2 of the Poseidon hash paper
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        // list of hashes used in a round
        let mut hash_list: Vec<AssignedValue<F>> = vec![init_rand];

        // 1 random element already in the list
        for i in 1..num_hash_per_rnd {
            // there is a difference between using a single chip and using multiple chips
            // I think the right way is to use multiple chips
            let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
            poseidon.update(&[hash_list[i - 1]]);
            hash_list.push(poseidon.squeeze(ctx, gate).unwrap());
        }
        // no more mutable
        let hash_list = hash_list;

        // for h in &hash_list {
        //     dbg!(h.value());
        // }

        let mut rand_bin_vec: Vec<AssignedValue<F>> = vec![];
        for i in 0..num_hash_per_rnd {
            let mut new_rand = gate.num_to_bits(ctx, hash_list[i], RAND_PER_HASH);
            rand_bin_vec.append(&mut new_rand);
        }

        let v = convert_vec(ctx, &fpchip, &rand_bin_vec, Some(d));
        // println!("The random vector is: ");
        // v.print(&fpchip);

        let c_times_v = v.mul(ctx, fpchip, c);
        let b_times_v = v.mul(ctx, fpchip, b);
        let ab_times_v = b_times_v.mul(ctx, fpchip, a);

        // println!("c_times_v is: ");
        // c_times_v.print(&fpchip);
        // println!("b_times_v is: ");
        // b_times_v.print(&fpchip);
        // println!("ab_times_v is: ");
        // ab_times_v.print(&fpchip);

        let dist_sq = c_times_v._dist_square(ctx, fpchip, &ab_times_v.v);

        // let dist_sq_dq = fpchip.dequantization(*dist_sq.value());
        // println!("The dist is= {dist_sq_dq}");

        println!("Est sum error= {:?}", fpchip.dequantization(*norm_sq_est_sum.value()));

        norm_sq_est_sum = fpchip.qadd(ctx, norm_sq_est_sum, dist_sq);

        println!("Est sum error= {:?}", fpchip.dequantization(*norm_sq_est_sum.value()));

        // the commitment for all randomness so far
        let mut prev_rand = hash_list[hash_list.len() - 1];

        for _ in 1..NUM_RNDS {
            println!("start rand = {:?}", prev_rand.value());
            let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
            // use old hash and the results of previous computation to compute next hash
            poseidon.update(&[prev_rand, norm_sq_est_sum]);
            let init_rand = poseidon.squeeze(ctx, gate).unwrap();

            // list of hashes used in a round
            let mut hash_list: Vec<AssignedValue<F>> = vec![init_rand];

            // 1 random element already in the list
            for i in 1..num_hash_per_rnd {
                let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
                poseidon.update(&[hash_list[i - 1]]);
                hash_list.push(poseidon.squeeze(ctx, gate).unwrap());
            }
            let hash_list = hash_list;

            let mut rand_bin_vec: Vec<AssignedValue<F>> = vec![];
            for i in 0..num_hash_per_rnd {
                let mut new_rand = gate.num_to_bits(ctx, hash_list[i], RAND_PER_HASH);
                rand_bin_vec.append(&mut new_rand);
            }
            let v = convert_vec(ctx, &fpchip, &rand_bin_vec, Some(d));

            let c_times_v = v.mul(ctx, fpchip, c);
            let b_times_v = v.mul(ctx, fpchip, b);
            let ab_times_v = b_times_v.mul(ctx, fpchip, a);

            let dist_sq = c_times_v._dist_square(ctx, fpchip, &ab_times_v.v);

            norm_sq_est_sum = fpchip.qadd(ctx, norm_sq_est_sum, dist_sq);
            println!("Est sum error= {:?}", fpchip.dequantization(*norm_sq_est_sum.value()));
            prev_rand = hash_list[hash_list.len() - 1];
        }

        let norm_sq_est =
            fpchip.qdiv(ctx, norm_sq_est_sum, Constant(fpchip.quantization(NUM_RNDS as f64)));
        println!("Est error= {:?}", fpchip.dequantization(*norm_sq_est.value()));
        // ensure dist is smaller than tolerance
        // should depend on size of matrix; make sizes constant
        // have to explicitly use quantization here
        let quant_tol = (tol * (2u64.pow(PRECISION_BITS) as f64)) as u64;
        fpchip.gate.check_less_than_safe(ctx, norm_sq_est, quant_tol);
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

    println!("**The errors for Norm and dist are pretty big**");
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

fn some_algorithm_in_zk<F: ScalarField>(
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
    let c = ZkMatrix::new(ctx, &fpchip, &c);

    // hashing requires ~1000 cells per element
    let init_rand = ZkMatrix::hash_matrix_list(ctx, gate, vec![&a, &b, &c]);
    // dbg!(init_rand.value());
    ZkMatrix::verify_mul(ctx, &fpchip, &a, &b, &c, init_rand, 1e-3);

    // number of advice columns seems to grow as 7200*dim^2- with 5 hashes
    // 26000*dim^2 with 30 hashes
    // 3000 would just be from init_hash
    // 2000 per hash- only 30*2000 overall
    // 777 from a single vector multiplication
}

fn main() {
    set_var("LOOKUP_BITS", 12.to_string());

    env_logger::init();

    let args = Cli::parse();

    // run different zk commands based on the command line arguments
    run(some_algorithm_in_zk, args);
}

// TODO:
// select good value of LOOKUP_BITS

// to run:
// export LOOKUP_BITS=5
// cargo run --example matrix -- --name divide_by_32 -k 12 mock
