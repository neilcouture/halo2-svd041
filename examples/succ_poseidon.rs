use clap::Parser;
use halo2_base::{
    gates::GateChip, safe_types::GateInstructions, utils::ScalarField, AssignedValue, Context,
};
use halo2_scaffold::scaffold::{cmd::Cli, run};
use poseidon::PoseidonChip;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CircuitInput {
    pub inputs: [String; 2], // two field elements, but as strings for easier deserialization
}

fn hash_two<F: ScalarField>(
    ctx: &mut Context<F>,
    inp: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    // Do hash a n list using 2->1 hash chips
    // compare with n->1 hash list
    // create successive hashing

    let init_rand = F::zero();
    let init_rand = ctx.load_witness(init_rand);
    // `Context` can roughly be thought of as a single-threaded execution trace of a program we want to ZK prove. We do some post-processing on `Context` to optimally divide the execution trace into multiple columns in a PLONKish arithmetization
    // More advanced usage with multi-threaded witness generation is possible, but we do not explain it here

    // first we load a private input `x` (let's not worry about public inputs for now)
    // let [x, y] = inp.inputs.map(|x| ctx.load_witness(F::from_str_vartime(&x).unwrap()));
    // make_public.extend([x, y]);

    // T, R_F, R_P values correspond to POSEIDON-128 values given in Table 2 of the paper
    // also see: https://www.poseidon-hash.info/
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 8;
    const R_P: usize = 57;

    let gate = GateChip::<F>::default();
    let mut hash = init_rand;
    const NUM_RNDS: usize = 5;
    // Comparison; advice cells for:
    // 1 hash- 2257
    // 5 hashes- 11281

    for i in 0..NUM_RNDS {
        // there is a difference between using a single chip and using multiple chips
        // I think the right way is to use multiple chips
        let mut poseidon = PoseidonChip::<F, T, RATE>::new(ctx, R_F, R_P).unwrap();
        poseidon.update(&[hash]);
        hash = poseidon.squeeze(ctx, &gate).unwrap();
        let hash_bits = gate.num_to_bits(ctx, hash, 254);
        // let rand_ve
        println!("poseidon: {:?}", hash.value());
    }
}

fn main() {
    env_logger::init();

    let args = Cli::parse();
    run(hash_two, args);
}
