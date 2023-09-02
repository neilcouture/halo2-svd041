use clap::Parser;
use halo2_base::gates::{GateChip, GateInstructions};
use halo2_base::utils::ScalarField;
use halo2_base::AssignedValue;
#[allow(unused_imports)]
use halo2_base::{
    Context,
    QuantumCell::{Constant, Existing, Witness},
};
use halo2_scaffold::scaffold::cmd::Cli;
use halo2_scaffold::scaffold::run;
use serde::{Deserialize, Serialize};

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
// for i in range(1000):
//     if i>=start and i <=end:
//         out.append(in[i])

fn some_algorithm_in_zk<F: ScalarField>(
    ctx: &mut Context<F>,
    input: &Vec<F>,
    make_public: &mut Vec<AssignedValue<F>>,
) {
}

fn main() {
    // env_logger::init();

    // let args = Cli::parse();

    // // run different zk commands based on the command line arguments
    // run(some_algorithm_in_zk, args);
}
