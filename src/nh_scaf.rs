use std::env::var;
use std::fs;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use axiom_eth::snark_verifier::loader::native::NativeLoader;

use snark_verifier_sdk::{CircuitExt, gen_pk, read_pk};
use snark_verifier_sdk::halo2::{gen_snark_shplonk, PoseidonTranscript, read_snark};
use crate::scaffold::cmd::{Cli, SnarkCmd};
use halo2_base::utils::{ScalarField, BigPrimeField};
use halo2_base::{
    AssignedValue,
    gates::{
        circuit::{BaseCircuitParams, builder::BaseCircuitBuilder, CircuitBuilderStage},
        flex_gate::MultiPhaseThreadBreakPoints,
    },
    halo2_proofs::{
        dev::MockProver,
        halo2curves::bn256::{Bn256, Fr, G1Affine},
        plonk::{Circuit, ProvingKey, verify_proof, VerifyingKey},
        poly::{
            commitment::{Params, ParamsProver},
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::VerifierSHPLONK,
                strategy::SingleStrategy,
            },
        },
        SerdeFormat,
    },
    utils::fs::gen_srs,
};


trait NHZKPrivate<F> {
    fn data(&self) -> (Vec<F>, F, Vec<Vec<f64>>, Vec<f64>, f64);
}

pub struct NHCircuitInput<F> {
    pub data : (Vec<F>, F, Vec<Vec<f64>>, Vec<f64>, f64),
}

impl<F: BigPrimeField> NHZKPrivate<F> for NHCircuitInput<F> {
    fn data(&self) -> (Vec<F>, F, Vec<Vec<f64>>, Vec<f64>, f64)
    {
        self.data.clone()
    }
}

// impl<T: BigPrimeField> NHZKPrivate<Fr> for NHCircuitInput<T> {
//     fn data(&self) -> (Vec<T>, T, Vec<Vec<f64>>, Vec<f64>, f64)
//     {
//         self.data.clone()
//     }
// }
#[derive(Clone, Debug)]
pub struct NHCircuitScaffold<F, Fn> {
    f: Fn,
    private_inputs: (Vec<F>, F, Vec<Vec<f64>>, Vec<f64>, f64),
}


pub fn run_nh<T: BigPrimeField, N: NHZKPrivate<T>>(
    f: impl FnOnce(&mut BaseCircuitBuilder<Fr>, (Vec<T>, T, Vec<Vec<f64>>, Vec<f64>, f64), &mut Vec<AssignedValue<Fr>>),
    data: N,
    cli: Cli )
{
    //let dd : (Vec<T>, T, Vec<Vec<f64>>, Vec<f64>, f64) = data.data();
    run_on_inputs_nh(f, cli, data);
}


pub fn run_on_inputs_nh<T: BigPrimeField, N: NHZKPrivate<T>>(
    f: impl FnOnce(
        &mut BaseCircuitBuilder<Fr>,
        (Vec<T>, T, Vec<Vec<f64>>, Vec<f64>, f64),
        &mut Vec<AssignedValue<Fr>>),
    cli: Cli,
    data: N,
) {
    let private_inputs = data.data();
    let precircuit = NHCircuitScaffold { f, private_inputs };

    let name = cli.name;
    let k = cli.degree;

    let config_path = cli.config_path.unwrap_or_else(|| PathBuf::from("configs"));
    let data_path = cli.data_path.unwrap_or_else(|| PathBuf::from("data"));
    fs::create_dir_all(&config_path).unwrap();
    fs::create_dir_all(&data_path).unwrap();

    let params = gen_srs(k);
    println!("Universal trusted setup (unsafe!) available at: params/kzg_bn254_{k}.srs");
    match cli.command {
        SnarkCmd::Mock => {
            let mut assigned_instances = vec![];
            let circuit = precircuit.create_circuit(
                CircuitBuilderStage::Mock,
                None,
                &params,
                &mut assigned_instances);
            MockProver::run(k, &circuit, circuit.instances()).unwrap().assert_satisfied();                          // MOCK
        }
        SnarkCmd::Keygen => {
            let pk_path = data_path.join(PathBuf::from(format!("{name}.pk")));
            if pk_path.exists() {
                fs::remove_file(&pk_path).unwrap();
            }
            let pinning_path = config_path.join(PathBuf::from(format!("{name}.json")));
            let mut assigned_instances = vec![];
            let circuit = precircuit.create_circuit(
                CircuitBuilderStage::Keygen, None, &params, &mut assigned_instances);  // KEYGEN

            // generate Proving Key ==> circuit used, i.e. f invoked
            let pk = gen_pk(&params, &circuit, None);
            let c_params = circuit.params();

            // breakpoints
            let break_points = circuit.break_points();

            let mut pinning_file = File::create(&pinning_path)
                .unwrap_or_else(|_| panic!("Could not create file at {pinning_path:?}"));
            serde_json::to_writer(&mut pinning_file, &(c_params, break_points))
                .expect("Could not write pinning file");

            let mut pk_file = BufWriter::new(
                File::create(&pk_path)
                    .unwrap_or_else(|_| panic!("Could not create file at {pk_path:?}")),
            );
            pk.write(&mut pk_file, SerdeFormat::RawBytes).expect("Failed to write proving key");
            println!("Proving key written to: {pk_path:?}");

            let vk_path = data_path.join(PathBuf::from(format!("{name}.vk")));
            let f = File::create(&vk_path)
                .unwrap_or_else(|_| panic!("Could not create file at {vk_path:?}"));
            let mut writer = BufWriter::new(f);
            pk.get_vk()
                .write(&mut writer, SerdeFormat::RawBytes)
                .expect("writing vkey should not fail");
            println!("Verifying key written to: {vk_path:?}");
        }
        SnarkCmd::Prove => {
            let pinning_path = config_path.join(PathBuf::from(format!("{name}.json")));
            let mut pinning_file = File::open(&pinning_path)
                .unwrap_or_else(|_| panic!("Could not read file at {pinning_path:?}"));
            let pinning: (BaseCircuitParams, MultiPhaseThreadBreakPoints) =
                serde_json::from_reader(&mut pinning_file).expect("Could not read pinning file");

            let mut assigned_instances = vec![];

            let circuit =
                precircuit.create_circuit(CircuitBuilderStage::Prover, Some(pinning), &params, &mut assigned_instances);                  // PROVE
            let pk_path = data_path.join(PathBuf::from(format!("{name}.pk")));
            let pk = nh_custom_read_pk(pk_path, &circuit);
            let snark_path = data_path.join(PathBuf::from(format!("{name}.snark")));
            if snark_path.exists() {
                fs::remove_file(&snark_path).unwrap();
            }
            let start = Instant::now();
            // GENERATE SNARK PROOF
            gen_snark_shplonk(&params, &pk, circuit, Some(&snark_path));
            let prover_time = start.elapsed();
            println!("Proving time: {:?}", prover_time);
            println!("Snark written to: {snark_path:?}");
        }
        SnarkCmd::Verify => {
            let vk_path = data_path.join(PathBuf::from(format!("{name}.vk")));
            let mut assigned_instances = vec![];
            let mut circuit = precircuit.create_circuit(
                CircuitBuilderStage::Keygen, None, &params, &mut assigned_instances);     // VERIFY
            let vk = nh_custom_read_vk(vk_path, &circuit);
            let snark_path = data_path.join(PathBuf::from(format!("{name}.snark")));
            let snark = read_snark(&snark_path)
                .unwrap_or_else(|e| panic!("Snark not found at {snark_path:?}. {e:?}"));

            let verifier_params = params.verifier_params();
            let strategy = SingleStrategy::new(&params);
            let mut transcript =
                PoseidonTranscript::<NativeLoader, &[u8]>::new::<0>(&snark.proof[..]);
            let instance = &snark.instances[0][..];
            let start = Instant::now();
            verify_proof::<
                KZGCommitmentScheme<Bn256>,
                VerifierSHPLONK<'_, Bn256>,
                _,
                _,
                SingleStrategy<'_, Bn256>,
            >(verifier_params, &vk, strategy, &[&[instance]], &mut transcript)
                .unwrap();
            let verification_time = start.elapsed();
            println!("Snark verified successfully in {:?}", verification_time);
            circuit.clear();
        }
    }
}


pub fn nh_proove_verify<T: BigPrimeField, N: NHZKPrivate<T>>(
    f: impl FnOnce(
        &mut BaseCircuitBuilder<Fr>,
        (Vec<T>, T, Vec<Vec<f64>>, Vec<f64>, f64),
        &mut Vec<AssignedValue<Fr>>),
    cli: Cli,
    data: N,
) -> Vec<Fr> {
    let private_inputs = data.data();
    let mut precircuit = NHCircuitScaffold { f, private_inputs};

    let name = cli.name;
    let k = cli.degree;

    let config_path = cli.config_path.unwrap_or_else(|| PathBuf::from("configs"));
    let data_path = cli.data_path.unwrap_or_else(|| PathBuf::from("data"));
    fs::create_dir_all(&config_path).unwrap();
    fs::create_dir_all(&data_path).unwrap();

    let params = gen_srs(k);
    println!("Universal trusted setup (unsafe!) available at: params/kzg_bn254_{k}.srs");
    match cli.command {
        SnarkCmd::Mock => {
            println!("Mock should not be used with nh_proove_verify");
            vec![]
        }
        SnarkCmd::Keygen => {
            println!("Keygen should not be used with nh_proove_verify");
            vec![]
        }
        SnarkCmd::Prove => {
            let pinning_path = config_path.join(PathBuf::from(format!("{name}.json")));
            let mut pinning_file = File::open(&pinning_path)
                .unwrap_or_else(|_| panic!("Could not read file at {pinning_path:?}"));
            let pinning: (BaseCircuitParams, MultiPhaseThreadBreakPoints) =
                serde_json::from_reader(&mut pinning_file).expect("Could not read pinning file");

            let mut assigned_instances = vec![];

            let circuit =
                precircuit.create_circuit(CircuitBuilderStage::Prover, Some(pinning), &params, &mut assigned_instances);                  // PROVE

            let pk_path = data_path.join(PathBuf::from(format!("{name}.pk")));
            let pk = nh_custom_read_pk(pk_path, &circuit);
            let snark_path = data_path.join(PathBuf::from(format!("{name}.snark")));
            if snark_path.exists() {
                fs::remove_file(&snark_path).unwrap();
            }
            let start = Instant::now();
            // GENERATE SNARK PROOF
            gen_snark_shplonk(&params, &pk, circuit, Some(&snark_path));
            let prover_time = start.elapsed();
            println!("Proving time: {:?}", prover_time);
            println!("Snark written to: {snark_path:?}");

            let public_io: Vec<Fr> = assigned_instances.iter().map(|v| *v.value()).collect();
            public_io
        }
        SnarkCmd::Verify => {
            // Start Verify !
            let vk_path = data_path.join(PathBuf::from(format!("{name}.vk")));
            let mut assigned_instances = vec![];
            let mut circuit = precircuit.create_circuit(
                CircuitBuilderStage::Keygen, None, &params, &mut assigned_instances);     // VERIFY
            let vk = nh_custom_read_vk(vk_path, &circuit);
            let snark_path = data_path.join(PathBuf::from(format!("{name}.snark")));
            let snark = read_snark(&snark_path)
                .unwrap_or_else(|e| panic!("Snark not found at {snark_path:?}. {e:?}"));

            let verifier_params = params.verifier_params();
            let strategy = SingleStrategy::new(&params);
            let mut transcript =
                PoseidonTranscript::<NativeLoader, &[u8]>::new::<0>(&snark.proof[..]);
            let instance = &snark.instances[0][..];
            let start = Instant::now();
            verify_proof::<
                KZGCommitmentScheme<Bn256>,
                VerifierSHPLONK<'_, Bn256>,
                _,
                _,
                SingleStrategy<'_, Bn256>,
            >(verifier_params, &vk, strategy, &[&[instance]], &mut transcript)
                .unwrap();
            let verification_time = start.elapsed();
            println!("Snark verified successfully in {:?}", verification_time);
            circuit.clear();

            vec![]
        }
        // SnarkCmd::Verify => {
        //     println!("Verify should not be used with nh_proove_verify");
        //     vec![]
        // }
    }
}



impl<T, Fn> NHCircuitScaffold<T, Fn>
    where
        Fn: FnOnce(&mut BaseCircuitBuilder<Fr>,
            (Vec<T>, T, Vec<Vec<f64>>, Vec<f64>, f64),
            &mut Vec<AssignedValue<Fr>>),
{
    /// Creates a Halo2 circuit from the given function.
    fn create_circuit(
        mut self,
        stage: CircuitBuilderStage,
        pinning: Option<(BaseCircuitParams, MultiPhaseThreadBreakPoints)>,
        params: &ParamsKZG<Bn256>,
        assigned_instances: &mut Vec<AssignedValue<Fr>>
    ) -> BaseCircuitBuilder<Fr>
    {
        let mut builder = BaseCircuitBuilder::from_stage(stage);
        if let Some((params, break_points)) = pinning {
            builder.set_params(params);
            builder.set_break_points(break_points);
        } else {
            let k = params.k() as usize;
            // we use env var `LOOKUP_BITS` to determine whether to use `GateThreadBuilder` or `RangeCircuitBuilder`. The difference is that the latter creates a lookup table with 2^LOOKUP_BITS rows, while the former does not.
            let lookup_bits: Option<usize> = var("LOOKUP_BITS")
                .map(|str| {
                    let lookup_bits = str.parse::<usize>().unwrap();
                    // we use a lookup table with 2^LOOKUP_BITS rows. Due to blinding factors, we need a little more than 2^LOOKUP_BITS rows total in our circuit
                    assert!(lookup_bits < k, "LOOKUP_BITS needs to be less than DEGREE");
                    lookup_bits
                })
                .ok();
            // we initiate a "thread builder". This is what keeps track of the execution trace of our program. If not in proving mode, it also keeps track of the ZK constraints.
            builder.set_k(k);
            if let Some(lookup_bits) = lookup_bits {
                builder.set_lookup_bits(lookup_bits);
            }
            builder.set_instance_columns(1);
        };

        // builder.main(phase) gets a default "main" thread for the given phase. For most purposes we only need to think about phase 0
        // we need a 64-bit number as input in this case
        // while `some_algorithm_in_zk` was written generically for any field `F`, in practice we use the scalar field of the BN254 curve because that's what the proving system backend uses
        //let mut assigned_instances = vec![];

        // this is where function is invoked
        (self.f)(&mut builder, self.private_inputs, assigned_instances);

        let public_io: Vec<Fr> = assigned_instances.iter().map(|v| *v.value()).collect();

        if !assigned_instances.is_empty() {
            assert_eq!(builder.assigned_instances.len(), 1, "num_instance_columns != 1");
            builder.assigned_instances[0] = assigned_instances.clone();
        }

        if !stage.witness_gen_only() {
            // now `builder` contains the execution trace, and we are ready to actually create the circuit
            // minimum rows is the number of rows used for blinding factors. This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
            let minimum_rows =
                var("MINIMUM_ROWS").unwrap_or_else(|_| "20".to_string()).parse().unwrap();
            builder.calculate_params(Some(minimum_rows));
        }

        builder
    }
}


fn nh_custom_read_pk<C, P>(fname: P, circuit: &C) -> ProvingKey<G1Affine>
    where
        C: Circuit<Fr>,
        P: AsRef<Path>,
{
    read_pk::<C>(fname.as_ref(), circuit.params())
        .unwrap_or_else(|e| panic!("Failed to open file: {:?}: {e:?}", fname.as_ref()))
}

fn nh_custom_read_vk<C, P>(fname: P, circuit: &C) -> VerifyingKey<G1Affine>
    where
        C: Circuit<Fr>,
        P: AsRef<Path>,
{
    let f = File::open(&fname)
        .unwrap_or_else(|e| panic!("Failed to open file: {:?}: {e:?}", fname.as_ref()));
    let mut bufreader = BufReader::new(f);
    VerifyingKey::read::<_, C>(&mut bufreader, SerdeFormat::RawBytes, circuit.params())
        .expect("Could not read vkey")
}