# THIS PROJECT IS CURRENTLY UNSTABLE and not fully working

From `examples/svd_examples.rs::main()

* `test_zkvector` is working
* `test_zkmatrix` is working
* `zk_svd` is not working...

  
# Halo2-svd

This repository provides functions for efficiently proving the singular value decomposition (SVD) of a real valued matrix in a Halo2 circuit. In addition, it also provides functions for manipulating real valued matrices and vectors.

See this [blog](https://hackmd.io/@SQko9rCYRT67XG7dx6zaRQ/r1cWTJEfT) for a description the algorithms used for this library.

## Main functionalities

Real numbers are encoded and manipulated using a [fork](https://github.com/goforashutosh/ZKFixedPointChip) of [ZKFixedPointChip](https://github.com/DCMMC/ZKFixedPointChip), which improves the efficiency of some operations (see [this](https://github.com/DCMMC/ZKFixedPointChip/pull/1) PR).

### struct ZkVector

A simple struct which holds a fixed-point circuit encoded real vector with support for basic functions for linear algebra including `inner_product`, `norm`, and `dist`.

### struct ZkMatrix

A simple struct which holds a fixed-point circuit encoded real matrix and its dimensions with support for basic functions for linear algebra including matrix multiplication (`verify_mul` and `rescale_matrix`) and `transpose_matrix`.

### Matrix multiplication

In order to multiply two fixed-point chip encoded matrices `A` and `B` in a zk-circuit, we use Freivalds' algorithm (implemented using a Schwartz-Zippel lemma based random vector) to simply check that a matrix `C` claimed to be the product `AB` by the prover is indeed correct. This allows us to perform matrix multiplication with only O($N^2$) operations in circuit (Note O$(N^2)$ is linear in the size of the matrix).

To multiply two ZkMatrix `a` and `b`, in the first phase of the circuit (see [Challenge API](https://hackmd.io/@axiom/SJw3p-qX3))

```
// this creates an unscaled product of `a` and `b` and commits to it in the first phase
let c_s = honest_prover_mat_mul(ctx, a, b);
// this rescales c_s
// c is the product of `a` and `b`
let c = ZkMatrix::rescale_matrix(ctx, fpchip, c_s)
// now use `c` however you wish
```

In the second phase of the circuit, one must verify that the claimed product above is correct by calling

```
ZkMatrix::verify_mul(ctx, fpchip, a, b, c_s, init_rand)
```

where `init_rand` is `rlc.gamma()`.

It should be noted that the `rescale_matrix` operation above is much costlier ($60N^2$ to $100N^2$ depending on the lookup table size; for precision greater than 32, this could be higher) than `verify_mul` (~$9N^2$) and should be avoided if possible.

_NOTE: The fixed point chip does not check for overflows, so one needs to place some bounds on matrices `a` and `b` for their multiplication `c` above to be correct. These bounds are assumed to be enforced by the function or program calling this library._

### Singular value decomposition (SVD)

Similar to matrix multiplication, instead of performing SVD in circuit, we simply verify it. For a matrix `a` (N X M matrix), to verify that claimed ZkMatrices `u` (N X N matrix) and `v` (M X M matrix), and a ZkVector `d` (min{N, M} long) are the SVD of `a`, i.e., `u` and `v` are orthogonal and `a = u*Diag(d)*v`, one can call `check_svd_phase0` in the first phase of the circuit and `check_svd_phase1` in the second phase of the circuit.

_NOTE: Once again, because the fixed point chip does not check for overflows, one needs to place some bound on $\Vert a \Vert_2$. Specifically, it should be sufficient to ensure that $m \Vert a \Vert_2 < 2^P$. This bound is assumed to be enforced by the function or program calling this library._

## Error parameter choices

For the choice of error parameters for the `check_svd_phase0` function and its relation to the error parameter of numpy's error parameters refer to the pdf [Error Analysis for SVD](<./Error Analysis for SVD.pdf>)

## Performance

The number of cells required for SVD depends on the `LOOKUP_BITS` and the `PRECISION_BITS`. For `LOOKUP_BITS =19` and `PRECISION_BITS= 32`, the number of advice cells grow as $162N^2 = 135N^2 + 27N^2$ (first phase + second phase) with $26N^2$ lookup cells and for `LOOKUP_BITS =19` and `PRECISION_BITS= 63` the number of advice cells grows as $228N^2 = 201N^2 + 27N^2$ (first phase + second phase) with $48N^2$ lookup cells.

## To Run

### With Mock Prover

To run the example file, first generate the input files using Python as

```
python3 input-creator.py <SIZE>
```

for random square matrices or

```
python3 input-creator.py <SIZE> <SIZE>
```

for random rectangular matrices.

Then, use

```
cargo run --example svd_example -- <FILE>
```

where `<FILE>` is either `matrix` or `matrix-wrong`. SVD should verify on `matrix` but fail on `matrix-wrong`.

### Real proof generation and verification

We need to use a fork of the axiom-eth repository for this. For this reason, you need to switch to the branch `full-proof` of this repo to run proof generation and verification. Once there, you can simply use the above commands.

## Contributors

- [Neil Couture](https://github.com/neilcouture) Effort to compile with Halo2-lib version [0.4.1](https://github.com/axiom-crypto/halo2-lib/tree/v0.4.1)
- [Ashutosh Marwah](https://github.com/goforashutosh)
- [Guillaume Remy](https://github.com/GuillaumeRemy92)
- Zhengxun Wu

## Acknowledgments

This project was conducted as part of [Axiom Open Source Program](https://www.axiom.xyz/open-source). We are grateful to N. Feng, Y. Sun, and J. Wang for organizing it. It’s build on top of ZK circuit primitives provided by [Halo2](https://github.com/privacy-scaling-explorations/halo2), Axiom’s [Halo2-lib](https://github.com/axiom-crypto/halo2-lib), [Halo2-scaffold](https://github.com/axiom-crypto/halo2-scaffold) and [ZKFixedPointChip](https://github.com/DCMMC/ZKFixedPointChip).
