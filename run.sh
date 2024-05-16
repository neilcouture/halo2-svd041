#!/bin/sh

export RUST_BACKTRACE=full
export RUST_BACKTRACE=1

cargo b --release
cargo run --release --package halo2-svd --example svd_example_nh matrix