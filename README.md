# Decentralized Privacy-Preserving Holographic Consensus Voting

This repository provides a complete implementation of a decentralized privacy-preserving Holographic Consensus (HC) voting protocol.

Holographic Consensus (HC) is a scalable governance mechanism designed for Decentralized Autonomous Organizations (DAOs). Existing HC implementations reveal individual voting information by publishing plaintext votes together with digital signatures, which compromises ballot privacy.

This repository implements a decentralized self-tallying HC voting protocol that preserves ballot secrecy while maintaining public verifiability. The protocol allows voters to independently compute the final tally without requiring a trusted tallying authority.

The implementation combines:

- Pedersen commitments for hiding vote values,
- Sigma protocols for commitment consistency and knowledge proofs,
- aggregated Bulletproof range proofs for enforcing voting constraints,
- self-tallying commitment mechanisms,
- dropout recovery mechanisms,
- privacy-preserving reward claims.

The protocol supports the complete HC workflow:

1. Boosting (prediction) stage
2. Voting (decision) stage
3. Public tally extraction
4. Reward distribution

The implementation includes:
- core HC voting protocol,
- zero-knowledge proof components,
- range proof integration,
- benchmark implementations,
- scripts for reproducing experimental results.


## Installation

To set up the environment for this project, visit the official Rust website:

https://www.rust-lang.org/tools/install

For Linux and macOS, Rust can be installed using:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

## Build and Test

This project requires the GMP library for high-performance arithmetic operations.

Install GMP

* For Ubuntu/Debian systems:
  `sudo apt-get install libgmp-dev`.

* For macOS:
  `brew install gmp`. 

  After installation, set the environment variables according to your Mac processor type so that the compiler and linker can find the GMP library files:    
  - For Apple-Silicon macOS:  
    `export LIBRARY_PATH="/opt/homebrew/lib"`

    `export CPATH="/opt/homebrew/include"`

  - For Intel Macs:  
    `export LIBRARY_PATH="/usr/local/lib"`

    `export CPATH="/usr/local/include"`

Build the project: `cargo build --release`

Run tests: `cargo test --release`

## Benchmark Scripts

We provide a set of shell scripts in the  `script` directory to reproduce data reported in the paper. 

Please ensure the `bc` command-line calculator is installed, as some scripts require it for floating-point calculations. On most Linux systems, install it with: `sudo apt install bc`. 


The benchmark evaluates the performance of the HC Voting protocol, including:

- commitment generation,
- zero-knowledge proof generation,
- zero-knowledge proof verification,
- range proof generation and verification,
- tally extraction.

### Running Benchmarks

To run the benchmark experiments:

```bash
cargo test benchmark_real_world_hc_voting_table --release -- --nocapture
     

## Notes

For large-scale experiments, multiple voters are simulated on a single machine. In a real deployment, each voter would independently execute the voting procedure.

Execution time may increase for large DAO configurations because the benchmark evaluates the complete cryptographic workflow, including proof generation, verification, and tally extraction.

The storage overhead is calculated based on the size of cryptographic objects stored during the protocol execution.

The implementation uses Secp256k1 curve parameters:

- Field element size: 32 bytes
- Group element size: 33 bytes

The tally extraction experiment uses Shanks' baby-step giant-step algorithm for bounded discrete logarithm recovery.



## File Organization

The HC Voting project is structured as follows:

### Root Directory

- **`Cargo.toml`**: Defines the project dependencies, package metadata, and compilation configuration.
- **`README.md`**: Provides an overview of the project, installation instructions, benchmark execution instructions, and usage guidelines.
- **`VarRange/`**: Contains the aggregated range proof component integrated into HC Voting. The component is used to generate and verify range proofs while preserving the privacy of committed voting values.
- **`src/`**: Contains the core implementation of the HC Voting protocol and its cryptographic building blocks.
- **`tests/`**: Contains benchmark implementations used to evaluate the computational performance of HC Voting, including proof generation, proof verification, and tallying operations.
- **`Dockerfile`**: Provides a reproducible environment with the required dependencies for building and running the implementation.

### `src/` Directory

- **`lib.rs`**: The main entry point of the HC Voting library. It organizes and exposes the core protocol modules.
- **`voting.rs`**: Implements the core HC Voting protocol, including voting operations, tallying, and protocol execution.
- **`sigma_dl.rs`**: Implements Sigma protocols for proving knowledge of discrete logarithms.
- **`sigma_dleq.rs`**: Implements Sigma protocols for proving equality of discrete logarithms.
- **`sigma_hc_eq.rs`**: Implements HC equality proofs used to verify consistency relations between cryptographic commitments.
- **`sigma_reward.rs`**: Implements zero-knowledge reward proofs used in the privacy-preserving reward mechanism.
- **`transcript.rs`**: Implements transcript management for Fiat-Shamir transformations used in non-interactive zero-knowledge proofs.

