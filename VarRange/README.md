# Aggregated Range Proof Component for HC Voting

This directory contains the aggregated range proof component used in the implementation of the decentralized privacy-preserving Holographic Consensus (HC) Voting protocol.

The component enables a prover to demonstrate that committed voting values satisfy predefined constraints without revealing the underlying values.

In HC Voting, the range proof is used to verify that committed values satisfy a token budget constraint. Specifically, given committed values:

\[
v_1, v_2, v_{slack}
\]

the proof demonstrates that:

\[
v_1 + v_2 + v_{slack}=T_i
\]

where \(T_i\) represents the allocated voting budget.

The implementation follows a Bulletproof-style aggregated range proof approach. It combines Pedersen commitments, Fiat-Shamir challenges, and an inner-product argument to provide zero-knowledge verification of the range constraint.

The proof structure consists of:

\[
\pi_i^{(ar)}=(s_{sum}, A, S, T_1, T_2, \tau_x, \mu, \pi_{IP})
\]

where the inner-product argument is used to verify the polynomial commitment relation without revealing the committed values.

## Installation

To set up the environment for this project, visit the official Rust website at [https://www.rust-lang.org/tools/install](https://www.rust-lang.org/tools/install) to install Rust.

For Linux and macOS, you can install Rust using the command:

`curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh`

Verify the installation: `rustc --version`

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


### File Organization

The HC Voting aggregated range proof component is structured as follows:

### Root Directory

- **`Cargo.toml`**: Defines the Rust project dependencies, package metadata, and compilation configuration.

- **`README.md`**: Provides an overview of the HC Voting range proof component, installation instructions, and usage guidelines.

- **`src/`**: Contains the Rust source code implementing the aggregated range proof, inner-product argument, transcript management, and supporting cryptographic components.

---

## `src/` Directory

- **`lib.rs`**: The main entry point of the library. It organizes and exposes the core modules used by the HC Voting range proof implementation.

- **`varrange.rs`**: Implements the main aggregated range proof protocol for HC Voting.

  This module provides:

  - HC Voting proof generation through:

    ```rust
    VarRange::prove_hc_voting()
    ```

  - HC Voting proof verification through:

    ```rust
    VarRange::verify_hc_voting()
    ```

  The implementation proves that committed voting values satisfy the required budget constraint while preserving zero-knowledge privacy.

  The proof construction includes:

  - aggregated bit decomposition,
  - Pedersen commitments,
  - Fiat-Shamir challenge generation,
  - polynomial commitment construction,
  - inner-product argument integration.

  The proof structure follows:

  \[
  \pi_i^{(ar)}
  =
  (s_{sum}, A, S, T_1, T_2, \tau_x, \mu, \pi_{IP})
  \]

  as implemented in the HC Voting protocol.

---

- **`ipa.rs`**: Implements the inner-product argument used by the aggregated range proof.

  The module provides the combined IPA construction:

  ```rust
  prove_combined()