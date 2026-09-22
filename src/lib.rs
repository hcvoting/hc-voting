#![allow(clippy::many_single_char_names, clippy::too_many_arguments)]
#![allow(dead_code)]
#![allow(non_snake_case)]

pub mod sigma_dl;
pub mod sigma_dleq;
pub mod sigma_hc_eq;
pub mod sigma_reward;
pub mod transcript;
pub mod voting;
//mod sum_square;

//extern crate serde_derive;
extern crate serde;

extern crate curv;
extern crate generic_array;
extern crate itertools;
extern crate sha2;
pub use voting::*;

#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum Errors {
    SigmaDlProofError,
    SigmaDleqProofError,
    VotingError,
    RangeProofError,
    RewardProofError
}