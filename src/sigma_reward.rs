#![allow(non_snake_case)]

// Homomorphic reward-claim proof π_i^(reward), newest paper §3.2.
//
// Public objects:
//
//     C'_{i,x}   = g^{s_{i,x}} h^{v_{i,x}}
//     C_pay,i   = g^{s_p,i} h^{P_i}
//     B_x, D    public constants
//
// If the exact relation P_i * B_x = v_{i,x} * D holds, then:
//
//     R_i = C_pay,i^{B_x} · (C'_{i,x})^{-D}
//         = g^{s_p,i B_x - s_{i,x} D}
//         = g^{Δ_i}
//
// The proof is a Schnorr proof of knowledge of Δ_i:
//
//     e = H(i, g, C'_{i,x}, C_pay,i, A_i)
//     z = ρ + e Δ_i
//     π_i^(reward) = (e, z)
//
// Verification reconstructs A_i = g^z · R_i^{-e} and checks the challenge.
//
// IMPORTANT: the newest paper says it ignores rounding dust. This implementation
// supports the exact equality case only. If D*v is not divisible by B_x, callers
// must decide a dust policy before using this proof for real settlement.

use curv::elliptic::curves::{Point, Scalar, Secp256k1};
use merlin::Transcript;

use crate::{transcript::TranscriptProtocol, Errors};

#[derive(Clone, Debug)]
pub struct SigmaRewardProof {
    pub e: Scalar<Secp256k1>,
    pub z: Scalar<Secp256k1>,
}

impl SigmaRewardProof {
    pub fn prove(
        transcript: &mut Transcript,
        voter_id: usize,
        g: &Point<Secp256k1>,
        C_prime: &Point<Secp256k1>,
        C_pay: &Point<Secp256k1>,
        delta: &Scalar<Secp256k1>,
    ) -> SigmaRewardProof {
        transcript.append_message(b"dom-sep", b"sigma_reward v1 exact");
        transcript.append_u64(b"voter_id", voter_id as u64);
        transcript.append_point(b"g", g);
        transcript.append_point(b"C_prime", C_prime);
        transcript.append_point(b"C_pay", C_pay);

        let rho = Scalar::<Secp256k1>::random();
        let A = g * &rho;
        transcript.append_point(b"A", &A);

        let e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");
        let z = rho + e.clone() * delta.clone();

        SigmaRewardProof { e, z }
    }

    pub fn verify(
        &self,
        transcript: &mut Transcript,
        voter_id: usize,
        g: &Point<Secp256k1>,
        C_prime: &Point<Secp256k1>,
        C_pay: &Point<Secp256k1>,
        reward_total: &Scalar<Secp256k1>,
        dao_bounty: &Scalar<Secp256k1>,
    ) -> Result<(), Errors> {
        transcript.append_message(b"dom-sep", b"sigma_reward v1 exact");
        transcript.append_u64(b"voter_id", voter_id as u64);
        transcript.append_point(b"g", g);
        transcript.append_point(b"C_prime", C_prime);
        transcript.append_point(b"C_pay", C_pay);

        // R_i = C_pay^{B_x} · (C'_{i,x})^{-D}.
        // Additive notation: R_i = C_pay * B_x - C_prime * D.
        let R_i = C_pay * reward_total - C_prime * dao_bounty;
        let A_hat = g * &self.z - &R_i * &self.e;

        transcript.append_point(b"A", &A_hat);
        let expected_e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");

        if expected_e != self.e {
            return Err(Errors::VotingError);
        }

        Ok(())
    }
}
