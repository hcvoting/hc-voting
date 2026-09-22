#![allow(non_snake_case)]

// Identity-bound compressed Chaum-Pedersen DLEQ proof.
//
// Used by the newest paper's recovery proof π_i^(rec):
//
//     log_g(h_{i,x}) = log_{\hat g_{i,x}}(\hat C_{i,x}) = r_{i,x}
//
// The proof stores only:
//
//     π_i^(rec) = (e, {z_x}_x)
//
// and reconstructs the ephemeral commitments during verification.

use curv::elliptic::curves::{Point, Scalar, Secp256k1};
use merlin::Transcript;

use crate::{transcript::TranscriptProtocol, Errors};

const DEFAULT_VOTER_ID: usize = 0;

#[derive(Clone, Debug)]
pub struct SigmaDleqProof {
    pub e: Scalar<Secp256k1>,
    pub z_vec: Vec<Scalar<Secp256k1>>,
}

impl SigmaDleqProof {
    /// Backward-compatible API used by existing benchmark code.
    ///
    /// Legacy order is `(w_vec, y1_vec, y2_vec, g_vec, h_vec, n)`, proving
    /// `y1_i = g_i^{w_i}` and `y2_i = h_i^{w_i}`. It uses the newest compressed
    /// proof shape but binds to voter id 0.
    pub fn prove(
        transcript: &mut Transcript,
        w_vec: &[Scalar<Secp256k1>],
        y1_vec: &[Point<Secp256k1>],
        y2_vec: &[Point<Secp256k1>],
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        n: usize,
    ) -> SigmaDleqProof {
        Self::prove_with_voter_id(
            transcript,
            DEFAULT_VOTER_ID,
            w_vec,
            y1_vec,
            y2_vec,
            g_vec,
            h_vec,
            n,
        )
    }

    /// Newest-paper API: identity-bound compressed recovery proof.
    pub fn prove_with_voter_id(
        transcript: &mut Transcript,
        voter_id: usize,
        w_vec: &[Scalar<Secp256k1>],
        y1_vec: &[Point<Secp256k1>],
        y2_vec: &[Point<Secp256k1>],
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        n: usize,
    ) -> SigmaDleqProof {
        assert!(n > 0);
        assert_eq!(w_vec.len(), n);
        assert_eq!(y1_vec.len(), n);
        assert_eq!(y2_vec.len(), n);
        assert_eq!(g_vec.len(), n);
        assert_eq!(h_vec.len(), n);

        transcript.append_message(b"dom-sep", b"sigma_dleq v2 identity-bound compressed");
        transcript.append_u64(b"n", n as u64);
        transcript.append_u64(b"voter_id", voter_id as u64);
        transcript.append_points_array(b"g_vec", g_vec);
        transcript.append_points_array(b"h_vec", h_vec);
        transcript.append_points_array(b"y1_vec", y1_vec);
        transcript.append_points_array(b"y2_vec", y2_vec);

        let rho_vec = (0..n)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let R1_vec = (0..n)
            .map(|i| &g_vec[i] * &rho_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let R2_vec = (0..n)
            .map(|i| &h_vec[i] * &rho_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        transcript.append_points_array(b"R1_vec", &R1_vec);
        transcript.append_points_array(b"R2_vec", &R2_vec);

        let e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");

        let z_vec = (0..n)
            .map(|i| rho_vec[i].clone() + e.clone() * w_vec[i].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();

        SigmaDleqProof { e, z_vec }
    }

    /// Backward-compatible verifier for benchmarks. Uses voter id 0.
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        y1_vec: &[Point<Secp256k1>],
        y2_vec: &[Point<Secp256k1>],
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        n: usize,
    ) -> Result<(), Errors> {
        self.verify_with_voter_id(transcript, DEFAULT_VOTER_ID, y1_vec, y2_vec, g_vec, h_vec, n)
    }

    /// Newest-paper verifier: identity-bound compressed recovery proof.
    pub fn verify_with_voter_id(
        &self,
        transcript: &mut Transcript,
        voter_id: usize,
        y1_vec: &[Point<Secp256k1>],
        y2_vec: &[Point<Secp256k1>],
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        n: usize,
    ) -> Result<(), Errors> {
        if n == 0
            || y1_vec.len() != n
            || y2_vec.len() != n
            || g_vec.len() != n
            || h_vec.len() != n
            || self.z_vec.len() != n
        {
            return Err(Errors::VotingError);
        }

        transcript.append_message(b"dom-sep", b"sigma_dleq v2 identity-bound compressed");
        transcript.append_u64(b"n", n as u64);
        transcript.append_u64(b"voter_id", voter_id as u64);
        transcript.append_points_array(b"g_vec", g_vec);
        transcript.append_points_array(b"h_vec", h_vec);
        transcript.append_points_array(b"y1_vec", y1_vec);
        transcript.append_points_array(b"y2_vec", y2_vec);

        let R1_hat_vec = (0..n)
            .map(|i| &g_vec[i] * &self.z_vec[i] - &y1_vec[i] * &self.e)
            .collect::<Vec<Point<Secp256k1>>>();

        let R2_hat_vec = (0..n)
            .map(|i| &h_vec[i] * &self.z_vec[i] - &y2_vec[i] * &self.e)
            .collect::<Vec<Point<Secp256k1>>>();

        transcript.append_points_array(b"R1_vec", &R1_hat_vec);
        transcript.append_points_array(b"R2_vec", &R2_hat_vec);

        let expected_e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");
        if expected_e != self.e {
            return Err(Errors::VotingError);
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use curv::elliptic::curves::{Point, Scalar, Secp256k1};
    use merlin::Transcript;

    #[test]
    fn test_sigma_dleq_single() {
        let g = Point::<Secp256k1>::generator().to_point();
        let h = &g * &Scalar::<Secp256k1>::from(2u64);
        let voter_id = 9usize;

        let w = Scalar::<Secp256k1>::random();
        let y1 = &g * &w;
        let y2 = &h * &w;

        let mut prover_transcript = Transcript::new(b"test_dleq_single");
        let proof = SigmaDleqProof::prove_with_voter_id(
            &mut prover_transcript,
            voter_id,
            &[w.clone()],
            &[y1.clone()],
            &[y2.clone()],
            &[g.clone()],
            &[h.clone()],
            1,
        );

        let mut verifier_transcript = Transcript::new(b"test_dleq_single");
        let result = proof.verify_with_voter_id(
            &mut verifier_transcript,
            voter_id,
            &[y1],
            &[y2],
            &[g],
            &[h],
            1,
        );

        assert!(result.is_ok());
    }

    #[test]
    fn test_sigma_dleq_rejects_wrong_voter_id() {
        let g = Point::<Secp256k1>::generator().to_point();
        let h = &g * &Scalar::<Secp256k1>::from(2u64);
        let w = Scalar::<Secp256k1>::random();
        let y1 = &g * &w;
        let y2 = &h * &w;

        let mut prover_transcript = Transcript::new(b"test_dleq_identity");
        let proof = SigmaDleqProof::prove_with_voter_id(
            &mut prover_transcript,
            1,
            &[w.clone()],
            &[y1.clone()],
            &[y2.clone()],
            &[g.clone()],
            &[h.clone()],
            1,
        );

        let mut verifier_transcript = Transcript::new(b"test_dleq_identity");
        let result = proof.verify_with_voter_id(
            &mut verifier_transcript,
            2,
            &[y1],
            &[y2],
            &[g],
            &[h],
            1,
        );

        assert!(result.is_err());
    }
}
