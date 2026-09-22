#![allow(non_snake_case)]

// Identity-bound AND-composition proof of knowledge of discrete logarithms.
//
// Newest paper (§3.2, π_i^(dl)):
//
//     e = H(i, g, {h_{i,x}}_x, {R_{i,x}}_x)
//     z_{i,x} = ρ_{i,x} + e r_{i,x}
//     π_i^(dl) = (e, {z_{i,x}}_x)
//
// Verification reconstructs:
//
//     R̂_{i,x} = g^{z_{i,x}} · h_{i,x}^{-e}
//
// and accepts iff:
//
//     e = H(i, g, {h_{i,x}}_x, {R̂_{i,x}}_x).
//
// In curv's additive notation, exponentiation is scalar multiplication and
// group multiplication/division is point addition/subtraction.

use curv::elliptic::curves::{secp256_k1::Secp256k1, Point, Scalar};
use merlin::Transcript;

use crate::{transcript::TranscriptProtocol, Errors};
use crate::Errors::SigmaDlProofError;

const DEFAULT_VOTER_ID: usize = 0;

#[derive(Clone, Debug)]
pub struct SigmaDlProof {
    /// Fiat-Shamir challenge e.
    pub e: Scalar<Secp256k1>,
    /// Responses z_{i,x}.
    pub z_vec: Vec<Scalar<Secp256k1>>,
}

impl SigmaDlProof {
    /// Backward-compatible API used by existing benchmark code.
    ///
    /// This still uses the compressed newest-paper proof format `(e,{z})`, but
    /// binds the transcript to voter id 0. Protocol code should call
    /// `prove_with_voter_id` so the actual voter identity is bound as required by
    /// the newest paper.
    pub fn prove(
        transcript: &mut Transcript,
        x_vec: &[Scalar<Secp256k1>],
        y_vec: &[Point<Secp256k1>],
        g: &Point<Secp256k1>,
        n: usize,
    ) -> SigmaDlProof {
        Self::prove_with_voter_id(transcript, DEFAULT_VOTER_ID, x_vec, y_vec, g, n)
    }

    /// Newest-paper API: identity-bound compressed transcript.
    pub fn prove_with_voter_id(
        transcript: &mut Transcript,
        voter_id: usize,
        x_vec: &[Scalar<Secp256k1>],
        y_vec: &[Point<Secp256k1>],
        g: &Point<Secp256k1>,
        n: usize,
    ) -> SigmaDlProof {
        assert!(n > 0);
        assert_eq!(x_vec.len(), n);
        assert_eq!(y_vec.len(), n);

        transcript.append_message(b"dom-sep", b"sigma_dl v2 identity-bound compressed");
        transcript.append_u64(b"n", n as u64);
        transcript.append_u64(b"voter_id", voter_id as u64);
        transcript.append_point(b"g", g);
        transcript.append_points_array(b"h_public_vec", y_vec);

        let rho_vec = (0..n)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let R_vec = (0..n)
            .map(|idx| g * &rho_vec[idx])
            .collect::<Vec<Point<Secp256k1>>>();

        transcript.append_points_array(b"R_vec", &R_vec);
        let e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");

        let z_vec = (0..n)
            .map(|idx| rho_vec[idx].clone() + e.clone() * x_vec[idx].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();

        SigmaDlProof { e, z_vec }
    }

    /// Backward-compatible verifier for benchmark code. Uses voter id 0.
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        y_vec: &[Point<Secp256k1>],
        g: &Point<Secp256k1>,
        n: usize,
    ) -> Result<(), Errors> {
        self.verify_with_voter_id(transcript, DEFAULT_VOTER_ID, y_vec, g, n)
    }

    /// Newest-paper verifier: identity-bound compressed transcript.
    pub fn verify_with_voter_id(
        &self,
        transcript: &mut Transcript,
        voter_id: usize,
        y_vec: &[Point<Secp256k1>],
        g: &Point<Secp256k1>,
        n: usize,
    ) -> Result<(), Errors> {
        if n == 0 || y_vec.len() != n || self.z_vec.len() != n {
            return Err(SigmaDlProofError);
        }

        transcript.append_message(b"dom-sep", b"sigma_dl v2 identity-bound compressed");
        transcript.append_u64(b"n", n as u64);
        transcript.append_u64(b"voter_id", voter_id as u64);
        transcript.append_point(b"g", g);
        transcript.append_points_array(b"h_public_vec", y_vec);

        let R_hat_vec = (0..n)
            .map(|idx| g * &self.z_vec[idx] - &y_vec[idx] * &self.e)
            .collect::<Vec<Point<Secp256k1>>>();

        transcript.append_points_array(b"R_vec", &R_hat_vec);
        let expected_e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");

        if expected_e != self.e {
            return Err(SigmaDlProofError);
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use curv::elliptic::curves::{Point, Scalar, Secp256k1};
    use merlin::Transcript;

    use crate::sigma_dl::SigmaDlProof;

    fn test_helper(n: usize) {
        let g = Point::<Secp256k1>::generator().to_point();
        let voter_id = 7usize;

        let x_vec = (0..n)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let y_vec = (0..n)
            .map(|i| &g * &x_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let mut prover_transcript = Transcript::new(b"sigmatest");
        let proof = SigmaDlProof::prove_with_voter_id(
            &mut prover_transcript,
            voter_id,
            &x_vec,
            &y_vec,
            &g,
            n,
        );

        let mut verifier_transcript = Transcript::new(b"sigmatest");
        let result = proof.verify_with_voter_id(
            &mut verifier_transcript,
            voter_id,
            &y_vec,
            &g,
            n,
        );

        assert!(result.is_ok());
    }

    #[test]
    fn test_sigma_dl_64() {
        test_helper(64);
    }

    #[test]
    fn test_sigma_dl_rejects_wrong_public_key() {
        let n = 4;
        let g = Point::<Secp256k1>::generator().to_point();
        let voter_id = 3usize;

        let x_vec = (0..n)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let mut y_vec = (0..n)
            .map(|i| &g * &x_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let mut prover_transcript = Transcript::new(b"sigmatest");
        let proof = SigmaDlProof::prove_with_voter_id(
            &mut prover_transcript,
            voter_id,
            &x_vec,
            &y_vec,
            &g,
            n,
        );

        let one = Scalar::<Secp256k1>::from(1u64);
        y_vec[0] = &y_vec[0] + &g * &one;

        let mut verifier_transcript = Transcript::new(b"sigmatest");
        let result = proof.verify_with_voter_id(
            &mut verifier_transcript,
            voter_id,
            &y_vec,
            &g,
            n,
        );

        assert!(result.is_err());
    }

    #[test]
    fn test_sigma_dl_rejects_wrong_voter_id() {
        let n = 4;
        let g = Point::<Secp256k1>::generator().to_point();

        let x_vec = (0..n)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let y_vec = (0..n)
            .map(|i| &g * &x_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let mut prover_transcript = Transcript::new(b"sigmatest");
        let proof = SigmaDlProof::prove_with_voter_id(
            &mut prover_transcript,
            1,
            &x_vec,
            &y_vec,
            &g,
            n,
        );

        let mut verifier_transcript = Transcript::new(b"sigmatest");
        let result = proof.verify_with_voter_id(
            &mut verifier_transcript,
            2,
            &y_vec,
            &g,
            n,
        );

        assert!(result.is_err());
    }
}
