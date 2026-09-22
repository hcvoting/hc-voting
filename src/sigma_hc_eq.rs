#![allow(non_snake_case)]

// Identity-bound EqDL consistency proof for HC voting.
//
// Newest paper (§3.2, π_i^(eq)) proves for every option x:
//
//     h_{i,x}  = g^{r_{i,x}}
//     C_{i,x}  = g_{i,x}^{r_{i,x}} h^{v_{i,x}}
//     C'_{i,x} = g^{s_{i,x}} h^{v_{i,x}}
//
// The newest proof stores only (e,{a,b,c}) and reconstructs R,S,S' during
// verification. The challenge is identity-bound.

use curv::elliptic::curves::{Point, Scalar, Secp256k1};
use merlin::Transcript;

use crate::{transcript::TranscriptProtocol, Errors};

const DEFAULT_VOTER_ID: usize = 0;

#[derive(Clone, Debug)]
pub struct SigmaHcEqProof {
    /// Fiat-Shamir challenge e.
    pub e: Scalar<Secp256k1>,
    /// Response for r_{i,x}.
    pub a_vec: Vec<Scalar<Secp256k1>>,
    /// Response for s_{i,x}.
    pub b_vec: Vec<Scalar<Secp256k1>>,
    /// Response for v_{i,x}.
    pub c_vec: Vec<Scalar<Secp256k1>>,
}

impl SigmaHcEqProof {
    /// Backward-compatible API used by existing benchmarks.
    ///
    /// Legacy argument order is:
    /// `(g, h, g_structured_vec, C_vec, C_prime_vec, h_public_vec, s_vec, v_vec, r_vec, n)`.
    /// It still uses the newest compressed proof shape, bound to voter id 0.
    pub fn prove(
        transcript: &mut Transcript,
        g: &Point<Secp256k1>,
        h: &Point<Secp256k1>,
        g_structured_vec: &[Point<Secp256k1>],
        C_vec: &[Point<Secp256k1>],
        C_prime_vec: &[Point<Secp256k1>],
        h_public_vec: &[Point<Secp256k1>],
        s_vec: &[Scalar<Secp256k1>],
        v_vec: &[Scalar<Secp256k1>],
        r_vec: &[Scalar<Secp256k1>],
        n: usize,
    ) -> SigmaHcEqProof {
        Self::prove_with_voter_id(
            transcript,
            DEFAULT_VOTER_ID,
            g,
            h,
            h_public_vec,
            g_structured_vec,
            C_vec,
            C_prime_vec,
            r_vec,
            s_vec,
            v_vec,
            n,
        )
    }

    /// Newest-paper API: identity-bound compressed EqDL proof.
    pub fn prove_with_voter_id(
        transcript: &mut Transcript,
        voter_id: usize,
        g: &Point<Secp256k1>,
        h: &Point<Secp256k1>,
        h_public_vec: &[Point<Secp256k1>],
        g_structured_vec: &[Point<Secp256k1>],
        C_vec: &[Point<Secp256k1>],
        C_prime_vec: &[Point<Secp256k1>],
        r_vec: &[Scalar<Secp256k1>],
        s_vec: &[Scalar<Secp256k1>],
        v_vec: &[Scalar<Secp256k1>],
        n: usize,
    ) -> SigmaHcEqProof {
        assert!(n > 0);
        assert_eq!(h_public_vec.len(), n);
        assert_eq!(g_structured_vec.len(), n);
        assert_eq!(C_vec.len(), n);
        assert_eq!(C_prime_vec.len(), n);
        assert_eq!(r_vec.len(), n);
        assert_eq!(s_vec.len(), n);
        assert_eq!(v_vec.len(), n);

        transcript.append_message(b"dom-sep", b"sigma_hc_eq v2 identity-bound compressed");
        transcript.append_u64(b"n", n as u64);
        transcript.append_u64(b"voter_id", voter_id as u64);
        transcript.append_point(b"g", g);
        transcript.append_point(b"h", h);
        transcript.append_points_array(b"g_structured_vec", g_structured_vec);
        transcript.append_points_array(b"h_public_vec", h_public_vec);
        transcript.append_points_array(b"C_vec", C_vec);
        transcript.append_points_array(b"C_prime_vec", C_prime_vec);

        let alpha_vec: Vec<Scalar<Secp256k1>> =
            (0..n).map(|_| Scalar::<Secp256k1>::random()).collect();
        let beta_vec: Vec<Scalar<Secp256k1>> =
            (0..n).map(|_| Scalar::<Secp256k1>::random()).collect();
        let gamma_vec: Vec<Scalar<Secp256k1>> =
            (0..n).map(|_| Scalar::<Secp256k1>::random()).collect();

        let mut R_vec = Vec::with_capacity(n);
        let mut S_vec = Vec::with_capacity(n);
        let mut S_prime_vec = Vec::with_capacity(n);

        for x in 0..n {
            let R_x = g * &alpha_vec[x];
            let S_x = &g_structured_vec[x] * &alpha_vec[x] + h * &gamma_vec[x];
            let S_prime_x = g * &beta_vec[x] + h * &gamma_vec[x];

            R_vec.push(R_x);
            S_vec.push(S_x);
            S_prime_vec.push(S_prime_x);
        }

        transcript.append_points_array(b"R_vec", &R_vec);
        transcript.append_points_array(b"S_vec", &S_vec);
        transcript.append_points_array(b"S_prime_vec", &S_prime_vec);

        let e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");

        let mut a_vec = Vec::with_capacity(n);
        let mut b_vec = Vec::with_capacity(n);
        let mut c_vec = Vec::with_capacity(n);

        for x in 0..n {
            a_vec.push(&alpha_vec[x] + &e * &r_vec[x]);
            b_vec.push(&beta_vec[x] + &e * &s_vec[x]);
            c_vec.push(&gamma_vec[x] + &e * &v_vec[x]);
        }

        SigmaHcEqProof { e, a_vec, b_vec, c_vec }
    }

    /// Backward-compatible verifier for benchmark code.
    /// Legacy order: `(g, h, g_structured_vec, C_vec, C_prime_vec, h_public_vec, n)`.
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        g: &Point<Secp256k1>,
        h: &Point<Secp256k1>,
        g_structured_vec: &[Point<Secp256k1>],
        C_vec: &[Point<Secp256k1>],
        C_prime_vec: &[Point<Secp256k1>],
        h_public_vec: &[Point<Secp256k1>],
        n: usize,
    ) -> Result<(), Errors> {
        self.verify_with_voter_id(
            transcript,
            DEFAULT_VOTER_ID,
            g,
            h,
            h_public_vec,
            g_structured_vec,
            C_vec,
            C_prime_vec,
            n,
        )
    }

    /// Newest-paper verifier: identity-bound compressed EqDL proof.
    pub fn verify_with_voter_id(
        &self,
        transcript: &mut Transcript,
        voter_id: usize,
        g: &Point<Secp256k1>,
        h: &Point<Secp256k1>,
        h_public_vec: &[Point<Secp256k1>],
        g_structured_vec: &[Point<Secp256k1>],
        C_vec: &[Point<Secp256k1>],
        C_prime_vec: &[Point<Secp256k1>],
        n: usize,
    ) -> Result<(), Errors> {
        if n == 0
            || h_public_vec.len() != n
            || g_structured_vec.len() != n
            || C_vec.len() != n
            || C_prime_vec.len() != n
            || self.a_vec.len() != n
            || self.b_vec.len() != n
            || self.c_vec.len() != n
        {
            return Err(Errors::VotingError);
        }

        transcript.append_message(b"dom-sep", b"sigma_hc_eq v2 identity-bound compressed");
        transcript.append_u64(b"n", n as u64);
        transcript.append_u64(b"voter_id", voter_id as u64);
        transcript.append_point(b"g", g);
        transcript.append_point(b"h", h);
        transcript.append_points_array(b"g_structured_vec", g_structured_vec);
        transcript.append_points_array(b"h_public_vec", h_public_vec);
        transcript.append_points_array(b"C_vec", C_vec);
        transcript.append_points_array(b"C_prime_vec", C_prime_vec);

        let mut R_hat_vec = Vec::with_capacity(n);
        let mut S_hat_vec = Vec::with_capacity(n);
        let mut S_prime_hat_vec = Vec::with_capacity(n);

        for x in 0..n {
            let R_hat_x = g * &self.a_vec[x] - &h_public_vec[x] * &self.e;
            let S_hat_x = &g_structured_vec[x] * &self.a_vec[x]
                + h * &self.c_vec[x]
                - &C_vec[x] * &self.e;
            let S_prime_hat_x = g * &self.b_vec[x]
                + h * &self.c_vec[x]
                - &C_prime_vec[x] * &self.e;

            R_hat_vec.push(R_hat_x);
            S_hat_vec.push(S_hat_x);
            S_prime_hat_vec.push(S_prime_hat_x);
        }

        transcript.append_points_array(b"R_vec", &R_hat_vec);
        transcript.append_points_array(b"S_vec", &S_hat_vec);
        transcript.append_points_array(b"S_prime_vec", &S_prime_hat_vec);

        let expected_e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");
        if expected_e != self.e {
            return Err(Errors::VotingError);
        }

        Ok(())
    }
}
