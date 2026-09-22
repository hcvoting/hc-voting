#![allow(non_snake_case)]

/// Aggregated Bulletproof-style range proof for HC Voting.
///
/// This proof is used for the paper's π_i^(ar):
///
///     π_i^(ar) = (s_sum, A, S, T1, T2, tau_x, mu, π_IP)
///
/// It proves that committed values are non-negative and satisfy a stage budget:
///
///     v_1 + v_2 + v_slack = T_i
///
/// where:
///
///     v_slack = T_i - v_1 - v_2
///
/// The proof must operate on the standard-base commitments:
///
///     C'_x = g^{s_x} h^{v_x}
///
/// not on the self-tallying commitments:
///
///     C_x = g_{i,x}^{r_{i,x}} h^{v_{i,x}}
///
/// Implementation note:
/// the paper describes vectors of logical length k*m. This implementation pads
/// them to n = next_power_of_two(k*m), because the current IPA implementation
/// requires a power-of-two vector length. Padded positions are dummy bit
/// positions with a_L = 0 and p(z) = 0.

use curv::{
    arithmetic::Modulo,
    elliptic::curves::{
        secp256_k1::{
            hash_to_curve::generate_random_point,
            Secp256k1,
        },
        Point,
        Scalar,
    },
    BigInt,
};
use curv::arithmetic::traits::*;
use merlin::Transcript;
use sha2::{Digest, Sha512};


use crate::{
    proofs::{
        transcript::TranscriptProtocol,
        ipa::InnerProductArg,
    },
    Errors::{self, RangeProofError},
};

// ---------------------- Helper Functions ----------------------

/// Compute m = ceil(log2(T + 1))
fn range_bit_length(limit: &Scalar<Secp256k1>) -> usize {
    let mut value = limit.to_bigint();
    value += BigInt::one();

    if value <= BigInt::one() {
        return 1;
    }

    let mut bits = 0usize;
    let mut pow = BigInt::one();

    while pow < value {
        pow <<= 1;
        bits += 1;
    }

    bits
}
fn scalar_to_bits_fixed(
    scalar: &Scalar<Secp256k1>,
    bit_len: usize,
) -> Vec<BigInt> {
    let mut value = scalar.to_bigint();
    let mut bits = Vec::with_capacity(bit_len);

    for _ in 0..bit_len {
        bits.push(if &value % 2 == BigInt::one() {
            BigInt::one()
        } else {
            BigInt::zero()
        });

        value >>= 1;
    }

    bits
}

fn concat_value_bits(
    values: &[Scalar<Secp256k1>],
    m: usize,
    n: usize,
) -> Vec<BigInt> {
    let mut bits = Vec::with_capacity(n);

    for value in values {
        bits.extend(scalar_to_bits_fixed(value, m));
    }

    // Pad to power-of-two length for IPA
    while bits.len() < n {
        bits.push(BigInt::zero());
    }

    bits
}

fn powers_of_bigint(
    base: &BigInt,
    len: usize,
    order: &BigInt,
) -> Vec<BigInt> {
    let mut powers = vec![BigInt::one(); len];

    for i in 1..len {
        powers[i] = BigInt::mod_mul(&powers[i - 1], base, order);
    }

    powers
}

fn two_powers_for_aggregated_values(
    k: usize,
    m: usize,
    n: usize,
    order: &BigInt,
) -> Vec<BigInt> {
    let mut result = Vec::with_capacity(n);

    for _ in 0..k {
        let mut current = BigInt::one();

        for _ in 0..m {
            result.push(current.clone());
            current = BigInt::mod_mul(&current, &BigInt::from(2), order);
        }
    }

    while result.len() < n {
        result.push(BigInt::zero());
    }

    result
}

fn p_z_vector(
    z: &BigInt,
    k: usize,
    m: usize,
    n: usize,
    order: &BigInt,
) -> Vec<BigInt> {
    let two_powers = two_powers_for_aggregated_values(k, m, n, order);
    let mut result = Vec::with_capacity(n);

    for value_index in 0..k {
        // Paper: z^2, z^3, ..., z^{k+1}
        let exponent = value_index + 2;

        let mut z_power = BigInt::one();
        for _ in 0..exponent {
            z_power = BigInt::mod_mul(&z_power, z, order);
        }

        for bit_index in 0..m {
            let idx = value_index * m + bit_index;
            result.push(BigInt::mod_mul(&z_power, &two_powers[idx], order));
        }
    }

    while result.len() < n {
        result.push(BigInt::zero());
    }

    result
}

/// Generate a vector of random generators deterministically from a seed
fn generate_generators(seed: &BigInt, label: &[u8], count: usize) -> Vec<Point<Secp256k1>> {
    let mut generators = Vec::with_capacity(count);
    
    for i in 0..count {
        // Create unique label for each generator
        let mut hasher = Sha512::new();
        hasher.update(label);
        hasher.update(&seed.to_bytes());
        hasher.update(&(i as u64).to_le_bytes());
        let hash = hasher.finalize();
        
        // Map to curve point
        let point = hash_to_point(&hash);
        generators.push(point);
    }
    
    generators
}

/// Hash bytes to a curve point.
fn hash_to_point(bytes: &[u8]) -> Point<Secp256k1> {
    generate_random_point(bytes)
}

/// Compute inner product of two BigInt vectors modulo group order
fn inner_product_mod(a: &[BigInt], b: &[BigInt]) -> BigInt {
    assert_eq!(a.len(), b.len(), "Vectors must have same length");
    
    let order = Scalar::<Secp256k1>::group_order();
    a.iter()
        .zip(b.iter())
        .fold(BigInt::zero(), |acc, (ai, bi)| {
            let prod = BigInt::mod_mul(ai, bi, order);
            BigInt::mod_add(&acc, &prod, order)
        })
}

/// Hadamard product (element-wise multiplication) modulo group order
fn hadamard_product(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    assert_eq!(a.len(), b.len(), "Vectors must have same length");
    
    let order = Scalar::<Secp256k1>::group_order();
    a.iter()
        .zip(b.iter())
        .map(|(ai, bi)| BigInt::mod_mul(ai, bi, order))
        .collect()
}

fn mod_inverse_bigint(value: &BigInt, order: &BigInt) -> BigInt {
    let exponent = order.clone() - BigInt::from(2);
    BigInt::mod_pow(value, &exponent, order)
}

fn reweight_H_by_y_inverse(
    H: &[Point<Secp256k1>],
    y_powers: &[BigInt],
    order: &BigInt,
) -> Vec<Point<Secp256k1>> {
    H.iter()
        .zip(y_powers.iter())
        .map(|(H_i, y_i)| {
            let y_inv = mod_inverse_bigint(y_i, order);
            let y_inv_scalar = Scalar::<Secp256k1>::from_bigint(&y_inv);
            H_i * &y_inv_scalar
        })
        .collect()
}

fn sum_bigints(values: &[BigInt], order: &BigInt) -> BigInt {
    values.iter().fold(BigInt::zero(), |acc, v| {
        BigInt::mod_add(&acc, v, order)
    })
}

fn delta_y_z(
    y_powers: &[BigInt],
    p_z: &[BigInt],
    z: &BigInt,
    order: &BigInt,
) -> BigInt {
    // delta = (z - z^2) * <1, y^n> - z * <1, p(z)>
    //
    // This matches the p(z) construction:
    // p(z) = z^2 2^m || z^3 2^m || ... || z^{k+1} 2^m

    let z_sq = BigInt::mod_mul(z, z, order);
    let z_minus_z_sq = BigInt::mod_sub(z, &z_sq, order);

    let sum_y = sum_bigints(y_powers, order);
    let sum_p = sum_bigints(p_z, order);

    let first = BigInt::mod_mul(&z_minus_z_sq, &sum_y, order);
    let second = BigInt::mod_mul(z, &sum_p, order);

    BigInt::mod_sub(&first, &second, order)
}

// ---------------------- Main Range Proof Structure ----------------------

#[derive(Clone, Debug)]
pub struct VarRange {
    // Paper proof:
    // π_i^(ar) = (s_sum, A, S, T1, T2, tau_x, mu, π_IP)

    pub s_sum: Scalar<Secp256k1>,

    pub A: Point<Secp256k1>,
    pub S: Point<Secp256k1>,

    pub T1: Point<Secp256k1>,
    pub T2: Point<Secp256k1>,

    pub tau_x: Scalar<Secp256k1>,
    pub mu: Scalar<Secp256k1>,

    pub ip_proof: InnerProductArg,
}

impl VarRange {
    /// Simplified API for HC Voting (boosting or voting stage)
    /// Proves that v1 + v2 ≤ limit using global generators g and h
    pub fn prove_hc_voting(
        transcript: &mut Transcript,
        g: &Point<Secp256k1>,
        h: &Point<Secp256k1>,
        v1: Scalar<Secp256k1>,
        v2: Scalar<Secp256k1>,
        s1: Scalar<Secp256k1>,
        s2: Scalar<Secp256k1>,
        limit: Scalar<Secp256k1>,
        seed: &BigInt,
    ) -> Result<Self, Errors> {
        let order = Scalar::<Secp256k1>::group_order();
    
        // Check v1 + v2 <= limit.
        // This is safe here because benchmark values are small positive integers.
        let v1_bn = v1.to_bigint();
        let v2_bn = v2.to_bigint();
        let limit_bn = limit.to_bigint();
    
        let v_sum_bn = &v1_bn + &v2_bn;
    
        if v_sum_bn > limit_bn {
            return Err(RangeProofError);
        }
    
        // v_slack = limit - v1 - v2
        let v_slack_bn = BigInt::mod_sub(&limit_bn, &v_sum_bn, order);
        let v_slack = Scalar::<Secp256k1>::from_bigint(&v_slack_bn);
    
        let s_slack = Scalar::<Secp256k1>::random();

        let C1 = g * &s1 + h * &v1;

        let C2 = g * &s2 + h * &v2;

        let C_slack = g * &s_slack + h * &v_slack;
    
        // Prove over v1, v2, and v_slack.
        // In the HC paper, the verifier later derives this slack commitment from s_sum.
        Self::range_prove(
            transcript,
            g,
            h,
            vec![v1, v2, v_slack],
            vec![s1, s2, s_slack],
            limit,
            3,  // v1, v2, and v_slack
            &[C1, C2, C_slack],
            seed,
        )
    }
    
    /// Simplified verification for HC Voting
    pub fn verify_hc_voting(
        &self,
        transcript: &mut Transcript,
        g: &Point<Secp256k1>,
        h: &Point<Secp256k1>,
        C1: &Point<Secp256k1>,
        C2: &Point<Secp256k1>,
        limit: Scalar<Secp256k1>,
        seed: &BigInt,
    ) -> Result<(), Errors> {
        // Paper-style slack commitment derivation:
        //
        // C'_slack = g^{s_sum} h^{T_i} (C'_1 C'_2)^{-1}
        //
        // In additive notation:
        //
        // C_slack = g*s_sum + h*limit - C1 - C2
    
        let C_slack = g * &self.s_sum
            + h * &limit
            - C1
            - C2;
    
        self.range_verify(
            transcript,
            g,
            h,
            &[C1.clone(), C2.clone(), C_slack],
            limit,
            3,  // C1, C2, and derived C_slack
            seed,
        )
    }
    
    /// Range proof for HC Voting - proves sum of values ≤ T
    /// Implements Appendix A.3 of the paper with modifications for sum constraints
    pub fn range_prove(
        transcript: &mut Transcript,
        g: &Point<Secp256k1>,
        h: &Point<Secp256k1>,
        values: Vec<Scalar<Secp256k1>>,
        blinding_factors: Vec<Scalar<Secp256k1>>,
        limit: Scalar<Secp256k1>,
        n_votes: usize,
        commitments: &[Point<Secp256k1>],
        seed: &BigInt,
    ) -> Result<Self, Errors> {
        assert_eq!(values.len(), n_votes);
        assert_eq!(blinding_factors.len(), n_votes);
        assert_eq!(commitments.len(), n_votes);
        
        let order = Scalar::<Secp256k1>::group_order();
        // ========== STEP 1: Summation for HC Voting ==========
        let v = values.iter()
            .fold(Scalar::<Secp256k1>::zero(), |acc, v_i| acc + v_i);

        let s_sum = blinding_factors.iter()
            .fold(Scalar::<Secp256k1>::zero(), |acc, s_i| acc + s_i);
        let mut C_agg = Point::<Secp256k1>::zero();
        for commitment in commitments {
            C_agg = C_agg + commitment;
        }
        
        let expected_C = g * &s_sum + h * &v;
        if C_agg != expected_C {
            return Err(RangeProofError);
        }
        
        // ========== STEP 2: Aggregated Bit Decomposition ==========
        //
        // Paper-aligned construction:
        //
        // k = number of committed values.
        // For HC Voting with two options plus slack, k = 3.
        //
        // m = ceil(log2(T_i + 1)).
        //
        // a_L is the concatenation:
        //
        //   a_L = bits(v_1) || bits(v_2) || ... || bits(v_k)
        //
        // Its logical length is k*m. We pad it to n = next_power_of_two(k*m)
        // because the current IPA implementation requires a power-of-two length.

        let k = values.len();
        let m = range_bit_length(&limit);

        // The paper's logical vector length is k*m.
        // The IPA implementation requires a power-of-two length, so we pad to n.
        // Padded positions are dummy positions:
        //   a_L = 0,
        //   a_R = -1 mod p,
        //   p(z) = 0.
        // This keeps the bit constraint a_L * (a_L - 1) = 0 valid for padding.
        let logical_n = k * m;
        let n = logical_n.next_power_of_two();

        let a_L = concat_value_bits(&values, m, n);
        // Compute a_R = a_L - 1^n
        let one_vec = vec![BigInt::one(); n];

        let a_R: Vec<BigInt> = a_L
            .iter()
            .zip(one_vec.iter())
            .map(|(a_i, one)| {
                if a_i == &BigInt::one() {
                    BigInt::zero()
                } else {
                    // a_i = 0, so 0 - 1 = -1 mod order
                    BigInt::mod_sub(&BigInt::zero(), one, &order)
                }
            })
            .collect();

        // ========== STEP 3: Generate Generators ==========

        let label_G = b"bulletproofs_G";
        let label_H = b"bulletproofs_H";
        let label_g0 = b"bulletproofs_g0";

        // Important: G and H must have length n, not m.
        let G = generate_generators(seed, label_G, n);
        let H = generate_generators(seed, label_H, n);

        let g0_vec = generate_generators(seed, label_g0, 1);
        let g0 = g0_vec[0].clone();

        // ========== STEP 4: Commit to Bits ==========
        //
        // A = G^{a_L} H^{a_R} h^{alpha}
        // S = G^{s_L} H^{s_R} h^{rho}

        let alpha = Scalar::<Secp256k1>::random();
        let rho = Scalar::<Secp256k1>::random();

        let s_L: Vec<Scalar<Secp256k1>> = (0..n)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect();

        let s_R: Vec<Scalar<Secp256k1>> = (0..n)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect();

        let mut A = h * &alpha;

        for i in 0..n {
            if a_L[i] != BigInt::zero() {
                let a_l_i = Scalar::<Secp256k1>::from_bigint(&a_L[i]);
                A = A + &G[i] * &a_l_i;
            }

            if a_R[i] != BigInt::zero() {
                let a_r_i = Scalar::<Secp256k1>::from_bigint(&a_R[i]);
                A = A + &H[i] * &a_r_i;
            }
        }

        let mut S = h * &rho;

        for i in 0..n {
            if s_L[i] != Scalar::<Secp256k1>::zero() {
                S = S + &G[i] * &s_L[i];
            }

            if s_R[i] != Scalar::<Secp256k1>::zero() {
                S = S + &H[i] * &s_R[i];
            }
        }

        // ========== STEP 5: Fiat-Shamir Challenges ==========

        // Newest paper (§3.2, π_i^(ar)): y and z are derived from
        // H({C'_{i,x}}_x, C'_slack, A, S).  In this implementation,
        // `commitments` is ordered as [C'_1, C'_2, C'_slack].
        transcript.append_points_array(b"C_prime_and_slack", commitments);
        transcript.append_point(b"A", &A);
        transcript.append_point(b"S", &S);

        let y = transcript.challenge_scalar(b"y");
        let y_bigint = y.to_bigint();

        let z = transcript.challenge_scalar(b"z");
        let z_bigint = z.to_bigint();

        // ========== STEP 6: Polynomial Construction ==========
        //
        // y_powers = (1, y, y^2, ..., y^{n-1})
        //
        // p(z) = z^2 2^m || z^3 2^m || ... || z^{k+1} 2^m,
        // padded to length n.

        let y_powers = powers_of_bigint(&y_bigint, n, &order);
        let p_z = p_z_vector(&z_bigint, k, m, n, &order);

        let s_L_bigint: Vec<BigInt> = s_L.iter().map(|s| s.to_bigint()).collect();
        let s_R_bigint: Vec<BigInt> = s_R.iter().map(|s| s.to_bigint()).collect();

        // a_L - z*1^n
        let a_L_minus_z: Vec<BigInt> = a_L
            .iter()
            .map(|a| BigInt::mod_sub(a, &z_bigint, &order))
            .collect();

        // a_R + z*1^n
        let a_R_plus_z: Vec<BigInt> = a_R
            .iter()
            .map(|a| BigInt::mod_add(a, &z_bigint, &order))
            .collect();

        // r0 = y^n ∘ (a_R + z*1^n) + p(z)
        let y_circ_a_R_plus_z = hadamard_product(&y_powers, &a_R_plus_z);

        let r0: Vec<BigInt> = y_circ_a_R_plus_z
            .iter()
            .zip(p_z.iter())
            .map(|(y_a, p_i)| BigInt::mod_add(y_a, p_i, &order))
            .collect();

        // ========== STEP 7: Compute Polynomial Coefficients ==========
        //
        // t(x) = <l(x), r(x)> = t0 + t1*x + t2*x^2

        let _t0 = inner_product_mod(&a_L_minus_z, &r0);

        // t2 = <s_L, y^n ∘ s_R>
        let y_circ_s_R = hadamard_product(&y_powers, &s_R_bigint);
        let t2 = inner_product_mod(&s_L_bigint, &y_circ_s_R);

        // t1 = <s_L, r0> + <a_L - z*1^n, y^n ∘ s_R>
        let t1_part1 = inner_product_mod(&s_L_bigint, &r0);
        let t1_part2 = inner_product_mod(&a_L_minus_z, &y_circ_s_R);
        let t1 = BigInt::mod_add(&t1_part1, &t1_part2, &order);
        
        // ========== STEP 8: Commit to Polynomial Coefficients ==========
        //
        // Paper convention:
        // T1 = g^{tau1} h^{t1}
        // T2 = g^{tau2} h^{t2}
        //
        // Additive notation in this code:
        // T1 = g * tau1 + h * t1
        // T2 = g * tau2 + h * t2

        let tau1 = Scalar::<Secp256k1>::random();
        let tau2 = Scalar::<Secp256k1>::random();

        let t1_scalar = Scalar::<Secp256k1>::from_bigint(&t1);
        let t2_scalar = Scalar::<Secp256k1>::from_bigint(&t2);

        let T1 = g * &tau1 + h * &t1_scalar;
        let T2 = g * &tau2 + h * &t2_scalar;
        
        // ========== STEP 9: Challenge x ==========
        transcript.append_point(b"T1", &T1);
        transcript.append_point(b"T2", &T2);
        let x = transcript.challenge_scalar(b"x");
        let x_bigint = x.to_bigint();
        
        // ========== STEP 10: Evaluate Polynomials ==========
        // l = l(x) = a_L - z·1^m + s_L·x
        let x_s_L: Vec<BigInt> = s_L_bigint.iter()
            .map(|s| BigInt::mod_mul(s, &x_bigint, &order))
            .collect();
        let l_vec: Vec<BigInt> = a_L_minus_z.iter()
            .zip(x_s_L.iter())
            .map(|(a_minus_z, x_s)| BigInt::mod_add(a_minus_z, x_s, &order))
            .collect();
        
        // r = r(x) = y^m ∘ (a_R + z·1^m + s_R·x) + z^2·2^m
        let x_s_R: Vec<BigInt> = s_R_bigint.iter()
            .map(|s| BigInt::mod_mul(s, &x_bigint, &order))
            .collect();
        let a_R_plus_z_plus_x_s_R: Vec<BigInt> = a_R_plus_z.iter()
            .zip(x_s_R.iter())
            .map(|(a_plus_z, x_s)| BigInt::mod_add(a_plus_z, x_s, &order))
            .collect();
        let y_circ_a_R_plus_z_plus_x_s_R = hadamard_product(&y_powers, &a_R_plus_z_plus_x_s_R);
        let r_vec: Vec<BigInt> = y_circ_a_R_plus_z_plus_x_s_R.iter()
        .zip(p_z.iter())
        .map(|(y_term, p_i)| BigInt::mod_add(y_term, p_i, &order))
        .collect();
        

        // ========== STEP 11: Compute Blinding Factors ==========
        //
        // Paper-aligned tau_x:
        //
        // tau_x = tau1*x + tau2*x^2 + sum_j z^{j+2} * s_j
        //
        // where s_j are the blinding factors of:
        // C'_1, C'_2, ..., C'_slack.

        let x_sq = BigInt::mod_mul(&x_bigint, &x_bigint, &order);

        let tau1_x = BigInt::mod_mul(&tau1.to_bigint(), &x_bigint, &order);
        let tau2_x_sq = BigInt::mod_mul(&tau2.to_bigint(), &x_sq, &order);

        let mut tau_x_bigint = BigInt::mod_add(&tau1_x, &tau2_x_sq, &order);

        for j in 0..k {
            // z^{j+2}
            let exponent = j + 2;

            let mut z_power = BigInt::one();
            for _ in 0..exponent {
                z_power = BigInt::mod_mul(&z_power, &z_bigint, &order);
            }

            let term = BigInt::mod_mul(
                &z_power,
                &blinding_factors[j].to_bigint(),
                &order,
            );

            tau_x_bigint = BigInt::mod_add(&tau_x_bigint, &term, &order);
        }

        let tau_x = Scalar::<Secp256k1>::from_bigint(&tau_x_bigint);
        
        // μ = α + ρ·x
        let mu_bigint = BigInt::mod_add(&alpha.to_bigint(), &BigInt::mod_mul(&rho.to_bigint(), &x_bigint, &order), &order);
        let mu = Scalar::<Secp256k1>::from_bigint(&mu_bigint);
        
        // ========== STEP 12: Inner Product Argument ==========
        //
        // Paper-style combined IPA:
        //
        // P = G^l · H'^r · g0^{<l,r>}
        //
        // where H'_i = H_i / y_i.

        let H_prime = reweight_H_by_y_inverse(&H, &y_powers, &order);

        let ip_proof = InnerProductArg::prove_combined(
            transcript,
            &G,
            &H_prime,
            &g0,
            &l_vec,
            &r_vec,
        );

        
        // ========== STEP 13: Return Complete Proof ==========
        Ok(VarRange {
            s_sum,
            A,
            S,
            T1,
            T2,
            tau_x,
            mu,
            ip_proof,
        })
    }
    
    /// Verify the range proof
    pub fn range_verify(
        &self,
        transcript: &mut Transcript,
        g: &Point<Secp256k1>,
        h: &Point<Secp256k1>,
        commitments: &[Point<Secp256k1>],
        limit: Scalar<Secp256k1>,
        n_votes: usize,
        seed: &BigInt,
    ) -> Result<(), Errors> {
        if commitments.len() != n_votes {
            return Err(RangeProofError);
        }
    // ========== STEP 1: Reconstruct Aggregated Commitment ==========

    let mut C_agg = Point::<Secp256k1>::zero();

    for commitment in commitments {
        C_agg = C_agg + commitment;
    }

    // ========== STEP 2: Reconstruct Generators ==========

    let k = commitments.len();
    let m = range_bit_length(&limit);
    let n = (k * m).next_power_of_two();

    let order = Scalar::<Secp256k1>::group_order();

    let label_G = b"bulletproofs_G";
    let label_H = b"bulletproofs_H";
    let label_g0 = b"bulletproofs_g0";

    let G = generate_generators(seed, label_G, n);
    let H = generate_generators(seed, label_H, n);

    let g0_vec = generate_generators(seed, label_g0, 1);
    let g0 = g0_vec[0].clone();

    // ========== STEP 3: Reconstruct Challenges ==========

    // Newest paper (§3.2, π_i^(ar)): y and z are derived from
    // H({C'_{i,x}}_x, C'_slack, A, S).  In this implementation,
    // `commitments` is ordered as [C'_1, C'_2, C'_slack].
    transcript.append_points_array(b"C_prime_and_slack", commitments);
    transcript.append_point(b"A", &self.A);
    transcript.append_point(b"S", &self.S);

    let y = transcript.challenge_scalar(b"y");
    let y_bigint = y.to_bigint();

    let z = transcript.challenge_scalar(b"z");
    let z_bigint = z.to_bigint();

    transcript.append_point(b"T1", &self.T1);
    transcript.append_point(b"T2", &self.T2);

    let x = transcript.challenge_scalar(b"x");
    let x_bigint = x.to_bigint();

    let y_powers = powers_of_bigint(&y_bigint, n, &order);
    let p_z = p_z_vector(&z_bigint, k, m, n, &order);
    let H_prime = reweight_H_by_y_inverse(&H, &y_powers, &order);

    // ========== STEP 4: Verify polynomial commitment equation ==========
    //
    // g*tau_x + h*t_hat
    // =
    // sum_j C'_j*z^{j+2} + h*delta(y,z) + T1*x + T2*x^2

    let t_hat = self.ip_proof.final_inner_product();
    let t_hat_scalar = Scalar::<Secp256k1>::from_bigint(&t_hat);

    let mut commitment_term = Point::<Secp256k1>::zero();

    for j in 0..k {
        let exponent = j + 2;

        let mut z_power = BigInt::one();

        for _ in 0..exponent {
            z_power = BigInt::mod_mul(&z_power, &z_bigint, &order);
        }

        let z_scalar = Scalar::<Secp256k1>::from_bigint(&z_power);
        commitment_term = commitment_term + &commitments[j] * &z_scalar;
    }

    let delta = delta_y_z(&y_powers, &p_z, &z_bigint, &order);
    let delta_scalar = Scalar::<Secp256k1>::from_bigint(&delta);

    let x_sq_bigint = BigInt::mod_mul(&x_bigint, &x_bigint, &order);
    let x_sq_scalar = Scalar::<Secp256k1>::from_bigint(&x_sq_bigint);

    let left = g * &self.tau_x + h * &t_hat_scalar;

    let right = commitment_term
        + h * &delta_scalar
        + &self.T1 * &x
        + &self.T2 * &x_sq_scalar;

    if left != right {
        return Err(RangeProofError);
    }

    // ========== STEP 5: Construct the public IPA statement ==========
    //
    // P = A + xS - z*G_sum + z*H_sum + H_prime^{p(z)} - mu*h + g0*t_hat

    let mut G_sum = Point::<Secp256k1>::zero();
    let mut H_sum = Point::<Secp256k1>::zero();
    let mut H_prime_pz = Point::<Secp256k1>::zero();

    for i in 0..n {
        G_sum = G_sum + &G[i];
        H_sum = H_sum + &H[i];

        if p_z[i] != BigInt::zero() {
            let p_i = Scalar::<Secp256k1>::from_bigint(&p_z[i]);
            H_prime_pz = H_prime_pz + &H_prime[i] * &p_i;
        }
    }

    let z_scalar = Scalar::<Secp256k1>::from_bigint(&z_bigint);

    let P_ipa = self.A.clone()
        + &self.S * &x
        - &G_sum * &z_scalar
        + &H_sum * &z_scalar
        + H_prime_pz
        - h * &self.mu
        + &g0 * &t_hat_scalar;

    // ========== STEP 6: Verify combined inner-product argument ==========

    let ip_verify_result = self.ip_proof.verify_combined(
        transcript,
        &G,
        &H_prime,
        &g0,
        &P_ipa,
    );

    if !ip_verify_result {
        return Err(RangeProofError);
    }

    Ok(())
}
}
// ---------------------- Tests ----------------------

#[cfg(test)]
mod tests {
    use super::*;
    use curv::arithmetic::Converter;
    use curv::cryptographic_primitives::hashing::DigestExt;
    
    #[test]
    fn test_range_proof_hc_voting() {
        // Test HC Voting use case: prove sum of 2 votes ≤ 1000 tokens
        
        // Setup
        let seed = BigInt::from(12345);
        let hash_g = Sha512::new().chain_bigint(&seed).result_bigint();
        let g = hash_to_point(&Converter::to_bytes(&hash_g));

        let hash_h = Sha512::new()
            .chain_bigint(&(seed.clone() + BigInt::one()))
            .result_bigint();
        let h = hash_to_point(&Converter::to_bytes(&hash_h));
        
        // Simulate boosting stage: v_b1 + v_b2 ≤ 1000
        let v_b1 = Scalar::<Secp256k1>::from(300u64);  // Predict agree
        let v_b2 = Scalar::<Secp256k1>::from(200u64);  // Predict disagree
        
        let s_b1 = Scalar::<Secp256k1>::random();
        let s_b2 = Scalar::<Secp256k1>::random();

        let C_b1 = &g * &s_b1 + &h * &v_b1;
        let C_b2 = &g * &s_b2 + &h * &v_b2;
        
        let token_budget = Scalar::<Secp256k1>::from(1000u64);
        
        // Create range proof using simplified API
        let mut transcript = Transcript::new(b"HC_Range_Test");
        let proof = VarRange::prove_hc_voting(
            &mut transcript,
            &g,
            &h,
            v_b1,
            v_b2,
            s_b1,
            s_b2,
            token_budget.clone(),
            &seed,
        ).expect("Range proof should succeed");
        
        // Verify proof using simplified API
        let mut transcript = Transcript::new(b"HC_Range_Test");
        let result = proof.verify_hc_voting(
            &mut transcript,
            &g,
            &h,
            &C_b1,
            &C_b2,
            token_budget,
            &seed,
        );
        
        assert!(result.is_ok(), "Range proof verification failed");
        
        // Test with invalid values (sum > limit)
        // Note: The proof generation should fail for invalid values
        // We're not testing this here as it would require modifying the proof generation
    }
    
    #[test]
    fn test_bit_decomposition() {
        let scalar = Scalar::<Secp256k1>::from(42u64);  // 42 in binary: 101010
        let bits = scalar_to_bits_fixed(&scalar, 8);
        
        // Check LSB first (little-endian)
        assert_eq!(bits[0], BigInt::zero());   // 0
        assert_eq!(bits[1], BigInt::one());    // 1
        assert_eq!(bits[2], BigInt::zero());   // 0
        assert_eq!(bits[3], BigInt::one());    // 1
        assert_eq!(bits[4], BigInt::zero());   // 0
        assert_eq!(bits[5], BigInt::one());    // 1
    }
    
    #[test]
    fn test_hc_voting_api_compatibility() {
        // Test that the simplified HC Voting API integrates with the voting.rs expectations
        
        // Setup
        let seed = BigInt::from(12345);
        let hash_g = Sha512::new().chain_bigint(&seed).result_bigint();
        let g = hash_to_point(&Converter::to_bytes(&hash_g));
        
        let hash_h = Sha512::new().chain_bigint(&(seed.clone() + BigInt::one())).result_bigint();
        let h = hash_to_point(&Converter::to_bytes(&hash_h));
        
        // Simulate HC Voting scenario
        let v1 = Scalar::<Secp256k1>::from(300u64);
        let v2 = Scalar::<Secp256k1>::from(200u64);
        let s1 = Scalar::<Secp256k1>::random();
        let s2 = Scalar::<Secp256k1>::random();
        let limit = Scalar::<Secp256k1>::from(1000u64);
        
        // Use simplified API
        let mut transcript = Transcript::new(b"test");
        let proof = VarRange::prove_hc_voting(
            &mut transcript,
            &g,
            &h,
            v1.clone(),
            v2.clone(),
            s1.clone(),
            s2.clone(),
            limit.clone(),
            &seed,
        ).unwrap();
        
        let C1 = &g * &s1 + &h * &v1;
        let C2 = &g * &s2 + &h * &v2;

        let mut transcript_verify = Transcript::new(b"test");

        let result = proof.verify_hc_voting(
            &mut transcript_verify,
            &g,
            &h,
            &C1,
            &C2,
            limit,
            &seed,
        );

        assert!(result.is_ok(), "HC voting range proof should verify");
    }
}
