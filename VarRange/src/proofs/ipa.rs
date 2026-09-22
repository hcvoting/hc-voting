#![allow(non_snake_case)]

/// This file implements the inner-product argument used by the aggregated
/// Bulletproof-style range proof.
///
/// The paper-facing path uses the combined IPA relation:
///
///     P = G^a · H^b · u^{<a,b>}
///
/// In additive notation used by curv:
///
///     P = <a,G> + <b,H> + u * <a,b>
///
/// For VarRange, the vectors are:
///
///     a = l
///     b = r
///     <a,b> = t_hat
///
/// The old two-statement IPA is kept only as legacy code for compatibility.
/// The range proof should use prove_combined() and verify_combined().
/// 
use curv::{elliptic::curves::{secp256_k1::Secp256k1, Point, Scalar}, BigInt};
use curv::arithmetic::{traits::*, Modulo};
use merlin::Transcript;

use crate::proofs::{transcript::TranscriptProtocol, vec_poly::inner_product};

#[derive(Clone, Debug)]
pub struct InnerProductArg {
    // For the combined IPA, Al and Ar are reused as L_vec and R_vec.
    // For the legacy IPA, Al/Ar/Bl/Br keep their old meanings.
    pub(super) Al: Vec<Point<Secp256k1>>,
    pub(super) Ar: Vec<Point<Secp256k1>>,
    pub(super) Bl: Vec<Point<Secp256k1>>,
    pub(super) Br: Vec<Point<Secp256k1>>,

    // Final folded witness scalars after logarithmic compression.
    pub(super) a_vec: Vec<BigInt>,
    pub(super) b_vec: Vec<BigInt>,

    // Original inner product t_hat = <a,b>.
    // In VarRange, this is t_hat = <l,r>.
    // It is kept inside π_IP, not as a separate VarRange field.
    pub(super) t_hat: BigInt,
}

fn mod_inverse(value: &BigInt, order: &BigInt) -> BigInt {
    let exponent = order.clone() - BigInt::from(2);
    BigInt::mod_pow(value, &exponent, order)
}

impl InnerProductArg {
    // This is a STATIC method - no &self parameter
    pub fn prove(
        transcript: &mut Transcript,
        G: &[Point<Secp256k1>],
        H: &[Point<Secp256k1>],
        ux: &Point<Secp256k1>,
        a: &[BigInt],
        b: &[BigInt],
        mut Al_vec: Vec<Point<Secp256k1>>,
        mut Ar_vec: Vec<Point<Secp256k1>>,
        mut Bl_vec: Vec<Point<Secp256k1>>,
        mut Br_vec: Vec<Point<Secp256k1>>,
    ) -> InnerProductArg {
        let n_hat = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n_hat);
        assert_eq!(H.len(), n_hat);
        assert_eq!(a.len(), n_hat);
        assert_eq!(b.len(), n_hat);
        // Check that n_hat is a power of two
        assert!(n_hat.is_power_of_two());

        transcript.ipa_domain_sep(n_hat as u64);
        
        if n_hat > 4 {
            let order = Scalar::<Secp256k1>::group_order();

            let n_hat = n_hat / 2;
            let (G_l, G_r) = G.split_at(n_hat);
            let (H_l, H_r) = H.split_at(n_hat);
            let (a_l, a_r) = a.split_at(n_hat);
            let (b_l, b_r) = b.split_at(n_hat);

            let c_l = inner_product(a_r, b_l, order);
            let c_r = inner_product(a_l, b_r, order);

            let c_l_fe = Scalar::<Secp256k1>::from(&c_l);
            let ux_cl = ux * c_l_fe;
            let c_r_fe = Scalar::<Secp256k1>::from(&c_r);
            let ux_cr = ux * c_r_fe;

            let A_l = G_r.iter().zip(a_l).fold(Point::<Secp256k1>::zero(), |acc, x| {
                if x.1 != &BigInt::zero() {
                    let ali = Scalar::<Secp256k1>::from(x.1);
                    let Gri_ali: Point<Secp256k1> = x.0 * &ali;
                    acc + &Gri_ali
                } else {
                    acc
                }
            });

            let A_r = G_l.iter().zip(a_r).fold(Point::<Secp256k1>::zero(), |acc, x| {
                if x.1 != &BigInt::zero() {
                    let ari = Scalar::<Secp256k1>::from(x.1);
                    let Gli_ari: Point<Secp256k1> = x.0 * &ari;
                    acc + &Gli_ari
                } else {
                    acc
                }
            });

            let B_l = H_r.iter().zip(b_l).fold(ux_cl, |acc, x| {
                if x.1 != &BigInt::zero() {
                    let bli = Scalar::<Secp256k1>::from(x.1);
                    let Hri_bli: Point<Secp256k1> = x.0 * &bli;
                    acc + &Hri_bli
                } else {
                    acc
                }
            });

            let B_r = H_l.iter().zip(b_r).fold(ux_cr, |acc, x| {
                if x.1 != &BigInt::zero() {
                    let bri = Scalar::<Secp256k1>::from(x.1);
                    let Hli_bri: Point<Secp256k1> = x.0 * &bri;
                    acc + &Hli_bri
                } else {
                    acc
                }
            });

            transcript.append_point(b"A_l", &A_l);
            transcript.append_point(b"A_r", &A_r);
            transcript.append_point(b"B_l", &B_l);
            transcript.append_point(b"B_r", &B_r);

            let ex: Scalar<Secp256k1> = transcript.challenge_scalar(b"ex");
            let ex_bn = ex.to_bigint();

            let a_new = (0..n_hat)
                .map(|i| {
                    let ali = a_l[i].clone();
                    let ari_ex = BigInt::mod_mul(&a_r[i], &ex_bn, order);
                    BigInt::mod_add(&ali, &ari_ex, order)
                })
                .collect::<Vec<BigInt>>();
            
            let b_new = (0..n_hat)
                .map(|i| {
                    let bli_ex = BigInt::mod_mul(&b_l[i], &ex_bn, order);
                    let bri = b_r[i].clone();
                    BigInt::mod_add(&bli_ex, &bri, order)
                })
                .collect::<Vec<BigInt>>();

            let G_new = (0..n_hat)
                .map(|i| {
                    let Glex = &G_l[i] * ex.clone();
                    let Gr = &G_r[i];
                    Gr + Glex
                })
                .collect::<Vec<Point<Secp256k1>>>();

            let H_new = (0..n_hat)
                .map(|i| {
                    let Hl = &H_l[i];
                    let Hrex = &H_r[i] * ex.clone();
                    Hl + Hrex
                })
                .collect::<Vec<Point<Secp256k1>>>();

            Al_vec.push(A_l);
            Ar_vec.push(A_r);
            Bl_vec.push(B_l);
            Br_vec.push(B_r);
            return InnerProductArg::prove(transcript, &G_new, &H_new, ux, &a_new, &b_new, Al_vec, Ar_vec, Bl_vec, Br_vec);
        }

        let order = Scalar::<Secp256k1>::group_order();
        let t_hat = inner_product(a, b, order);

        InnerProductArg {
            Al: Al_vec,
            Ar: Ar_vec,
            Bl: Bl_vec,
            Br: Br_vec,
            a_vec: a.to_vec(),
            b_vec: b.to_vec(),
            t_hat,
        }
    }

    pub fn final_inner_product(&self) -> BigInt {
        self.t_hat.clone()
    }
    
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        G: &[Point<Secp256k1>],
        H: &[Point<Secp256k1>],
        ux: &Point<Secp256k1>,
        P: &Point<Secp256k1>,
        Q: &Point<Secp256k1>,
        _Al_vec: Vec<Point<Secp256k1>>,
        _Ar_vec: Vec<Point<Secp256k1>>,
        _Bl_vec: Vec<Point<Secp256k1>>,
        _Br_vec: Vec<Point<Secp256k1>>,
    ) -> bool {
        let n_hat = G.len();
    
        assert_eq!(G.len(), n_hat);
        assert_eq!(H.len(), n_hat);
        assert!(n_hat.is_power_of_two());
    
        transcript.ipa_domain_sep(n_hat as u64);
    
        let order = Scalar::<Secp256k1>::group_order();
    
        if n_hat > 4 {
            let n_hat = n_hat / 2;
            let (G_l, G_r) = G.split_at(n_hat);
            let (H_l, H_r) = H.split_at(n_hat);
    
            transcript.append_point(b"A_l", &self.Al[0]);
            transcript.append_point(b"A_r", &self.Ar[0]);
            transcript.append_point(b"B_l", &self.Bl[0]);
            transcript.append_point(b"B_r", &self.Br[0]);
    
            let ex: Scalar<Secp256k1> = transcript.challenge_scalar(b"ex");
            let ex_bn = ex.to_bigint();
            let ex_sq_bn = BigInt::mod_mul(&ex_bn, &ex_bn, order);
            let ex_sq_fe = Scalar::<Secp256k1>::from(&ex_sq_bn);
    
            let G_new = (0..n_hat)
                .map(|i| {
                    let Glex = &G_l[i] * ex.clone();
                    let Gr = &G_r[i];
                    Gr + Glex
                })
                .collect::<Vec<Point<Secp256k1>>>();
    
            let H_new = (0..n_hat)
                .map(|i| {
                    let Hl = &H_l[i];
                    let Hrex = &H_r[i] * ex.clone();
                    Hl + Hrex
                })
                .collect::<Vec<Point<Secp256k1>>>();
    
            let Pex = P * ex.clone();
            let Arex_sq = &self.Ar[0] * ex_sq_fe.clone();
            let P_tag = self.Al[0].clone() + Pex + Arex_sq;
    
            let Blex_sq = &self.Bl[0] * ex_sq_fe;
            let Qex = Q * ex;
            let Q_tag = Blex_sq + Qex + self.Br[0].clone();
    
            let ipa = InnerProductArg {
                Al: self.Al[1..].to_vec(),
                Ar: self.Ar[1..].to_vec(),
                Bl: self.Bl[1..].to_vec(),
                Br: self.Br[1..].to_vec(),
                a_vec: self.a_vec.clone(),
                b_vec: self.b_vec.clone(),
                t_hat: self.t_hat.clone(),
            };
    
            return ipa.verify(
                transcript,
                &G_new,
                &H_new,
                ux,
                &P_tag,
                &Q_tag,
                vec![],
                vec![],
                vec![],
                vec![],
            );
        }
    
        let c = inner_product(&self.a_vec, &self.b_vec, order);
        let ux_c = ux * Scalar::<Secp256k1>::from_bigint(&c);
    
        let G_a = G
            .iter()
            .zip(self.a_vec.clone())
            .fold(Point::<Secp256k1>::zero(), |acc, x| {
                if x.1 != BigInt::zero() {
                    let ai = Scalar::<Secp256k1>::from(x.1);
                    let Gi_ai: Point<Secp256k1> = x.0 * &ai;
                    acc + &Gi_ai
                } else {
                    acc
                }
            });
    
        let H_b_c = H
            .iter()
            .zip(self.b_vec.clone())
            .fold(ux_c, |acc, x| {
                if x.1 != BigInt::zero() {
                    let bi = Scalar::<Secp256k1>::from(x.1);
                    let Hi_bi: Point<Secp256k1> = x.0 * &bi;
                    acc + &Hi_bi
                } else {
                    acc
                }
            });
    
        P.clone() == G_a && Q.clone() == H_b_c
    }
    
    pub fn prove_combined(
        transcript: &mut Transcript,
        G: &[Point<Secp256k1>],
        H: &[Point<Secp256k1>],
        u: &Point<Secp256k1>,
        a: &[BigInt],
        b: &[BigInt],
    ) -> InnerProductArg {
        let order = Scalar::<Secp256k1>::group_order();
    
        assert_eq!(G.len(), H.len());
        assert_eq!(G.len(), a.len());
        assert_eq!(G.len(), b.len());
        assert!(G.len().is_power_of_two());
    
        transcript.ipa_domain_sep(G.len() as u64);
    
        let mut G_vec = G.to_vec();
        let mut H_vec = H.to_vec();
        let mut a_vec = a.to_vec();
        let mut b_vec = b.to_vec();
    
        let mut L_vec: Vec<Point<Secp256k1>> = Vec::new();
        let mut R_vec: Vec<Point<Secp256k1>> = Vec::new();
    
        while G_vec.len() > 1 {
            let n = G_vec.len();
            let half = n / 2;
    
            let (G_l, G_r) = G_vec.split_at(half);
            let (H_l, H_r) = H_vec.split_at(half);
            let (a_l, a_r) = a_vec.split_at(half);
            let (b_l, b_r) = b_vec.split_at(half);
    
            let c_L = inner_product(a_l, b_r, order);
            let c_R = inner_product(a_r, b_l, order);
    
            let c_L_scalar = Scalar::<Secp256k1>::from_bigint(&c_L);
            let mut L = u * &c_L_scalar;
    
            for i in 0..half {
                if a_l[i] != BigInt::zero() {
                    let s = Scalar::<Secp256k1>::from_bigint(&a_l[i]);
                    L = L + &G_r[i] * &s;
                }
    
                if b_r[i] != BigInt::zero() {
                    let s = Scalar::<Secp256k1>::from_bigint(&b_r[i]);
                    L = L + &H_l[i] * &s;
                }
            }
    
            let c_R_scalar = Scalar::<Secp256k1>::from_bigint(&c_R);
            let mut R = u * &c_R_scalar;
    
            for i in 0..half {
                if a_r[i] != BigInt::zero() {
                    let s = Scalar::<Secp256k1>::from_bigint(&a_r[i]);
                    R = R + &G_l[i] * &s;
                }
    
                if b_l[i] != BigInt::zero() {
                    let s = Scalar::<Secp256k1>::from_bigint(&b_l[i]);
                    R = R + &H_r[i] * &s;
                }
            }
    
            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);
    
            let x = transcript.challenge_scalar(b"x_ip");
            let x_bn = x.to_bigint();
    
            let x_inv_bn = mod_inverse(&x_bn, order);
            let x_inv = Scalar::<Secp256k1>::from_bigint(&x_inv_bn);
    
            let mut a_new = Vec::with_capacity(half);
            let mut b_new = Vec::with_capacity(half);
            let mut G_new = Vec::with_capacity(half);
            let mut H_new = Vec::with_capacity(half);
    
            for i in 0..half {
                let left = BigInt::mod_mul(&x_bn, &a_l[i], order);
                let right = BigInt::mod_mul(&x_inv_bn, &a_r[i], order);
                a_new.push(BigInt::mod_add(&left, &right, order));
    
                let left = BigInt::mod_mul(&x_inv_bn, &b_l[i], order);
                let right = BigInt::mod_mul(&x_bn, &b_r[i], order);
                b_new.push(BigInt::mod_add(&left, &right, order));
    
                let g_left = &G_l[i] * &x_inv;
                let g_right = &G_r[i] * &x;
                G_new.push(g_left + g_right);
    
                let h_left = &H_l[i] * &x;
                let h_right = &H_r[i] * &x_inv;
                H_new.push(h_left + h_right);
            }
    
            L_vec.push(L);
            R_vec.push(R);
    
            G_vec = G_new;
            H_vec = H_new;
            a_vec = a_new;
            b_vec = b_new;
        }
    
        let t_hat = inner_product(a, b, order);

        InnerProductArg {
            Al: L_vec,
            Ar: R_vec,
            Bl: Vec::new(),
            Br: Vec::new(),
            a_vec,
            b_vec,
            t_hat,
        }
    }
    
    pub fn verify_combined(
        &self,
        transcript: &mut Transcript,
        G: &[Point<Secp256k1>],
        H: &[Point<Secp256k1>],
        u: &Point<Secp256k1>,
        P: &Point<Secp256k1>,
    ) -> bool {
        let order = Scalar::<Secp256k1>::group_order();
    
        if G.len() != H.len() {
            return false;
        }
    
        if G.is_empty() || !G.len().is_power_of_two() {
            return false;
        }
        
        if self.Al.len() != self.Ar.len() {
            return false;
        }
        
        if !self.Bl.is_empty() || !self.Br.is_empty() {
            return false;
        }
        
        let expected_rounds = G.len().ilog2() as usize;

        if self.Al.len() != expected_rounds {
            return false;
        }
        transcript.ipa_domain_sep(G.len() as u64);
    
        let mut G_vec = G.to_vec();
        let mut H_vec = H.to_vec();
        let mut P_current = P.clone();
    
        for round in 0..self.Al.len() {
            let L = &self.Al[round];
            let R = &self.Ar[round];
    
            transcript.append_point(b"L", L);
            transcript.append_point(b"R", R);
    
            let x = transcript.challenge_scalar(b"x_ip");
            let x_bn = x.to_bigint();
    
            let x_inv_bn = mod_inverse(&x_bn, order);
            let x_inv = Scalar::<Secp256k1>::from_bigint(&x_inv_bn);
    
            let x_sq_bn = BigInt::mod_mul(&x_bn, &x_bn, order);
            let x_inv_sq_bn = BigInt::mod_mul(&x_inv_bn, &x_inv_bn, order);
    
            let x_sq = Scalar::<Secp256k1>::from_bigint(&x_sq_bn);
            let x_inv_sq = Scalar::<Secp256k1>::from_bigint(&x_inv_sq_bn);
    
            P_current = L * &x_sq + P_current + R * &x_inv_sq;
    
            let n = G_vec.len();
            let half = n / 2;
    
            let (G_l, G_r) = G_vec.split_at(half);
            let (H_l, H_r) = H_vec.split_at(half);
    
            let mut G_new = Vec::with_capacity(half);
            let mut H_new = Vec::with_capacity(half);
    
            for i in 0..half {
                let g_left = &G_l[i] * &x_inv;
                let g_right = &G_r[i] * &x;
                G_new.push(g_left + g_right);
    
                let h_left = &H_l[i] * &x;
                let h_right = &H_r[i] * &x_inv;
                H_new.push(h_left + h_right);
            }
    
            G_vec = G_new;
            H_vec = H_new;
        }
    
        if G_vec.len() != self.a_vec.len() || H_vec.len() != self.b_vec.len() {
            return false;
        }
    
        let c = inner_product(&self.a_vec, &self.b_vec, order);
        let c_scalar = Scalar::<Secp256k1>::from_bigint(&c);
    
        let mut expected = u * &c_scalar;
    
        for i in 0..G_vec.len() {
            if self.a_vec[i] != BigInt::zero() {
                let s = Scalar::<Secp256k1>::from_bigint(&self.a_vec[i]);
                expected = expected + &G_vec[i] * &s;
            }
    
            if self.b_vec[i] != BigInt::zero() {
                let s = Scalar::<Secp256k1>::from_bigint(&self.b_vec[i]);
                expected = expected + &H_vec[i] * &s;
            }
        }
        P_current == expected
    }
}
#[cfg(test)]
mod test {
    use curv::{arithmetic::Converter, cryptographic_primitives::hashing::DigestExt, elliptic::curves::{secp256_k1::hash_to_curve::generate_random_point, Point, Scalar, Secp256k1}, BigInt};
    use curv::arithmetic::One;
    use merlin::Transcript;
    use sha2::{Digest, Sha512};

    use crate::proofs::vec_poly::inner_product;
    use super::InnerProductArg;

    fn test_helper(n: usize) {
        let order = Scalar::<Secp256k1>::group_order();
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);

        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let label = BigInt::one();
        let hash = Sha512::new().chain_bigint(&label).result_bigint();
        let Gx = generate_random_point(&Converter::to_bytes(&hash));

        let a: Vec<_> = (0..n)
            .map(|_| {
                let rand = Scalar::<Secp256k1>::random();
                rand.to_bigint()
            })
            .collect();

        let b: Vec<_> = (0..n)
            .map(|_| {
                let rand = Scalar::<Secp256k1>::random();
                rand.to_bigint()
            })
            .collect();

        let c = inner_product(&a, &b, order);

        let c_fe = Scalar::<Secp256k1>::from(&c);
        let ux_c: Point<Secp256k1> = &Gx * &c_fe;

        let P = (0..n)
            .map(|i| {
                let ai = Scalar::<Secp256k1>::from(&a[i]);
                &g_vec[i] * &ai
            })
            .fold(Point::<Secp256k1>::zero(), |acc, x: Point<Secp256k1>| acc + x as Point<Secp256k1>);

        let Q = (0..n)
            .map(|i| {
                let bi = Scalar::<Secp256k1>::from(&b[i]);
                &h_vec[i] * &bi
            })
            .fold(ux_c, |acc, x: Point<Secp256k1>| acc + x as Point<Secp256k1>);

        let Al_vec: Vec<Point<Secp256k1>> = Vec::new();
        let Ar_vec: Vec<Point<Secp256k1>> = Vec::new();
        let Bl_vec: Vec<Point<Secp256k1>> = Vec::new();
        let Br_vec: Vec<Point<Secp256k1>> = Vec::new();
        let mut verifier = Transcript::new(b"ipatest");
        let ipa = InnerProductArg::prove(&mut verifier, &g_vec, &h_vec, &Gx, &a, &b, Al_vec, Ar_vec, Bl_vec, Br_vec);
        let mut verifier = Transcript::new(b"ipatest");
        let result = ipa.verify(&mut verifier, &g_vec, &h_vec, &Gx, &P, &Q, vec![], vec![], vec![], vec![]);
        assert!(result);
    }

    #[test]
    pub fn test_ipa_1024() {
        test_helper(1024);
    }
    #[test]
pub fn test_combined_ipa_1024() {
    let n = 1024;

    let order = Scalar::<Secp256k1>::group_order();
    let KZen: &[u8] = &[75, 90, 101, 110];
    let kzen_label = BigInt::from_bytes(KZen);

    let g_vec = (0..n)
        .map(|i| {
            let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
            let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
            generate_random_point(&Converter::to_bytes(&hash_i))
        })
        .collect::<Vec<Point<Secp256k1>>>();

    let h_vec = (0..n)
        .map(|i| {
            let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
            let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
            generate_random_point(&Converter::to_bytes(&hash_j))
        })
        .collect::<Vec<Point<Secp256k1>>>();

    let label = BigInt::one();
    let hash = Sha512::new().chain_bigint(&label).result_bigint();
    let u = generate_random_point(&Converter::to_bytes(&hash));

    let a: Vec<BigInt> = (0..n)
        .map(|_| Scalar::<Secp256k1>::random().to_bigint())
        .collect();

    let b: Vec<BigInt> = (0..n)
        .map(|_| Scalar::<Secp256k1>::random().to_bigint())
        .collect();

    let c = inner_product(&a, &b, order);
    let c_scalar = Scalar::<Secp256k1>::from_bigint(&c);

    // P = G^a H^b u^{<a,b>}
    let mut P = &u * &c_scalar;

    for i in 0..n {
        let ai = Scalar::<Secp256k1>::from_bigint(&a[i]);
        let bi = Scalar::<Secp256k1>::from_bigint(&b[i]);

        P = P + &g_vec[i] * &ai;
        P = P + &h_vec[i] * &bi;
    }

    let mut prover_transcript = Transcript::new(b"combined_ipa_test");

    let proof = InnerProductArg::prove_combined(
        &mut prover_transcript,
        &g_vec,
        &h_vec,
        &u,
        &a,
        &b,
    );

    let mut verifier_transcript = Transcript::new(b"combined_ipa_test");

    let result = proof.verify_combined(
        &mut verifier_transcript,
        &g_vec,
        &h_vec,
        &u,
        &P,
    );

    assert!(result);
}

#[test]
pub fn test_combined_ipa_rejects_tampered_statement() {
    let n = 1024;

    let order = Scalar::<Secp256k1>::group_order();
    let KZen: &[u8] = &[75, 90, 101, 110];
    let kzen_label = BigInt::from_bytes(KZen);

    let g_vec = (0..n)
        .map(|i| {
            let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
            let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
            generate_random_point(&Converter::to_bytes(&hash_i))
        })
        .collect::<Vec<Point<Secp256k1>>>();

    let h_vec = (0..n)
        .map(|i| {
            let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
            let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
            generate_random_point(&Converter::to_bytes(&hash_j))
        })
        .collect::<Vec<Point<Secp256k1>>>();

    let label = BigInt::one();
    let hash = Sha512::new().chain_bigint(&label).result_bigint();
    let u = generate_random_point(&Converter::to_bytes(&hash));

    let a: Vec<BigInt> = (0..n)
        .map(|_| Scalar::<Secp256k1>::random().to_bigint())
        .collect();

    let b: Vec<BigInt> = (0..n)
        .map(|_| Scalar::<Secp256k1>::random().to_bigint())
        .collect();

    let c = inner_product(&a, &b, order);
    let c_scalar = Scalar::<Secp256k1>::from_bigint(&c);

    let mut P = &u * &c_scalar;

    for i in 0..n {
        let ai = Scalar::<Secp256k1>::from_bigint(&a[i]);
        let bi = Scalar::<Secp256k1>::from_bigint(&b[i]);

        P = P + &g_vec[i] * &ai;
        P = P + &h_vec[i] * &bi;
    }

    let mut prover_transcript = Transcript::new(b"combined_ipa_test");

    let proof = InnerProductArg::prove_combined(
        &mut prover_transcript,
        &g_vec,
        &h_vec,
        &u,
        &a,
        &b,
    );

    // Tamper the public statement P.
    let tamper = Scalar::<Secp256k1>::from(1u64);
    let P_bad = P + &g_vec[0] * &tamper;

    let mut verifier_transcript = Transcript::new(b"combined_ipa_test");

    let result = proof.verify_combined(
        &mut verifier_transcript,
        &g_vec,
        &h_vec,
        &u,
        &P_bad,
    );

    assert!(!result);
}

}