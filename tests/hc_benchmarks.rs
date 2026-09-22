//! HC Voting REAL Performance Benchmarks
//! Optimized version with performance improvements
//! Run with: cargo test benchmark_all_operations --release -- --nocapture
#![allow(non_snake_case)]
use std::time::{Instant, Duration};
use curv::{
    ////arithmetic::Converter,
    elliptic::curves::{Point, Scalar, Secp256k1},
    BigInt,
};
use merlin::Transcript;
use VarRange::proofs::varrange::VarRange;
use HC_Voting::sigma_dl::SigmaDlProof;
use HC_Voting::sigma_dleq::SigmaDleqProof;
use HC_Voting::sigma_hc_eq::SigmaHcEqProof;
use HC_Voting::sigma_reward::SigmaRewardProof;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::sync::Arc;
use std::collections::HashMap;

const G_BYTES: usize = 33;
const FP_BYTES: usize = 32;

fn size_h_vec(n_c: usize) -> usize {
    n_c * G_BYTES
}

fn size_c_hat(n_c: usize) -> usize {
    n_c * G_BYTES
}

fn size_commitment_pair(n_c: usize) -> usize {
    2 * n_c * G_BYTES
}

fn size_pi_dl(n_c: usize) -> usize {
    (n_c + 1) * FP_BYTES
}

fn size_pi_eq(n_c: usize) -> usize {
    (3 * n_c + 1) * FP_BYTES
}

fn size_pi_rec(n_c: usize) -> usize {
    (n_c + 1) * FP_BYTES
}

fn size_c_pay(n_c: usize) -> usize {
    n_c * G_BYTES
}

fn size_s_sum_stage() -> usize {
    2 * FP_BYTES
}

fn size_pi_reward(n_c: usize) -> usize {
    (n_c + 1) * FP_BYTES
}

fn integer_sqrt(n: u64) -> u64 {
    (n as f64).sqrt().floor() as u64
}

fn boost_cap_from_t(t: u64) -> u64 {
    (2 * integer_sqrt(t)).max(1)
}

struct CachedGenerators {
    g: Point<Secp256k1>,
    h: Point<Secp256k1>,
}

impl CachedGenerators {
    fn new() -> Self {
        Self {
            g: Point::<Secp256k1>::generator() * Scalar::<Secp256k1>::random(),
            h: Point::<Secp256k1>::generator() * Scalar::<Secp256k1>::random(),
        }
    }
}

/// Fast random scalar generator with caching
struct FastRng {
    rng: ChaCha8Rng,
    cache: Vec<Scalar<Secp256k1>>,
    cache_index: usize,
}

impl FastRng {
    fn new(seed: u64) -> Self {
        let rng = ChaCha8Rng::seed_from_u64(seed); // Remove 'mut'
        Self {
            rng,
            cache: Vec::with_capacity(1000),
            cache_index: 0,
        }
    }

    fn next_scalar(&mut self) -> Scalar<Secp256k1> {
        if self.cache_index >= self.cache.len() {
            // Refill cache
            self.cache.clear();
            for _ in 0..1000 {
                let mut bytes = [0u8; 32];
                self.rng.fill_bytes(&mut bytes);
                if let Ok(scalar) = Scalar::<Secp256k1>::from_bytes(&bytes) {
                    self.cache.push(scalar);
                }
            }
            self.cache_index = 0;
        }
        let scalar = self.cache[self.cache_index].clone();
        self.cache_index += 1;
        scalar
    }

    fn batch_scalars(&mut self, n: usize) -> Vec<Scalar<Secp256k1>> {
        let mut result = Vec::with_capacity(n);
        for _ in 0..n {
            result.push(self.next_scalar());
        }
        result
    }
}
#[derive(Clone)]
struct HcEqInstance {
    r_vec: Vec<Scalar<Secp256k1>>,
    s_vec: Vec<Scalar<Secp256k1>>,
    v_vec: Vec<Scalar<Secp256k1>>,
    h_vec: Vec<Point<Secp256k1>>,
    g_structured_vec: Vec<Point<Secp256k1>>,
    C_vec: Vec<Point<Secp256k1>>,
    C_prime_vec: Vec<Point<Secp256k1>>,
}

fn make_structured_bases(
    g: &Point<Secp256k1>,
    n_c: usize,
) -> Vec<Point<Secp256k1>> {
    let mut bases = Vec::with_capacity(n_c);

    for x in 0..n_c {
        let scalar = Scalar::<Secp256k1>::from((x + 2) as u64);
        bases.push(g * &scalar);
    }

    bases
}

fn make_hc_eq_instance(
    g: &Point<Secp256k1>,
    h: &Point<Secp256k1>,
    n_c: usize,
    fast_rng: &mut FastRng,
    vote_value: Scalar<Secp256k1>,
) -> HcEqInstance {
    let r_vec = fast_rng.batch_scalars(n_c);
    let s_vec = fast_rng.batch_scalars(n_c);
    let v_vec = vec![vote_value; n_c];

    // h_{i,x} = g^{r_{i,x}}
    let h_vec: Vec<Point<Secp256k1>> = r_vec
        .iter()
        .map(|r| g * r)
        .collect();

    // For benchmark timing, assume g_{i,x} has already been derived.
    // This is correct for the Gen {C_i,x, C'_i,x} row,
    // because Table 1 counts this row as 4n_c G.
    let g_structured_vec = make_structured_bases(g, n_c);

    let mut C_vec = Vec::with_capacity(n_c);
    let mut C_prime_vec = Vec::with_capacity(n_c);

    for x in 0..n_c {
        // C_{i,x} = g_{i,x}^{r_{i,x}} · h^{v_{i,x}}
        let C_x = &g_structured_vec[x] * &r_vec[x]
            + h * &v_vec[x];

        // C'_{i,x} = g^{s_{i,x}} · h^{v_{i,x}}
        let C_prime_x = g * &s_vec[x]
            + h * &v_vec[x];

        C_vec.push(C_x);
        C_prime_vec.push(C_prime_x);
    }

    HcEqInstance {
        r_vec,
        s_vec,
        v_vec,
        h_vec,
        g_structured_vec,
        C_vec,
        C_prime_vec,
    }
}

fn make_all_public_keys(
    g: &Point<Secp256k1>,
    n_v: usize,
    n_c: usize,
    fast_rng: &mut FastRng,
) -> (
    Vec<Vec<Scalar<Secp256k1>>>,
    Vec<Vec<Point<Secp256k1>>>,
) {
    let mut all_r_vecs = Vec::with_capacity(n_v);
    let mut all_h_vecs = Vec::with_capacity(n_v);

    for _ in 0..n_v {
        let r_vec = fast_rng.batch_scalars(n_c);

        let h_vec: Vec<Point<Secp256k1>> = r_vec
            .iter()
            .map(|r| g * r)
            .collect();

        all_r_vecs.push(r_vec);
        all_h_vecs.push(h_vec);
    }

    (all_r_vecs, all_h_vecs)
}

fn compute_recovery_bases_for_all(
    all_h_vecs: &[Vec<Point<Secp256k1>>],
    dropouts: &[usize],
    n_c: usize,
) -> Vec<Vec<Point<Secp256k1>>> {
    let n_v = all_h_vecs.len();

    let mut is_dropout = vec![false; n_v];
    for &j in dropouts {
        is_dropout[j] = true;
    }

    let mut recovery_bases = vec![vec![Point::<Secp256k1>::zero(); n_c]; n_v];

    for x in 0..n_c {
        // prefix[i] = sum of dropout public keys h_{j,x} for j < i
        let mut prefix = vec![Point::<Secp256k1>::zero(); n_v + 1];

        for i in 0..n_v {
            prefix[i + 1] = prefix[i].clone();

            if is_dropout[i] {
                prefix[i + 1] = &prefix[i + 1] + &all_h_vecs[i][x];
            }
        }

        let total_dropout_product = prefix[n_v].clone();

        for i in 0..n_v {
            // product over j in M, j < i
            let before_i = prefix[i].clone();

            // product over j in M, j > i
            let after_i = total_dropout_product.clone() - &prefix[i + 1];

            // \hat{g}_{i,x} = product_{j in M, j>i} h_{j,x}
            //                · product_{j in M, j<i} h_{j,x}^{-1}
            recovery_bases[i][x] = after_i - &before_i;
        }
    }

    recovery_bases
}
fn ceil_sqrt_u64(n: u64) -> u64 {
    let mut r = (n as f64).sqrt().floor() as u64;

    while (r as u128) * (r as u128) < n as u128 {
        r += 1;
    }

    while r > 0 && ((r - 1) as u128) * ((r - 1) as u128) >= n as u128 {
        r -= 1;
    }

    r
}

fn point_key(point: &Point<Secp256k1>) -> Vec<u8> {
    point.to_bytes(false).to_vec()
}

/// Solve target = base^x for x in [0, bound].
/// In this codebase, group multiplication is written additively:
/// base^x means base * x.
fn bounded_bsgs(
    base: &Point<Secp256k1>,
    target: &Point<Secp256k1>,
    bound: u64,
) -> Option<u64> {
    let m = ceil_sqrt_u64(bound + 1);

    // Baby steps: base^j for j = 0, ..., m-1
    let mut table: HashMap<Vec<u8>, u64> = HashMap::with_capacity(m as usize);

    let mut baby = Point::<Secp256k1>::zero();

    for j in 0..m {
        table.entry(point_key(&baby)).or_insert(j);
        baby = baby + base;
    }

    // Giant step size: base^m
    let giant_step = base * Scalar::<Secp256k1>::from(m);

    // Search target - i * base^m
    let mut current = target.clone();

    for i in 0..=m {
        if let Some(&j) = table.get(&point_key(&current)) {
            let candidate = i * m + j;

            if candidate <= bound {
                return Some(candidate);
            }
        }

        current = current - &giant_step;
    }

    None
}
/// Run benchmarks for a specific DAO configuration with optimizations
fn run_benchmarks_for_config_optimized(name: &str, n_p: usize, n_c: usize, n_v: usize, t: u64, iterations: usize) {
    println!("\n=== {} DAO Benchmark (Optimized) ===", name);
    println!("Parameters: n_p={}, n_c={}, n_v={}, t={}", n_p, n_c, n_v, t);

    // Shared cached generators
    let gens = Arc::new(CachedGenerators::new());
    
    // Adjust iterations for large DAOs to avoid excessive runtime
    let effective_iterations = match n_v {
        0..=200 => iterations,
        201..=1000 => iterations.min(5),
        _ => iterations.min(2),
    };

    // Benchmark 1: Generate {h_{i,x}} (OPTIMIZED with batch operations)
    {
        let gens = gens.clone();
        let mut total_time = Duration::new(0, 0);
        let mut fast_rng = FastRng::new(42);
        
        for _ in 0..effective_iterations {
            let start = Instant::now();
            
            // Batch all voters at once
            let batch_size = n_v;
            let all_r_vecs: Vec<Vec<Scalar<Secp256k1>>> = (0..batch_size)
                .map(|_| fast_rng.batch_scalars(n_c))
                .collect();
            
            let all_h_vecs: Vec<Vec<Point<Secp256k1>>> = all_r_vecs
                .iter()
                .map(|r_vec| r_vec.iter().map(|r| &gens.g * r).collect())
                .collect();
            
            std::hint::black_box(all_h_vecs);
            total_time += start.elapsed();
        }
        
        let avg_time = total_time / effective_iterations as u32;
        let per_voter_time = avg_time.as_secs_f64() * 1000.0 / n_v as f64;
        println!("Gen h_{{i,x}} (per voter): {:.6}ms", per_voter_time);
        println!("Sz h_{{i,x}}: {} bytes", size_h_vec(n_c));
    }

    // Benchmark 2: Generate {\hat{C}_{i,x}} recovery objects
{
    let gens = gens.clone();
    let mut total_time = Duration::new(0, 0);
    let mut fast_rng = FastRng::new(42);

    for _ in 0..effective_iterations {
        // Public keys are assumed to be already posted.
        let (all_r_vecs, all_h_vecs) = make_all_public_keys(
            &gens.g,
            n_v,
            n_c,
            &mut fast_rng,
        );

        let n_dropouts = (n_v as f64 * 0.1).ceil() as usize;
        let dropouts: Vec<usize> = (0..n_dropouts).collect();

        let start = Instant::now();

        let recovery_bases = compute_recovery_bases_for_all(
            &all_h_vecs,
            &dropouts,
            n_c,
        );

        // Only live voters generate \hat{C}_{i,x}
        for voter_idx in n_dropouts..n_v {
            for x in 0..n_c {
                // \hat{C}_{i,x} = \hat{g}_{i,x}^{r_{i,x}}
                let C_hat = &recovery_bases[voter_idx][x]
                    * &all_r_vecs[voter_idx][x];

                std::hint::black_box(C_hat);
            }
        }

        total_time += start.elapsed();
    }

    let live_voters = n_v - ((n_v as f64 * 0.1).ceil() as usize);
    let avg_time = total_time / effective_iterations as u32;
    let per_live_voter_time = avg_time.as_secs_f64() * 1000.0 / live_voters as f64;

    println!("Gen {{C_hat_i,x}} (per live voter): {:.6}ms", per_live_voter_time);
    println!("Sz {{C_hat_i,x}}: {} bytes", size_c_hat(n_c));
}

    // Benchmark 3: Generate {C_{i,x}, C'_{i,x}}
{
    let gens = gens.clone();
    let mut total_time = Duration::new(0, 0);
    let mut fast_rng = FastRng::new(42);

    let vote_value = Scalar::<Secp256k1>::from((t / n_v as u64).max(1));

    // Assume structured bases g_{i,x} have already been derived.
    // This row measures only C_{i,x} and C'_{i,x}, matching 4n_c G in Table 1.
    let g_structured_vec = make_structured_bases(&gens.g, n_c);

    for _ in 0..effective_iterations {
        let start = Instant::now();

        for _ in 0..n_v {
            let r_vec = fast_rng.batch_scalars(n_c);
            let s_vec = fast_rng.batch_scalars(n_c);

            for x in 0..n_c {
                // C_{i,x} = g_{i,x}^{r_{i,x}} · h^{v_{i,x}}
                let C_x = &g_structured_vec[x] * &r_vec[x]
                    + &gens.h * &vote_value;

                // C'_{i,x} = g^{s_{i,x}} · h^{v_{i,x}}
                let C_prime_x = &gens.g * &s_vec[x]
                    + &gens.h * &vote_value;

                std::hint::black_box((C_x, C_prime_x));
            }
        }

        total_time += start.elapsed();
    }

    let avg_time = total_time / effective_iterations as u32;
    let per_voter_time = avg_time.as_secs_f64() * 1000.0 / n_v as f64;

    println!("Gen {{C_i,x, C'_i,x}} (per voter): {:.6}ms", per_voter_time);
    println!("Sz {{C_i,x, C'_i,x}}: {} bytes", size_commitment_pair(n_c));
}
// Benchmark 3B: Generate {C_pay,i}
{
    let gens = gens.clone();
    let mut total_time = Duration::new(0, 0);
    let mut fast_rng = FastRng::new(42);

    let payout_value = Scalar::<Secp256k1>::from(1u64);

    for _ in 0..effective_iterations {
        let start = Instant::now();

        for _ in 0..n_v {
            for _x in 0..n_c {
                let s_pay = fast_rng.next_scalar();

                // C_pay,i = g^{s_p,i} h^{P_i}
                let C_pay = &gens.g * &s_pay + &gens.h * &payout_value;

                std::hint::black_box(C_pay);
            }
        }

        total_time += start.elapsed();
    }

    let avg_time = total_time / effective_iterations as u32;
    let per_voter_time = avg_time.as_secs_f64() * 1000.0 / n_v as f64;

    println!("Gen {{C_pay,i}} (per voter): {:.6}ms", per_voter_time);
    println!("Sz {{C_pay,i}}: {} bytes", size_c_pay(n_c));
}

// Benchmark 3C: Generate s_sum_stage
{
    let mut total_time = Duration::new(0, 0);
    let mut fast_rng = FastRng::new(42);

    for _ in 0..effective_iterations {
        let start = Instant::now();

        for _ in 0..n_v {
            let s_b1 = fast_rng.next_scalar();
            let s_b2 = fast_rng.next_scalar();
            let s_slack_b = fast_rng.next_scalar();
            let s_sum_b = s_slack_b + s_b1 + s_b2;

            let s_c1 = fast_rng.next_scalar();
            let s_c2 = fast_rng.next_scalar();
            let s_slack_c = fast_rng.next_scalar();
            let s_sum_c = s_slack_c + s_c1 + s_c2;

            std::hint::black_box((s_sum_b, s_sum_c));
        }

        total_time += start.elapsed();
    }

    let avg_time = total_time / effective_iterations as u32;
    let per_voter_time = avg_time.as_secs_f64() * 1000.0 / n_v as f64;

    println!("Gen s_sum_stage (per voter): {:.6}ms", per_voter_time);
    println!("Sz s_sum_stage: {} bytes", size_s_sum_stage());
}
    // Benchmark 4: Generate π_i^{(dl)} (OPTIMIZED with batch proof generation)
    {
        let gens = gens.clone();
        let mut total_time = Duration::new(0, 0);
        let mut fast_rng = FastRng::new(42);
        
        for _ in 0..effective_iterations {
            let start = Instant::now();
            
            for _ in 0..n_v {
                let witnesses = fast_rng.batch_scalars(n_c);
                let statements: Vec<Point<Secp256k1>> = witnesses
                    .iter()
                    .map(|w| &gens.g * w)
                    .collect();
                
                let mut transcript = Transcript::new(b"Benchmark_DL_Proof");
                let proof = SigmaDlProof::prove(
                    &mut transcript,
                    &witnesses,
                    &statements,
                    &gens.g,
                    n_c,
                );
                
                std::hint::black_box(proof);
            }
            
            total_time += start.elapsed();
        }
        
        let avg_time = total_time / effective_iterations as u32;
        let per_voter_time = avg_time.as_secs_f64() * 1000.0 / n_v as f64;
        println!("Gen π_i^(dl) (per voter): {:.6}ms", per_voter_time);
        println!("Sz π_i^(dl): {} bytes", size_pi_dl(n_c));
    }

    // Benchmark 5: Generate π_i^{(eq)} using SigmaHcEqProof
{
    let gens = gens.clone();
    let mut total_time = Duration::new(0, 0);
    let mut fast_rng = FastRng::new(42);

    let vote_value = Scalar::<Secp256k1>::from((t / n_v as u64).max(1));

    for _ in 0..effective_iterations {
        let start = Instant::now();

        for _ in 0..n_v {
            let instance = make_hc_eq_instance(
                &gens.g,
                &gens.h,
                n_c,
                &mut fast_rng,
                vote_value.clone(),
            );

            let mut transcript = Transcript::new(b"Benchmark_EQ");

            let proof = SigmaHcEqProof::prove(
                &mut transcript,
                &gens.g,
                &gens.h,
                &instance.g_structured_vec,
                &instance.C_vec,
                &instance.C_prime_vec,
                &instance.h_vec,
                &instance.s_vec,
                &instance.v_vec,
                &instance.r_vec,
                n_c,
            );

            std::hint::black_box(proof);
        }

        total_time += start.elapsed();
    }

    let avg_time = total_time / effective_iterations as u32;
    let per_voter_time = avg_time.as_secs_f64() * 1000.0 / n_v as f64;

    println!("Gen π_i^(eq) (per voter): {:.6}ms", per_voter_time);
    println!("Sz π_i^(eq): {} bytes", size_pi_eq(n_c));
}
    // Benchmark 6: Generate π_i^{(rec)}
{
    let gens = gens.clone();
    let mut total_time = Duration::new(0, 0);
    let mut fast_rng = FastRng::new(42);

    for _ in 0..effective_iterations {
        let (all_r_vecs, all_h_vecs) = make_all_public_keys(
            &gens.g,
            n_v,
            n_c,
            &mut fast_rng,
        );

        let n_dropouts = (n_v as f64 * 0.1).ceil() as usize;
        let dropouts: Vec<usize> = (0..n_dropouts).collect();

        let recovery_bases = compute_recovery_bases_for_all(
            &all_h_vecs,
            &dropouts,
            n_c,
        );

        let start = Instant::now();

        for voter_idx in n_dropouts..n_v {
            let r_vec = &all_r_vecs[voter_idx];
            let h_vec = &all_h_vecs[voter_idx];
            let g_hat_vec = &recovery_bases[voter_idx];

            let C_hat_vec: Vec<Point<Secp256k1>> = (0..n_c)
                .map(|x| &g_hat_vec[x] * &r_vec[x])
                .collect();

            let g_vec = vec![gens.g.clone(); n_c];

            let mut transcript = Transcript::new(b"Benchmark_REC");

            let proof = SigmaDleqProof::prove(
                &mut transcript,
                r_vec,
                h_vec,
                &C_hat_vec,
                &g_vec,
                g_hat_vec,
                n_c,
            );

            std::hint::black_box(proof);
        }

        total_time += start.elapsed();
    }

    let live_voters = n_v - ((n_v as f64 * 0.1).ceil() as usize);
    let avg_time = total_time / effective_iterations as u32;
    let per_live_voter_time = avg_time.as_secs_f64() * 1000.0 / live_voters as f64;

    println!("Gen π_i^(rec) (per live voter): {:.6}ms", per_live_voter_time);
    println!("Sz π_i^(rec): {} bytes", size_pi_rec(n_c));
}

// Benchmark 6B: Generate π_i^(reward)
{
    let gens = gens.clone();
    let mut total_time = Duration::new(0, 0);
    let mut fast_rng = FastRng::new(42);

    // Choose exact values so P_i * B_x = v_i,x * D holds.
    // v = 1, B_x = 10, D = 10, P = 1.
    let vote_value = Scalar::<Secp256k1>::from(1u64);
    let payout_value = Scalar::<Secp256k1>::from(1u64);
    let reward_total = Scalar::<Secp256k1>::from(10u64); // B_x
    let dao_bounty = Scalar::<Secp256k1>::from(10u64);   // D

    for _ in 0..effective_iterations {
        let start = Instant::now();

        for voter_id in 0..n_v {
            for _x in 0..n_c {
                let s_i = fast_rng.next_scalar();
                let s_pay = fast_rng.next_scalar();

                // C'_{i,x} = g^{s_i,x} h^{v_i,x}
                let C_prime = &gens.g * &s_i + &gens.h * &vote_value;

                // C_pay,i = g^{s_p,i} h^{P_i}
                let C_pay = &gens.g * &s_pay + &gens.h * &payout_value;

                // Delta = s_p,i * B_x - s_i,x * D
                let delta = s_pay.clone() * reward_total.clone()
                    - s_i.clone() * dao_bounty.clone();

                let mut transcript = Transcript::new(b"Benchmark_Reward");

                let proof = SigmaRewardProof::prove(
                    &mut transcript,
                    voter_id,
                    &gens.g,
                    &C_prime,
                    &C_pay,
                    &delta,
                );

                std::hint::black_box(proof);
            }
        }

        total_time += start.elapsed();
    }

    let avg_time = total_time / effective_iterations as u32;
    let per_voter_time = avg_time.as_secs_f64() * 1000.0 / n_v as f64;

    println!("Gen π_i^(reward) (per voter): {:.6}ms", per_voter_time);
    println!("Sz π_i^(reward): {} bytes", size_pi_reward(n_c));
}

// Benchmark 7: Generate π_{i,boost}^{(ar)} and π_{i,vote}^{(ar)}
{
    let gens = gens.clone();
    let seed = BigInt::from(42);

    let mut total_boost_time = Duration::new(0, 0);
    let mut total_vote_time = Duration::new(0, 0);

    let mut fast_rng = FastRng::new(42);

    let boost_cap = boost_cap_from_t(t);
    let vote_cap = t;

    for _ in 0..effective_iterations {
        // Boost range proof generation
        let boost_start = Instant::now();

        for _ in 0..n_v {
            let v1 = Scalar::<Secp256k1>::from(boost_cap / 4);
            let v2 = Scalar::<Secp256k1>::from(boost_cap / 4);

            // These are s_{i,b1}, s_{i,b2}, the blinding values of C'
            let s1 = fast_rng.next_scalar();
            let s2 = fast_rng.next_scalar();

            let token_budget = Scalar::<Secp256k1>::from(boost_cap);

            let mut transcript = Transcript::new(b"Benchmark_Boost_Range");

            let proof = VarRange::prove_hc_voting(
                &mut transcript,
                &gens.g,
                &gens.h,
                v1,
                v2,
                s1,
                s2,
                token_budget,
                &seed,
            ).expect("Boost range proof generation failed");

            std::hint::black_box(proof);
        }

        total_boost_time += boost_start.elapsed();

        // Vote range proof generation
        let vote_start = Instant::now();

        for _ in 0..n_v {
            let v1 = Scalar::<Secp256k1>::from(vote_cap / 4);
            let v2 = Scalar::<Secp256k1>::from(vote_cap / 4);

            // These are s_{i,c1}, s_{i,c2}, the blinding values of C'
            let s1 = fast_rng.next_scalar();
            let s2 = fast_rng.next_scalar();

            let token_budget = Scalar::<Secp256k1>::from(vote_cap);

            let mut transcript = Transcript::new(b"Benchmark_Vote_Range");

            let proof = VarRange::prove_hc_voting(
                &mut transcript,
                &gens.g,
                &gens.h,
                v1,
                v2,
                s1,
                s2,
                token_budget,
                &seed,
            ).expect("Vote range proof generation failed");

            std::hint::black_box(proof);
        }

        total_vote_time += vote_start.elapsed();
    }

    let avg_boost_time = total_boost_time / effective_iterations as u32;
    let avg_vote_time = total_vote_time / effective_iterations as u32;

    let per_voter_boost_time = avg_boost_time.as_secs_f64() * 1000.0 / n_v as f64;
    let per_voter_vote_time = avg_vote_time.as_secs_f64() * 1000.0 / n_v as f64;

    println!("Gen π_i,boost^(ar) (per voter): {:.6}ms", per_voter_boost_time);
    println!("Sz π_i,boost^(ar): {} bytes", calculate_range_proof_size(t, true));

    println!("Gen π_i,vote^(ar) (per voter): {:.6}ms", per_voter_vote_time);
    println!("Sz π_i,vote^(ar): {} bytes", calculate_range_proof_size(t, false));
}

// Verification Benchmarks: Vfy π_dl, π_eq, π_rec, π_ar
{
    let gens = gens.clone();
    let seed = BigInt::from(42);

    let mut dl_verify_time = Duration::new(0, 0);
    let mut eq_verify_time = Duration::new(0, 0);
    let mut rec_verify_time = Duration::new(0, 0);
    let mut reward_verify_time = Duration::new(0, 0);
    let mut ar_verify_time = Duration::new(0, 0);

    let mut fast_rng = FastRng::new(42);

    let boost_cap = boost_cap_from_t(t);
    let vote_cap = t;

    for _ in 0..effective_iterations {
        // Vfy π_i^(dl)
        for _ in 0..n_v {
            let witnesses = fast_rng.batch_scalars(n_c);

            let statements: Vec<Point<Secp256k1>> = witnesses
                .iter()
                .map(|w| &gens.g * w)
                .collect();

            let mut transcript_prove = Transcript::new(b"Benchmark_DL");
            let proof = SigmaDlProof::prove(
                &mut transcript_prove,
                &witnesses,
                &statements,
                &gens.g,
                n_c,
            );

            let verify_start = Instant::now();

            let mut transcript_verify = Transcript::new(b"Benchmark_DL");
            proof.verify(
                &mut transcript_verify,
                &statements,
                &gens.g,
                n_c,
            ).expect("DL proof verification failed");

            dl_verify_time += verify_start.elapsed();
        }

        // Vfy π_i^(eq)
        for _ in 0..n_v {
            let vote_value = Scalar::<Secp256k1>::from((t / n_v as u64).max(1));

            let instance = make_hc_eq_instance(
                &gens.g,
                &gens.h,
                n_c,
                &mut fast_rng,
                vote_value,
            );

            let mut transcript_prove = Transcript::new(b"Benchmark_EQ");

            let proof = SigmaHcEqProof::prove(
                &mut transcript_prove,
                &gens.g,
                &gens.h,
                &instance.g_structured_vec,
                &instance.C_vec,
                &instance.C_prime_vec,
                &instance.h_vec,
                &instance.s_vec,
                &instance.v_vec,
                &instance.r_vec,
                n_c,
            );

            let verify_start = Instant::now();

            let mut transcript_verify = Transcript::new(b"Benchmark_EQ");

            proof.verify(
                &mut transcript_verify,
                &gens.g,
                &gens.h,
                &instance.g_structured_vec,
                &instance.C_vec,
                &instance.C_prime_vec,
                &instance.h_vec,
                n_c,
            ).expect("EQ proof verification failed");

            eq_verify_time += verify_start.elapsed();
        }

        // Vfy π_i^(rec)
        let (all_r_vecs, all_h_vecs) = make_all_public_keys(
            &gens.g,
            n_v,
            n_c,
            &mut fast_rng,
        );

        let n_dropouts = (n_v as f64 * 0.1).ceil() as usize;
        let dropouts: Vec<usize> = (0..n_dropouts).collect();

        let recovery_bases = compute_recovery_bases_for_all(
            &all_h_vecs,
            &dropouts,
            n_c,
        );

        for voter_idx in n_dropouts..n_v {
            let r_vec = &all_r_vecs[voter_idx];
            let h_vec = &all_h_vecs[voter_idx];
            let g_hat_vec = &recovery_bases[voter_idx];

            let C_hat_vec: Vec<Point<Secp256k1>> = (0..n_c)
                .map(|x| &g_hat_vec[x] * &r_vec[x])
                .collect();

            let g_vec = vec![gens.g.clone(); n_c];

            let mut transcript_prove = Transcript::new(b"Benchmark_REC");

            let proof = SigmaDleqProof::prove(
                &mut transcript_prove,
                r_vec,
                h_vec,
                &C_hat_vec,
                &g_vec,
                g_hat_vec,
                n_c,
            );

            let verify_start = Instant::now();

            let mut transcript_verify = Transcript::new(b"Benchmark_REC");

            proof.verify(
                &mut transcript_verify,
                h_vec,
                &C_hat_vec,
                &g_vec,
                g_hat_vec,
                n_c,
            ).expect("REC proof verification failed");

            rec_verify_time += verify_start.elapsed();
        }

        // Vfy π_i^(reward)
for voter_id in 0..n_v {
    for _x in 0..n_c {
        // Exact benchmark relation:
        // v = 1, B_x = 10, D = 10, P = 1.
        let vote_value = Scalar::<Secp256k1>::from(1u64);
        let payout_value = Scalar::<Secp256k1>::from(1u64);
        let reward_total = Scalar::<Secp256k1>::from(10u64);
        let dao_bounty = Scalar::<Secp256k1>::from(10u64);

        let s_i = fast_rng.next_scalar();
        let s_pay = fast_rng.next_scalar();

        let C_prime = &gens.g * &s_i + &gens.h * &vote_value;
        let C_pay = &gens.g * &s_pay + &gens.h * &payout_value;

        let delta = s_pay.clone() * reward_total.clone()
            - s_i.clone() * dao_bounty.clone();

        let mut transcript_prove = Transcript::new(b"Benchmark_Reward");

        let proof = SigmaRewardProof::prove(
            &mut transcript_prove,
            voter_id,
            &gens.g,
            &C_prime,
            &C_pay,
            &delta,
        );

        let verify_start = Instant::now();

        let mut transcript_verify = Transcript::new(b"Benchmark_Reward");

        proof.verify(
            &mut transcript_verify,
            voter_id,
            &gens.g,
            &C_prime,
            &C_pay,
            &reward_total,
            &dao_bounty,
        ).expect("Reward proof verification failed");

        reward_verify_time += verify_start.elapsed();
    }
}
        // Vfy π_i^(ar), combined boost + vote range verification
        for _ in 0..n_v {
            // Boost range proof
            let v1_boost = Scalar::<Secp256k1>::from(boost_cap / 4);
            let v2_boost = Scalar::<Secp256k1>::from(boost_cap / 4);
            let s1_boost = fast_rng.next_scalar();
            let s2_boost = fast_rng.next_scalar();
            let boost_budget = Scalar::<Secp256k1>::from(boost_cap);

            let C_prime_b1 = &gens.g * &s1_boost + &gens.h * &v1_boost;
            let C_prime_b2 = &gens.g * &s2_boost + &gens.h * &v2_boost;

            let mut transcript_boost_prove = Transcript::new(b"Benchmark_Boost_Range");

            let proof_boost = VarRange::prove_hc_voting(
                &mut transcript_boost_prove,
                &gens.g,
                &gens.h,
                v1_boost,
                v2_boost,
                s1_boost,
                s2_boost,
                boost_budget.clone(),
                &seed,
            ).expect("Boost range proof generation failed");

            let boost_verify_start = Instant::now();

            let mut transcript_boost_verify = Transcript::new(b"Benchmark_Boost_Range");

            proof_boost.verify_hc_voting(
                &mut transcript_boost_verify,
                &gens.g,
                &gens.h,
                &C_prime_b1,
                &C_prime_b2,
                boost_budget,
                &seed,
            ).expect("Boost range proof verification failed");

            ar_verify_time += boost_verify_start.elapsed();

            // Vote range proof
            let v1_vote = Scalar::<Secp256k1>::from(vote_cap / 4);
            let v2_vote = Scalar::<Secp256k1>::from(vote_cap / 4);
            let s1_vote = fast_rng.next_scalar();
            let s2_vote = fast_rng.next_scalar();
            let vote_budget = Scalar::<Secp256k1>::from(vote_cap);

            let C_prime_c1 = &gens.g * &s1_vote + &gens.h * &v1_vote;
            let C_prime_c2 = &gens.g * &s2_vote + &gens.h * &v2_vote;

            let mut transcript_vote_prove = Transcript::new(b"Benchmark_Vote_Range");

            let proof_vote = VarRange::prove_hc_voting(
                &mut transcript_vote_prove,
                &gens.g,
                &gens.h,
                v1_vote,
                v2_vote,
                s1_vote,
                s2_vote,
                vote_budget.clone(),
                &seed,
            ).expect("Vote range proof generation failed");

            let vote_verify_start = Instant::now();

            let mut transcript_vote_verify = Transcript::new(b"Benchmark_Vote_Range");

            proof_vote.verify_hc_voting(
                &mut transcript_vote_verify,
                &gens.g,
                &gens.h,
                &C_prime_c1,
                &C_prime_c2,
                vote_budget,
                &seed,
            ).expect("Vote range proof verification failed");

            ar_verify_time += vote_verify_start.elapsed();
        }
    }

    let live_voters = n_v - ((n_v as f64 * 0.1).ceil() as usize);

    println!("Vfy π_i^(dl) (per voter): {:.6}ms",
        dl_verify_time.as_secs_f64() * 1000.0
            / (n_v as f64 * effective_iterations as f64)
    );

    println!("Vfy π_i^(eq) (per voter): {:.6}ms",
        eq_verify_time.as_secs_f64() * 1000.0
            / (n_v as f64 * effective_iterations as f64)
    );

    println!("Vfy π_i^(rec) (per live voter): {:.6}ms",
        rec_verify_time.as_secs_f64() * 1000.0
            / (live_voters as f64 * effective_iterations as f64)
    );

    println!("Vfy π_i^(reward) (per voter): {:.6}ms",
    reward_verify_time.as_secs_f64() * 1000.0
        / (n_v as f64 * effective_iterations as f64)
    );
    println!("Vfy π_i^(ar) (per voter, boost+vote): {:.6}ms",
        ar_verify_time.as_secs_f64() * 1000.0
            / (n_v as f64 * effective_iterations as f64)
    );
}

// Benchmark 11A: Aggregating commitments
{
    let gens = gens.clone();
    let mut total_time = Duration::new(0, 0);
    let mut fast_rng = FastRng::new(42);

    let vote_per_voter = (t / n_v as u64).max(1);
    let vote_scalar = Scalar::<Secp256k1>::from(vote_per_voter);

    // Precompute commitments outside the timed section.
    // This benchmark measures only aggregation:
    // C_final_x = product_i C_i,x
    let commitments: Vec<Vec<Point<Secp256k1>>> = (0..n_v)
        .map(|_| {
            (0..n_c)
                .map(|_| {
                    let r = fast_rng.next_scalar();

                    // A generic commitment-shaped group element.
                    // The randomness does not matter for aggregation timing.
                    &gens.g * &r + &gens.h * &vote_scalar
                })
                .collect()
        })
        .collect();

    for _ in 0..effective_iterations {
        let start = Instant::now();

        let mut final_commitments = vec![Point::<Secp256k1>::zero(); n_c];

        for voter_idx in 0..n_v {
            for option in 0..n_c {
                final_commitments[option] =
                    &final_commitments[option] + &commitments[voter_idx][option];
            }
        }

        std::hint::black_box(final_commitments);

        total_time += start.elapsed();
    }

    let avg_time = total_time / effective_iterations as u32;
    let total_time_ms = avg_time.as_secs_f64() * 1000.0;

    println!("Aggregating (total for {} voters): {:.6}ms", n_v, total_time_ms);
}

// Benchmark 11B: Tally extraction using bounded BSGS
{
    let gens = gens.clone();
    let mut total_time = Duration::new(0, 0);

    // Public worst-case bound for the voting stage:
    // V_x <= n_v * T_i,vote = n_v * t.
    let tally_bound = (n_v as u64).saturating_mul(t);

    // Worst-case target for extraction.
    // This follows the paper's idea of benchmarking bounded extraction.
    let target_value = tally_bound;

    let target = &gens.h * Scalar::<Secp256k1>::from(target_value);

    for _ in 0..effective_iterations {
        let start = Instant::now();

        for _option in 0..n_c {
            let recovered = bounded_bsgs(
                &gens.h,
                &target,
                tally_bound,
            ).expect("BSGS tally extraction failed");

            assert_eq!(recovered, target_value);

            std::hint::black_box(recovered);
        }

        total_time += start.elapsed();
    }

    let avg_time = total_time / effective_iterations as u32;
    let total_time_ms = avg_time.as_secs_f64() * 1000.0;

    println!(
        "Tallying / BSGS (total for {} voters, {} options): {:.6}ms",
        n_v,
        n_c,
        total_time_ms
    );
}    

}
/// Calculate actual range proof size based on VarRange struct
fn calculate_range_proof_size(t: u64, is_boost: bool) -> usize {
    const G_BYTES: usize = 33;

    // floor(log2(x)) for x>0
    fn floor_log2_u64(x: u64) -> u32 {
        63 - x.leading_zeros()
    }

    // Table 1: 2^{b-1} <= 2*sqrt(t) < 2^b
    // Integer-safe equivalent: b = floor_log2(4t)/2 + 1
    fn compute_b(t: u64) -> u32 {
        let four_t = 4u64 * t;
        (floor_log2_u64(four_t) / 2) + 1
    }

    // Table 1: 2^{b̄-1} <= t < 2^{b̄}
    fn compute_bbar(t: u64) -> u32 {
        floor_log2_u64(t) + 1
    }

    let num_group_elems = if is_boost {
        compute_b(t) as usize
    } else {
        compute_bbar(t) as usize
    };

    num_group_elems * G_BYTES
}





/// All benchmarks in one test
#[test]
#[ignore]
fn benchmark_bsgs_tally_extraction_table() {
    use std::env;

    println!("=== BSGS Tally Extraction Benchmark ===");

    // Default range is practical for normal laptops.
    // For the full paper table, set BSGS_MAX_EXP=55.
    let min_exp: u32 = env::var("BSGS_MIN_EXP")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(20);

    let max_exp: u32 = env::var("BSGS_MAX_EXP")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(55);

    let repeats: usize = env::var("BSGS_REPEATS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1);

    assert!(min_exp <= max_exp, "BSGS_MIN_EXP must be <= BSGS_MAX_EXP");
    assert!(max_exp <= 62, "max_exp too large for u64 shifting");

    println!("Range: 2^{} to 2^{}", min_exp, max_exp);
    println!("Repeats per bound: {}", repeats);

    let gens = CachedGenerators::new();
    let base = gens.h.clone();

    let mut results: Vec<(u32, f64)> = Vec::new();

    for exp in min_exp..=max_exp {
        let bound = 1u64 << exp;
        let baby_steps = ceil_sqrt_u64(bound + 1);

        println!(
            "\nBenchmarking bnd = 2^{} = {} ; baby steps ≈ {}",
            exp, bound, baby_steps
        );

        let target = &base * Scalar::<Secp256k1>::from(bound);

        let mut total_time = Duration::new(0, 0);

        for repeat in 0..repeats {
            let start = Instant::now();

            let recovered = bounded_bsgs(
                &base,
                &target,
                bound,
            ).expect("BSGS failed to recover the tally");

            let elapsed = start.elapsed();

            assert_eq!(recovered, bound);

            println!(
                "  repeat {}: {:.6}s",
                repeat + 1,
                elapsed.as_secs_f64()
            );

            total_time += elapsed;
        }

        let avg = total_time.as_secs_f64() / repeats as f64;

        println!("  average: {:.6}s", avg);

        results.push((exp, avg));
    }

    println!("\n=== BSGS Benchmark Complete ===");

    println!("\nRaw results:");
    for (exp, time_s) in &results {
        println!("2^{}    {:.4}", exp, time_s);
    }

    println!("\nLaTeX table rows:");
    for chunk in results.chunks(4) {
        for (idx, (exp, time_s)) in chunk.iter().enumerate() {
            if idx > 0 {
                print!(" & ");
            }

            print!("$2^{{{}}}$ & {:.4}", exp, time_s);
        }

        println!(r" \\");
    }
}

fn benchmark_all_operations_optimized() {
    println!("=== HC Voting OPTIMIZED Benchmark Suite ===");
    println!("Running all cryptographic operations...\n");
    
    // Define all 4 DAO configurations from Table 3
    let configs = vec![
        //("Small",       1,  2,   50,    1024),
        //("Medium",      3,  6,   200,   16384),
        //("Large",       5,  10,  1000,  16384),
        ("Extra Large", 10, 20,  4000,  1_048_576),
    ];
    
    // Run benchmarks for each configuration
    for (name, n_p, n_c, n_v, t) in configs {
        run_benchmarks_for_config_optimized(name, n_p, n_c, n_v, t, 1);
    }
    
    println!("\n=== OPTIMIZED Benchmark Complete ===");
    println!("Note: All generation operations are per voter times");
    println!("Tallying is total time for the entire DAO");
    println!("Optimizations applied:");
    println!("1. Cached generator points");
    println!("2. Fast random number generation with caching");
    println!("3. Precomputed dropout products");
    println!("4. Vectorized operations");
    println!("5. Dynamic iteration count based on DAO size");
}

#[test]
#[ignore = "Run manually to generate the full HC Voting performance table"]
fn benchmark_real_world_hc_voting_table() {
    benchmark_all_operations_optimized();
}