use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use super::basic::*;

pub fn paramgen_from_seed<Blob: AsRef<[u8]>>(
    seed: Blob,
    seed2: Blob,
    n: usize,
) -> Result<(ProverParams, VerifierParams), String> {
    // check the length of the seed
    if seed.as_ref().len() < 32 {
        return Err(String::from("Seed is too short"));
    }
    if n > 65536 {
        return Err(String::from("N is greater than 65536"));
    }

    // invoke the internal parameter generation function
    Ok(paramgen(
        &Fr::from_repr(hash_to_field_repr(&seed)).unwrap(),
        &Fr::from_repr(hash_to_field_repr(&seed2)).unwrap(),
        n,
    ))
}

fn paramgen(
    alpha: &Fr,
    beta: &Fr,
    n: usize,
) -> (ProverParams, VerifierParams) {
    //{g1^{\bm{\alpha}||\alpha^N\bm{\alpha}[-1]}}
    let mut g1_vec_alpha = Vec::with_capacity(2 * n);

    //g1^{\bm{\alpha}(\bm{\beta}||\beta^N\bm{\beta}[-1])^T}
    let mut g1_vec_alpha_beta = Vec::with_capacity(2 * n * n);

    //g2^{\bm{\alpha}}
    let mut g2_vec_alpha = Vec::with_capacity(n);

    //g2^{\bm{\beta}||\beta^{N+1}}
    let mut g2_vec_beta = Vec::with_capacity(n + 1);
    
    let mut alpha_power = Fr::one();
    let mut beta_power = Fr::one();
    for _ in 0..n {
        alpha_power.mul_assign(&alpha); // compute alpha^i
        g1_vec_alpha.push(G1Affine::one().mul(alpha_power).into_affine());
        g2_vec_alpha.push(G2Affine::one().mul(alpha_power).into_affine());

        let mut alpha_beta_power = alpha_power;
        for _ in 0..n {
            alpha_beta_power.mul_assign(&beta); //compute alpha^i beta^j
            g1_vec_alpha_beta.push(G1Affine::one().mul(alpha_beta_power).into_affine());
        }
        // skip g1^{alpha^i beta^{n+1}}
        alpha_beta_power.mul_assign(&beta);
        g1_vec_alpha_beta.push(G1::zero().into_affine()); // this 0 is important -- without it, prove will not work correctly
        // Now do the rest of the prover
        for _ in n..2 * n - 1 {
            alpha_beta_power.mul_assign(&beta); //compute alpha^i beta^j
            g1_vec_alpha_beta.push(G1Affine::one().mul(alpha_beta_power).into_affine());
        }


        beta_power.mul_assign(&beta); // compute beta^i
        g2_vec_beta.push(G2Affine::one().mul(beta_power).into_affine());
    }

    // skip g1^{alpha^{n+1}}
    alpha_power.mul_assign(&alpha);
    g1_vec_alpha.push(G1::zero().into_affine()); // this 0 is important -- without it, prove will not work correctly

    //compute g1^{beta^{n+1}}
    beta_power.mul_assign(&beta);
    g2_vec_beta.push(G2Affine::one().mul(beta_power).into_affine());

    // Now do the rest
    for _ in n..2 * n - 1 {
        alpha_power.mul_assign(&alpha); // compute alpha^i
        g1_vec_alpha.push(G1Affine::one().mul(alpha_power).into_affine());
    }

    // gt^{alpha^{n+1}}=e(g1^alpha, g2^alpha^n)
    let gt = Bls12::pairing(g1_vec_alpha[0], g2_vec_alpha[n - 1]);

    (
        ProverParams {
            n,
            generators_alpha: g1_vec_alpha,
            generators_alpha_beta: g1_vec_alpha_beta, 
        },
        VerifierParams {
            n,
            generators_alpha: g2_vec_alpha,
            generators_beta: g2_vec_beta,
            gt_elt: gt,
        },
    )
}

