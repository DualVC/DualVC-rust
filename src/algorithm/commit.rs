use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective};
use ff_zeroize::{PrimeField};
use super::basic::*;

impl Commitment {
    /// generate a new commitment.
    pub fn new(
        prover_params: &ProverParams,
        values: &[FrRepr],
    ) -> Result<Self, String> {
        if (prover_params.n * prover_params.n) != values.len() {
            return Err(String::from("Invalid Size"));
        };

        let scalars_u64: Vec<&[u64; 4]> = values.iter().map(|s| &s.0).collect();

        //C_2=g_1^{\sum_{i\in[N]}\sum_{j\in[N]}m_{ij}\alpha^j\beta^i}
        let mut rearrange_alpha_beta_vec = Vec::with_capacity(prover_params.n * prover_params.n);
        for i in 0..prover_params.n{
            for j in 0..prover_params.n{
                rearrange_alpha_beta_vec.push(prover_params.generators_alpha_beta[j*(2*prover_params.n)+i]);
            }
        }
        let commit_c2 = G1Affine::sum_of_products(&rearrange_alpha_beta_vec, &scalars_u64);
        //C1=(c_1, ..., c_n)
        let mut commit_c1 = Vec::with_capacity(prover_params.n);
    
        for i in 0..prover_params.n {
            commit_c1.push(G1Affine::sum_of_products(
                &prover_params.generators_alpha[0..prover_params.n],
                &scalars_u64[i*prover_params.n..(i+1)*prover_params.n]));
        }
       
        Ok(Self {
            commit_c2,
            commit_c1
        })
    }

    // updated an existing outer commitment
    pub fn update_outer_commitment(
        &mut self,
        prover_params: &ProverParams,
        changed_index: (usize, usize),//\in [N-1]\times [N-1]
        delta_value: Fr
    ) -> Result<(), String> {
        if prover_params.n <= changed_index.0 || prover_params.n <= changed_index.1 {
            return Err(String::from("Invalid Index"));
        };

        // new_commit = old_commit * g[index]^multiplier
        let res_c2 = prover_params.generators_alpha_beta[changed_index.0*(2*prover_params.n)+changed_index.1].mul(delta_value);

        self.commit_c2.add_assign(&res_c2);

        Ok(())
    }

    // updated an existing outer commitment
    pub fn update_inner_commitment(
        &mut self,
        prover_params: &ProverParams,
        changed_index: (usize, usize),//\in [N-1]\times [N-1]
        delta_value: Fr
    ) -> Result<(), String> {
        if prover_params.n <= changed_index.0 || prover_params.n <= changed_index.1 {
            return Err(String::from("Invalid Index"));
        };
        // new_commit = old_commit * g[index]^multiplier
        let resci =  prover_params.generators_alpha[changed_index.1].mul(delta_value);

        self.commit_c1[changed_index.0].add_assign(&resci);

        Ok(())
    }

    // update an existing commitment with a list of messages
    pub fn batch_update_commitment(
        &mut self,
        prover_params: &ProverParams,
        changed_index: &[(usize, usize)],
        delta_value: &[Fr],
    ) -> Result<(), String> {
        // check the parameters are valid
        for index in changed_index {
            if prover_params.n <= (*index).0 || prover_params.n <= (*index).1{
                return Err(String::from("Invalid Index"));
            };
        }
        if changed_index.len() != delta_value.len() {
            return Err(String::from("Mismatch Size"));
        }

        let mut multiplier_set: Vec<FrRepr> = Vec::with_capacity(delta_value.len());
        let mut multiplier_ci_set: Vec<Vec<FrRepr>> = Vec::with_capacity(prover_params.n);
        let mut multiplier_ci_index_set: Vec<Vec<usize>> = Vec::with_capacity(prover_params.n);
        for _ in 0..prover_params.n{
            multiplier_ci_set.push(Vec::with_capacity(prover_params.n));
            multiplier_ci_index_set.push(Vec::with_capacity(prover_params.n));
        }
        for i in 0..delta_value.len() {
            let multiplier = &delta_value[i];
            multiplier_set.push(multiplier.into_repr());

            multiplier_ci_set[(&changed_index[i]).0].push(multiplier.into_repr());
            multiplier_ci_index_set[(&changed_index[i]).0].push((&changed_index[i]).1);
        }
        let scalars_u64: Vec<&[u64; 4]> = multiplier_set.iter().map(|s| &s.0).collect();

        // form the basis for `sum_of_products`
        let basis = changed_index
            .iter()
            .map(|i| prover_params.generators_alpha_beta[(*i).0*(2*prover_params.n)+(*i).1])
            .collect::<Vec<G1Affine>>();

        // compute delta = \prod g[index.0*prover_params.n+index.1]^multiplier
        let delta = {
            // without pre_computation
            G1Affine::sum_of_products(&basis[..], &scalars_u64)
        };
        // new_commit = old_commit * \prod delta
        self.commit_c2.add_assign(&delta);

        /*update C1=(c_1, ..., c_n)*/
        for i in 0..prover_params.n {
            let scalars_u64: Vec<&[u64; 4]> = multiplier_ci_set[i].iter().map(|s| &s.0).collect();

            // form the basis for `sum_of_products`
            let basis = multiplier_ci_index_set[i]
                .iter()
                .map(|j| prover_params.generators_alpha[*j])
                .collect::<Vec<G1Affine>>();

            // compute delta = \prod g[index.1]^multiplier
            let delta = {
                // without pre_computation
                G1Affine::sum_of_products(&basis[..], &scalars_u64)
            };
            // new_commit = old_commit * \prod delta
            self.commit_c1[i].add_assign(&delta);
        }
        Ok(())
    }
}