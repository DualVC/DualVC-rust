use pairing_plus::{bls12_381::*, CurveAffine, CurveProjective, Engine};
use ff_zeroize::{Field, PrimeField};
use super::basic::*;

impl LocalProof {
    // Generate a new proof.
    pub fn new(
        prover_params: &ProverParams,
        values: &[FrRepr],//M_i
        index: usize,//j \in [N-1]
    ) -> Result<Self, String> {
        // check index is valid
        if index >= prover_params.n{
            return Err(String::from("Invalid Index"));
        };
        // check param
        if values.len() != prover_params.n {
            return Err(String::from("Invalid Size"));
        }

        let scalars_u64: Vec<&[u64; 4]> = values.iter().map(|s| &s.0).collect();

        // proof = \sum_{i=prover_params.n - index}^{2 * prover_params.n - index}
        //          param.generator[i]^scarlar_u64[i]
        let local_proof_content = G1Affine::sum_of_products(&prover_params.generators_alpha[prover_params.n-index..2*prover_params.n-index], &scalars_u64);
      
        Ok(Self {
            local_proof_content
        })
    }

    // Updating an existing local proof.
    pub fn update_local_proof(
        &mut self,
        prover_params: &ProverParams,
        proof_index: (usize, usize),//(i, j)
        changed_index: (usize, usize),//(i, k)
        delta_value: Fr
    ) -> Result<(), String> {
        // check indices are valid
        if proof_index.0!=changed_index.0{
            return Err(String::from("Only local proof in the same row needs updating"));
        }
        if proof_index.0 >= prover_params.n || proof_index.1 >= prover_params.n || changed_index.1 >= prover_params.n {
            return Err(String::from("Invalid Index"));
        }
        //j!=k
        if proof_index.1 != changed_index.1 {
           
            let param_index = prover_params.n + changed_index.1 - proof_index.1;//n+k-j
            let res = prover_params.generators_alpha[param_index].mul(delta_value);

            //\pi'_{ij}=\pi_{ij}\cdot g_1^{\Delta m_{ik}\alpha^{N+1-j+k}}
            self.local_proof_content.add_assign(&res);
        }

        // if proof_index.1 == changed_index.1, do nothing
        Ok(())
    }

    // Part 1 of aggregate_local_proof: Aggregate the proofs in the same local commitment
    pub fn aggregate_local_proofs_same_inner_commitment(
        commit: &G1,
        proofs: &[Self],
        set: &[usize],
        value_sub_vector: &[FrRepr],
        n: usize,
    )-> Result<Self, String>
    {
        // check that the length of proofs and sets match
        if proofs.len() != set.len() || proofs.len() != value_sub_vector.len() {
            return Err(String::from("Mismatch Size"));
        }
        // get the list of scalas
        let ti = dim1_hash_repr(commit, set, value_sub_vector, n)?;
        let scalars_u64: Vec<&[u64; 4]> = ti.iter().map(|s| &s.0).collect();

        let mut bases: Vec<G1> = proofs.iter().map(|s| s.local_proof_content).collect();
        CurveProjective::batch_normalization(&mut bases);
        let bases_affine: Vec<G1Affine> =
            bases.iter().map(|s| s.into_affine()).collect();
        // proof = \prod proofs[i]^ti[i]
        let local_proof_content = G1Affine::sum_of_products(&bases_affine[..], &scalars_u64);

        Ok(LocalProof{local_proof_content})
    }
    // Part 2 of aggregate_local_proof: cross-commitment aggregate the already aggregated proofs
    pub fn aggregate_aggregated_local_proofs_from_different_inner_commitments(
        commits: &[G1],
        proofs: &[Self],
        set: &[Vec<usize>],
        value_sub_vector: &[Vec<FrRepr>],
        n: usize,
    ) -> Result<Self, String> {
        // check the length are correct
        if commits.len() != proofs.len()
        || commits.len() != set.len()
        || commits.len() != value_sub_vector.len()
        || commits.is_empty()
        {
            return Err(String::from("Mismatch Size"));
        };
        // if commit.len() == 1, return the aggregated proof
        if commits.len() == 1 {
            return Ok(proofs[0].clone());
        }

        // start aggregation
        let scalars = dim2_hash_repr(&commits, &set, &value_sub_vector, n)?;
        if scalars.len() != proofs.len() {
            return Err(String::from("Mismatch Size"));
        }

        let scalars_u64: Vec<&[u64; 4]> = scalars.iter().map(|s| &s.0).collect();

        let mut bases: Vec<G1> = proofs.iter().map(|s| s.local_proof_content).collect();
        CurveProjective::batch_normalization(&mut bases);
        let bases_affine: Vec<G1Affine> =
            bases.iter().map(|s| s.into_affine()).collect();

        // proof = \prod pi[i] ^ tj[i]
        let local_proof_content = G1Affine::sum_of_products(&bases_affine[..], &scalars_u64);

        Ok(LocalProof{local_proof_content})
    }

    // Addition of the above two functions. Aggregate a 2-dim array of proofs, each row corresponding to a commit, into a single proof.
    pub fn aggregate_local_proof(
        commits: &[G1],//C1[R(S)]
        proofs: &[Vec<Self>],//\pi_{ij}
        set: &[Vec<usize>],//S
        value_sub_vector: &[Vec<FrRepr>],//M[S]
        n: usize,
    ) -> Result<Self, String> {
        for e in set.iter() {
            for ee in e.iter() {
                if *ee >= n {
                    return Err(String::from("Invalid Index"));
                }
            }
        }

        // check the length are correct
        if commits.len() != proofs.len()
            || commits.len() != set.len()
            || commits.len() != value_sub_vector.len()
            || commits.is_empty()
        {
            return Err(String::from("Mismatch Size"));
        };

        // start aggregation
        // generate the random Fr-s
        let ti = dim2_hash_fr(&commits, &set, &value_sub_vector, n)?;
        let mut ti_s: Vec<Vec<Fr>> = Vec::with_capacity(commits.len());
        for i in 0..commits.len() {
            ti_s.push(dim1_hash_fr(
                &commits[i],
                &set[i],
                &value_sub_vector[i],
                n,
            )?);
        }
        // form the final scalars by multiplying Fr-s
        // for i in 0..# com, for k in 0..#proof, ti[i] * ti_s[i,k]
        let mut scalars_repr: Vec<FrRepr> = vec![];
        for i in 0..ti.len() {
            for e in ti_s[i].iter() {
                let mut tmp = *e;
                tmp.mul_assign(&ti[i]);
                scalars_repr.push(tmp.into_repr());
            }
        }
        let scalars_u64: Vec<&[u64; 4]> = scalars_repr.iter().map(|s| &s.0).collect();

        // form the final basis
        let mut bases: Vec<G1> = proofs.concat().iter().map(|x| x.local_proof_content).collect();
        CurveProjective::batch_normalization(&mut bases);
    
        // the CurveProjective points are already normalized via batch nomarlization
        let bases_affine: Vec<G1Affine> =
            bases.iter().map(|s| s.into_affine()).collect();

        // inner_proof_content = \prod pi[j] ^ {ti[i] * ti_s[i,j]}
        let local_proof_content = G1Affine::sum_of_products(&bases_affine[..], &scalars_u64);

        Ok(LocalProof{local_proof_content})
    }

    // Verify the single local proof.
    pub fn verify_single_local_proof(
        &self,
        verifier_params: &VerifierParams,
        com: &G1,
        value: FrRepr,
        index: usize,
    ) -> bool {
        if index >= verifier_params.n{
            return false;
        }

        // verification formula: e(com, param[n-index.1-1]) = gt_elt ^ value * e(proof, generator_of_g2)
        // which is to check
        // e(com^hash_inverse,  param[n-index.1-1]) * e(proof^{-hash_inverse}, generator_of_g2)?= gt_elt
        // We modify the formula as above in order to avoid slow exponentation in the target group (which is Fq12)
        // and perform two scalar multiplication by to 1/hash(value) in G1 instead, which is considerably faster.
        // We also move the pairing from the right-hand-side to the left-hand-side in order
        // to take advantage of the pairing product computation, which is faster than two pairings.

        // step 1. compute hash_inverse
        let hash = Fr::from_repr(value).unwrap();
        // we can safely assume that hash is invertible
        // see `hash_to_field` function
        let hash_inverse = hash.inverse().unwrap();

        // step 2, compute com^hash_inverse and proof^{-hash_inverse}
        let mut com_mut = com.clone();
        let mut proof_mut = self.local_proof_content;
        proof_mut.negate();
        com_mut.mul_assign(hash_inverse);
        proof_mut.mul_assign(hash_inverse);

        // step 3. check pairing product
        Bls12::pairing_product(
            com_mut.into_affine(),
            verifier_params.generators_alpha[verifier_params.n - index - 1],
            proof_mut.into_affine(),
            G2Affine::one(),
        ) == verifier_params.gt_elt
    }

    pub fn batch_verify_local_proof_same_commitment(
        &self,
        verifier_params: &VerifierParams,
        com: &G1,
        set: &[usize],
        value_sub_vector: &[FrRepr],
    ) -> bool {
        // we want to check if e(com, g2^{\sum_{i \in set} \alpha^{N+1-i} t_i})?= e(proof, g2) * e(g1, g2)^{alpha^{N+1} \sum value_i*t_i}
        // which is to check
        // e(com, g2^{\sum_{i \in set} \alpha^{N+1-i} t_i * tmp}) * e(proof^{-tmp}, g2) ?= e(g1, g2)^{alpha^N+1}
        // where tmp = 1/ \sum value_i*t_i

        // 0. check the validity of the inputs: csid, length, etc
        if set.len() != value_sub_vector.len() {
            return false;
        }
        if value_sub_vector.len() > verifier_params.n {
            return false;
        }
        for e in set {
            if *e >= verifier_params.n {
                return false;
            }
        }

        // if the length == 1, call normal verification method
        if set.len() == 1 {
            return self.verify_single_local_proof(&verifier_params, &com, value_sub_vector[0], set[0]);
        }
        // 1. compute tmp
        // 1.1 get the list of scalas, return false if this failed
        let mut ti = match dim1_hash_fr(com, set, value_sub_vector, verifier_params.n) {
            Err(_e) => return false,
            Ok(p) => p,
        };

        // 1.2 tmp = 1/\sum value_i*t_i
        let mut tmp = Fr::zero();
        for k in 0..set.len() {
            let mut mi = Fr::from_repr(value_sub_vector[k]).unwrap();
            mi.mul_assign(&ti[k]);
            tmp.add_assign(&mi);
        }

        // 1.3 if tmp == 0 (should never happen in practise)
        assert!(!tmp.is_zero());
        let mut tmp = tmp.inverse().unwrap();

        // 2 check e(com, g2^{\sum_{i \in set} \alpha^{N+1-i} t_i * tmp})* e(proof^{-tmp}, g2)?= e(g1, g2)^{alpha^N+1}

        // 2.1 compute t_i*tmp
        let ti_repr: Vec<FrRepr> = (0..ti.len())
            .map(|k| {
                ti[k].mul_assign(&tmp);
                ti[k].into_repr()
            })
            .collect();

        // 2.2 g2^{\sum_{i \in set} \alpha^{N+1-i} t_i*tmp}
        let bases: Vec<G2Affine> = set
            .iter()
            .map(|index| verifier_params.generators_alpha[verifier_params.n - index - 1])
            .collect();
        let scalars_u64: Vec<&[u64; 4]> = ti_repr.iter().map(|s| &s.0).collect();
        let param_subset_sum = {G2Affine::sum_of_products(&bases, &scalars_u64)};

        // 2.3 proof ^ {-tmp}
        let mut proof_mut = self.local_proof_content;
        tmp.negate();
        proof_mut.mul_assign(tmp);

        // 3 pairing product
        Bls12::pairing_product(
            com.into_affine(),
            param_subset_sum.into_affine(),
            proof_mut.into_affine(),
            G2Affine::one(),
        ) == verifier_params.gt_elt
    }

    // Verify local proofs which were aggregated from 2-dim array of proofs
    pub fn batch_verify_local_proof(
        &self,
        verifier_params: &VerifierParams,
        com: &[G1],
        set: &[Vec<usize>],
        value_sub_vector: &[Vec<FrRepr>],
    ) -> bool {
        // check length
        let num_commit = com.len();
        if num_commit != set.len() || num_commit != value_sub_vector.len() || num_commit == 0 {
            // length does not match
            return false;
        }
        for j in 0..num_commit {
            if set[j].len() != value_sub_vector[j].len()
                || set[j].is_empty()
                || set[j].len() > verifier_params.n
            {
                // length does not match
                return false;
            }
        }

        // generate all the t_i-s for j \in [num_commit] as in aggregating algorithm
        let mut ti_s: Vec<Vec<Fr>> = Vec::with_capacity(num_commit);
        for j in 0..num_commit {
            let ti_v = match dim1_hash_fr(&com[j], &set[j], &value_sub_vector[j], verifier_params.n)
            {
                Err(_e) => return false,
                Ok(p) => p,
            };
            ti_s.push(ti_v);
        }
        // generate tj
        let ti = match dim2_hash_fr(&com, &set, &value_sub_vector, verifier_params.n) {
            Err(_e) => return false,
            Ok(p) => p,
        };

        // we want to check
        //  \prod_{i=1}^num_commit e(com[i], g2^{\sum alpha^{n + 1 -j} * t_i,j} ) ^ t_i
        //      ?= e (proof, g2) * e (g1, g2)^{alpha^{n+1} * {\sum m_i,j * t_i,j * ti}}
        // step 1. compute tmp = \sum m_i,j * t_i,j * ti
        let mut tmp = Fr::zero();
        for j in 0..num_commit {
            let mut tmp2 = Fr::zero();

            // tmp2 = sum_i m_ij * t_ij
            for k in 0..ti_s[j].len() {
                let mut tmp3 = ti_s[j][k];
                let mij = Fr::from_repr(value_sub_vector[j][k]).unwrap();
                tmp3.mul_assign(&mij);
                tmp2.add_assign(&tmp3);
            }
            // tmp2 = tj * tmp2
            // safe to unwrap here
            // the output of hash should always be a field element
            let tmp3 = ti[j];
            tmp2.mul_assign(&tmp3);
            // tmp += tj * (sum_i m_ji * t_ij)
            tmp.add_assign(&tmp2);
        }

        let tmp_inverse = match tmp.inverse() {
            Some(p) => p,
            // tmp == 0 should never happen in practice
            None => panic!("some thing is wrong, check verification formula"),
        };

        // step 2. now the formula becomes
        // \prod e(com[i], g2^{\sum alpha^{n + 1 - j} * t_i,j * ti/tmp} )
        //  * e(proof^{-1/tmp}, g2)
        //  ?= e(g1, g2)^{alpha^{n+1}} == verifier_params.gt_elt

        // g1_vec stores the g1 components for the pairing product
        // for j \in [num_commit], store com[j]
        let mut g1_proj: Vec<G1> = com.to_vec();
        // the last element for g1_vec is proof^{-1/tmp}
        let mut tmp2 = self.local_proof_content;
        tmp2.negate();
        tmp2.mul_assign(tmp_inverse);
        g1_proj.push(tmp2);

        // convert g1_proj into g1_affine
        G1::batch_normalization(&mut g1_proj);
        let g1_vec: Vec<G1Affine> = g1_proj.iter().map(|s| s.into_affine()).collect();

        // g2_vec stores the g2 components for the pairing product
        // for j \in [num_commit], g2^{\sum alpha^{n + 1 - j} * t_i,j} * ti/tmp )
        let mut g2_proj: Vec<G2> = Vec::with_capacity(num_commit + 1);
        for j in 0..num_commit {
            let num_proof = ti_s[j].len();
            let mut tmp3 = tmp_inverse;
            // safe to unwrap here
            // the output of hash should always be a field element
            let scalar = ti[j];
            tmp3.mul_assign(&scalar);

            // subset_sum = \sum alpha^{n + 1 - j} * t_i,j}
            let mut bases: Vec<G2Affine> = Vec::with_capacity(num_proof);
            let mut scalars_u64: Vec<[u64; 4]> = Vec::with_capacity(num_proof);
            for k in 0..num_proof {
                bases.push(verifier_params.generators_alpha[verifier_params.n - set[j][k] - 1]);
                let mut t = ti_s[j][k];
                t.mul_assign(&tmp3);
                scalars_u64.push(t.into_repr().0);
            }
            let scalars_u64_ref: Vec<&[u64; 4]> = scalars_u64.iter().collect();

            let param_subset_sum = {
                G2Affine::sum_of_products(&bases, &scalars_u64_ref)
            };
            g2_proj.push(param_subset_sum);
        }
        // the last element for g1_vec is g2
        g2_proj.push(G2::one());
        // convert g2_proj into g2_affine
        G2::batch_normalization(&mut g2_proj);
        let g2_vec: Vec<G2Affine> = g2_proj.iter().map(|s| s.into_affine()).collect();
        
        // println!("batch_verify_inner_proof");
        // println!("lhs={}", Bls12::pairing_multi_product(&g1_vec[..], &g2_vec[..]));
        // println!("rhs={}", verifier_params.gt_elt);
        // now check the pairing product ?= verifier_params.gt_elt
        Bls12::pairing_multi_product(&g1_vec[..], &g2_vec[..]) == verifier_params.gt_elt
    }
}

impl GlobalProof {
    // Generate a new global proof.
    pub fn new(
        prover_params: &ProverParams,
        values: &[FrRepr],
        index: usize,//i \in [N-1]
    ) -> Result<Self, String> {
        // check index is valid
        if index >= prover_params.n{
            return Err(String::from("Invalid Index"));
        };
        // check param
        if values.len() != prover_params.n * prover_params.n{
            return Err(String::from("Invalid Size"));
        }

        let scalars_u64: Vec<&[u64; 4]> = values.iter().map(|s| &s.0).collect();

        // generate the proof use `sum of product` function
        // proof = \sum_{i=prover_params.n - index}^{2 * prover_params.n - index}
        //          param.generator[i]^scarlar_u64[i]
        let mut new_beta_alpha_power = Vec::with_capacity(prover_params.n * prover_params.n);
        for j in 0..prover_params.n {
            for k in 0..prover_params.n {
                new_beta_alpha_power.push(prover_params.generators_alpha_beta[k*(2*prover_params.n)+prover_params.n-index+j]);
            }
        }
        //Compute proofOuter: \pi_i=g_1^{\sum_{j\in[N]}\sum_{k\in[N]}m_{jk}\alpha^k\beta^{N+1-i+j}}
        let global_proof_content =  G1Affine::sum_of_products(&new_beta_alpha_power, &scalars_u64);

        Ok(Self {
            global_proof_content
        })
    }

    // Updating an existing global proof.
    pub fn update_global_proof(
        &mut self,
        prover_params: &ProverParams,
        proof_index: usize, //j
        changed_index: (usize, usize),//(i, k)
        delta_value: Fr
    ) -> Result<(), String> {
        // check indices are valid
        if proof_index >= prover_params.n || changed_index.0 >= prover_params.n || changed_index.1 >= prover_params.n {
            return Err(String::from("Invalid Index"));
        }

        // j!=i
        if proof_index != changed_index.0 {
            let param_index = changed_index.0 + prover_params.n - proof_index;//N+1-j+i
            let res = prover_params.generators_alpha_beta[changed_index.1*(2*prover_params.n)+param_index].mul(delta_value);
            //\pi'_j=\pi_j\cdot g_1^{\Delta m_{ik}\alpha^k\beta^{N+1-j+i}}.
            self.global_proof_content.add_assign(&res);
        }

        // if proof_index == changed_index, do nothing
        Ok(())
    }

    // Aggregates a vector of global proofs into a single one.
    pub fn aggregate_global_proof(
        commit: &G1,
        proofs: &[Self],
        set: &[usize],
        inner_commitment_sub_vector: &[G1],
        n: usize,
    ) -> Result<Self, String> {
        // check that the length of proofs and sets match
        if proofs.len() != set.len() || proofs.len() != inner_commitment_sub_vector.len() {
            return Err(String::from("Mismatch Size"));
        }

        // get the list of scalas
        let ti = dim1_hash_g1_repr(commit, set, inner_commitment_sub_vector, n)?;
        let scalars_u64: Vec<&[u64; 4]> = ti.iter().map(|s| &s.0).collect();

        let mut bases: Vec<G1> = proofs.iter().map(|s| s.global_proof_content).collect();
        CurveProjective::batch_normalization(&mut bases);
        let bases_affine: Vec<G1Affine> =
            bases.iter().map(|s| s.into_affine()).collect();
        // proof = \prod proofs[i]^ti[i]
        let global_proof_content = G1Affine::sum_of_products(&bases_affine[..], &scalars_u64);

        Ok(GlobalProof{global_proof_content})
    }

    // Verify the single global proof.
    pub fn verify_single_global_proof(
        &self,
        verifier_params: &VerifierParams,
        com: &G1,
        inner_commit_value: &G1,
        index: usize,
    ) -> bool {
        if index >= verifier_params.n {
            return false;
        }    
        // verification formula: e(com, beta_param[n-index-1]) = e(proof, generator_of_g2) * e(inner_commit_value, g2^{\beta^{N+1}})
        //step 1. compute LHS with inner function Bls12::pairing_product
        let lhs = Bls12::pairing(com.into_affine(), verifier_params.generators_beta[verifier_params.n - index - 1]);

        //step 2. compute RHS
        let rhs = Bls12::pairing_product(
            self.global_proof_content.into_affine(),
            G2Affine::one(),
            inner_commit_value.into_affine(),
            verifier_params.generators_beta[verifier_params.n]
        );
        lhs==rhs
    }

    // batch verify a proof for a list of values/indices
    pub fn batch_verify_global_proof(
        &self,
        verifier_params: &VerifierParams,
        com: &G1,
        set: &[usize],
        inner_commitment_sub_vector: &[G1],
    ) -> bool {
        // we want to check if
        //   e(com, g2^{\sum_{i \in set} \beta^{N+1-i} t_i})
        //    ?= e(proof, g2) * \Prod_{i\in set} e(c_i^{t_i}, g2^{\beta^{N+1}})

        // 0. check the validity of the inputs: csid, length, etc
        if set.len() != inner_commitment_sub_vector.len() {
            return false;
        }
        if inner_commitment_sub_vector.len() > verifier_params.n {
            return false;
        }
        for e in set {
            if *e >= verifier_params.n {
                return false;
            }
        }

        // if the length == 1, call normal verification method
        if set.len() == 1 {
            return self.verify_single_global_proof(&verifier_params, com, &inner_commitment_sub_vector[0], set[0]);
        }
        // 1. compute t_i
        // 1.1 get the list of scalas, return false if this failed
        let ti = match dim1_hash_g1_repr(com, set, inner_commitment_sub_vector, verifier_params.n) {
            Err(_e) => return false,
            Ok(p) => p,
        };

        // 1.2 g2^{\sum_{i \in set} \beta^{N+1-i} t_i}
        let bases: Vec<G2Affine> = set
            .iter()
            .map(|index| verifier_params.generators_beta[verifier_params.n - index - 1])
            .collect();
        let scalars_u64: Vec<&[u64; 4]> = ti.iter().map(|s| &s.0).collect();
        let param_subset_sum = {
            G2Affine::sum_of_products(&bases, &scalars_u64)
        };

        let lhs = Bls12::pairing(com.into_affine(), param_subset_sum.into_affine());

        let set_len = set.len();
        // 2 compute RHS=e(proof, g2) * \Prod_{i\in set} e(c_i^{t_i}, g2^{\beta^{N+1}})
        // 2.1 
        let mut g1_vec: Vec<G1Affine> = Vec::with_capacity(set_len + 1);
        let mut g2_vec: Vec<G2Affine> = Vec::with_capacity(set_len + 1);

        g1_vec.push(self.global_proof_content.into_affine());
        g2_vec.push(G2Affine::one());

        for i in 0..set_len{            
            g1_vec.push(inner_commitment_sub_vector[i].into_affine().mul(ti[i]).into_affine());
            g2_vec.push(verifier_params.generators_beta[verifier_params.n]);
        }

        let rhs = Bls12::pairing_multi_product(&g1_vec[..], &g2_vec[..]);
        // println!("batch_verify_outer_proof");
        // println!("lhs={}", lhs);
        // println!("rhs={}", rhs);
        // 3 pairing product
        lhs==rhs
    }
}