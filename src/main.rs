mod algorithm;
use  algorithm::basic::LocalCommitment;
use  algorithm::basic::GlobalCommitment;
use  algorithm::basic::LocalProof;
use  algorithm::basic::GlobalProof;
use  algorithm::basic::hash_to_field_repr;

extern crate time;
use pairing_plus::{bls12_381::*};
use ff_zeroize::{Field, PrimeField};

fn main() {
    test_all_alg();
}

fn test_all_alg()
{
        // generate parameter for dimension n
        let n: usize=32;
    
        let mut strings: Vec<String> = Vec::with_capacity(n*n);
        for i in 0..n {
            for j in 0..n {
                strings.push(format!("this is message number {}", i*n+j));
            }
        }
    
        // hash the values into scalars
        let mut values: Vec<FrRepr> = strings
        .iter()
        .map(|s| hash_to_field_repr(s))
        .collect();
    
        let (pp, vp) = algorithm::setup::paramgen_from_seed(
            "This is a very very long seed for vector commitment benchmarking",
            "This is a very very long seed for vector commitment benchmarking1",
            n,
        )
        .unwrap();
    
        println!("parameters generated");
    
        /*generate global commitment*/
        let start = time::now();//获取开始时间
        let mut gCom = GlobalCommitment::new(&pp, &values).unwrap();
        let end = time::now();//获取结束时间
        println!("Global Commit:{:?}",end-start);
        
        /*generate local commitment*/
        let mut lComs: Vec<LocalCommitment> = vec![];
        let start = time::now();//获取开始时间
        for i in 0..n {
            lComs.push(LocalCommitment::new(&pp, &values[i*n..(i+1)*n]).unwrap());   
        }
        let end = time::now();//获取结束时间
        println!("A Local Commit:{:?}",(end-start)/n as i32);

        /*generate local proofs and global proofs*/
        let mut local_proofs: Vec<LocalProof> = vec![];
        let mut global_proofs: Vec<GlobalProof> = vec![];
    
        let start = time::now();//获取开始时间  
        for i in 0..n {
            for j in 0..n{ 
                local_proofs.push(LocalProof::new(&pp, &values[i*n..(i+1)*n], j).unwrap());
            }
        }
        let end = time::now();//获取结束时间
        println!("Single ProveLocal:{:?}",(end-start)/(n*n) as i32);
    
        let start = time::now();//获取开始时间  
        for i in 0..n {
            global_proofs.push(GlobalProof::new(&pp, &values, i).unwrap());
        }
        let end = time::now();//获取结束时间
        println!("Single ProveGlobal:{:?}",(end-start)/n as i32);
    
        /*single verification*/
        let start = time::now();//获取开始时间  
        for i in 0..n {
            for j in 0..n{
                let index=i*n+j;
                let res=local_proofs[index].verify_single_local_proof(&vp, &lComs[i].local_commit, values[index], j);
                if !res {
                    println!("({},{})local proof verify res is {}",i, j, res);
                }
            }
        }
        let end = time::now();//获取结束时间
        println!("Single Verify Local Proof:{:?}",(end-start)/(n*n) as i32);
    
        let start = time::now();//获取开始时间  
        for i in 0..n {
            let res= global_proofs[i].verify_single_global_proof(&vp, &gCom.global_commit, &lComs[i].local_commit, i);
            if !res {
                println!("({})global proof verfy res is {}",i, res);
            }   
        }
        let end = time::now();//获取结束时间
        println!("Single Verify Global Proof:{:?}",(end-start)/n as i32);
    
        /*aggregate proofs*/
        //1. prepare the aggregated proofs
        let outer_size = n;
        let inner_size = n;
        let mut in_set: Vec<Vec<usize>> = vec![];//S
        let mut in_sub_value: Vec<Vec<FrRepr>> = vec![];//M[S]
        let mut in_sub_proof: Vec<Vec<LocalProof>> = vec![];//{\pi_ij}(i, j)\in S
        let mut out_set: Vec<usize> = vec![];
        let mut out_sub_value: Vec<G1> =vec![];
        let mut out_sub_proof: Vec<GlobalProof> = vec![];
        for i in 0..outer_size {
            let mut line_in_set: Vec<usize> = vec![];
            let mut line_in_sub_value: Vec<FrRepr> = vec![];
            let mut line_in_sub_proof: Vec<LocalProof> = vec![];
            for j in 0..inner_size {
                line_in_set.push(j);
                line_in_sub_value.push(values[i*n+j].clone());
                line_in_sub_proof.push(local_proofs[i*n+j].clone());
            }
            in_set.push(line_in_set);
            in_sub_value.push(line_in_sub_value);
            in_sub_proof.push(line_in_sub_proof);
    
            out_set.push(i);
            out_sub_value.push(lComs[i].local_commit);
            out_sub_proof.push(global_proofs[i].clone());
        }
       
        //2. aggregate proofs
        let start = time::now();//获取开始时间  
        let agg_local_pf=LocalProof::aggregate_local_proof(&out_sub_value, &in_sub_proof, &in_set, &in_sub_value, n).unwrap();
        let end = time::now();//获取结束时间
        println!("Aggregate {} local Proofs:{:?}",outer_size*inner_size, end-start);
        
        let start = time::now();//获取开始时间  
        let agg_global_pf=GlobalProof::aggregate_global_proof(&gCom.global_commit, &out_sub_proof, &out_set, &out_sub_value, n). unwrap();
        let end = time::now();//获取结束时间
        println!("Aggregate {} global Proofs:{:?}",outer_size, end-start);
    
        /*batch verification*/
        let start = time::now();//获取开始时间  
        let res = agg_local_pf.batch_verify_local_proof(&vp, &out_sub_value, &in_set, &in_sub_value);
        if !res{
            println!("The verification of agg_lo_pf is {}", res);
        }
        let end = time::now();//获取结束时间
        println!("Batch verify the aggregated local proof:{:?}",end-start);
    
        let start = time::now();//获取开始时间  
        let res = agg_global_pf.batch_verify_global_proof(&vp, &gCom.global_commit, &out_set, &out_sub_value);
        if !res{
            println!("The verification of agg_glo_pf is {}", res);
        }
        let end = time::now();//获取结束时间
        println!("Batch verify the aggregated global proof:{:?}",end-start);
    
        /*update*/
        //1. prepare the delta_value
        let changed_index=(1,1);//\in [N-1]\times [N-1]
        let old_value = values[changed_index.0*n+changed_index.1].clone();
        let new_value = hash_to_field_repr("this is new message number");
        values[changed_index.0*n+changed_index.1]=new_value;//in order to further verification
    
        let mut multiplier = Fr::from_repr(old_value).unwrap();
        multiplier.negate();
        multiplier.add_assign(&Fr::from_repr(new_value).unwrap());
        let delta_value = multiplier;
    
        //2. update commit
        let start = time::now();//获取开始时间   
        lComs[changed_index.0].update_local_commitment(&pp, changed_index, delta_value).unwrap();
        let end = time::now();//获取结束时间
        println!("Update inner commitment:{:?}",end-start);
    
        let start = time::now();//获取开始时间   
        gCom.update_global_commitment(&pp, changed_index, delta_value).unwrap();
        let end = time::now();//获取结束时间
        println!("Update global commitment:{:?}",end-start);
        //3. update local proof in the same line
        let start = time::now();//获取开始时间   
        for j in 0..n{
            local_proofs[changed_index.0*n+j].update_local_proof(&pp, (changed_index.0, j), changed_index, delta_value).unwrap();
        }
        let end = time::now();//获取结束时间
        println!("Update an local proof:{:?}",(end-start)/n as i32);
        println!("Update all related local proofs:{:?}",end-start);
    
        //4. update global proof
        let start = time::now();//获取开始时间   
        for i in 0..n{
            global_proofs[i].update_global_proof(&pp, i, changed_index, delta_value).unwrap();
        }
        let end = time::now();//获取结束时间
        println!("Update an global proof:{:?}",(end-start)/n as i32);
        println!("Update all related global proofs:{:?}",end-start);
    
        /*single verification after updating*/
        for i in 0..n {
            for j in 0..n{
                let index=i*n+j;
                let res=local_proofs[index].verify_single_local_proof(&vp, &lComs[i].local_commit, values[index], j);
                if !res {
                    println!("({},{})local proof verfy res is {}",i, j, res);
                }
                
            }
            let res= global_proofs[i].verify_single_global_proof(&vp, &gCom.global_commit, &lComs[i].local_commit, i);
            if !res {
                println!("({})global proof verfy res is {}",i, res);
            }   
        }  
}

/*
fn test_smart_contract()
{
        // generate parameter for dimension n
        let n: usize=1024;
        //let n: usize=32;
    
        let mut strings: Vec<String> = Vec::with_capacity(n*n);
        for i in 0..n {
            for j in 0..n {
                strings.push(format!("this is message number {}", i*n+j));
            }
        }
    
        // hash the values into scalars
        let mut values: Vec<FrRepr> = strings
        .iter()
        .map(|s| hash_to_field_repr(s))
        .collect();
    
        let (pp, vp) = algorithm::setup::paramgen_from_seed(
            "This is a very very long seed for vector commitment benchmarking",
            "This is a very very long seed for vector commitment benchmarking1",
            n,
        )
        .unwrap();
    
        println!("parameters generated");
    
        /*generate com=(commitC2, commitC1)*/
        let start = time::now();//获取开始时间
        let mut com = Commitment::new(&pp, &values).unwrap();
        let end = time::now();//获取结束时间
        println!("Commit:{:?}",end-start);
        
        /*generate outer proofs*/      
        let mut outer_proofs: Vec<OuterProof> = vec![]; 
        let start = time::now();//获取开始时间  
        for i in 0..n {
            outer_proofs.push(OuterProof::new(&pp, &values, i).unwrap());
        }
        let end = time::now();//获取结束时间
        println!("ProveOuter:{:?}",end-start);
    
        /*Different b*/
        let b_vec = vec![32, 128, 256, 512, 1024];
        //let b_vec = vec![2, 4, 32];

        let l=n;
        for b in b_vec.clone(){
            println!("b={:?}",b);
            /*propose a new transaction=generate b inner proofs and aggregate them*/
            let mut inner_proofs: Vec<InnerProof> = Vec::with_capacity(l);//aggregated proofs
            let mut in_sets: Vec<Vec<usize>> = Vec::with_capacity(l);
            let mut in_sub_values: Vec<Vec<FrRepr>> = Vec::with_capacity(l);
            let mut sub_commitments: Vec<G1> = Vec::with_capacity(l);

            let start = time::now();//获取开始时间  
            for i in 0..l {  
                let mut in_sub_proof: Vec<InnerProof> = Vec::with_capacity(b);
                let mut in_set: Vec<usize> = Vec::with_capacity(b);
                let mut in_sub_value: Vec<FrRepr> = Vec::with_capacity(b);
                 
                for j in 0..b{ 
                    in_sub_proof.push(InnerProof::new(&pp, &values[i*n..(i+1)*n], j).unwrap());
                    in_set.push(j);
                    in_sub_value.push(values[i*n+j]);
                }
              
                let agg_in_pf=InnerProof::aggregate_inner_proofs_same_inner_commitment(&com.commit_c1[i], &in_sub_proof, &in_set, &in_sub_value, n).unwrap();

                inner_proofs.push(agg_in_pf);
                in_sets.push(in_set);
                in_sub_values.push(in_sub_value);
                sub_commitments.push(com.commit_c1[i]);
            }
            let end = time::now();//获取结束时间
            println!("Propose a transaction:{:?}",(end-start)/l as i32);

            /*Verify a transaction at the block proposer*/
            let start = time::now();//获取开始时间  
            for i in 0..l{
                //step 1: verify one outer proof
                let res = outer_proofs[i].verify_single_outer_proof(&vp, &com.commit_c2, &com.commit_c1[i], i);
                if !res {
                    println!("({})outer proof verfy res is {}",i, res);
                }
                //step 2: verify the aggregated inner proof
                let res = inner_proofs[i].batch_verify_inner_proof_same_commitment(&vp, &sub_commitments[i], &in_sets[i], &in_sub_values[i]);
                if !res{
                    println!("The verification of agg_in_pf is {}", res);
                }   
            }
            let end = time::now();//获取结束时间
            println!("Verify a transaction at the block proposer:{:?}",(end-start)/l as i32);
        
            /*Aggregate proofs at the block proposer*/  
            let mut out_set: Vec<usize> = vec![];
            let mut out_sub_proof: Vec<OuterProof> = vec![];
            for i in 0..l{
                out_set.push(i);
                out_sub_proof.push(outer_proofs[i].clone());     
            }  

            let start = time::now();//获取开始时间  
            //step 1: aggregate l outer proofs
            let agg_out_pf=OuterProof::aggregate_outer_proof(&com.commit_c2, &out_sub_proof, &out_set, &sub_commitments, n). unwrap();
            //step 2: aggregate l aggregated inner proofs
            let agg_in_pf=InnerProof::aggregate_aggregated_inner_proofs_from_different_inner_commitments(&sub_commitments, &inner_proofs, &in_sets, &in_sub_values, n).unwrap();
            let end = time::now();//获取结束时间
            println!("Aggregate proofs at the block proposer:{:?}",end-start);
            
            /*Verify a new block*/
            let start = time::now();//获取开始时间  
            let res = agg_out_pf.batch_verify_outer_proof(&vp, &com.commit_c2, &out_set, &sub_commitments);
            if !res{
                println!("The verification of agg_out_pf is {}", res);
            }
            let res = agg_in_pf.batch_verify_inner_proof(&vp, &sub_commitments, &in_sets, &in_sub_values);
            if !res{
                println!("The verification of agg_in_pf is {}", res);
            }
            let end = time::now();//获取结束时间
            println!("Verify a new block:{:?}",end-start);      
        }

        /*Update Commitment at the block proposer*/
        for b in b_vec{
            //step 1. prepare the bl delta_value
            let mut changed_indexes = vec![];
            let mut delta_values = vec![];
            for i in 0..l{
                for j in 0..b{
                    let changed_index=(i,j);//\in [N-1]\times [N-1]
                    let old_value = values[changed_index.0*n+changed_index.1].clone();
                    let new_value = hash_to_field_repr(format!("this is new message number {}", i*n+j));
                    values[changed_index.0*n+changed_index.1]=new_value;//in order to further verification
                
                    let mut multiplier = Fr::from_repr(old_value).unwrap();
                    multiplier.negate();
                    multiplier.add_assign(&Fr::from_repr(new_value).unwrap());
                    let delta_value = multiplier;
    
                    changed_indexes.push(changed_index);
                    delta_values.push(delta_value);
                }
            }
            
            //step 2. batch update commit
            let start = time::now();//获取开始时间
            //com.batch_update_commitment(&pp, &changed_indexes, &delta_values).unwrap();   
            let end = time::now();//获取结束时间
            println!("Update Commitment at the block proposer:{:?}",end-start);
        }       
}*/