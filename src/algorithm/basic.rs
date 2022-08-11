use pairing_plus::{bls12_381::*, CurveProjective};
use ff_zeroize::{PrimeField};
use sha2::{Digest, Sha512};
use bigint::U512;
use std::ops::Rem;
use pairing_plus::serdes::SerDes;
use byteorder::{LittleEndian, ByteOrder};

#[derive(Clone, Debug)]
pub struct ProverParams {
    pub n: usize,
    pub generators_alpha: Vec<G1Affine>,
    pub generators_alpha_beta: Vec<G1Affine>,
}

#[derive(Clone, Debug)]
pub struct VerifierParams {
    pub(crate) n: usize,
    pub generators_alpha: Vec<G2Affine>,
    pub generators_beta: Vec<G2Affine>,
    pub gt_elt: Fq12,
}

#[derive(Clone, Debug, PartialEq)]
pub struct GlobalCommitment {
    pub(crate) global_commit: G1,
}

#[derive(Clone, Debug, PartialEq)]
pub struct LocalCommitment {
    pub(crate) local_commit: G1,
}

#[derive(Clone, Debug, PartialEq)]
pub struct LocalProof {   
    pub(crate) local_proof_content: G1,
}

#[derive(Clone, Debug, PartialEq)]
pub struct GlobalProof {   
    pub(crate) global_proof_content: G1,
}

/// Hashes a blob into a non-zero field element.
/// hash_to_field_pointproofs use SHA 512 to hash a blob into a non-zero field element.
pub(crate) fn hash_to_field_repr<Blob: AsRef<[u8]>>(input: Blob) -> FrRepr {
    let mut hasher = Sha512::new();
    hasher.input(input);
    let hash_output = hasher.result();
    let mut t = os2ip_mod_p(&hash_output);

    // if we get 0, return 1
    // this should not happen in practise
    if t == FrRepr([0, 0, 0, 0]) {
        t = FrRepr([1, 0, 0, 0]);
    }
    t
}

pub(crate) fn os2ip_mod_p(oct_str: &[u8]) -> FrRepr {
    // "For the purposes of this document, and consistent with ASN.1 syntax,
    // an octet string is an ordered sequence of octets (eight-bit bytes).
    // The sequence is indexed from first (conventionally, leftmost) to last
    // (rightmost).  For purposes of conversion to and from integers, the
    // first octet is considered the most significant in the following
    // conversion primitives.
    //
    // OS2IP converts an octet string to a nonnegative integer.
    // OS2IP (X)
    // Input:  X octet string to be converted
    // Output:  x corresponding nonnegative integer
    // Steps:
    // 1.  Let X_1 X_2 ... X_xLen be the octets of X from first to last,
    //  and let x_(xLen-i) be the integer value of the octet X_i for 1
    //  <= i <= xLen.
    // 2.  Let x = x_(xLen-1) 256^(xLen-1) + x_(xLen-2) 256^(xLen-2) +
    //  ...  + x_1 256 + x_0.
    // 3.  Output x. "

    let r_sec = U512::from(oct_str);

    // hard coded modulus p
    let p = U512::from([
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0x73, 0xED, 0xA7, 0x53, 0x29, 0x9D, 0x7D, 0x48, 0x33, 0x39, 0xD8, 0x08, 0x09, 0xA1,
        0xD8, 0x05, 0x53, 0xBD, 0xA4, 0x02, 0xFF, 0xFE, 0x5B, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
        0x00, 0x00, 0x01,
    ]);
    // t = r % p
    let t_sec = r_sec.rem(p);

    // convert t from a U512 into a primefield object s
    let mut tslide: [u8; 64] = [0; 64];
    let bytes: &mut [u8] = tslide.as_mut();
    t_sec.to_big_endian(bytes);

    FrRepr([
        u64::from_be_bytes([
            bytes[56], bytes[57], bytes[58], bytes[59], bytes[60], bytes[61], bytes[62], bytes[63],
        ]),
        u64::from_be_bytes([
            bytes[48], bytes[49], bytes[50], bytes[51], bytes[52], bytes[53], bytes[54], bytes[55],
        ]),
        u64::from_be_bytes([
            bytes[40], bytes[41], bytes[42], bytes[43], bytes[44], bytes[45], bytes[46], bytes[47],
        ]),
        u64::from_be_bytes([
            bytes[32], bytes[33], bytes[34], bytes[35], bytes[36], bytes[37], bytes[38], bytes[39],
        ]),
    ])
}

// A wrapper of `hash_to_outer_repr` that outputs `Fr`s instead of `FrRepr`s.
pub(crate) fn dim2_hash_fr(
    commits: &[G1],
    set: &[Vec<usize>],
    value_sub_vector: &[Vec<FrRepr>],
    n: usize,
) -> Result<Vec<Fr>, String> {
    Ok(dim2_hash_repr(commits, set, value_sub_vector, n)?
        .iter()
        .map(|s| Fr::from_repr(*s).unwrap())
        .collect())
}

/// Hash a two dim array of bytes into non-zero scalars.
pub(crate) fn dim2_hash_repr(
    commits: &[G1],
    set: &[Vec<usize>],
    value_sub_vector: &[Vec<FrRepr>],
    n: usize,
) -> Result<Vec<FrRepr>, String> {
    if commits.len() != set.len() || commits.len() != value_sub_vector.len() {
        return Err(String::from("Mismatch Size"));
    };

    if commits.len() == 1 {
        return Ok(vec![FrRepr([1, 0, 0, 0])]);
    }

    // tmp = {C | S | m[S]} for i \in [0 .. commit.len-1]
    let mut tmp: Vec<u8> = vec![];
    for i in 0..commits.len() {
        // serialize commitment
        match commitment_serialize(&commits[i], &mut tmp, true) {
            Ok(_p) => _p,
            Err(e) => return Err(e.to_string()),
        };
        // add the set to tmp
        for j in 0..set[i].len() {
            let t = set[i][j].to_be_bytes();
            tmp.append(&mut t.to_vec());
        }

        // if the set leng does not mathc values, return an error
        if set[i].len() != value_sub_vector[i].len() {
            return Err(String::from("Mismatch Size"));
        }

        // add values to set; returns an error if index is out of range
        for j in 0..set[i].len() {
            if set[i][j] >= n {
                return Err(String::from("Invalid Index"));
            }
            let t = value_sub_vector[i][j].as_ref();
           // tmp.append(&mut t.to_vec());
            let input = t.to_vec();//u64
            let mut output: Vec<u8> = vec!(0;32);
            LittleEndian::write_u64_into(&input, &mut output);
            tmp.append(&mut output);
        }
    }

    let mut hasher = Sha512::new();
    hasher.input(tmp);
    let digest = hasher.result();

    // formulate the output
    Ok((0..commits.len())
        .map(|i| {
            // each field element t_i is generated as
            // t_i = hash_to_field (i | C | S | m[S])
            hash_to_field_repr([&i.to_be_bytes()[..], digest.as_ref()].concat())
        })
        .collect::<Vec<FrRepr>>())
}

// A wrapper of `hash_to_ti` that outputs `Fr`s instead of `FrRepr`s.
pub(crate) fn dim1_hash_fr(
    commit: &G1,
    set: &[usize],
    value_sub_vector: &[FrRepr],
    n: usize,
) -> Result<Vec<Fr>, String> {
    Ok(dim1_hash_repr(commit, set, value_sub_vector, n)?
        .iter()
        // the hash_to_ti_repr should already produce valid Fr elements
        // so it is safe to unwrap here
        .map(|s| Fr::from_repr(*s).unwrap())
        .collect())
}

/// Hash a array of bytes into non-zero scalars. 
pub(crate) fn dim1_hash_repr(
    commit: &G1,
    set: &[usize],
    value_sub_vector: &[FrRepr],
    n: usize,
) -> Result<Vec<FrRepr>, String> {
    // if the set leng does not mathc values, return an error
    if set.len() != value_sub_vector.len() {
        return Err(String::from("Mismatch Size"));
    }

    // handle the case where there is only one input
    // in this case, simply return FrRepr::one()
    if set.len() == 1 {
        return Ok(vec![FrRepr([1, 0, 0, 0])]);
    }

    // add values to set; returns an error if index is out of range
    for e in set {
        if *e >= n {
            return Err(String::from("Invalid Index"));
        }
    }

    // tmp = C | S | m[S]
    let mut tmp: Vec<u8> = vec![];
    // serialize commitment
    match commitment_serialize(commit, &mut tmp, true) {
        Ok(_p) => _p,
        Err(e) => return Err(e.to_string()),
    };
    // add the set to tmp
    for index in set {
        let t = index.to_be_bytes();
        tmp.append(&mut t.to_vec());
    }
    // add values to set; returns an error if index is out of range
    for e in value_sub_vector {
        let t = e.as_ref();

        let input = t.to_vec();//u64
        let mut output: Vec<u8> = vec!(0;32);
        LittleEndian::write_u64_into(&input, &mut output);
        tmp.append(&mut output);
    }

    let mut hasher = Sha512::new();
    hasher.input(tmp);
    let digest = hasher.result();

    // formulate the output
    Ok(set
        .iter()
        .map(|index| {
            hash_to_field_repr([&index.to_be_bytes()[..], digest.as_ref()].concat())
        })
        .collect())
}

/// Hash a array of bytes into non-zero scalars. 
pub(crate) fn dim1_hash_g1_repr(
    commit: &G1,
    set: &[usize],
    value_sub_vector: &[G1],
    n: usize,
) -> Result<Vec<FrRepr>, String> {
    // if the set leng does not mathc values, return an error
    if set.len() != value_sub_vector.len() {
        return Err(String::from("Mismatch Length"));
    }

    // handle the case where there is only one input
    // in this case, simply return FrRepr::one()
    if set.len() == 1 {
        return Ok(vec![FrRepr([1, 0, 0, 0])]);
    }

    // add values to set; returns an error if index is out of range
    for e in set {
        if *e >= n {
            return Err(String::from("Invalid Index"));
        }
    }

    // tmp = C | S | m[S]
    let mut tmp: Vec<u8> = vec![];
    // serialize commitment
    match commitment_serialize(commit, &mut tmp, true) {
        Ok(_p) => _p,
        Err(e) => return Err(e.to_string()),
    };
    // add the set to tmp
    for index in set {
        let t = index.to_be_bytes();
        tmp.append(&mut t.to_vec());
    }
    // add values to set; returns an error if index is out of range
    for e in value_sub_vector {
        commitment_serialize(e, &mut tmp, true).unwrap();
        // let t = commitment_serialize(e, &mut tmp, true);
        // tmp.append(&mut t.to_vec());
    }

    let mut hasher = Sha512::new();
    hasher.input(tmp);
    let digest = hasher.result();

    // formulate the output
    Ok(set
        .iter()
        .map(|index| {
            hash_to_field_repr([&index.to_be_bytes()[..], digest.as_ref()].concat())
        })
        .collect())
}

/// Convert a pop into a blob:
///
/// `| commit |` => bytes
///
/// Returns an error if ciphersuite id is invalid or serialization fails.
fn commitment_serialize<W: std::io::Write>(
    commit: &G1,
    writer: &mut W,
    compressed: bool,
) -> std::io::Result<()> {
    // compressed must be true
    if !compressed {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            String::from("Error Compress"),
        ));
    }

    let mut buf: Vec<u8> = vec![0];
    commit.into_affine().serialize(&mut buf, compressed)?;

    // format the output
    writer.write_all(&buf)?;
    Ok(())
}
