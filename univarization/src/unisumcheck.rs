use crate::*;

use crate::unipoly::{UniPolynomial};
use crate::kzg10::{KZG10PCS, Commitment};
use crate::transcript::Transcript;

// argument: <a_vec, b_vec> ?= u
//   a(X) * b(X) ?= q(X) * z_H(X) + X * g(X) + u/N

pub struct UniSumcheckSystem {
    kzg10: KZG10PCS,
}

pub struct UniSumcheckArg {
    q_commitment: Commitment,
    g_commitment: Commitment,
    a_eval: Scalar,
    b_eval: Scalar,
    q_eval: Scalar,
    g_eval: Scalar,
}

impl UniSumcheckSystem {

    pub fn setup() -> Self {
        let kzg10 = KZG10PCS::setup(64);
        UniSumcheckSystem {
            kzg10: kzg10,
        }
    }

    // TODO: mock prover
    pub fn prove(&self, 
        uni_poly_a: &UniPolynomial, 
        uni_poly_b: &UniPolynomial, 
        v: &Scalar,
        trans: &mut Transcript,
    ) -> UniSumcheckArg
    {
        let poly_q = uni_poly_a.clone();
        let poly_g = uni_poly_b.clone();

        UniSumcheckArg{
            q_commitment: self.kzg10.commit(&poly_q),
            g_commitment: self.kzg10.commit(&poly_g),
            a_eval: Scalar::one(),
            b_eval: Scalar::one(),
            q_eval: Scalar::one(),
            g_eval: Scalar::one(),
        }
    }
    
    // TODO: mock verifier
    pub fn verify(&self, 
        uni_a_commitment: Commitment, 
        uni_b_commitment: Commitment,
        v: &Scalar,
        prf: UniSumcheckArg,
        trans: &mut Transcript,

    ) -> bool 
    {
        true
    }
}