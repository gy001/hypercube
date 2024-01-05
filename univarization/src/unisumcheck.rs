#![allow(non_snake_case)]

use crate::*;

use crate::unipoly::UniPolynomial;
use crate::kzg10::{KZG10PCS, Commitment};
use crate::transcript::Transcript;

// univariate sumcheck system
// public input: a_cm, b_cm, u
// witnesses: a_vec, b_vec
// argument: <a_vec, b_vec> ?= u
//   a(X) * b(X) ?= q(X) * z_H(X) + X * g(X) + u/N

#[derive(Clone)]
pub struct UniSumcheckSystem {
    kzg10: KZG10PCS,
}

#[derive(Clone)]
pub struct UniSumcheckArgPlain {
    domain_size: usize,
    q_commitment: Commitment,
    g_commitment: Commitment,
    a_eval: Scalar,
    b_eval: Scalar,
    q_eval: Scalar,
    g_eval: Scalar,
    a_eval_proof: kzg10::EvalArgument,
    b_eval_proof: kzg10::EvalArgument,
    q_eval_proof: kzg10::EvalArgument,
    g_eval_proof: kzg10::EvalArgument,
    // q_deg_proof: kzg10::DegreeBoundArgument,
    g_deg_proof: kzg10::DegreeBoundArgument,
}

impl UniSumcheckSystem {

    pub fn setup(kzg10: &KZG10PCS) -> Self {
        UniSumcheckSystem {
            kzg10: kzg10.clone(),
        }
    }

    pub fn prove_plain(&self,
        a_cm: &Commitment,
        b_cm: &Commitment,
        a_uni: &UniPolynomial, 
        b_uni: &UniPolynomial, 
        c: &Scalar, 
        tr: &mut Transcript,
    ) -> UniSumcheckArgPlain {
        assert_eq!(a_uni.coeffs.len(), b_uni.coeffs.len());
        let n = a_uni.coeffs.len();
        let domain_size = n.next_power_of_two();

        tr.update_with_g1(&a_cm.group_element);
        tr.update_with_g1(&b_cm.group_element);
        tr.update_with_scalar(&c);


        let ab_prod_uni = a_uni.mul(&b_uni);
        let zH_uni = UniPolynomial::vanishing_polynomial_fft(domain_size);

        let (q_uni, r_uni) = ab_prod_uni.div(&zH_uni);

        let mut coeffs = r_uni.coeffs.clone();
        coeffs.remove(0);
        let g_uni = UniPolynomial::from_coeffs(&coeffs);

        let q_cm = self.kzg10.commit_uni_poly(&q_uni);
        let g_cm = self.kzg10.commit_uni_poly(&g_uni);

        tr.update_with_g1(&q_cm.group_element);
        tr.update_with_g1(&g_cm.group_element);

        let zeta = tr.generate_challenge();
        // let zeta = Scalar::one();

        // TODO: adopt batched evaluation argument
        // TODO: adopt linearization technique
        let (a_zeta, a_eval_prf) = self.kzg10.prove_eval(&a_uni, &zeta);
        let (b_zeta, b_eval_prf) = self.kzg10.prove_eval(&b_uni, &zeta);
        let (q_zeta, q_eval_prf) = self.kzg10.prove_eval(&q_uni, &zeta);
        let (g_zeta, g_eval_prf) = self.kzg10.prove_eval(&g_uni, &zeta);
        // let q_degree = a_uni.degree + b_uni.degree - domain_size;
        // let q_deg_prf = self.kzg10.prove_degree_bound(&q_uni, q_degree+1);
        let g_degree_bound = domain_size - 1;
        let g_deg_prf = self.kzg10.prove_degree_bound(&g_uni, g_degree_bound);

        let zH_zeta = zH_uni.evaluate(&zeta);

        assert_eq!(a_zeta * b_zeta, 
            q_zeta * zH_zeta + zeta * g_zeta + (*c / Scalar::from_usize(domain_size)));

        UniSumcheckArgPlain {
            domain_size: domain_size,
            q_commitment: q_cm,
            g_commitment: g_cm,
            a_eval: a_zeta,
            b_eval: b_zeta,
            q_eval: q_zeta,
            g_eval: g_zeta,
            a_eval_proof: a_eval_prf,
            b_eval_proof: b_eval_prf,
            q_eval_proof: q_eval_prf,
            g_eval_proof: g_eval_prf,
            g_deg_proof: g_deg_prf,
        }
    }
    
    pub fn verify_plain(&self, 
        a_cm: &Commitment, 
        b_cm: &Commitment,
        c: &Scalar,
        prf: &UniSumcheckArgPlain,
        tr: &mut Transcript,
    ) -> bool
    {
        let domain_size = prf.domain_size;

        tr.update_with_g1(&a_cm.group_element);
        tr.update_with_g1(&b_cm.group_element);
        tr.update_with_scalar(&c);

        let q_cm = prf.q_commitment.clone();
        let g_cm = prf.g_commitment.clone();

        let zH_uni = UniPolynomial::vanishing_polynomial_fft(domain_size);

        tr.update_with_g1(&q_cm.group_element);
        tr.update_with_g1(&g_cm.group_element);

        let zeta = tr.generate_challenge();

        assert!(self.kzg10.verify_eval(&a_cm, &zeta, &prf.a_eval, &prf.a_eval_proof));
        assert!(self.kzg10.verify_eval(&b_cm, &zeta, &prf.b_eval, &prf.b_eval_proof));
        assert!(self.kzg10.verify_eval(&q_cm, &zeta, &prf.q_eval, &prf.q_eval_proof));
        assert!(self.kzg10.verify_eval(&g_cm, &zeta, &prf.g_eval, &prf.g_eval_proof));
        assert!(self.kzg10.verify_degree_bound(&g_cm, domain_size - 1, &prf.g_deg_proof));

        let zH_eval = zH_uni.evaluate(&zeta);

        assert_eq!(prf.a_eval * prf.b_eval, 
            prf.q_eval * zH_eval + zeta * prf.g_eval + (*c / Scalar::from_usize(domain_size)));
        
        true
    }
}

mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn test_prove_verify() {
        init_logger();

        let rng = &mut ark_std::test_rng();
        let a = Scalar::from_i64_vector(&vec![1, 2, 3, 4]);
        let b = Scalar::from_i64_vector(&vec![2, 3, 1, 2]);

        // sum = 19
        let c: Scalar = (0..a.len()).map(|i| a[i] * b[i]).sum();

        let kzg10 = KZG10PCS::setup(100, rng);
        let sumcheck_sys = UniSumcheckSystem::setup(&kzg10);
        let a_uni = UniPolynomial::from_evals(&a);
        let b_uni = UniPolynomial::from_evals(&b);

        let a_cm = kzg10.commit_uni_poly(&a_uni);
        let b_cm = kzg10.commit_uni_poly(&b_uni);
        let tr = Transcript::new();

        let prf = sumcheck_sys.prove_plain(&a_cm, &b_cm, &a_uni, &b_uni, &c, &mut tr.clone());
        let b = sumcheck_sys.verify_plain(&a_cm, &b_cm, &c, &prf, &mut tr.clone());
        assert!(b);
    }   
}