use ark_poly::domain;

use crate::*;

use crate::unipoly::{UniPolynomial};
use crate::fftunipoly::FftUniPolynomial;
use crate::kzg10::{KZG10PCS, Commitment};
use crate::transcript::Transcript;

// univariate sumcheck system
// public input: a_cm, b_cm, u
// witnesses: a_vec, b_vec
// argument: <a_vec, b_vec> ?= u
//   a(X) * b(X) ?= q(X) * z_H(X) + X * g(X) + u/N

pub struct UniSumcheckSystem {
    kzg10: KZG10PCS,
}

pub struct UniSumcheckArg {
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
    q_deg_proof: kzg10::DegreeBoundArgument,
    g_deg_proof: kzg10::DegreeBoundArgument,
}

impl UniSumcheckSystem {

    pub fn setup(kzg10: &KZG10PCS) -> Self {
        UniSumcheckSystem {
            kzg10: kzg10.clone(),
        }
    }

    pub fn prove(&self,
        a_cm: &Commitment,
        b_cm: &Commitment,
        a_poly: &FftUniPolynomial, 
        b_poly: &FftUniPolynomial, 
        c: &Scalar, 
        trans: &mut Transcript,
    ) -> UniSumcheckArg {
        assert_eq!(a_poly.coeffs.len(), b_poly.coeffs.len());
        let n = a_poly.coeffs.len();
        let domain_size = n.next_power_of_two();

        let ab_prod_poly = a_poly.multiply(&b_poly);
        let zH_poly = FftUniPolynomial::vanishing_polynomial(domain_size);

        let (q_poly, r_poly) = ab_prod_poly.div(&zH_poly);

        let mut coeffs = r_poly.coeffs.clone();
        coeffs.remove(0);
        let g_poly = FftUniPolynomial::from_coeffs_fft(&coeffs);

        let q_cm = self.kzg10.commit_poly(&q_poly);
        let g_cm = self.kzg10.commit_poly(&g_poly);

        trans.update_with_scalar_vec(&a_cm.values);
        trans.update_with_scalar_vec(&b_cm.values);

        trans.update_with_scalar_vec(&q_cm.values);
        trans.update_with_scalar_vec(&g_cm.values);

        let zeta = trans.generate_challenge();
        // let zeta = Scalar::one();

        let (a_zeta, a_eval_prf) = self.kzg10.prove(&a_poly, &zeta);
        let (b_zeta, b_eval_prf) = self.kzg10.prove(&b_poly, &zeta);
        let (q_zeta, q_eval_prf) = self.kzg10.prove(&q_poly, &zeta);
        let (g_zeta, g_eval_prf) = self.kzg10.prove(&g_poly, &zeta);
        let q_degree = a_poly.degree + b_poly.degree - domain_size;
        let q_deg_prf = self.kzg10.prove_degree_bound(&q_cm, &q_poly, q_degree);
        let g_degree = q_degree - 1;
        let g_deg_prf = self.kzg10.prove_degree_bound(&g_cm, &g_poly, g_degree);

        let zH_zeta = zH_poly.evaluate(&zeta);

        assert_eq!(a_zeta * b_zeta, 
            q_zeta * zH_zeta + zeta * g_zeta + (*c / Scalar::from_usize(domain_size)));

        UniSumcheckArg {
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
            q_deg_proof: q_deg_prf,
            g_deg_proof: g_deg_prf,
        }
    }
    
    pub fn verify(&self, 
        a_cm: &Commitment, 
        b_cm: &Commitment,
        c: &Scalar,
        prf: &UniSumcheckArg,
        trans: &mut Transcript,
    ) -> bool 
    {
        let domain_size = prf.domain_size;

        let q_cm = prf.q_commitment.clone();
        let g_cm = prf.g_commitment.clone();

        let zH_poly = FftUniPolynomial::vanishing_polynomial(domain_size);

        trans.update_with_scalar_vec(&a_cm.values);
        trans.update_with_scalar_vec(&b_cm.values);

        trans.update_with_scalar_vec(&q_cm.values);
        trans.update_with_scalar_vec(&g_cm.values);

        let zeta = trans.generate_challenge();

        assert!(self.kzg10.verify(&a_cm, &prf.a_eval_proof, &zeta, &prf.a_eval));
        assert!(self.kzg10.verify(&b_cm, &prf.b_eval_proof, &zeta, &prf.b_eval));
        assert!(self.kzg10.verify(&q_cm, &prf.q_eval_proof, &zeta, &prf.q_eval));
        assert!(self.kzg10.verify(&g_cm, &prf.g_eval_proof, &zeta, &prf.g_eval));
        assert!(self.kzg10.verify_degree_bound(&q_cm, domain_size, &prf.q_deg_proof));
        assert!(self.kzg10.verify_degree_bound(&g_cm, domain_size - 1, &prf.g_deg_proof));

        let zH_eval = zH_poly.evaluate(&zeta);

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

        let a = Scalar::from_i64_vector(&vec![1, 2, 3, 4]);
        let b = Scalar::from_i64_vector(&vec![2, 3, 1, 2]);

        // sum = 19
        let c: Scalar = (0..a.len()).map(|i| a[i] * b[i]).sum();

        let kzg10 = KZG10PCS::setup(100);
        let sumcheck_sys = UniSumcheckSystem::setup(&kzg10);
        let a_poly = FftUniPolynomial::from_evals_fft(&a, 4);
        let b_poly = FftUniPolynomial::from_evals_fft(&b, 4);

        let a_cm = kzg10.commit_poly(&a_poly);
        let b_cm = kzg10.commit_poly(&b_poly);
        let mut tr = Transcript::new();

        let prf = sumcheck_sys.prove(&a_cm, &b_cm, &a_poly, &b_poly, &c, &mut tr.clone());
        let b = sumcheck_sys.verify(&a_cm, &b_cm, &c, &prf, &mut tr.clone());
    }   
}