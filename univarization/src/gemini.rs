
use crate::*;
use crate::fftunipoly::FftUniPolynomial;
use crate::mle::{MLEPolynomial, EqPolynomial};
use crate::unipoly::UniPolynomial;
use crate::kzg10::{KZG10PCS, Commitment};
use crate::transcript::Transcript;
use log::debug;

pub struct MlePCSystem {
    kzg10: KZG10PCS,
}

pub struct EvalArgument {
    poly_cm_vec: Vec<Commitment>,
    evals_pos: Vec<Scalar>,
    evals_neg: Vec<Scalar>,
    evals_sq: Vec<Scalar>,
    evals_pos_proof: Vec<kzg10::EvalArgument>,
    evals_neg_proof: Vec<kzg10::EvalArgument>,
    evals_sq_proof: Vec<kzg10::EvalArgument>,
}

impl MlePCSystem {

    pub fn setup() -> Self {
        let kzg10 = KZG10PCS::setup(64);
        MlePCSystem {
            kzg10: kzg10,
        }
    }

    pub fn commit(&self, mle: &MLEPolynomial) -> Commitment {
        let coeffs = mle.compute_coeffs();
        let f_poly = FftUniPolynomial::from_coeffs_fft(&coeffs);
        // debug!("f_coeffs={}", scalar_vector_to_string(&f_coeffs));

        let f_cm = self.kzg10.commit_poly(&f_poly);
        f_cm
    }

    pub fn prove(&self, mle_cm: &Commitment, 
        mle_poly: &MLEPolynomial, xs: &[Scalar],
        tr: &mut Transcript,
    ) -> (Scalar, EvalArgument) {
        assert_eq!(mle_poly.num_var, xs.len());
        let n = xs.len();
        let mut domain_size = pow_2(mle_poly.num_var);
        let e = mle_poly.evaluate(xs);

        tr.update_with_scalar_vec(&mle_cm.values);

        // let mut mle = mle_poly.clone();
        // let mut len = mle.num_var;
        // let mut domain_size = mle.len();

        let mut coeffs: Vec<Scalar> = mle_poly.compute_coeffs();
        println!("coeffs={}", scalar_vector_to_string(&coeffs));

        let mut unipoly_cm_vec: Vec<Commitment> = Vec::new();
        let mut unipoly_vec: Vec<FftUniPolynomial> = Vec::new();
        for i in (0..xs.len()).rev() {
            
            let f_poly = FftUniPolynomial::from_coeffs_fft(&coeffs); 

            let f_cm = self.kzg10.commit_poly(&f_poly);

            let coeffs_e: Vec<Scalar> = coeffs.iter().step_by(2).cloned().collect();
            let coeffs_o: Vec<Scalar> = coeffs.iter().skip(1).step_by(2).cloned().collect();
            debug!("rd={}, coeffs_e={}", i, scalar_vector_to_string(&coeffs_e));
            debug!("rd={}, coeffs_o={}", i, scalar_vector_to_string(&coeffs_o));

            coeffs = coeffs_e.iter().zip(coeffs_o.iter())
                .map(| (&e, &o) | e + xs[i] * o).collect();
            debug!("rd={}, coeffs_next={}", i, scalar_vector_to_string(&coeffs));
            domain_size /= 2;
            tr.update_with_scalar_vec(&f_cm.values);
            unipoly_cm_vec.push(f_cm);
            unipoly_vec.push(f_poly);
        }

        assert_eq!(e, coeffs[0]);
        assert_eq!(coeffs.len(), 1);

        let beta = tr.generate_challenge();
        // let beta = Scalar::from(2);

        let mut f_eval_pos_vec: Vec<Scalar> = Vec::new();
        let mut f_eval_pos_proof: Vec<kzg10::EvalArgument> = Vec::new();
        let mut f_eval_neg_vec: Vec<Scalar> = Vec::new();
        let mut f_eval_neg_proof: Vec<kzg10::EvalArgument> = Vec::new();
        let mut f_eval_sq_vec: Vec<Scalar> = Vec::new();
        let mut f_eval_sq_proof: Vec<kzg10::EvalArgument> = Vec::new();

        // TODO: compute in O(n)
        for i in 0..xs.len() {
            let f_cm = &unipoly_cm_vec[i];
            let f_poly = &unipoly_vec[i];
            let (f_eval_pos, eval_proof) = self.kzg10.prove(&f_poly, &beta);
            f_eval_pos_vec.push(f_eval_pos);
            f_eval_pos_proof.push(eval_proof);

            let (f_eval_neg, eval_proof) = self.kzg10.prove(&f_poly, &(-beta));
            f_eval_neg_vec.push(f_eval_neg);
            f_eval_neg_proof.push(eval_proof);

            debug!("rd={}, f_eval_pos={}", i, ScalarExt::to_string(&f_eval_pos));
            debug!("rd={}, f_eval_neg={}", i, ScalarExt::to_string(&f_eval_neg));

            if i != 0 {
                let f_eval_sq = f_poly.evaluate(&(beta * beta));
                let (f_eval_sq, eval_proof) = self.kzg10.prove(&f_poly, &(beta * beta));
                f_eval_sq_vec.push(f_eval_sq);
                f_eval_sq_proof.push(eval_proof);
                debug!("rd={}, f_eval_sq={}", i, ScalarExt::to_string(&f_eval_sq));
            }
        }
        f_eval_sq_vec.push(e);

        (e, EvalArgument {
            poly_cm_vec: unipoly_cm_vec,
            evals_pos: f_eval_pos_vec,
            evals_pos_proof: f_eval_pos_proof,
            evals_neg: f_eval_neg_vec,
            evals_neg_proof: f_eval_neg_proof,
            evals_sq: f_eval_sq_vec,
            evals_sq_proof: f_eval_sq_proof,
        })
    }

    pub fn verify(&self, mle_cm: &Commitment, 
        xs: &[Scalar], e: &Scalar,
        prf: &EvalArgument, 
        tr: &mut Transcript,
    ) -> bool {

        let num_rounds = xs.len();
        let mut rho_vec = xs.to_vec();
        let cm_vec = &prf.poly_cm_vec;
        tr.update_with_scalar_vec(&mle_cm.values);

        for i in (0..num_rounds) {
            let f_cm = &cm_vec[i];
            tr.update_with_scalar_vec(&f_cm.values);
        }
        // TODO: challenge from the transcript
        let beta = tr.generate_challenge();

        for i in (0..num_rounds) {
            let rho = rho_vec.pop().unwrap();
            let rhs = ((prf.evals_pos[i] + prf.evals_neg[i]) / Scalar::from(2)) + rho * (prf.evals_pos[i] - prf.evals_neg[i]) / (Scalar::from(2) * beta);
            debug!("rd={}, rhs={}", i, ScalarExt::to_string(&rhs));
            debug!("rd={}, sq={}", i, ScalarExt::to_string(&prf.evals_sq[i]));
            assert_eq!(prf.evals_sq[i], rhs);
        }

        true
    }
}

mod tests {
    use super::*;

    #[test]
    fn test_prove_verify() {
        init_logger();

        // f(X2, X1, X0) = 1 + X0 + 2*X1 + 0*X0X1 + 4*X2
        let f_vs = Scalar::from_usize_vector(&[1,2,3,4,5,6,7,8]);
        let f_mle = MLEPolynomial::new(&f_vs);
        let rs = Scalar::from_usize_vector(&[0,1,1]);
        let mut tr = Transcript::new();

        let mle_pcs = MlePCSystem::setup();

        let f_cm = mle_pcs.commit(&f_mle);

        let (e, prf) = mle_pcs.prove(&f_cm, &f_mle, &rs, &mut tr.clone());
        debug!("e={}", ScalarExt::to_string(&e));

        let b = mle_pcs.verify(&f_cm, &rs, &e, &prf, &mut tr.clone());
        assert!(b);
    }   
}