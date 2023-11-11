use ark_poly::domain;

use crate::*;
use crate::mle::{MLEPolynomial, EqPolynomial};
use crate::unipoly::UniPolynomial;
use crate::kzg10::{KZG10PCS, Commitment};
use log::debug;

pub struct TensorProductSystem {
    kzg10: KZG10PCS,
}


pub struct TensorProductArg {
    poly_cm_vec: Vec<Commitment>,
    evals_pos: Vec<Scalar>,
    evals_neg: Vec<Scalar>,
    evals_sq: Vec<Scalar>,
}

impl TensorProductSystem {


    pub fn setup() -> Self {
        let kzg10 = KZG10PCS::setup(64);
        TensorProductSystem {
            kzg10: kzg10,
        }
    }
    // TODO: add transcript
    pub fn prove(&self, mle_polynomial: &MLEPolynomial, xs: &[Scalar]) -> (Scalar, TensorProductArg) {
        assert_eq!(mle_polynomial.num_var, xs.len());

        let e = mle_polynomial.evaluate(xs);

        let mut mle = mle_polynomial.clone();
        let mut len = mle.num_var;
        let mut domain_size = mle.len();

        let mut coeffs: Vec<Scalar> = mle.compute_coeffs();
        let mut unipoly_cm_vec: Vec<Commitment> = Vec::new();
        let mut unipoly_vec: Vec<UniPolynomial> = Vec::new();
        for i in (0..xs.len()).rev() {
            
            let unipoly = { 
                // TODO: unipoly reverse
                let mut coeffs = coeffs.clone();
                coeffs.reverse();
                UniPolynomial::from_coeffs(&coeffs, domain_size)
            };

            let f_cm = self.kzg10.commit(&unipoly);
            let coeffs_e: Vec<Scalar> = coeffs.iter().step_by(2).cloned().collect();
            let coeffs_o: Vec<Scalar> = coeffs.iter().skip(1).step_by(2).cloned().collect();
            debug!("rd={}, coeffs_e={}", i, scalar_vector_to_string(&coeffs_e));
            debug!("rd={}, coeffs_o={}", i, scalar_vector_to_string(&coeffs_o));

            coeffs = coeffs_e.iter().zip(coeffs_o.iter())
                .map(| (&e, &o) | e + xs[i] * o).collect();
            debug!("rd={}, coeffs_next={}", i, scalar_vector_to_string(&coeffs));
            domain_size /= 2;
            unipoly_cm_vec.push(f_cm);
            unipoly_vec.push(unipoly);
        }

        assert_eq!(e, coeffs[0]);
        assert_eq!(coeffs.len(), 1);

        // TODO: challenge from the transcript
        let beta = Scalar::from(2);

        let mut f_eval_pos_vec: Vec<Scalar> = Vec::new();
        let mut f_eval_neg_vec: Vec<Scalar> = Vec::new();
        let mut f_eval_sq_vec: Vec<Scalar> = Vec::new();

        // TODO: compute in O(n)
        for i in 0..xs.len() {
            let f_cm = &unipoly_cm_vec[i];
            let f_poly = &unipoly_vec[i];
            let f_eval_pos = f_poly.evaluate(&beta);
            f_eval_pos_vec.push(f_eval_pos);
            let f_eval_neg = f_poly.evaluate(&(-beta));
            f_eval_neg_vec.push(f_eval_neg);
            debug!("rd={}, f_eval_pos={}", i, ScalarExt::to_string(&f_eval_pos));
            debug!("rd={}, f_eval_neg={}", i, ScalarExt::to_string(&f_eval_neg));

            if i != 0 {
                let f_eval_sq = f_poly.evaluate(&(beta * beta));
                f_eval_sq_vec.push(f_eval_sq);
                debug!("rd={}, f_eval_sq={}", i, ScalarExt::to_string(&f_eval_sq));
            }
        }
        f_eval_sq_vec.push(e);

        (e, TensorProductArg{
            poly_cm_vec: unipoly_cm_vec,
            evals_pos: f_eval_pos_vec,
            evals_neg: f_eval_neg_vec,
            evals_sq: f_eval_sq_vec,
        })
    }

    pub fn verify(&self, commitment: &Commitment, arg: &TensorProductArg, xs: &[Scalar], e: &Scalar) -> bool {

        let num_rounds = xs.len();
        let mut rho_vec = xs.to_vec();

        // TODO: challenge from the transcript
        let beta = Scalar::from(2);

        for i in 0..num_rounds {
            let rho = rho_vec.pop().unwrap();
            let rhs = ((arg.evals_pos[i] + arg.evals_neg[i]) / Scalar::from(2)) + rho * (arg.evals_pos[i] - arg.evals_neg[i]) / (Scalar::from(2) * beta);
            debug!("rd={}, rhs={}", i, ScalarExt::to_string(&rhs));
            debug!("rd={}, sq={}", i, ScalarExt::to_string(&arg.evals_sq[i]));
            assert_eq!(arg.evals_sq[i], rhs);
        }
        // let coeffs = &commitment.values;
        // let result = UniPolynomial::evaluate_from_coeffs(&coeffs, x);

        // result == eval_argument.eval_at_x
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

        let kzg10 = KZG10PCS::setup(128);

        let f_coeffs = f_mle.compute_coeffs();
        debug!("f_coeffs={}", scalar_vector_to_string(&f_coeffs));

        let f_uni = {
            let mut f_coeffs = f_coeffs.clone();
            f_coeffs.reverse();
            UniPolynomial::from_coeffs(&f_coeffs, f_mle.len())
        };

        let f_cm = kzg10.commit(&f_uni);

        let tensor_product_sys = TensorProductSystem::setup();

        let (e, arg) = tensor_product_sys.prove(&f_mle, &rs);
        debug!("e={}", ScalarExt::to_string(&e));

        let b = tensor_product_sys.verify(&f_cm, &arg, &rs, &e);
        assert!(b);
    }   
}