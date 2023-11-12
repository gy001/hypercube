use crate::*;

use crate::mle::{MLEPolynomial, EqPolynomial};
use crate::transcript::Transcript;
use crate::unipoly::UniPolynomial;
use crate::kzg10::{KZG10PCS, Commitment};
use crate::fftunipoly::FftUniPolynomial;

pub struct MlePCSystem {
    kzg10: KZG10PCS,
}

pub struct EvalArgument {
    c_commitment: kzg10::Commitment,
    q_commitment: kzg10::Commitment,
    c_evals: Vec<Scalar>,
    c_eval_proofs: Vec<kzg10::EvalArgument>,
    q_eval: Scalar,
}

impl MlePCSystem {

    pub fn setup() -> Self {
        let kzg10 = KZG10PCS::setup(64);
        MlePCSystem {
            kzg10: kzg10,
        }
    }

    pub fn commit(&self, mle_poly: &MLEPolynomial) -> Commitment {
        self.kzg10.commit_evals(&mle_poly.evals, pow_2(mle_poly.num_var))
    }

    pub fn prove(&self, mle_cm: &Commitment, mle: &MLEPolynomial, xs: &[Scalar], tr: &mut Transcript)
        -> (Scalar, EvalArgument) {
        assert_eq!(mle.num_var, xs.len());
        let n = mle.num_var;
        let domain_size = pow_2(mle.num_var);
        let e = mle.evaluate(xs);
        
        tr.update_with_scalar_vec(&mle_cm.values);

        let c_vec = EqPolynomial::new(&xs.to_vec()).evals_over_hypercube();
        let c_poly = FftUniPolynomial::from_evals_fft(&c_vec, domain_size);
        println!("c_vec={}", scalar_vector_to_string(&c_vec));

        let c_cm = self.kzg10.commit_poly(&c_poly);

        tr.update_with_scalar_vec(&c_cm.values);
        
        let alpha = tr.generate_challenge();
        // let alpha = Scalar::one();

        let zH_poly = FftUniPolynomial::vanishing_polynomial(domain_size);
        let mut s_polys = Vec::new();
        for k in 0..n {
            let (s_poly, r_poly) = zH_poly.div(&FftUniPolynomial::vanishing_polynomial(pow_2(k)));
            assert!(r_poly.is_zero());
            s_polys.push(s_poly);
        }
        
        // println!("s0_poly.coeffs={}", scalar_vector_to_string(&s0_poly.coeffs));
        // println!("r_poly.coeffs={}", scalar_vector_to_string(&r_poly.coeffs));
        // println!("s0_poly.evals={}", scalar_vector_to_string(&s0_poly.evaluations()));

        let f0_poly = c_poly.add_constant(&c_vec[0], true);
        let p0_poly = s_polys[0].multiply(&f0_poly);
        let mut h_poly = p0_poly.clone();
        for k in 1..=n {
            let domain_k = pow_2(k);
            let omega_k = FftUniPolynomial::get_root_of_unity(k);
            let f_poly = c_poly.mul_constant(&xs[k-1])
                .add(&c_poly.shift(&omega_k).mul_constant(&(Scalar::one() - xs[k-1])), true);
            let p_poly = s_polys[k-1].multiply(&f_poly).mul_constant(&alpha.exp(k));
            h_poly = h_poly.add(&p_poly, false);
        }

        println!("h_poly.evals={}", scalar_vector_to_string(&h_poly.evaluations_over_domain(domain_size)));

        let (q_poly, r_poly) = h_poly.div(&zH_poly);
        assert!(r_poly.is_zero());

        let q_cm = self.kzg10.commit_poly(&q_poly);
        tr.update_with_scalar_vec(&q_cm.values);
        let zeta = tr.generate_challenge();

        // let zeta = Scalar::from(2);

        let s_polys_eval = s_polys.iter().map(|s_poly| s_poly.evaluate(&zeta)).collect::<Vec<Scalar>>();
        let mut c_evals: Vec<Scalar> = Vec::new();
        let mut c_eval_prfs = Vec::new();
        for k in 0..=n {
            let omega_k = FftUniPolynomial::get_root_of_unity(k);
            // c_poly.evaluate(&(omega_k * zeta))
            let (eval, eval_prf) = self.kzg10.prove(&c_poly, &(omega_k * zeta));
            c_evals.push(eval);
            c_eval_prfs.push(eval_prf);
        };

        // verify the evaluations
        let mut h = s_polys[0].evaluate(&zeta) * (c_evals[0] - c_vec[0]);
        for k in 1..=n {
            let f = c_evals[0] * xs[k-1] - c_evals[k] * (Scalar::one() - xs[k-1]);
            let p = s_polys_eval[k-1] * f * alpha.exp(k);
            // println!("p={}", ScalarExt::to_string(&p));
            h += p;
        }
        // println!("h={}", ScalarExt::to_string(&h));
        assert_eq!(h, q_poly.evaluate(&zeta) * zH_poly.evaluate(&zeta));

        (e, EvalArgument{
            c_commitment: c_cm,
            q_commitment: q_cm,
            c_evals: c_evals,
            c_eval_proofs: c_eval_prfs,
            q_eval: q_poly.evaluate(&zeta),
        })
    }

    pub fn verify(&self, mle_cm: &Commitment, xs: &[Scalar], e: &Scalar, 
        prf: &EvalArgument, tr: &mut Transcript) -> bool {
            let n = xs.len();
            let domain_size = pow_2(n);
            let c_eq = EqPolynomial::new(&xs.to_vec());

            tr.update_with_scalar_vec(&mle_cm.values);
    
            let c_cm = &prf.c_commitment;
    
            tr.update_with_scalar_vec(&c_cm.values);
            
            let alpha = tr.generate_challenge();
    
            let zH_poly = FftUniPolynomial::vanishing_polynomial(domain_size);
            let mut s_polys = Vec::new();
            for k in 0..n {
                let (s_poly, r_poly) = zH_poly.div(&FftUniPolynomial::vanishing_polynomial(pow_2(k)));
                assert!(r_poly.is_zero());
                s_polys.push(s_poly);
            }
            
            let q_cm = &prf.q_commitment;
            tr.update_with_scalar_vec(&q_cm.values);
            let zeta = tr.generate_challenge();
    
            // let zeta = Scalar::from(2);
    
            let s_polys_eval = s_polys.iter().map(|s_poly| s_poly.evaluate(&zeta)).collect::<Vec<Scalar>>();
            let c_evals = &prf.c_evals;
            let c_eval_prfs = &prf.c_eval_proofs;
            for k in 0..=n {
                let omega_k = FftUniPolynomial::get_root_of_unity(k);
                // c_poly.evaluate(&(omega_k * zeta))
                let b = self.kzg10.verify(&c_cm, &c_eval_prfs[k], &(omega_k * zeta));
                assert!(b);
            };
    
            // verify the evaluations
            let mut h = s_polys[0].evaluate(&zeta) * (c_evals[0] - c_eq.eval(0));
            for k in 1..=n {
                let f = c_evals[0] * xs[k-1] - c_evals[k] * (Scalar::one() - xs[k-1]);
                let p = s_polys_eval[k-1] * f * alpha.exp(k);
                // println!("p={}", ScalarExt::to_string(&p));
                h += p;
            }
            // println!("h={}", ScalarExt::to_string(&h));
            assert_eq!(h, prf.q_eval * zH_poly.evaluate(&zeta));
    
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

        let pcs = MlePCSystem::setup();
        let f_cm = pcs.commit(&f_mle);

        let tr = &mut Transcript::new();
        let (e, prf) = pcs.prove(&f_cm, &f_mle, &rs, &mut tr.clone());
        let b = pcs.verify(&f_cm, &rs, &e, &prf, &mut tr.clone());
        assert!(b);
    }   
}