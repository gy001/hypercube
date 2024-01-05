
use crate::unipoly::UniPolynomial;
use crate::mle::{*, evals::*, coeffs_sparse::*};
use crate::kzg10::{Commitment, KZG10PCS, DegreeBoundArgument};
use crate::transcript::Transcript;
use crate::*;
use log::{debug, info, warn};

// Main Equation:
//  
// ⟦f⟧_n - v * 𝚽_n(X) = ∑_k (X^{2^k} * 𝚽_{n-k-1}(X^{2^{k+1}}) - u_k * 𝚽_{n-k}(X^{2^k}) * ⟦q_k⟧_k
//
//  where v = f(u_0, u_1, ..., u_{n-1}) 
//    and q_k = q_k(u_0, u_1, ..., u_k) s.t.
//
//  f(X_0, X_1, ..., X_{n-1}) - v = ∑_k (X_k - u_k) * q_k(X_0, X_1, ..., X_{k-1})    (1️⃣)
// 
//  We apply ⟦·⟧_n to the both sides of (1️⃣), and get the main equation.
//
//
//    f(X_0, X_1, ..., X_{n-1}) - f(u_0, u_1, ..., u_{n-1}) =
//        (X_{n-1} - u_{n-1}) * q_{n-1}(X_0, X_1, ..., X_{n-2}) 
//      + (X_{n-2} - u_{n-2}) * q_{n-2}(X_0, X_1, ..., X_{n-3}) 
//      ... 
//      + (X_1 - u_1)         *     q_1(X_0)
//      + (X_0 - u_0)         *     q_0()    
//

pub struct MlePCSystem {
    kzg10: KZG10PCS,
}

pub struct EvalArgumentSimple {
    q_commitment_vec: Vec<Commitment>,
    deg_proof_vec: Vec<DegreeBoundArgument>,
    eval_proof: kzg10::EvalArgument,
}

pub struct EvalArgumentOpt {
    q_commitment_vec: Vec<Commitment>,
    q_hat_commitment: Commitment,
    eval_proof: kzg10::EvalArgument,
}

impl MlePCSystem {

    pub fn setup_with_rng<R: Rng>(rng: &mut R) -> Self {
        let kzg10 = KZG10PCS::setup(64, rng);
        MlePCSystem { kzg10: kzg10 }
    }

    // @return: a univariate commitment for Commit(⟦f_mle⟧_n)
    pub fn commit(&self, f_mle: &MleEvals) -> Commitment {
        self.kzg10
            .commit_values(&f_mle.evals)
    }

    // The prover proves that f_mle(u0, u1, ..., u{n-1}) = v, that is mapped the goal of
    // the univariate polynomial, G_z(X), evaluates to ZERO at z, where  
    // 
    //    G_z(X) = ⟦f_mle⟧_n - v * 𝚽_n(z) - ∑_k(z^{2^k}𝚽_{n-k-1}(z^{2^{k+1}}) - uk * 𝚽_{n-k}(z^{2^k})) * ⟦q_k⟧_k
    //             ^^^^^^^^                                                                              ^^^^^^^
    //                     = G0(X)                                                                  = G1(X), ..., Gk(X)
    //
    // @param: f_cm, a (univariate) commitment for f_mle, Commit(⟦f_mle⟧_n)
    // @param: f_mle, a mle polynomial for f_mle
    // @param: us, a vector of scalars, u0, u1, ..., u{n-1}
    // @param: tr, transcript of Fiat-Shamir scheme
    // @return: (v, prf)
    //      v, the value of f_mle(u0, u1, ..., u{n-1})
    //      prf, evaluation argument
    pub fn prove_plain(
        &self,
        f_mle_cm: &Commitment,
        f_mle: &MleEvals,
        us: &[Scalar],
        tr: &mut Transcript,
    ) -> (Scalar, EvalArgumentSimple) 
    {
        info!("🔽 proving zeromorph isomorphism start ...");
        let n = f_mle.num_var;
        
        // let coeffs: Vec<(usize, Scalar)> = mle.compute_coeffs().into_iter().enumerate().filter(|(_i, c)| !c.is_zero()).collect();
        // let mle = MLEPolynomial::new(coeffs, n);
        let f_uni = U_from_evals(n, &f_mle);

        debug!("f_uni.coeffs={}", scalar_vector_to_string(&f_uni.coeffs));

        let v = f_mle.evaluate(us);

        let f_mle_cof = MleCoeffs::from_coeffs(&f_mle.to_coeffs(), n);

        // compute quotients {q_k}, where q_i = f(X0, X1, ..., X{k-1})
        let q_vec = f_mle_cof.decompose_by_division_alt(us);
        
        // initialize the commitments of quotients
        let mut q_cm_vec = Vec::new();
        let mut q_uni_vec = Vec::new();

        for i in 0..n {
            assert_eq!(i, q_vec[i].num_var());
            let qi_uni = U(i, &q_vec[i]);
            let qi_cm = self.kzg10.commit_values(&qi_uni.coefficients());
            q_cm_vec.push(qi_cm);
            q_uni_vec.push(qi_uni);
        }

        for i in 0..q_cm_vec.len() {
            tr.update_with_g1(&q_cm_vec[i].group_element);
        }
        
        let mut deg_prf_vec = Vec::new();
        // TODO: use a new kzg10
        let f_deg_prf = self.kzg10.prove_degree_bound(&f_uni, pow_2(n));

        for i in 0..n {
            let qi_deg_prf = self.kzg10.prove_degree_bound(&q_uni_vec[i], pow_2(i));
            deg_prf_vec.push(qi_deg_prf);
        }
        deg_prf_vec.push(f_deg_prf);

        for i in 0..deg_prf_vec.len() {
            // TODO: add support degree_bound proofs
            tr.update_with_g1(&deg_prf_vec[i].commitment.group_element);
        }

        let zeta = tr.generate_challenge();

        let ph_n = Phi(n, 1).evaluate(&zeta);
        
        // Compute G_z(X) = G0(X) - v * Phi_n(z) - ∑_k (c_k * Gk(X))
        //   s.t. G_z(z) == 0
        let mut g_uni = f_uni.sub_scalar(&(ph_n * v));  // G0(X)
        for k in 0..n {
            let c_k = zeta.exp(pow_2(k)) * Phi(n-k-1, pow_2(k+1)).evaluate(&zeta) - us[k] * Phi(n-k, pow_2(k)).evaluate(&zeta);
            let q_k_uni = q_uni_vec[k].mul_scalar(&c_k);
            g_uni = g_uni.sub(&q_k_uni);
        }

        let (eval_at_zeta, eval_prf) = self.kzg10.prove_eval(&g_uni, &zeta);

        assert_eq!(&eval_at_zeta, &Scalar::zero());


        {   // verify
            // let z_cm = self.kzg10.commit_poly(&g_uni);
            let v_cm = self.kzg10.commit_values(&UniPolynomial::from_coeffs(&[ph_n * v]).coefficients());
            let mut z_cm = f_mle_cm.clone();
            z_cm = z_cm.sub(&v_cm);
            for i in 0..n {
                let mut q_cm = q_cm_vec[i].clone();
                let c = zeta.exp(pow_2(i)) * Phi(n-i-1, pow_2(i+1)).evaluate(&zeta) - us[i] * Phi(n-i, pow_2(i)).evaluate(&zeta);
                z_cm = z_cm.sub(&q_cm.mul_scalar(&c));
            }
            
            // 
            assert_eq!(g_uni.evaluate(&zeta), Scalar::zero()); 
            info!("👀  z(zeta) == 0 ✅");


            let _b = self.kzg10.open_with_values(&v_cm, &[v]);
            for i in 0..n {
                let _b = self.kzg10.open_with_values(&q_cm_vec[i], &q_uni_vec[i].coeffs);
            }

            // let mut g_cm = self.kzg10.commit_values(&[Scalar::zero()]);
            // for i in 0..n {
            //     let c = zeta.exp(pow_2(i)) * phi(n-i-1, pow_2(i+1)).evaluate(&zeta) - xs[i] * phi(n-i, pow_2(i)).evaluate(&zeta);
            //     g_cm = g_cm.add(&q_cm_vec[i].mul_scalar(&c));
            // }

            let b = self.kzg10.open_with_values(&f_mle_cm, &f_uni.coeffs);
            println!("f_cm={}", scalar_vector_to_string(&f_mle_cm.internal_values));
            println!("f_uni.coeffs={}", scalar_vector_to_string(&f_uni.coeffs));
            println!("open(f(X), [f(X)])={}", b);

            let b = self.kzg10.open_with_values(&z_cm, &g_uni.coeffs);
            assert_eq!(b, true); 
            info!("👀  open(z(X), [z(X)]) == true ✅");
        }
        info!("🔼 proving zeromorph isomorphism end");

        (v, EvalArgumentSimple {
            q_commitment_vec: q_cm_vec,
            deg_proof_vec: deg_prf_vec,
            eval_proof: eval_prf,
        })
    }

    // Verify the evaluation argument of f_mle(u0, u1, ..., u{n-1}) = v
    // @param: f_cm, a (univariate) commitment for ⟦f_mle⟧_n
    // @param: us, a vector of scalars, (u0, u1, ..., u{n-1})
    // @param: v, a scalar, v = f_mle(u0, u1, ..., u{n-1})
    // @param: num_var, the number of variables of f_mle
    // @param: prf, evaluation argument
    // @param: tr, transcript of Fiat-Shamir scheme
    // @return: true if the proof is valid
    pub fn verify_plain(
        &self,
        f_cm: &Commitment,
        us: &[Scalar],
        v: &Scalar,
        num_var: usize,
        prf: &EvalArgumentSimple,
        tr: &mut Transcript,
    ) -> bool 
    {
        let n = num_var;
        assert_eq!(n, us.len());

        let q_cm_vec = &prf.q_commitment_vec;
        for q in q_cm_vec {
            tr.update_with_g1(&q.group_element);
        }

        let deg_prf_vec = &prf.deg_proof_vec;
        for p in deg_prf_vec {
            // TODO: add support degree_bound proofs
            tr.update_with_g1(&p.commitment.group_element);
        }

        let eval_prf = &prf.eval_proof;

        let zeta = tr.generate_challenge();

        let ph_n = Phi(n, 1).evaluate(&zeta);

        let v_cm = self.kzg10.commit_values(&UniPolynomial::from_coeffs(&[ph_n * v]).coefficients());
        let mut z_cm = f_cm.clone();
        z_cm = z_cm.sub(&v_cm);
        for i in 0..n {
            let mut q_cm = q_cm_vec[i].clone();
            let c = zeta.exp(pow_2(i)) * Phi(n-i-1, pow_2(i+1)).evaluate(&zeta) - us[i] * Phi(n-i, pow_2(i)).evaluate(&zeta);
            z_cm = z_cm.sub(&q_cm.mul_scalar(&c));
        }

        let checked = self.kzg10.verify_eval(&z_cm, &zeta, &Scalar::zero(), eval_prf);
        // assert!(checked); 
        info!("👀  z(zeta) == 0 ✅");
        checked
    }

    // @param: f_mle_cm, a (univariate) commitment for f_mle, Commit( [[f_mle]]_n )
    // @param: f_mle, a mle polynomial for f_mle
    // @param: us, a vector of scalars, u0, u1, ..., u{n-1}
    // @param: tr, transcript of Fiat-Shamir scheme
    // @return: (v, prf)
    //      v, the value of f_mle(u0, u1, ..., u{n-1})
    //      prf, evaluation argument
    pub fn prove_opt(
        &self, 
        f_mle_cm: &Commitment,
        f_mle: &MleEvals,
        us: &[Scalar],
        tr: &mut Transcript,
    ) -> (Scalar, EvalArgumentOpt) 
    {
        info!("🔽 proving zeromorph isomorphism start ...");
        let n = f_mle.num_var;

        let f_uni = U_from_evals(n, &f_mle);
        // check: f_cm == Commit(f_uni)

        let v = f_mle.evaluate(us);

        // Round 1: 

        // transform f_mle into coefficient form 
        let f_mle_cof = MleCoeffs::from_coeffs(&f_mle.to_coeffs(), n);

        // compute quotients {q_k}, where q_k = f(X0, X1, ..., X{k-1})
        let q_vec = f_mle_cof.decompose_by_division_alt(us);

        // univariatise {⟦q_k⟧_k} and commit to them
        let (q_cm_vec, q_uni_vec) = {
            let mut q_cm_vec = Vec::new();
            let mut q_uni_vec = Vec::new();

            for i in 0..n {
                assert_eq!(i, q_vec[i].num_var());
                let qi_uni = U(i, &q_vec[i]);
                let qi_cm = self.kzg10.commit_values(&qi_uni.coefficients());
                q_cm_vec.push(qi_cm);
                q_uni_vec.push(qi_uni);
            } 
            (q_cm_vec, q_uni_vec)
        };

        // update transcript with {Commit(⟦q_k⟧_k)}
        for q_cm in q_cm_vec.iter() {
            tr.update_with_g1(&q_cm.group_element);
        }

        // Round 2:

        // retrieve a challenge to aggregate {q_k}
        let beta = tr.generate_challenge();

        // compute the aggregated polynomial, q_hat(X) = ∑_k (beta^k * q_k(X))
        let q_hat_uni = {
            let mut coeffs = vec![Scalar::zero(); pow_2(n)];
            coeffs.push(Scalar::one());
            let mut q_hat = UniPolynomial::zero();
            let mut powers_of_beta = Scalar::one();
            for k in 0..n {
                // construct unipoly: X^{2^n - 2^k}
                let x_deg_2_to_n_uni = UniPolynomial::from_coeffs(&coeffs[pow_2(k)..]);
                q_hat = q_hat.add(&q_uni_vec[k].mul(&x_deg_2_to_n_uni).mul_scalar(&powers_of_beta));
                powers_of_beta *= beta;
            }
            q_hat
        };

        // commit to q_hat(X)
        let q_hat_cm = self.kzg10.commit_uni_poly(&q_hat_uni);

        tr.update_with_g1(&q_hat_cm.group_element);

        // Round 3: 

        // retrieve a challenge zeta (ζ) to check polynomial identies
        let zeta = tr.generate_challenge();

        // construct G(X), and prove it is a zero polynomial
        //
        //      G(X) = f(X) - v * 𝚽_n(X) 
        //          - ∑_k ( X^{2^k} * 𝚽_{n-k-1}(X^{2^{k+1}}) - u_k * 𝚽_{n-k}(X^{2^k}) ) * q_k(X)
        //
        // use linearization trick, partially instantiate G(X) at X = ζ (zeta)
        // 
        //      G_ζ(X) = f(X) - v * 𝚽_n(ζ) 
        //          - ∑_k ( ζ^{2^k} * 𝚽_{n-k-1}(ζ^{2^{k+1}}) - u_k * 𝚽_{n-k}(ζ^{2^k}) ) * q_k(X)
        //             = f(X) - v_𝚽 - ∑_k c_k * q_k(X)


        // compute v * 𝚽_n(ζ)
        let phi_n = Phi(n, 1).evaluate(&zeta);

        // compute G_ζ(X) = f(X) - v * 𝚽_n(ζ) - ∑_k c_k * q_k(X)
        let g_zeta_uni = {
            let mut g_uni = f_uni.sub_scalar(&(phi_n * v));
            for k in 0..n {
                let c_k = zeta.exp(pow_2(k)) * Phi(n-k-1, pow_2(k+1)).evaluate(&zeta) 
                            - us[k] * Phi(n-k, pow_2(k)).evaluate(&zeta);
                let q_k_uni = q_uni_vec[k].mul_scalar(&c_k);
                g_uni = g_uni.sub(&q_k_uni);
            }
            g_uni
        };

        println!("g_zeta(zeta)={}", g_zeta_uni.evaluate(&zeta));
        // println!("g_zeta_uni={}", scalar_vector_to_string(&g_zeta_uni.coeffs));


        // Construct H(X), and prove it is a zero polynomial
        //
        //      H(X) = q_hat(X) - ∑_k ( beta^{k} * X^{2^n - 2^k} * q_k(X) ) 
        // 
        //      H_ζ(X) = q_hat(X) - ∑_k ( beta^{k} * ζ^{2^n - 2^k} * q_k(X) )

        // compute H_ζ(X) = q_hat(X) - ∑_k e_k * q_k(X)
        let h_zeta_uni = {
            let mut h_uni = q_hat_uni.clone();
            for k in 0..n {
                let e_k = beta.exp(k) * zeta.exp(pow_2(n) - pow_2(k));
                println!("e_k={}", ScalarExt::to_string(&e_k));
                let q_k_uni = q_uni_vec[k].mul_scalar(&e_k);
                h_uni = h_uni.sub(&q_k_uni);
            }
            h_uni
        };

        println!("h_zeta(zeta)={}", h_zeta_uni.evaluate(&zeta));

        // Round 4: 

        // retrieve a challenge alpha (α) to aggregate H_ζ(X) and G_ζ(X)
        let alpha = tr.generate_challenge();

        let a_uni = g_zeta_uni.mul_scalar(&alpha).add(&h_zeta_uni);
        //
        let (e, e_pf, _d_pf) = self.kzg10.prove_eval_and_deg(&a_uni, &zeta, pow_2(n));
        
        assert_eq!(e, Scalar::zero());

        tr.update_with_g1(&e_pf.commitment.group_element);

        { 
            // actions by verifier 

            // compute Commit(v * 𝚽_n(z); 0)
            let v_cm = self.kzg10.commit_values(&UniPolynomial::from_coeffs(&[phi_n * v]).coefficients());

            assert!(self.kzg10.check_commitment(
                &v_cm, 
                &UniPolynomial::from_coeffs(&[phi_n * v])
            ));

            // compute Commit(G_ζ(X))
            let g_zeta_cm = {
                let mut g_cm = f_mle_cm.sub(&v_cm); 
                for k in 0..n {
                    let c_k = zeta.exp(pow_2(k)) * Phi(n-k-1, pow_2(k+1)).evaluate(&zeta) 
                                - us[k] * Phi(n-k, pow_2(k)).evaluate(&zeta);
                    let q_k_cm = q_cm_vec[k].mul_scalar(&c_k);
                    g_cm = g_cm.sub(&q_k_cm);
                }
                g_cm
            };

            println!("g_zeta_uni={}", scalar_vector_to_string(&g_zeta_uni.coeffs));

            assert!(self.kzg10.check_commitment(
                &g_zeta_cm, 
                &g_zeta_uni,
            ));

            // compute Commit(H_ζ(X))
            let h_zeta_cm = {
                let mut h_cm = q_hat_cm.clone();
                for k in 0..n {
                    let e_k = beta.exp(k) * zeta.exp(pow_2(n) - pow_2(k));
                    let q_k_cm = q_cm_vec[k].mul_scalar(&e_k);
                    h_cm = h_cm.sub(&q_k_cm);
                }
                h_cm
            };

            assert!(self.kzg10.check_commitment(
                &h_zeta_cm, 
                &h_zeta_uni,
            ));
            
            let a_cm = g_zeta_cm.mul_scalar(&alpha).add(&h_zeta_cm);

            let b = self.kzg10.verify_eval(&a_cm, &zeta, &Scalar::zero(), &e_pf);
            assert!(b);
        }

        (v, EvalArgumentOpt {
            q_commitment_vec: q_cm_vec,
            q_hat_commitment: q_hat_cm,
            eval_proof: e_pf,
        })
    }

    pub fn verify_opt(&self, 
        mle_cm: &Commitment, 
        us: &[Scalar],
        v: &Scalar,
        prf: &EvalArgumentOpt,
        tr: &mut Transcript,
    ) -> bool 
    {
        // Round 1:

        let n = us.len();
        // unpack the elements from the proof and update the transcript
        let q_cm_vec = &prf.q_commitment_vec;
        for q in q_cm_vec {
            tr.update_with_g1(&q.group_element);
        }

        // Round 2: 

        let beta = tr.generate_challenge();

        let q_hat_cm = &prf.q_hat_commitment;
        tr.update_with_g1(&q_hat_cm.group_element);

        let eval_prf = &prf.eval_proof;

        // Round 3: 

        // retrieve the challenge zeta (ζ)
        let zeta = tr.generate_challenge();

        let phi_n = Phi(n, 1).evaluate(&zeta);

        // compute Commit(v * 𝚽_n(z); 0)
        let v_cm = self.kzg10.commit_values(
            &UniPolynomial::from_coeffs(&[phi_n * v]).coefficients());

        // compute Commit(G_ζ(X))
        let g_zeta_cm = {
            let mut g_cm = mle_cm.sub(&v_cm); 
            for k in 0..n {
                let c_k = zeta.exp(pow_2(k)) * Phi(n-k-1, pow_2(k+1)).evaluate(&zeta) 
                            - us[k] * Phi(n-k, pow_2(k)).evaluate(&zeta);
                let q_k_cm = q_cm_vec[k].mul_scalar(&c_k);
                g_cm = g_cm.sub(&q_k_cm);
            }
            g_cm
        };

        // compute Commit(H_ζ(X))
        let h_zeta_cm = {
            let mut h_cm = q_hat_cm.clone();
            for k in 0..n {
                let e_k = beta.exp(k) * zeta.exp(pow_2(n) - pow_2(k));
                let q_k_cm = q_cm_vec[k].mul_scalar(&e_k);
                h_cm = h_cm.sub(&q_k_cm);
            }
            h_cm
        };
        
        // Round 4: 

        // retrieve a challenge alpha (α) to aggregate C(H_ζ(X)) and C(G_ζ(X))
        let alpha = tr.generate_challenge();

        let a_cm = g_zeta_cm.mul_scalar(&alpha).add(&h_zeta_cm);

        let b = self.kzg10.verify_eval(&a_cm, &zeta, &Scalar::zero(), eval_prf);
        b
    }
}  

#[allow(non_snake_case)]
pub fn U(num_var: usize, mle: &MleCoeffs) -> UniPolynomial {
    assert!(num_var >= mle.num_var());
    let coeffs = mle.coefficients();
    let evals = compute_evals_from_coeffs(num_var, &coeffs);
    UniPolynomial::from_coeffs(&evals)
}

#[allow(non_snake_case)]
pub fn U_from_evals(num_var: usize, mle: &MleEvals) -> UniPolynomial {
    assert!(num_var >= mle.num_var);
    UniPolynomial::from_coeffs(&mle.evals)
}

// Compute the periodic polynomial Phi(X^d)
// Phi_n(X) = 1 + X + X^2 + X^3 + ... + X^(2^n-1)
// Phi(X^d) = 1 + X^d + X^2d + X^4d + ... + X^(2^(n-1))d
#[allow(non_snake_case)]
pub fn Phi(num_var: usize, d: usize) -> UniPolynomial {
    let mut coeffs = vec![Scalar::zero(); pow_2(num_var) * d];    
    for i in 0..pow_2(num_var) {
        coeffs[i*d] = Scalar::one();

    }
    UniPolynomial::from_coeffs(&coeffs)
}

#[cfg(test)]
mod tests {
    use super::*;
    // use std::collections::HashMap;


    #[test]
    fn test_phi() {

        // f1(X) = 1 + X + X^2 + X^3 + X^4 + X^5 + X^6 + X^7
        let f1_uni = Phi(3, 1);
        println!("f_uni.coeffs={}", scalar_vector_to_string(&f1_uni.coeffs));

        // f2(X) = X - 1;
        let f2_uni = UniPolynomial::from_coeffs(&vec![-Scalar::from(1), Scalar::from(1)]);

        // f1(X)*f2(X) = X^8 - 1
        let f_uni = f2_uni.mul(&f1_uni);

        assert_eq!(f_uni, UniPolynomial::from_coeffs(&{
            let mut coeffs = vec![Scalar::zero(); 8];
            coeffs[0] = -Scalar::one();
            coeffs.push(Scalar::one());
            coeffs
        }));
        assert_eq!(f_uni.degree, 8);

        println!("f_uni.coeffs={}", scalar_vector_to_string(&f_uni.coeffs));
    }


    #[test]
    fn test_map_mle_to_uni() {

        // f(x2, x1, x0) = 4*x0 + 3x1 + x0*x1 + 2*x0x2 + 5*x0*x1*x2 

        let f1_mle = MleCoeffs::new(vec![
            (0b001, Scalar::from(4)),
            (0b010, Scalar::from(3)),
            (0b011, Scalar::from(1)),
            (0b101, Scalar::from(2)),
            (0b111, Scalar::from(5)),
        ], 3);

        // f[0,0,0] = 0
        // f[0,0,1] = 4
        // f[0,1,0] = 3
        // f[0,1,1] = 4+3+1 = 8
        // f[1,0,0] = 0
        // f[1,0,1] = 4+2 = 6
        // f[1,1,0] = 3
        // f[1,1,1] = 4+3+1+2+5 = 15

        let f1_mle_coeffs = f1_mle.coefficients();
        let f1_mle_evals = mle::compute_evals_from_coeffs(3, &f1_mle_coeffs);
        // println!("f1_mle.evals={}", scalar_vector_to_string(&f1_mle_evals));

        // f2(X0, X1) = 4*X0 + 3*X1 + 1*X0X1
        // f2.evals[00, 01, 10, 11] = [0, 4, 3, 8]
        let f2_mle = MleCoeffs::new({
            let mut coe: Vec<(usize, Scalar)> = f1_mle_coeffs.clone().into_iter().enumerate().collect(); 
            coe.truncate(4); 
            coe}, 2);

        println!("f2_mle.evals={}", scalar_vector_to_string(&mle::compute_evals_from_coeffs(3, &f2_mle.coefficients())));

        let f1_uni = U(3, &f1_mle);
        println!("f1_uni={}", scalar_vector_to_string(&f1_uni.coeffs));
        assert_eq!(&f1_uni.coeffs, &f1_mle_evals);

        let f2_uni = U(4, &f2_mle);
        assert_eq!(f2_uni.coeffs, (0..4).map(|_i| f2_mle.evaluations()).collect::<Vec<Vec<Scalar>>>().concat());
        println!("f2_uni={}", scalar_vector_to_string(&f2_uni.coeffs));

    }

    #[test]
    fn lemma_2_5_1() {

        // define a constant polynomial 
        // mle = 2 + 0*X0 + 0*X1 + 0*X0X1
        let mle = MleCoeffs::new(
            vec![
                (0b00, Scalar::from(2)),
            ]
            .into_iter()
            .collect(), 2);
        // compute f = [[ mle ]] = 2 + 2X + 2X^2 + 2X^3
        let f = U(2, &mle);
        // compute g = Phi_2(X) = 1 + X + X^2 + X^3
        let g = Phi(2, 1);
        // f == g * 2
        assert_eq!(f.coeffs, g.mul_scalar(&Scalar::from(2)).coeffs);
    }

    #[test]
    fn lemma_2_5_2() {

        let n = 4;
        let k = 2;

        let mut rng = ark_std::test_rng();

        // define a simple MLE
        let mle = MleCoeffs::new(vec![
                (0b00, Scalar::from(2)),
                (0b01, Scalar::from(3)),
                (0b10, Scalar::from(4)),
                (0b11, Scalar::from(5)),
            ]
            .into_iter()
            .collect(), 2);
        // compute f(X) = [[ mle ]]
        let uni_f = U(n, &mle);
        
        // compute f_k(X) = [[ mle ]]_k
        let uni_f_k = U(k, &mle);

        let ph = Phi(n-k, pow_2(k));
        // println!("^f={}", &uni_f);
        let uni_g = ph.mul(&uni_f_k);
        // println!("^g={}", &uni_g);

        // test \hat{f} ?= \hat{g}
        let zeta = Scalar::rand(&mut rng);
        assert_eq!(uni_f.evaluate(&zeta), uni_g.evaluate(&zeta));
    }


    #[test]
    fn lemma_2_5_3() {

        let n = 4;
        let k = 2;

        let mut rng = ark_std::test_rng();

        // define a simple MLE
        let mut mle = MleCoeffs::new(vec![
                (0b00, Scalar::from(2)),
                (0b01, Scalar::from(3)),
                (0b10, Scalar::from(4)),
                (0b11, Scalar::from(5)),
            ]
            .into_iter()
            .collect(),2);
        // 
        let uni_f = U(n, &mle);

        mle.expand_vars(1);

        let uni_xf = U(n, &mle.mul(&MleCoeffs::new(vec![
                (0b100, Scalar::from(1))
            ]
            .into_iter()
            .collect(),3)));

        // g(X) = X^{2^k} + 1
        let g = UniPolynomial { degree: pow_2(k), coeffs: {
            let mut zeros = vec![Scalar::zero(); pow_2(k)];
            zeros[0] = Scalar::one();
            zeros.push(Scalar::one());
            zeros
        }};
        let uni_g = uni_xf.mul(&g);
        println!("^g={}", &uni_g);

        let h = UniPolynomial { degree: pow_2(k), coeffs: {
            let mut zeros = vec![Scalar::zero(); pow_2(k)];
            zeros.push(Scalar::one());
            zeros
        }};

        let uni_h = uni_f.mul(&h);
        println!("^h={}", &uni_h);

        // test \hat{f} ?= \hat{g}
        let zeta = Scalar::rand(&mut rng);
        assert_eq!(uni_g.evaluate(&zeta), uni_h.evaluate(&zeta));
    }


    #[test]
    fn corollary_2_5_3_1() {

        let n = 4;
        let k = 2;

        let mut rng = ark_std::test_rng();

        // f1(X0, X1, X2) = X2
        let f1_mle = &MleCoeffs::new(vec![
                (0b100, Scalar::from(1))
            ]
            .into_iter()
            .collect(), 3);

        let f1_uni = U(n, &f1_mle);

        // f2(X) = X^{2^k} + 1
        let f2_uni = UniPolynomial { degree: pow_2(k), coeffs: {
            let mut zeros = vec![Scalar::zero(); pow_2(k)];
            zeros[0] = Scalar::one();
            zeros.push(Scalar::one());
            zeros
        }};

        // f3(X) = X - 1

        let f3_uni = UniPolynomial { degree: 1, 
            coeffs: vec![-Scalar::one(), Scalar::one()] };

        let f_uni = f1_uni.mul(&f2_uni).mul(&f3_uni);

        println!("^f={}", &f_uni);

        // g1(X) = X^{2^k}
        let g1_uni = UniPolynomial { degree: pow_2(k), coeffs: {
            let mut zeros = vec![Scalar::zero(); pow_2(k)];
            zeros.push(Scalar::one());
            zeros
        }};

        // g2(X) = X^{2^n} - 1
        let g2_uni = UniPolynomial { degree: pow_2(n), coeffs: {
            let mut zeros = vec![Scalar::zero(); pow_2(n)];
            zeros[0] = - Scalar::one();
            zeros.push(Scalar::one());
            zeros
        }};

        let g_uni = g1_uni.mul(&g2_uni);

        println!("^g_uni={}", &g_uni);

        // test \hat{f} ?= \hat{g}
        let zeta = Scalar::rand(&mut rng);
        assert_eq!(f_uni.evaluate(&zeta), g_uni.evaluate(&zeta));
    }


    #[test]
    fn corollary_2_5_3_2() {

        let n = 4;
        let k = 2;

        let mut rng = ark_std::test_rng();

        // define a simple MLE
        let mut f_mle = MleCoeffs::new(vec![
                (0b00, Scalar::from(2)),
                (0b01, Scalar::from(3)),
                (0b10, Scalar::from(4)),
                (0b11, Scalar::from(5)),
            ].into_iter().collect(), 
            k);

        // 
        let f1_uni_deg_k = U(k, &f_mle);

        f_mle.expand_vars(1);

        let xf_uni = U(n, &f_mle.mul(&&MleCoeffs::new(vec![
                (0b100, Scalar::from(1))
            ], k+1)));
            

        println!("^xf_uni={}", &xf_uni);

        // g1(X) = X^{2^k}
        let g1_uni = UniPolynomial { degree: pow_2(k), coeffs: {
            let mut zeros = vec![Scalar::zero(); pow_2(k)];
            zeros.push(Scalar::one());
            zeros
        }};

        // g2(X) = Phi_{n-k-1}(X^{2^{k+1}})
        let g2_uni = Phi(n-k-1, pow_2(k+1));

        let g_uni = g1_uni.mul(&g2_uni).mul(&f1_uni_deg_k);

        // test \hat{f} ?= \hat{g}
        let zeta = Scalar::rand(&mut rng);
        assert_eq!(g_uni.evaluate(&zeta), xf_uni.evaluate(&zeta));
    }
/*
    #[test]
    fn test_evaluate() {
        let coeffs = vec![
            (0b101, Scalar::from(2)),
            (0b010, Scalar::from(3)),
            (0b001, Scalar::from(4)),
        ].into_iter().collect();
        let num_var = 3;
        let poly = MLEPolynomial{
            num_var: num_var,
            coeffs: coeffs, 
        };

        // Test evaluation at different points
        let point1 = vec![Scalar::from(1), Scalar::from(0), Scalar::from(1)];
        assert_eq!(poly.evaluate(&point1), Scalar::from(6));

        let point2 = vec![Scalar::from(0), Scalar::from(1), Scalar::from(1)];
        assert_eq!(poly.evaluate(&point2), Scalar::from(7));

        let point3 = vec![Scalar::from(1), Scalar::from(1), Scalar::from(1)];
        assert_eq!(poly.evaluate(&point3), Scalar::from(9));

        let point4 = vec![Scalar::from(2), Scalar::from(2), Scalar::from(2)];
        assert_eq!(poly.evaluate(&point4), Scalar::from(22));
    }

    // #[test]
    // fn test_compute_quotients_2() {
    //     // Create a MLE instance with coefficients
    //     let coeffs = vec![
    //         (0b001, Scalar::from(4)),
    //         (0b010, Scalar::from(3)),
    //         (0b011, Scalar::from(1)),
    //         (0b101, Scalar::from(2)),
    //         (0b111, Scalar::from(5)),
    //     ];
    //     let num_var = 3;
    //     let poly = MLEPolynomial::new(coeffs, num_var);

    //     // Test compute_quotients at different points
    //     let point1 = vec![Scalar::from(1), Scalar::from(2), Scalar::from(1)];
    //     let quotients1 = poly.compute_quotients(&point1);
    //     assert_eq!(quotients1.len(), 3);
    //     println!("quotients1[0]={}", quotients1[0]);
    //     println!("quotients1[1]={}", quotients1[1]);
    //     println!("quotients1[2]={}", quotients1[2]);

    //     let quotients2 = poly.compute_quotients_alt(&point1);
    //     assert_eq!(quotients2.len(), 3);
    //     println!("quotients2[0]={}", quotients2[0]);
    //     println!("quotients2[1]={}", quotients2[1]);
    //     println!("quotients2[2]={}", quotients2[2]);

    //     // assert_eq!(quotients1[0].coeffs, vec![(0b001, Scalar::from(2))].into_iter().collect());
    //     // assert_eq!(quotients1[1].coeffs, vec![(0b000, Scalar::from(3))].into_iter().collect());
    //     // assert_eq!(quotients1[2].coeffs, vec![(0b000, Scalar::from(6))].into_iter().collect());

    //     // let point2 = vec![Scalar::from(2), Scalar::from(2), Scalar::from(2)];
    //     // let quotients2 = poly.compute_quotients(&point2);
    //     // assert_eq!(quotients2.len(), 3);
    //     // assert_eq!(quotients2[0].coeffs, vec![(0b001, Scalar::from(2))].into_iter().collect());
    //     // assert_eq!(quotients2[1].coeffs, vec![(0b000, Scalar::from(3))].into_iter().collect());
    //     // assert_eq!(quotients2[2].coeffs, vec![(0b000, Scalar::from(8))].into_iter().collect());
    // }


    #[test]
    fn test_mle_div_mul() {
        let rng = &mut ark_std::test_rng();
        let num_var = 5;
        let poly1 = MLEPolynomial {
            num_var: num_var,
            coeffs: (0..pow_2(num_var))
                .map(|i| (i, Scalar::rand(rng)))
                .collect(),
        };
        let div2: Divisor = (3, Scalar::rand(rng));
        let (quo, rem) = poly1.div(&div2);
        let poly2 = quo
            .mul(&MLEPolynomial::from_divisor(num_var, &div2))
            .add(&rem);
        assert_eq!(poly1, poly2);
    }
     */

     #[test]
     fn test_prove_verify_plain() {
        init_logger();
 
        let mut rng = ark_std::test_rng();
        let vs = Scalar::from_usize_vector(&[1,2,3,4]);
        let f_mle = MleEvals::new(&vs);
        println!("num_var={}", f_mle.num_var);

        let pcs = MlePCSystem::setup_with_rng(&mut rng);
        let f_cm = pcs.commit(&f_mle);

        let us = Scalar::from_usize_vector(&[3,2]);
        let tr = Transcript::new();
        let (v, prf) = pcs.prove_plain(&f_cm, &f_mle, &us, &mut tr.clone());
 
        let verified = pcs.verify_plain(&f_cm, &us, &v, f_mle.num_var, &prf, &mut tr.clone());
        assert!(verified);
     }

     #[test]
     fn test_prove_verify_opt() {
        init_logger();
 
        let mut rng = ark_std::test_rng();
        let vs = Scalar::from_usize_vector(&[1,2,3,4]);
        let f_mle = MleEvals::new(&vs);
        println!("num_var={}", f_mle.num_var);

        let pcs = MlePCSystem::setup_with_rng(&mut rng);
        let f_cm = pcs.commit(&f_mle);

        let us = Scalar::from_usize_vector(&[3,2]);
        let tr = Transcript::new();
        let (v, prf) = pcs.prove_opt(&f_cm, &f_mle, &us, &mut tr.clone());
 
        let verified = pcs.verify_opt(&f_cm, &us, &v, &prf, &mut tr.clone());
        assert!(verified);
     }
}

