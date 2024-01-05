#![allow(non_snake_case)]

use crate::*;
use crate::unipoly::UniPolynomial;
use crate::mle::evals::*;
use crate::kzg10::{KZG10PCS, Commitment};
use crate::transcript::Transcript;
use log::debug;
use std::rc::Rc;
use std::result;

use crate::groupsim::pairing;

/// The protocol:
/// 
///    P                                   V
/// 
/// compute h0(X), h1(X), ..., h{n-1}(X)
/// 
///   h0(X) = f(X)
/// k=1..n-1
///   hi(X) = (h{i-1}(X) + h{i-1}(-X)) / 2 
///     + u_{i-1} * (h{i-1}(X) - h{i-1}(-X)) / 2X
/// 
///   P   -- [h0], [h1], ..., [h{n-1}] -->  V
///   P   <--- β  ------------------------  V
/// 
///   P   - h0(β), h1(β), ..., h{n-1}(β) -> V
///   P   - h0(-β), h1(-β), ..., h{n-1}(-β) -> V
///   P   <--- γ  ------------------------  V
///   
///  compute g(X)
/// 
///    g(X) = h0(X)(X-β^2) - B0(X)
///         + γ * (h1(X) - B1(X))
///         + γ^2 * (h2(X) - B2(X)) 
///         ... 
///         + γ^{n-1} * (h{n-1}(X) - B{n-1}(X))
/// 
///  s.t. 
///    g(X) = q(X) * (X-β)(X+β)(X-β^2)
/// 
///   P   ---- Q=[q] ------------------->  V
///   P   <---  ζ  ----------------------  V
///   
///  compute r(X)
///   
///    r(X) = g_ζ(X) - (ζ - β^2)^2 * q(X)
/// 
///  compute w(X)
/// 
///    w(X) = r(X) / (X - ζ)
/// 
///   P   ---- W=[w] --------------------->  V
///
///  Verification:
///    1. compute h1(β^2), h2(β^2), ..., h{n-1}(β^2) in O(n)
///    2. compute B0(ζ), B1(ζ), ..., B{n-1}(ζ) in O(n)
///    3. compute R
/// 
///       R = ((ζ - β^2) * H0 - B0(ζ) * [1])
///            + γ * (H1 - B1(ζ) * [1])
///            + γ^2 * (H2 - B2(ζ) * [1])
///            ...
///            + γ^{n-1} * (H{n-1} - B{n-1}(ζ) * [1])
///            - (ζ - β^2)^2 * Q
///    4. check  e(R + ζ*W, [1]) ?= e(W, [τ])

pub struct MlePCSystem {
    kzg10: Rc<KZG10PCS>,
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

pub struct EvalArgumentOpt{
    h_cm_vec: Vec<Commitment>,
    h_eval_pos_vec: Vec<Scalar>,
    h_eval_neg_vec: Vec<Scalar>,
    q_commitment: Commitment,
    w_commitment: Commitment,
}

impl MlePCSystem {

    pub fn setup(kzg10: &Rc<KZG10PCS>) -> Self {
        MlePCSystem {
            kzg10: kzg10.clone(),
        }
    }

    pub fn commit(&self, f_mle: &MleEvals) -> Commitment {
        let coeffs = f_mle.to_coeffs();
        let f_uni = UniPolynomial::from_coeffs(&coeffs);
        let f_cm = self.kzg10.commit_uni_poly(&f_uni);
        f_cm
    }

    /// Prove the evaluation argument naively (for testing purpose)
    /// 
    /// # Arguments
    /// 
    /// - `f_cm`, a (univariate) commitment for f_mle, Commit(⟦f_mle⟧_n)
    /// - `f_mle`, a mle polynomial for f_mle
    /// - `us`, a vector of scalars, `us = [u0, u1, ..., u{n-1}]`
    /// - `tr`, a transcript for interaction
    ///    
    /// # Returns
    /// 
    /// - v, the value of `f_mle(u0, u1, ..., u{n-1})`
    /// - prf, evaluation argument
    /// 
    pub fn prove_opt(&self, 
        f_cm: &Commitment, 
        f_mle: &MleEvals, 
        us: &[Scalar],
        tr: &mut Transcript,
    ) -> (Scalar, EvalArgumentOpt) {
        assert_eq!(f_mle.num_var, us.len());

        let n = us.len();
        let v = f_mle.evaluate(us);
        tr.update_with_g1(&f_cm.group_element);
        tr.update_with_scalar_vec(us);

        // Round 1.

        let mut coeffs: Vec<Scalar> = f_mle.to_coeffs();
        // println!("coeffs={}", scalar_vector_to_string(&coeffs));

        let mut h_uni_cm_vec: Vec<Commitment> = Vec::new();
        let mut h_uni_vec: Vec<UniPolynomial> = Vec::new();
        for i in 0..us.len() {
            
            let h_uni = UniPolynomial::from_coeffs(&coeffs); 

            let h_cm = self.kzg10.commit_uni_poly(&h_uni);

            let coeffs_e: Vec<Scalar> = coeffs.iter().step_by(2).cloned().collect();
            let coeffs_o: Vec<Scalar> = coeffs.iter().skip(1).step_by(2).cloned().collect();
            // debug!("rd={}, coeffs_e={}", i, scalar_vector_to_string(&coeffs_e));
            // debug!("rd={}, coeffs_o={}", i, scalar_vector_to_string(&coeffs_o));
            // debug!("i={}, us[i]={}", i, ScalarExt::to_string(&us[i]));

            coeffs = coeffs_e.iter().zip(coeffs_o.iter())
                .map(| (&e, &o) | e + us[i] * o).collect();
            // println!("coeffs={}", scalar_vector_to_string(&coeffs));
            tr.update_with_g1(&h_cm.group_element);
            h_uni_cm_vec.push(h_cm);
            h_uni_vec.push(h_uni);
        }

        assert_eq!(v, coeffs[0]);
        assert_eq!(coeffs.len(), 1);

        // Round 2.

        let beta = tr.generate_challenge();
        debug!("beta={}", ScalarExt::to_string(&beta));
        let beta_sq = beta * beta;

        let mut h_eval_pos_vec: Vec<Scalar> = Vec::new();
        let mut h_eval_neg_vec: Vec<Scalar> = Vec::new();
        let mut h_eval_sq_vec: Vec<Scalar> = Vec::new();

        // TODO: compute in O(n)
        for i in 0..us.len() {
            let hi_uni = &h_uni_vec[i];
            let h_eval_pos = hi_uni.evaluate(&beta);
            h_eval_pos_vec.push(h_eval_pos);

            let h_eval_neg = hi_uni.evaluate(&(-beta));
            h_eval_neg_vec.push(h_eval_neg);
            if i != 0 {
                let h_eval_sq = hi_uni.evaluate(&beta_sq);
                h_eval_sq_vec.push(h_eval_sq);
                // debug!("rd={}, h_eval_sq={}", i, ScalarExt::to_string(&h_eval_sq));
            }
        }
        h_eval_sq_vec.push(v);

        tr.update_with_scalar_vec(&h_eval_pos_vec);
        tr.update_with_scalar_vec(&h_eval_neg_vec);

        // Round 3.

        let gamma = tr.generate_challenge();
        debug!("gamma={}", ScalarExt::to_string(&gamma));

        let b_uni_vec = {
            let mut b_vec = Vec::new();
            let b_uni = UniPolynomial::from_coeffs(
                &UniPolynomial::compute_coeffs_from_evals_slow(
                    &[h_eval_pos_vec[0], h_eval_neg_vec[0]], &[beta, -beta]));
            b_vec.push(b_uni);
            for i in 1..us.len() {
                let b_uni = UniPolynomial::from_coeffs(
                    &UniPolynomial::compute_coeffs_from_evals_slow(
                        &[h_eval_pos_vec[i], h_eval_neg_vec[i], h_eval_sq_vec[i-1]],
                        &[beta, -beta, beta_sq]));         
                b_vec.push(b_uni);   
            };
            b_vec
        };

        {   // double check -- B_i(X)
            for i in 0..us.len() {
                assert_eq!(b_uni_vec[i].evaluate(&beta), h_eval_pos_vec[i]);
                assert_eq!(b_uni_vec[i].evaluate(&(-beta)), h_eval_neg_vec[i]);
                if i != 0 {
                    assert_eq!(b_uni_vec[i].evaluate(&beta_sq), h_eval_sq_vec[i-1]);
                }
            }
        }

        let g_uni = {
            let mut g = UniPolynomial::zero();
            let gi = &h_uni_vec[0]
                .sub(&b_uni_vec[0])
                .mul(&UniPolynomial::from_coeffs(&[-beta_sq, Scalar::one()]));
            {   // double check -- g(X)
                assert_eq!(gi.evaluate(&beta), Scalar::zero());
                assert_eq!(gi.evaluate(&(-beta)), Scalar::zero());
                assert_eq!(gi.evaluate(&beta_sq), Scalar::zero());
            }

            g.add_inplace(&gi);

            for i in 1..us.len() {
                let gi = &h_uni_vec[i]
                    .sub(&b_uni_vec[i])
                    .mul_scalar(&gamma.exp(i));
                {   // double check -- g(X)
                    assert_eq!(gi.evaluate(&beta), Scalar::zero(), "failed at i={}", i);
                    assert_eq!(gi.evaluate(&(-beta)), Scalar::zero(), "failed at i={}", i);
                    assert_eq!(gi.evaluate(&beta_sq), Scalar::zero(), "failed at i={}", i);
                }
                g.add_inplace(&gi);
            }
            g
        };

        {   // double check -- g(X)
            assert_eq!(g_uni.evaluate(&beta), Scalar::zero());
            assert_eq!(g_uni.evaluate(&(-beta)), Scalar::zero());
            assert_eq!(g_uni.evaluate(&beta_sq), Scalar::zero());
        }

        let d_uni = {
            let mut d = UniPolynomial::from_coeffs(&[-beta_sq, Scalar::one()]);
            d = d.mul(&UniPolynomial::from_coeffs(&[-beta, Scalar::one()]));
            d = d.mul(&UniPolynomial::from_coeffs(&[beta, Scalar::one()]));
            d
        };

        {   // double check -- d(X)
            assert_eq!(d_uni.evaluate(&beta), Scalar::zero());
            assert_eq!(d_uni.evaluate(&(-beta)), Scalar::zero());
            assert_eq!(d_uni.evaluate(&beta_sq), Scalar::zero());
        }

        let (q_uni, _r_uni) = g_uni.div(&d_uni);

        {   // double check -- q(X)
            assert_eq!(_r_uni, UniPolynomial::zero());
        }

        let q_cm = self.kzg10.commit_uni_poly(&q_uni);

        tr.update_with_g1(&q_cm.group_element);

        // Round 4.

        let zeta = tr.generate_challenge();

        let r_uni = {
            let mut r = UniPolynomial::zero();

            let ri = &h_uni_vec[0]
                .sub_scalar(&b_uni_vec[0].evaluate(&zeta))
                .mul_scalar(&(zeta - beta_sq));
            r.add_inplace(&ri);

            for i in 1..n {
                let ri = &h_uni_vec[i]
                    .sub_scalar(&b_uni_vec[i].evaluate(&zeta))
                    .mul_scalar(&gamma.exp(i));
                r.add_inplace(&ri);
            }
            r.sub_inplace(&q_uni.mul_scalar(
                &((zeta - beta_sq) * (zeta - beta) * (zeta + beta))));
            r
        };

        {   // double check
            assert_eq!(r_uni.evaluate(&zeta), Scalar::zero());
        }

        let (w_uni, _r_uni) = r_uni.div_by_linear_divisor(&zeta);
        {
            assert_eq!(_r_uni, Scalar::zero());
        }
        let w_cm = self.kzg10.commit_uni_poly(&w_uni);

        {
            assert_eq!(r_uni.evaluate(&beta), w_uni.evaluate(&beta) * (beta - zeta));
        }

        tr.update_with_g1(&w_cm.group_element);

        { //double check

            let b_zeta_vec = {
                let domain = &[beta, -beta, beta*beta];
                let mut b = Vec::new();
    
                let bi =  UniPolynomial::evaluate_from_evals(&[h_eval_pos_vec[0], h_eval_neg_vec[0]], &zeta, &[beta, -beta]);
                b.push(bi);
                for i in 1..n {
                    let values = &[h_eval_pos_vec[i], h_eval_neg_vec[i], h_eval_sq_vec[i-1]];
                    let bi = UniPolynomial::evaluate_from_evals(values, &zeta, domain);
                    b.push(bi);
                }
                b
            };
    
            for i in 0..n {
                assert_eq!(b_zeta_vec[i], b_uni_vec[i].evaluate(&zeta));
            }

            // compute R
    
            let C_r = {
    
                let mut r = h_uni_cm_vec[0].sub(&Commitment::commit(&b_zeta_vec[0])).mul_scalar(&(zeta - beta_sq));
                for i in 1..n {
                    let ri = h_uni_cm_vec[i].sub(&Commitment::commit(&b_zeta_vec[i])).mul_scalar(&gamma.exp(i));
                    r = r.add(&ri);
                }
                r = r.sub(&q_cm.mul_scalar(&((zeta - beta_sq) * (zeta - beta) * (zeta + beta))));
                r
            };

            assert_eq!(C_r.group_element, self.kzg10.commit_uni_poly(&r_uni).group_element);
        }

        (v, EvalArgumentOpt {
            h_cm_vec: h_uni_cm_vec,
            h_eval_pos_vec: h_eval_pos_vec,
            h_eval_neg_vec: h_eval_neg_vec,
            q_commitment: q_cm,
            w_commitment: w_cm,
        })
    }

    /// Verify the evaluation argument efficiently
    ///  
    /// # Arguments 
    /// 
    /// - `f_cm`, a (univariate) commitment for f_mle, Commit(⟦f_mle⟧_n)
    /// - `us`, a vector of scalars, u0, u1, ..., u{n-1}
    /// - `v`, the value of `f_mle(u0, u1, ..., u{n-1})`
    /// - `prf`, evaluation argument
    /// - `tr`, transcript of Fiat-Shamir scheme
    /// 
    /// # Return
    /// 
    /// - true if the evaluation argument is valid
    /// 
    pub fn verify_opt(&self, 
        // vk: &VerifierKey,
        f_cm: &Commitment, 
        us: &[Scalar], 
        v: &Scalar,
        prf: &EvalArgumentOpt,
        tr: &mut Transcript
    ) -> bool {
        let n = us.len();

        let domain_size = pow_2(n);

        tr.update_with_g1(&f_cm.group_element);
        tr.update_with_scalar_vec(us);

        let EvalArgumentOpt{
            h_cm_vec,
            h_eval_pos_vec: h_beta_vec,
            h_eval_neg_vec: h_mbeta_vec,
            q_commitment: q_cm,
            w_commitment: w_cm,
        } = prf;

        // Round 1.

        for i in 0..n {
            let h_cm = &h_cm_vec[i];
            tr.update_with_g1(&h_cm.group_element);
        }

        // Round 2.

        let beta = tr.generate_challenge();
        debug!("V> beta={}", ScalarExt::to_string(&beta));

        let beta_sq = beta * beta;
        tr.update_with_scalar_vec(&h_beta_vec);
        tr.update_with_scalar_vec(&h_mbeta_vec);

        // Round 3.

        let gamma = tr.generate_challenge();
        debug!("V> gamma={}", ScalarExt::to_string(&gamma));

        tr.update_with_g1(&q_cm.group_element);

        // Round 4.

        let zeta = tr.generate_challenge();

        debug!("V> zeta={}", ScalarExt::to_string(&zeta));

        tr.update_with_g1(&w_cm.group_element);

        // Verify 

        // 1. compute h1(β^2), h2(β^2), ..., h{n-1}(β^2) in O(n)

        let h_beta_sq_vec = {
            let mut h = Vec::new();
            for i in 1..=n {
                let hi = ((h_beta_vec[i-1] + h_mbeta_vec[i-1])/Scalar::from(2))
                + us[i-1] * (h_beta_vec[i-1] - h_mbeta_vec[i-1])/(Scalar::from(2) * beta);
                h.push(hi);
            }
            h
        };

        // 2. compute B0(ζ), B1(ζ), ..., B{n-1}(ζ) in O(n)

        let b_zeta_vec = {
            let domain = &[beta, -beta, beta*beta];
            let mut b = Vec::new();

            let bi =  UniPolynomial::evaluate_from_evals(&[h_beta_vec[0], h_mbeta_vec[0]], &zeta, &[beta, -beta]);
            b.push(bi);
            for i in 1..n {
                let values = &[h_beta_vec[i], h_mbeta_vec[i], h_beta_sq_vec[i-1]];
                let bi = UniPolynomial::evaluate_from_evals(values, &zeta, domain);
                b.push(bi);
            }
            b
        };

        // 3. check evaluation result

        let result_0 = h_beta_sq_vec[n-1] == *v;

        // 4. compute R

        let C_r = {

            let mut r = h_cm_vec[0].sub(&Commitment::commit(&b_zeta_vec[0])).mul_scalar(&(zeta - beta_sq));
            for i in 1..n {
                let ri = h_cm_vec[i].sub(&Commitment::commit(&b_zeta_vec[i])).mul_scalar(&gamma.exp(i));
                r = r.add(&ri);
            }
            r = r.sub(&q_cm.mul_scalar(&((zeta - beta_sq) * (zeta - beta) * (zeta + beta))));
            r
        };

        let h = &self.kzg10.srs.h;
        let h_tau = &self.kzg10.srs.h_tau;
        let C1 = C_r.add(&w_cm.mul_scalar(&zeta));
        let lhs = pairing(&C1.group_element, h);
        let rhs = pairing(&w_cm.group_element, h_tau);

        let result_1 = lhs == rhs;
        assert_eq!(result_1, true);
        result_0 && result_1
    }

    /// Prove the evaluation argument naively (for testing purpose)
    /// 
    /// # Arguments
    /// 
    /// - `f_cm`, a (univariate) commitment for f_mle, Commit(⟦f_mle⟧_n)
    /// - `f_mle`, a mle polynomial for f_mle
    /// - `us`, a vector of scalars, `us = [u0, u1, ..., u{n-1}]`
    /// - `tr`, a transcript for interaction
    ///    
    /// # Returns
    /// 
    /// - v, the value of `f_mle(u0, u1, ..., u{n-1})`
    /// - prf, evaluation argument
    /// 
    pub fn prove_plain(&self, 
        f_cm: &Commitment, 
        f_mle: &MleEvals, 
        us: &[Scalar],
        tr: &mut Transcript,
    ) -> (Scalar, EvalArgument) {
        assert_eq!(f_mle.num_var, us.len());

        let n = us.len();
        let v = f_mle.evaluate(us);
        tr.update_with_g1(&f_cm.group_element);
        tr.update_with_scalar_vec(us);

        let mut coeffs: Vec<Scalar> = f_mle.to_coeffs();
        println!("coeffs={}", scalar_vector_to_string(&coeffs));

        // let mut domain_size = pow_2(n);
        let mut h_uni_cm_vec: Vec<Commitment> = Vec::new();
        let mut h_uni_vec: Vec<UniPolynomial> = Vec::new();
        for i in (0..us.len()) {
            
            let h_uni = UniPolynomial::from_coeffs(&coeffs); 

            let h_cm = self.kzg10.commit_uni_poly(&h_uni);

            let coeffs_e: Vec<Scalar> = coeffs.iter().step_by(2).cloned().collect();
            let coeffs_o: Vec<Scalar> = coeffs.iter().skip(1).step_by(2).cloned().collect();
            debug!("rd={}, coeffs_e={}", i, scalar_vector_to_string(&coeffs_e));
            debug!("rd={}, coeffs_o={}", i, scalar_vector_to_string(&coeffs_o));

            debug!("i={}, us[i]={}", i, ScalarExt::to_string(&us[i]));
            coeffs = coeffs_e.iter().zip(coeffs_o.iter())
                .map(| (&e, &o) | e + us[i] * o).collect();
            println!("coeffs={}", scalar_vector_to_string(&coeffs));
            // debug!("rd={}, coeffs_next={}", i, scalar_vector_to_string(&coeffs));
            // domain_size /= 2;
            tr.update_with_g1(&h_cm.group_element);
            h_uni_cm_vec.push(h_cm);
            h_uni_vec.push(h_uni);
        }

        assert_eq!(v, coeffs[0]);
        assert_eq!(coeffs.len(), 1);

        let beta = tr.generate_challenge();
        debug!("beta={}", ScalarExt::to_string(&beta));

        let mut f_eval_pos_vec: Vec<Scalar> = Vec::new();
        let mut f_eval_pos_proof: Vec<kzg10::EvalArgument> = Vec::new();
        let mut f_eval_neg_vec: Vec<Scalar> = Vec::new();
        let mut f_eval_neg_proof: Vec<kzg10::EvalArgument> = Vec::new();
        let mut f_eval_sq_vec: Vec<Scalar> = Vec::new();
        let mut f_eval_sq_proof: Vec<kzg10::EvalArgument> = Vec::new();

        // TODO: compute in O(n)
        for i in 0..us.len() {
            let f_poly = &h_uni_vec[i];
            let (f_eval_pos, eval_proof) = self.kzg10.prove_eval(&f_poly, &beta);

            // assert!(self.kzg10.verify(&f_cm, &eval_proof, &beta, &f_eval_pos));
            f_eval_pos_vec.push(f_eval_pos);
            f_eval_pos_proof.push(eval_proof);

            let (f_eval_neg, eval_proof) = self.kzg10.prove_eval(&f_poly, &(-beta));
            f_eval_neg_vec.push(f_eval_neg);
            f_eval_neg_proof.push(eval_proof);

            // debug!("rd={}, f_eval_pos={}", i, ScalarExt::to_string(&f_eval_pos));
            // debug!("rd={}, f_eval_neg={}", i, ScalarExt::to_string(&f_eval_neg));

            if i != 0 {
                let (f_eval_sq, eval_proof) = self.kzg10.prove_eval(&f_poly, &(beta * beta));
                f_eval_sq_vec.push(f_eval_sq);
                f_eval_sq_proof.push(eval_proof);
                debug!("rd={}, f_eval_sq={}", i, ScalarExt::to_string(&f_eval_sq));
            }
        }
        f_eval_sq_vec.push(v);

        (v, EvalArgument {
            poly_cm_vec: h_uni_cm_vec,
            evals_pos: f_eval_pos_vec,
            evals_pos_proof: f_eval_pos_proof,
            evals_neg: f_eval_neg_vec,
            evals_neg_proof: f_eval_neg_proof,
            evals_sq: f_eval_sq_vec,
            evals_sq_proof: f_eval_sq_proof,
        })
    }

    /// Verify the evaluation argument naively
    /// 
    /// # Arguments
    /// 
    /// - `f_cm`, a (univariate) commitment for f_mle, Commit(⟦f_mle⟧_n)
    /// - `us`, a vector of scalars, `us = [u0, u1, ..., u{n-1}]`
    /// - `v`, the value of `f_mle(u0, u1, ..., u{n-1})`
    /// - `prf`, evaluation argument
    /// - `tr`, transcript of Fiat-Shamir scheme
    /// 
    /// # Returns
    /// 
    /// - true if the evaluation argument is valid
    /// 
    pub fn verify_plain(&self, 
        f_cm: &Commitment, 
        us: &[Scalar], 
        v: &Scalar,
        prf: &EvalArgument, 
        tr: &mut Transcript,
    ) -> bool {

        let num_rounds = us.len();
        let mut rho_vec = us.to_vec();

        tr.update_with_g1(&f_cm.group_element);
        tr.update_with_scalar_vec(us);

        let h_cm_vec = &prf.poly_cm_vec;

        for i in (0..num_rounds) {
            let h_cm = &h_cm_vec[i];
            tr.update_with_g1(&h_cm.group_element);
        }

        let beta = tr.generate_challenge();
        debug!("beta={}", ScalarExt::to_string(&beta));

        for i in 0..num_rounds {
            let rho = us[i];
            let rhs = ((prf.evals_pos[i] + prf.evals_neg[i]) / Scalar::from(2)) + rho * (prf.evals_pos[i] - prf.evals_neg[i]) / (Scalar::from(2) * beta);
            debug!("rd={}, rhs={}", i, ScalarExt::to_string(&rhs));
            debug!("rd={}, sq={}", i, ScalarExt::to_string(&prf.evals_sq[i]));
            assert_eq!(prf.evals_sq[i], rhs);
        }

        for i in 0..prf.evals_pos.len() {
            let b = self.kzg10.verify_eval(
                &prf.poly_cm_vec[i], 
                &beta,
                &prf.evals_pos[i],
                &prf.evals_pos_proof[i], 
            );
            assert!(b, "failed at round {}", i);
        }

        for i in 0..prf.evals_neg.len() {
            let b = self.kzg10.verify_eval(
                &prf.poly_cm_vec[i], 
                &(-beta),
                &prf.evals_neg[i],
                &prf.evals_neg_proof[i], 
            );
            assert!(b, "failed at round {}", i);
        }

        for i in 0..prf.evals_sq_proof.len() {
            let b = self.kzg10.verify_eval(
                &prf.poly_cm_vec[i+1], 
                &(beta * beta),
                &prf.evals_sq[i],
                &prf.evals_sq_proof[i], 
            );
            assert!(b, "failed at round {}", i);
        }

        prf.evals_sq[num_rounds-1] == *v
    }
}

mod tests {
    use super::*;

    #[test]
    fn test_prove_verify_plain() {
        init_logger();

        let rng = &mut ark_std::test_rng();
        // f(X2, X1, X0) = 1 + X0 + 2*X1 + 0*X0X1 + 4*X2
        let f_vs = Scalar::from_usize_vector(&[1,2,3,4,5,6,7,8]);
        let f_mle = MleEvals::new(&f_vs);
        let rs = Scalar::from_usize_vector(&[1,2,3]);
        let mut tr = Transcript::new();

        let kzg10_sys = Rc::new(KZG10PCS::setup(100, rng));
        let mle_pcs = MlePCSystem::setup(&kzg10_sys);

        let f_cm = mle_pcs.commit(&f_mle);

        let (v, prf) = mle_pcs.prove_plain(&f_cm, &f_mle, &rs, &mut tr.clone());
        debug!("v={}", ScalarExt::to_string(&v));

        let b = mle_pcs.verify_plain(&f_cm, &rs, &v, &prf, &mut tr.clone());
        assert!(b);
    }   

    #[test]
    fn test_prove_verify_opt() {
        init_logger();

        let rng = &mut ark_std::test_rng();
        // f(X2, X1, X0) = 1 + X0 + 2*X1 + 0*X0X1 + 4*X2
        let f_vs = Scalar::from_usize_vector(&[1,2,3,4,5,6,7,8]);
        let f_mle = MleEvals::new(&f_vs);
        let rs = Scalar::from_usize_vector(&[1,2,3]);
        let mut tr = Transcript::new();

        let kzg10_sys = Rc::new(KZG10PCS::setup(100, rng));
        let mle_pcs = MlePCSystem::setup(&kzg10_sys);

        let f_cm = mle_pcs.commit(&f_mle);

        let (v, prf) = mle_pcs.prove_opt(&f_cm, &f_mle, &rs, &mut tr.clone());
        debug!("v={}", ScalarExt::to_string(&v));

        let b = mle_pcs.verify_opt(&f_cm, &rs, &v, &prf, &mut tr.clone());
        assert!(b);
    }   
}