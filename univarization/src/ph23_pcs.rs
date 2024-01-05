#![allow(non_snake_case)]

use crate::*;

use crate::groupsim::pairing;
use crate::mle::{*, evals::*};
use crate::transcript::Transcript;
use crate::unipoly::UniPolynomial;
use crate::kzg10::{KZG10PCS, Commitment};
use crate::unisumcheck::UniSumcheckSystem;
use log::{debug, info, warn};

/// MLE evaluation argument for `f_mle(u0, u1, ..., u{n-1}) = v`
/// 
/// We map `f_mle` to a univariate polynomial `f(X)`
///
/// ```
///    f(X) = e_0 * L0(X) + e_1 * L1(X) + ... + e_{N-1} * L_{N-1}(X)
/// ```
/// 
/// where `[e_0, e_1, ..., e_{N-1}]` are the evaluations of `f_mle` over the hypercube
/// 
/// ```
///    f_mle(0, 0, ..., 0) = e_0
///    f_mle(1, 0, ..., 0) = e_1
///    f_mle(0, 1, ..., 0) = e_2
///      ...
///    f_mle(1, 1, ..., 1) = e_{N-1}
/// ```
/// 
/// Because `f_mle` is a multilinear polynomial, we can write `f_mle` as
/// 
/// ```
///   f_mle(u0, u1, ..., u{n-1}) = ∑_{i in B} e_i * c_i, B = {0, 1}^n
/// ```
/// 
/// where `[c_0, c_1, ..., c_{N-1}]` are the evaluations of `eq(..)` at 
/// `[u0, u1, ..., u{n-1}]` over the hypercube
/// 
/// ```
///    c_0     = eq(0, u[])   = (1-u0)(1-u1)(1-u2)...(1-u{n-1})
///    c_1     = eq(1, u[])   =   u0  (1-u1)(1-u2)...(1-u{n-1})
///    c_2     = eq(2, u[])   = (1-u0)  u1  (1-u2)...(1-u{n-1})
///     ...
///    c_{N-1} = eq(N-1, u[]) = u0    u1    u2  ...  u{n-1}
/// ```
/// 
///  The statement of `f_mle(u0, u1, ..., u{n-1}) = v` is reduced to 
/// 
/// ```
///    v = e_0 * c_0 + e_1 * c_1 + ... + e_{N-1} * c_{N-1}
/// ```
///  That is 
/// ```
///    v = ∑_H f(X) * c(X),   
/// ```
/// where `c(omega^i) = c_i`
/// 
/// The key point of [PH23] is to prove the well-formedness of c(X):
/// 
/// ```
///    p_0(X) = s_0(X) * ( c(X) - (1-u0)(1-u1)...(1-u{n-1}) ) = 0, 
///                                                 forall X in H
/// 
///  k = 1..n:
///    p_k(X) = s_{k-1} * ( c(X) * u{n-k} - c(X * omega^k) * (1-u{n-k}) ) = 0,
///                                                forall X in H
/// ```
/// 
///  Here, we introduce `n` selector polynomials, s_0(X) ~ s_{n-1}(X),
///  which select the indices of
///
/// ``` 
///      s_0(X) = z_H(X) / (X - 1),  selected domain: {1}
///      s_1(X) = z_H(X) / (X^2 - 1),  selected domain: {1, omega^{N/2}
///      s_2(X) = z_H(X) / (X^4 - 1),  
///        selected domain: {1, omega^{N/4}, omega^{N/2}, omega^{3N/4}}
/// 
///      s_k(X) = z_H(X) / (X^{2^{k}} - 1),
///        selected domain: H_k = {1, omega^{N/2^{k}}, omega^{2N/2^{k}}, 
///                                        ..., omega^{(2^{k}-1)N/2^{k}}}
/// ```

/// The protocol:
///
///    P                               V
///
///  compute f(X), c(X)
/// 
/// 
///  compute c(X)
///   
///    P   ----- [c(τ)]------------->  V
///    P   <---   α   ---------------  V
///
///  (pre)-compute s_0(X) ~ s_{n-1}(X), zH(X)
///  compute p_0(X) ~ p_{n-1}(X)
/// 
///     p_0(X)=s_0(X) * (c(X) - (1-u0)(1-u1)...(1-u{n-1}))
///  k=1..n:
///     p_k(X)=s_{k-1}(X) * (u_{n-k} * c(X) - (1-u_{n-k}) * c(ω^k * X))
/// 
///  compute p(X) = p_0(X) + α * p_1(X) + α^2 * p_2(X) 
///                           + ... + α^{n} * p_{n}(X)
///  compute g(X) s.t.
/// 
///    f(X) * c(X) - X * g(X) - (v/N) = 0 (mod zH(X))
///      
///    and deg(g(X)) < deg(zH(X)) - 1
///
///  compute t(X) = p(X) and h(X) into a single polynomial t(X)
///    t(X) = (p(X) + α^{n+1) * (f(X) * c(X) - X * g(X) - (v/N)) 
///                 + α^{n+2) * (X^2 * G(X) - X^2 * G(X)) 
///           ) / zH(X)
///
///    P   -- [t(τ)], [g(τ)], [τ^2*g(τ)] -> V
///    P   <---   ζ   ---------------- V
///
///  compute c(ζ), c(ζω), c(ζω^2), ..., c(ζω^{2^{n-1}})
/// 
///  
///  compute r_ζ(X)  (INFO: linearized r_ζ(X) = 0 iff r(ζ) = 0)
/// 
///    r_ζ(X) = [s_0(X) * (c(ζ) - c_0)
///             + α * s_0(X) * (c(ζ) * u0 - c(ζω^{2^{n-1}}) * (1-u0))
///             + α^2 * s_1(X) * (c(ζ) * u1 - c(ζω^{2^{n-2}}) * (1-u1))
///             + ...
///             + α^{n} * s_{n-1}(X) * (c(ζ) * u{n-1} - c(ζω) * (1-u{n-1}))
///             + α^{n+1} * (f(X) * c(ζ) - ζ * g(X) - (v/N)) 
///             + α^{n+2} * (X^2 * g(X)- ζ^2 * g(X))]
///             - zH(ζ) * t(X)
///    s.t.
///      r_ζ(ζ) = 0           
/// 
///  compute quotient polynomial q_ζ(X)
///      q_ζ(X) = (1/(X-ζ)) * (r_ζ(X) ) 
///
///  compute c_ζ(X) by interpolating 
///     [(ζ, c(ζ)), (ζω, c(ζω)),..., (ζω^{2^{n-1}}, c(ζω^{2^{n-1}}))]
/// 
///  compute quotient polynomial q_c(X)
/// 
///     zH_ζ(X) = (X-ζ)(X-ζω)(X-ζω^2)...(X-ζω^{2^{n-1}})
/// 
///     q_c(X) = (c(X) - c_ζ(X)) / zH_ζ(X)
/// 
///    P   -- [q_ζ(τ)], [q_c(τ)] ----> V
///    P   -- f(ζ),c(ζ), c(ζω)... ----> V
///    P   <---   ξ   ----------------> V
/// 
///  compute q_ξ(X)
/// 
///    q_ξ(X) = (c(X) - c_ζ(ξ) - zH_ζ(ξ) * q_c(X)  / (X-ξ)
///
///  P   -- [q_ξ(τ)] ----------------> V
///  
///  Verification:
///   1. compute c_ζ(ξ) in O(n)
///   2. compute C_r = [r_ζ(τ)]
///   3. check e(C_r + ζ*[q_ζ(τ)], [1]) ?= e([q_ζ(τ)], [τ])
///   4. check e(C - c_ζ(ξ)*[1] - zH_ζ(ξ)*[q_c(τ)], [1]) ?= e([q_ξ(τ)], [τ])
///   5. check e([τ^2*g(τ)], [τ^{MAX-N}]) ?= e([g(τ)], [τ^{MAX-N+2}])
/// 
///  TODO:  step 3 & 4 can be batched by another challenge γ
/// 
#[derive(Clone)]
pub struct MlePCSystem {
    kzg10: KZG10PCS,
    unisc: UniSumcheckSystem,
}

#[derive(Clone)]
pub struct EvalArgument {
    c_commitment: kzg10::Commitment,
    q_commitment: kzg10::Commitment,
    c_evals: Vec<Scalar>,
    c_eval_proofs: Vec<kzg10::EvalArgument>,
    q_eval: Scalar,
    sc_proof: unisumcheck::UniSumcheckArgPlain,
}

pub struct EvalArgumentOpt {
    c_commitment: kzg10::Commitment,
    t_commitment: kzg10::Commitment,
    g_commitment: kzg10::Commitment,
    x_sq_g_commitment: kzg10::Commitment,
    q_zeta_commitment: kzg10::Commitment,
    q_xi_commitment: kzg10::Commitment,
    q_c_commitment: kzg10::Commitment,
    c_evals: Vec<Scalar>,
}

pub struct VerifierKey {
    pub s_cm: Vec<Commitment>,
    pub w_vec: Vec<Scalar>,
}

pub struct ProverKey {
    pub vanishing_poly_H: UniPolynomial,
    pub selector_poly_vec: Vec<UniPolynomial>,
}

impl MlePCSystem {

    pub fn setup() -> Self {
        let kzg10 = KZG10PCS::setup(64, &mut ark_std::test_rng());
        let unisc = UniSumcheckSystem::setup(&kzg10);
        MlePCSystem {
            kzg10: kzg10,
            unisc: unisc,
        }
    }

    pub fn commit(&self, f_mle: &MleEvals) -> Commitment {
        let f_uni = UniPolynomial::from_evals(&f_mle.evals);
        self.kzg10.commit_uni_poly(&f_uni)
    }

    pub fn preprocessing_opt(
        &self,
        n: usize,
    ) -> (VerifierKey, ProverKey) {

        let domain_size = pow_2(n);

        let omega = UniPolynomial::get_root_of_unity(n);

        let zH_uni = UniPolynomial::vanishing_polynomial_fft(domain_size);

        let mut s_uni_vec = Vec::new();
        for k in 0..n {
            let (s_uni, r_uni) = zH_uni.div(&UniPolynomial::vanishing_polynomial_fft(pow_2(k)));
            assert!(r_uni.is_zero());
            s_uni_vec.push(s_uni);
        }

        let s_cm_vec = s_uni_vec.iter().map(|s_uni| self.kzg10.commit_uni_poly(&s_uni)).collect::<Vec<Commitment>>();

        let w_vec = {
            let mut Hp = (0..n).map(|k| omega.exp(pow_2(k))).collect::<Vec<Scalar>>();
            Hp.insert(0, Scalar::one());
            let barycentric_weights = UniPolynomial::barycentric_weights(&Hp);
            UniPolynomial::barycentric_weights(&Hp)
        };

        let vk = VerifierKey {
            s_cm: s_cm_vec,
            w_vec: w_vec,
        };
        
        let pk = ProverKey {
            vanishing_poly_H: zH_uni,
            selector_poly_vec: s_uni_vec,
        };

        (vk, pk)
    }

    /// Prove the evaluation argument efficiently
    ///  
    /// # Arguments 
    /// 
    /// - `pk`, prover key with precomputed values/polynomials
    /// - `f_cm`, a (univariate) commitment for f_mle, Commit(⟦f_mle⟧_n)
    /// - `f_mle`, a mle polynomial for f_mle
    /// - `us`, a vector of scalars, u0, u1, ..., u{n-1}
    /// - `tr`, transcript of Fiat-Shamir scheme
    /// 
    /// # Return
    /// 
    /// - v, the value of `f_mle(u0, u1, ..., u{n-1})`
    /// - prf, evaluation argument
    pub fn prove_opt(&self, 
        pk: &ProverKey,
        f_cm: &Commitment, 
        f_mle: &MleEvals, 
        us: &[Scalar], 
        tr: &mut Transcript
    ) -> (Scalar, EvalArgumentOpt)
    {
        assert_eq!(f_mle.num_var, us.len());
        let n = f_mle.num_var;
        let domain_size = pow_2(n);
        let v = f_mle.evaluate(us);

        let f_vec = f_mle.evals.clone();
        let f_uni = UniPolynomial::from_evals(&f_vec);

        { // double check
            assert!(self.kzg10.check_commitment(&f_cm, &f_uni));
        }

        tr.update_with_g1(&f_cm.group_element);

        // preprocessing phase

        let omega = UniPolynomial::get_root_of_unity(n);
        let s_uni_vec = &pk.selector_poly_vec;
        let zH_uni = &pk.vanishing_poly_H;

        // Round 1. 

        // compute c(X), and C=[c(X)]
        let c_vec = EqPolynomial::new(&us.to_vec()).evals_over_hypercube();
        let c_uni = UniPolynomial::from_evals(&c_vec);

        let c_cm = self.kzg10.commit_uni_poly(&c_uni);

        { // double check

            let sum = f_vec.iter().zip(c_vec.iter()).map(
                | (f, c) |  *f * *c).sum::<Scalar>();
            
            assert_eq!(v, sum);
        }

        tr.update_with_g1(&c_cm.group_element);

        // Round 2.

        let alpha = tr.generate_challenge();
        debug!("P> alpha={}", ScalarExt::to_string(&alpha));

        // compute p_0(X) = s_0(X) * (c(X) - (1-r0)(1-r1)...(1-r{n-1})) = 0
        let g0_uni = c_uni.sub_scalar(&c_vec[0]);
        let p0_uni = s_uni_vec[0].mul(&g0_uni);

        let mut h_uni = p0_uni.clone();
        for k in 1..=n {
            let omega_k = UniPolynomial::get_root_of_unity(k);

            let g_uni = c_uni.mul_scalar(&us[n-k])
                .sub(&c_uni.shift(&omega_k).mul_scalar(&(Scalar::one() - us[n-k])));
            let p_uni = s_uni_vec[k-1].mul(&g_uni).mul_scalar(&alpha.exp(k));
            h_uni = h_uni.add(&p_uni);
        }

        // compute g(X) (uni-sumcheck)

        let (g_uni, q_uni) = {
            let (q_uni, r_uni) = f_uni.mul(&c_uni).div(&zH_uni);
            {// double check
                assert_eq!(r_uni.coeffs[0], v/Scalar::from_usize(domain_size));
            }
            let (g_uni, rr_uni) = r_uni.sub_scalar(&(v/Scalar::from_usize(domain_size))).div_by_linear_divisor(&Scalar::zero());
            {
                assert!(rr_uni.is_zero());
            }
            (g_uni, q_uni)
        };

        let g_cm = self.kzg10.commit_uni_poly(&g_uni);

        let x_sq_g_uni = g_uni.mul(&UniPolynomial::from_coeffs(&vec![Scalar::zero(), Scalar::zero(), Scalar::one()]));

        let x_sq_g_cm = self.kzg10.commit_uni_poly(&x_sq_g_uni);
        // compute quotient polynomial -- t(X)

        let (mut t_uni, r_uni) = h_uni.div(&zH_uni);
        { // double check
            assert!(r_uni.is_zero());
        }
        t_uni = t_uni.add(&q_uni.mul_scalar(&alpha.exp(n+1)));

        {  // double check
            let t_uni_2 = {
                let (mut _q_uni, r_uni) = f_uni.mul(&c_uni).div(&zH_uni);
                let a = &f_uni.mul(&c_uni).sub(&r_uni).mul_scalar(&alpha.exp(n+1));
                let h_uni = h_uni.add(&a);
                let (t_uni, r_uni) = h_uni.div(&zH_uni);
                assert!(r_uni.is_zero());
                t_uni
            };

            assert_eq!(t_uni, t_uni_2);
        }
        
        let t_cm = self.kzg10.commit_uni_poly(&t_uni);

        tr.update_with_g1(&g_cm.group_element);
        tr.update_with_g1(&t_cm.group_element);
        tr.update_with_g1(&x_sq_g_cm.group_element);

        // Round 3.

        let zeta = tr.generate_challenge();

        // compute `c(ζ), c(ζω), c(ζω^2), ..., c(ζω^{2^{n-1}})`
        let mut c_evals = vec![c_uni.evaluate(&zeta)];
        for k in 0..n {
            let omega_2_pow_k = omega.exp(pow_2(k));
            let c_eval_zeta_k = c_uni.evaluate(&(zeta * omega_2_pow_k));
            c_evals.push(c_eval_zeta_k);
        }

        { // double check
            assert_eq!(c_evals.len(), n+1);
        }   

        { // double check
            // let f = 
            // assert_eq!(s_uni_vec[0].evaluate(&zeta) * (c_evals[0] - c_vec[0]), Scalar::zero());
            // for k in 0..n {
            //     assert_eq!(s_uni_vec[k].evaluate(&zeta) * (us[n-1-k] * c_evals[0] - (Scalar::one() - us[n-1-k]) * c_evals[n-k]), Scalar::zero());
            // }
        }

        // compute linearization polynomial -- r_ζ(X)

        let r_zeta_uni = {
            let mut r_zeta_uni = UniPolynomial::zero();
            let c_constarint_0 = s_uni_vec[0].mul_scalar(&(c_evals[0] - c_vec[0]));
            for k in 0..n {
                let ck = c_evals[0] * us[n-1-k] - c_evals[n-k] * (Scalar::one() - us[n-1-k]);
                let c_constarint_k = s_uni_vec[k].mul_scalar(&ck);
                r_zeta_uni.add_inplace(&c_constarint_k.mul_scalar(&alpha.exp(k+1)));
            }
            r_zeta_uni.add_inplace(&c_constarint_0);
            let sc_constraint = f_uni.mul_scalar(&c_evals[0])
                .sub(&g_uni.mul_scalar(&zeta))
                .sub_scalar(&(v/Scalar::from_usize(domain_size)));
            r_zeta_uni.add_inplace(&sc_constraint.mul_scalar(&alpha.exp(n+1)));
            
            let degree_bound_constraint = x_sq_g_uni.sub(&g_uni.mul_scalar(&(zeta*zeta)));
            r_zeta_uni.add_inplace(&degree_bound_constraint.mul_scalar(&alpha.exp(n+2)));

            r_zeta_uni.sub_inplace(&t_uni.mul_scalar(&zH_uni.evaluate(&zeta)));
            r_zeta_uni
        };

        { // double check
            assert_eq!(r_uni.evaluate(&zeta), Scalar::zero());
        }

        // compute quotient polynomial -- q_ζ(X)
        let q_zeta_uni = {
            let (q_uni, r_uni) = r_zeta_uni.div_by_linear_divisor(&zeta);
            assert!(r_uni.is_zero());
            q_uni
        };

        // compute interpolation polynomial -- c_ζ(X)
        // TODO: use fast interpolation in O(nlog^2(n)) time
        let domain_zeta = {
            let mut Hz = (0..n).map(|k| zeta * omega.exp(pow_2(k))).collect::<Vec<Scalar>>();
            Hz.insert(0, zeta);
            Hz
        };

        let z_H_zeta_uni = {
            let mut z = UniPolynomial::from_coeffs(&[Scalar::one()]);
            for k in 0..=n {
                z = z.mul(&UniPolynomial::from_coeffs(&[-domain_zeta[k], Scalar::one()]));
            }
            z
        };

        let barycentric_weights_zeta = UniPolynomial::barycentric_weights(&domain_zeta);

        let c_zeta_uni = {
            let mut z = UniPolynomial::zero();
            for k in 0..=n {
                let (q_uni, r_uni) = z_H_zeta_uni.div_by_linear_divisor(&domain_zeta[k]);
                assert!(r_uni.is_zero());
                let w = c_evals[k] * barycentric_weights_zeta[k];
                z = z.add(&q_uni.mul_scalar(&w));
            }
            z
        };

        // compute quotient polynomial -- q_c(X)

        let (q_c_uni, r_c_uni) = c_uni.sub(&c_zeta_uni).div(&z_H_zeta_uni);
        {
            assert_eq!(r_c_uni.is_zero(), true);
        }

        let q_c_cm = self.kzg10.commit_uni_poly(&q_c_uni);
        let q_zeta_cm = self.kzg10.commit_uni_poly(&q_zeta_uni);

        // send (c(ζ), [q_ζ(X)], [q_c(X)]) to the Verifier
        for k in 0..=n {
            tr.update_with_scalar(&c_evals[k]);
        }
        tr.update_with_g1(&q_c_cm.group_element);
        tr.update_with_g1(&q_zeta_cm.group_element);

        // Round 4.

        let xi = tr.generate_challenge();
        debug!("P> xi={}", ScalarExt::to_string(&xi));
        // compute q_ξ(X)

        let q_xi_uni = {
            let f1 = q_c_uni.mul_scalar(&z_H_zeta_uni.evaluate(&xi));
            let f2 = c_uni.sub_scalar(&c_zeta_uni.evaluate(&xi)).sub(&f1); 
            let (q_uni, r_uni) = f2.div_by_linear_divisor(&xi);
            {
                assert_eq!(r_uni.is_zero(), true);
            }
            q_uni
        };

        let q_xi_cm = self.kzg10.commit_uni_poly(&q_xi_uni);

        // send [q_ξ(X)] to the Verifier
        tr.update_with_g1(&q_xi_cm.group_element);

        { // double check
            let lhs = pairing(&x_sq_g_cm.group_element, &self.kzg10.srs.powers_over_G2[4]);
            let rhs = pairing(&g_cm.group_element, &self.kzg10.srs.powers_over_G2[6]);
            assert_eq!(lhs, rhs);
        }

        { // double check

            let c_zeta_uni = {
                let mut z = UniPolynomial::zero();
                for k in 0..=n {
                    let (q_uni, r_uni) = z_H_zeta_uni.div_by_linear_divisor(&domain_zeta[k]);

                    assert!(r_uni.is_zero());
                    let w = c_evals[k] * barycentric_weights_zeta[k];
                    z = z.add(&q_uni.mul_scalar(&w));
                }
                z
            };

            let domain_pyramid = {
                let mut Hp = (0..n).map(|k| omega.exp(pow_2(k))).collect::<Vec<Scalar>>();
                Hp.insert(0, Scalar::one());
                Hp
            };
    
            let w_vec = {
                let zeta_n_inv = zeta.exp(n).inverse().unwrap();

                let w_vec = UniPolynomial::barycentric_weights(&domain_pyramid);
                for k in 0..=n {
                    assert_eq!(w_vec[k]*zeta_n_inv, barycentric_weights_zeta[k]);
                }
            };

            let c_zeta_at_xi = c_zeta_uni.evaluate(&xi);
            let mut C1 = c_cm.sub(&Commitment::commit(&c_zeta_at_xi)).sub(&q_c_cm.mul_scalar(&z_H_zeta_uni.evaluate(&xi)));

            C1 = C1.add(&q_xi_cm.mul_scalar(&xi));
            let lhs = pairing(&C1.group_element, &self.kzg10.srs.h);
            let rhs = pairing(&q_xi_cm.group_element, &self.kzg10.srs.h_tau);
            assert_eq!(lhs, rhs);
        }

        { // double check

            let s_cm_vec = s_uni_vec.iter().map(|s_uni| self.kzg10.commit_uni_poly(&s_uni)).collect::<Vec<Commitment>>();
            let mut C_r = s_cm_vec[0].mul_scalar(&(c_evals[0] - c_vec[0]));
            assert_eq!(c_vec[0], us.iter().map(|u| Scalar::one() - u).product());

            for k in 0..n {
                let e = c_evals[0] * us[n-1-k] - c_evals[n-k] * (Scalar::one() - us[n-1-k]);
                let p = s_cm_vec[k].mul_scalar(&(e * alpha.exp(k+1)));
                C_r = C_r.add(&p);
            }
            C_r = C_r.add(&(
                &f_cm.mul_scalar(&c_evals[0])
                .sub(&g_cm.mul_scalar(&zeta))
                .sub(&&self.kzg10.commit_values(&[v/Scalar::from_usize(domain_size)]))
                .mul_scalar(&alpha.exp(n+1))));
            C_r = C_r.add(&x_sq_g_cm.sub(&g_cm.mul_scalar(&(zeta*zeta)))
                .mul_scalar(&alpha.exp(n+2)));
            C_r = C_r.sub(&t_cm.mul_scalar(&zH_uni.evaluate(&zeta)));
            // double check
            assert_eq!(zH_uni.evaluate(&zeta), zeta.exp(domain_size) - Scalar::one());

            let C2 = C_r.add(&q_zeta_cm.mul_scalar(&zeta));
            let lhs = pairing(&C2.group_element, &self.kzg10.srs.h);
            let rhs = pairing(&q_zeta_cm.group_element, &self.kzg10.srs.h_tau);
            assert_eq!(lhs, rhs);
        }

        (v, EvalArgumentOpt{
            c_commitment: c_cm,
            t_commitment: t_cm,
            g_commitment: g_cm,
            x_sq_g_commitment: x_sq_g_cm,
            q_zeta_commitment: q_zeta_cm,
            q_xi_commitment: q_xi_cm,
            q_c_commitment: q_c_cm,
            c_evals: c_evals,
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
        vk: &VerifierKey,
        f_cm: &Commitment, 
        us: &[Scalar], 
        v: &Scalar,
        prf: EvalArgumentOpt,
        tr: &mut Transcript
    ) -> bool {

        let n = us.len();

        let domain_size = pow_2(n);

        let omega = UniPolynomial::get_root_of_unity(n);

        let s_cm_vec = vk.s_cm.clone();
        let w_vec = vk.w_vec.clone();

        tr.update_with_g1(&f_cm.group_element);

        // Round 1.

        let c_cm = prf.c_commitment;
        tr.update_with_g1(&c_cm.group_element);

        // Round 2.

        let alpha = tr.generate_challenge();
        debug!("V> alpha={}", ScalarExt::to_string(&alpha));

        let g_cm = prf.g_commitment;
        let t_cm = prf.t_commitment;
        let x_sq_g_cm = prf.x_sq_g_commitment;

        tr.update_with_g1(&g_cm.group_element);
        tr.update_with_g1(&t_cm.group_element);
        tr.update_with_g1(&x_sq_g_cm.group_element);

        // Round 3.

        let zeta = tr.generate_challenge();

        let c_evals = prf.c_evals;

        let q_zeta_cm = prf.q_zeta_commitment;
        let q_c_cm = prf.q_c_commitment;

        for k in 0..=n {
            tr.update_with_scalar(&c_evals[k]);
        }

        tr.update_with_g1(&q_c_cm.group_element);
        tr.update_with_g1(&q_zeta_cm.group_element);

        // Round 4.

        let xi = tr.generate_challenge();

        debug!("V> xi={}", ScalarExt::to_string(&xi));

        let q_xi_cm = prf.q_xi_commitment;

        tr.update_with_g1(&q_xi_cm.group_element);

        // Verify 

        // compute zH(ζ) in O(log(N))

        let z_H_at_zeta = zeta.exp(domain_size) - Scalar::one();

        // compute c_0 
        let c_0: Scalar = us.iter().map(|u| Scalar::one() - u).product();

        // compute c_ζ(ξ) in O(n)
        //   c_ζ(ξ) = ∑ c_i * w_i * (z_H_ζ(ξ) / ξ - ζ*ω^_)

        let (c_zeta_at_xi, z_H_zeta_uni_at_xi) = {
            // let mut H_I = (0..n).map(|k| omega.exp(pow_2(k))).collect::<Vec<Scalar>>();
            // H_I.insert(0, Scalar::one());
            // 1, ω, ω^2, w^4, w^8, w^16
            // let barycentric_weights = UniPolynomial::barycentric_weights(&H_I);
            let mut hi = Scalar::one();
            let mut o = omega;
            let mut nominator = Scalar::zero();
            let mut denominator = Scalar::zero();
            let mut z = Scalar::one();
            for k in 0..=n {
                let w = w_vec[k] / (xi - zeta * hi);
                nominator += c_evals[k] * w ;
                denominator += w;
                z = z * (xi - zeta * hi);
                hi = o;
                o = o * o;
            };
            (nominator / denominator, z)
        };

        { // double check

            let domain_zeta = {
                let mut Hz = (0..n).map(|k| zeta * omega.exp(pow_2(k))).collect::<Vec<Scalar>>();
                Hz.insert(0, zeta);
                Hz
            };

            // let barycentric_weights_zeta = UniPolynomial::barycentric_weights(&domain_zeta);

            // compute z_H_ζ(ξ) in O(log(N))
            //   z_H_ζ(ξ) = (ξ - ζ)(ξ - ζ*ω)...(ξ - ζ*ω^_)

            let z2 = {
                let mut z = Scalar::one();
                for k in 0..=n {
                    z = z * (xi - domain_zeta[k]);
                }
                z
            };
            assert_eq!(z2, z_H_zeta_uni_at_xi);
        }

        // { // double check
        //     let mut z = Scalar::zero();
        //     for k in 0..=n {
        //         let w = c_evals[k] * barycentric_weights_zeta[k];
        //         z = z + w * (z_H_zeta_uni_at_xi / (xi - domain_zeta[k]));
        //     }
        //     assert_eq!(z, c_zeta_at_xi);
        // }

        // let c_zeta_cm = {
        //     let zeta_n_inv = zeta.exp(n).inverse().unwrap();
        //     let mut c_cm = self.kzg10.commit_values(&[Scalar::zero()]);
        //     for k in 0..=n {
        //         let cm = w_cm_vec[k].mul_scalar(&(c_evals[k] * zeta_n_inv * (z_H_zeta_uni_at_xi / (xi - domain_zeta[k]))));

        //         let q_uni_at_xi = (z_H_zeta_uni_at_xi / (xi - domain_zeta[k]));
        //         // println!("V> q_uni[{}]={}", k, ScalarExt::to_string(&q_uni_at_xi));
        //         println!("V> c_zeta_cm[{}]={}", k, ScalarExt::to_string(&cm.group_element.x));
        //         c_cm = c_cm.add(&cm);
        //     }
        //     c_cm
        // };

        // verify the first pairing identity
        //   e([τ^2 * g(τ)], [τ^{max-N+1}]) ?= e([g(τ)], [τ^{max-N+3}])
        let lhs = pairing(&x_sq_g_cm.group_element, &self.kzg10.srs.powers_over_G2[4]);
        let rhs = pairing(&g_cm.group_element, &self.kzg10.srs.powers_over_G2[6]);
        assert_eq!(lhs, rhs);

        // verify the second pairing identity
        //   e(C - Cz - zH(ζ, ξ)*[q_c(τ)] + ξ*[q_ξ(τ)], [1]) ?= e([q_ξ(τ)], [τ])
        
        // let c_zeta_cm = self.kzg10.commit_uni_poly(&c_zeta_uni);
        // println!("V> c_zeta_cm={}", ScalarExt::to_string(&c_zeta_cm.group_element.x));
        let mut C1 = c_cm.sub(&Commitment::commit(&c_zeta_at_xi)).sub(&q_c_cm.mul_scalar(&z_H_zeta_uni_at_xi));
        // println!("V> C1={}", ScalarExt::to_string(&C1.group_element.x));
        C1 = C1.add(&q_xi_cm.mul_scalar(&xi));
        let lhs = pairing(&C1.group_element, &self.kzg10.srs.h);
        let rhs = pairing(&q_xi_cm.group_element, &self.kzg10.srs.h_tau);
        assert_eq!(lhs, rhs);

        // TODO: 2nd & 3rd pairing equations can be batched into one (4P -> 2P)
        // verify the third pairing identity
        //    e(C_r + ζ*[q_ζ(τ)], [1]) ?= e([q_ζ(τ)], [τ])
        let mut C_r = s_cm_vec[0].mul_scalar(&(c_evals[0] - c_0));
        for k in 0..n {
            let e = c_evals[0] * us[n-1-k] - c_evals[n-k] * (Scalar::one() - us[n-1-k]);
            let p = s_cm_vec[k].mul_scalar(&(e * alpha.exp(k+1)));
            C_r = C_r.add(&p);
        }
        C_r = C_r.add(&(
            &f_cm.mul_scalar(&c_evals[0])
            .sub(&g_cm.mul_scalar(&zeta))
            .sub(&&self.kzg10.commit_values(&[*v/Scalar::from_usize(domain_size)]))
            .mul_scalar(&alpha.exp(n+1))));
        C_r = C_r.add(&x_sq_g_cm.sub(&g_cm.mul_scalar(&(zeta*zeta)))
            .mul_scalar(&alpha.exp(n+2)));
        C_r = C_r.sub(&t_cm.mul_scalar(&z_H_at_zeta));
        let C2 = C_r.add(&q_zeta_cm.mul_scalar(&zeta));
        let lhs = pairing(&C2.group_element, &self.kzg10.srs.h);
        let rhs = pairing(&q_zeta_cm.group_element, &self.kzg10.srs.h_tau);
        assert_eq!(lhs, rhs);

        true
    }

    /// Prove the evaluation argument naively (for testing purpose)
    /// 
    /// # Arguments
    /// 
    /// - `f_cm`, a (univariate) commitment for f_mle, Commit(⟦f_mle⟧_n)
    /// - `f_mle`, a mle polynomial for f_mle
    /// - `us`, a vector of scalars, `us = [u0, u1, ..., u{n-1}]`
    ///    
    /// # Returns
    /// 
    /// - v, the value of `f_mle(u0, u1, ..., u{n-1})`
    /// - prf, evaluation argument
    pub fn prove_plain(&self, 
        f_cm: &Commitment, 
        f_mle: &MleEvals, 
        us: &[Scalar], 
        tr: &mut Transcript
    ) -> (Scalar, EvalArgument) 
    {
        assert_eq!(f_mle.num_var, us.len());
        let n = f_mle.num_var;
        let domain_size = pow_2(n);
        let v = f_mle.evaluate(us);
        debug!("domain_size={}", domain_size);

        tr.update_with_g1(&f_cm.group_element);

        let f_vec = f_mle.evals.clone();
        let f_uni = UniPolynomial::from_evals(&f_vec);
        let f_cm = f_cm;
        assert!(self.kzg10.check_commitment(&f_cm, &f_uni));

        let c_vec = EqPolynomial::new(&us.to_vec()).evals_over_hypercube();
        let c_uni = UniPolynomial::from_evals(&c_vec);

        let c_cm = self.kzg10.commit_uni_poly(&c_uni);

        let sum = f_vec.iter().zip(c_vec.iter()).map(
            | (f, c) |  *f * *c).sum::<Scalar>();
        
        assert_eq!(v, sum);

        // println!("sum={}", ScalarExt::to_string(&sum));

        tr.update_with_g1(&c_cm.group_element);
        
        let alpha = tr.generate_challenge();
        // let alpha = Scalar::one();

        let zH_uni = UniPolynomial::vanishing_polynomial_fft(domain_size);

        let mut s_uni_vec = Vec::new();
        for k in 0..n {
            let (s_uni, r_uni) = zH_uni.div(&UniPolynomial::vanishing_polynomial_fft(pow_2(k)));
            assert!(r_uni.is_zero());
            s_uni_vec.push(s_uni);
        }
        
        // println!("s0_poly.coeffs={}", scalar_vector_to_string(&s0_poly.coeffs));
        // println!("r_poly.coeffs={}", scalar_vector_to_string(&r_poly.coeffs));
        // println!("s0_poly.evals={}", scalar_vector_to_string(&s0_poly.evaluations()));

        // p_0(X) = s_0(X) * (c(X) - (1-r0)(1-r1)...(1-r{n-1})) = 0
        let g0_uni = c_uni.sub_scalar(&c_vec[0]);
        let p0_uni = s_uni_vec[0].mul(&g0_uni);
        // println!("p[0]={}", scalar_vector_to_string(&p0_uni.evaluations_fft(n)));

        let omega = UniPolynomial::get_root_of_unity(n);

        let mut h_uni = p0_uni.clone();
        for k in 1..=n {
            let omega_k = UniPolynomial::get_root_of_unity(k);

            let g_uni = c_uni.mul_scalar(&us[n-k])
                .sub(&c_uni.shift(&omega_k).mul_scalar(&(Scalar::one() - us[n-k])));
            let p_uni = s_uni_vec[k-1].mul(&g_uni).mul_scalar(&alpha.exp(k));
            // println!("p[{}]={}", k, scalar_vector_to_string(&p_uni.evaluations_fft(n)));
            h_uni = h_uni.add(&p_uni);
        }
        // println!("h_uni.coeffs={}", scalar_vector_to_string(&h_uni.coeffs));
        // println!("h_uni.evals={}", scalar_vector_to_string(&h_uni.evaluations_fft(n)));

        let (q_uni, r_uni) = h_uni.div(&zH_uni);
        assert!(r_uni.is_zero());

        let q_cm = self.kzg10.commit_uni_poly(&q_uni);
        tr.update_with_g1(&q_cm.group_element);
        let zeta = tr.generate_challenge();

        // let zeta = Scalar::from(2);

        let s_uni_eval_vec = s_uni_vec.iter().map(|s_poly| s_poly.evaluate(&zeta)).collect::<Vec<Scalar>>();
        let mut c_evals: Vec<Scalar> = Vec::new();
        let mut c_eval_prfs = Vec::new();
        for k in 0..=n {
            let omega_k = UniPolynomial::get_root_of_unity(k);
            // c_poly.evaluate(&(omega_k * zeta))
            let (eval, eval_prf) = self.kzg10.prove_eval(&c_uni, &(omega_k * zeta));
            c_evals.push(eval);
            c_eval_prfs.push(eval_prf);
        };

        // verify the evaluations
        let mut h = s_uni_vec[0].evaluate(&zeta) * (c_evals[0] - c_vec[0]);
        for k in 1..=n {
            let f = c_evals[0] * us[n-k] - c_evals[k] * (Scalar::one() - us[n-k]);
            let p = s_uni_eval_vec[k-1] * f * alpha.exp(k);
            h += p;
        }
        // println!("h={}", ScalarExt::to_string(&h));
        assert_eq!(h, q_uni.evaluate(&zeta) * zH_uni.evaluate(&zeta));

        let sc_prf = self.unisc.prove_plain(&f_cm, &c_cm, &f_uni, &c_uni, &sum, tr);

        // println!("f_uni(zeta)={}", f_uni.evaluate(&zeta));
        assert!(self.kzg10.check_commitment(&f_cm, &f_uni));
        assert!(self.kzg10.check_commitment(&c_cm, &c_uni));

        (v, EvalArgument{
            c_commitment: c_cm,
            q_commitment: q_cm,
            c_evals: c_evals,
            c_eval_proofs: c_eval_prfs,
            q_eval: q_uni.evaluate(&zeta),
            sc_proof: sc_prf,
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
    pub fn verify_plain(&self, f_cm: &Commitment, xs: &[Scalar], e: &Scalar, 
        prf: &EvalArgument, tr: &mut Transcript
    ) -> bool 
    {
        let n = xs.len();
        let domain_size = pow_2(n);
        let c_eq = EqPolynomial::new(&xs.to_vec());

        tr.update_with_g1(&f_cm.group_element);

        let c_cm = &prf.c_commitment;
        
        tr.update_with_g1(&c_cm.group_element);
        
        let alpha = tr.generate_challenge();

        let zH_uni = UniPolynomial::vanishing_polynomial_fft(domain_size);
        let mut s_uni_vec = Vec::new();
        for k in 0..n {
            let (s_uni, r_uni) = zH_uni.div(&UniPolynomial::vanishing_polynomial_fft(pow_2(k)));
            assert!(r_uni.is_zero());
            s_uni_vec.push(s_uni);
        }
        
        let q_cm = &prf.q_commitment;
        tr.update_with_g1(&q_cm.group_element);

        let zeta = tr.generate_challenge();

        // let zeta = Scalar::from(2);

        let s_uni_eval_vec = s_uni_vec.iter().map(|s_poly| s_poly.evaluate(&zeta)).collect::<Vec<Scalar>>();
        let c_evals = &prf.c_evals;
        let c_eval_prfs = &prf.c_eval_proofs;
        for k in 0..=n {
            let omega_k = UniPolynomial::get_root_of_unity(k);
            // c_poly.evaluate(&(omega_k * zeta))
            let b = self.kzg10.verify_eval(&c_cm, &(omega_k * zeta), &c_evals[k], &c_eval_prfs[k]);
            assert!(b);
        };

        // verify the evaluations
        let mut h = s_uni_vec[0].evaluate(&zeta) * (c_evals[0] - c_eq.eval(0));
        for k in 1..=n {
            let f = c_evals[0] * xs[n-k] - c_evals[k] * (Scalar::one() - xs[n-k]);
            let p = s_uni_eval_vec[k-1] * f * alpha.exp(k);
            h += p;
        }
        assert_eq!(h, prf.q_eval * zH_uni.evaluate(&zeta));

        self.unisc.verify_plain(&f_cm, &c_cm, &e, &prf.sc_proof, tr)
    }
}

mod tests {
    use super::*;

    #[test]
    fn test_prove_verify_plain() {
        init_logger();

        // f(X2, X1, X0) = 1 + X0 + 2*X1 + 0*X0X1 + 4*X2
        let f_vs = Scalar::from_usize_vector(&[1,2,3,4,5,6,7,8]);
        let f_mle = MleEvals::new(&f_vs);
        let rs = Scalar::from_usize_vector(&[2,3,4]);

        let pcs = MlePCSystem::setup();
        let f_cm = pcs.commit(&f_mle);

        let tr = &mut Transcript::new();
        let (v, prf) = pcs.prove_plain(&f_cm, &f_mle, &rs, &mut tr.clone());
        let b = pcs.verify_plain(&f_cm, &rs, &v, &prf, &mut tr.clone());
        assert!(b);
    }

    #[test]
    fn test_prove_verify_xopt() {
        init_logger();

        // f(X2, X1, X0) = 1 + X0 + 2*X1 + 0*X0X1 + 4*X2
        let f_vs = Scalar::from_usize_vector(&[1,2,3,4,5,6,7,8]);
        let f_mle = MleEvals::new(&f_vs);
        let rs = Scalar::from_usize_vector(&[2,3,4]);

        let pcs = MlePCSystem::setup();
        let f_cm = pcs.commit(&f_mle);

        let n = rs.len();
        let (vk, pk) = pcs.preprocessing_opt(n);
        let tr = &mut Transcript::new();
        let (v, prf) = pcs.prove_opt(&pk, &f_cm, &f_mle, &rs, &mut tr.clone());
        let b = pcs.verify_opt(&vk, &f_cm, &rs, &v, prf, &mut tr.clone());
        assert!(b);
    }
}