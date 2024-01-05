#![allow(non_snake_case)]

use crate::*;
use crate::mle::{EqPolynomial, evals::MleEvals, coeffs_sparse::MleCoeffs};
use crate::unipoly::UniPolynomial;
use crate::transcript::Transcript;
use log::debug;

// TODO: any setup for sumcheck?
pub struct SumcheckSystem { }

// TODO: do we need to store the degree of the polynomial?
pub struct SumcheckProof {
    pub name: String,
    pub internal_unipolys: Vec<Vec<Scalar>>,
}

impl SumcheckSystem {

    // a simple sumcheck for summarize a vector
    //
    // prove: claimed_sum ?= ∑ f(x_vec)
    // return: 
    //      1. randomness r_vec
    //      2. reduced sum
    //      3. proof

    // NOTE: `name` is useful for debugging, give me a better name pls.
    pub fn prove_single(
        name: &str,
        claimed_sum: &Scalar,
        f: &MleEvals,
        trans: &mut Transcript,
    ) -> (Vec<Scalar>, Scalar, SumcheckProof) {
        let rounds = f.num_var;
        let domain = [Scalar::zero(), Scalar::one()];

        // TODO: do we need to truncate `poly`?
        let mut poly = MleEvals::new(&f.evals.clone());
        let mut e = claimed_sum.to_owned();

        // r_vec for collecting randomness generated in each round by RO 
        let mut r_vec: Vec<Scalar> = Vec::new();

        // ipoly_vec for collecting uni-polynomials generated in each round
        let mut ipoly_vec: Vec<Vec<Scalar>> = Vec::new();

        let mut half = poly.len() / 2;

        for _rd in 0..rounds {
            debug!("rd={}, poly={}", _rd, poly);
            let mut eval_at_0 = Scalar::zero();
            let mut eval_at_1 = Scalar::zero();

            //start folding
            for i in 0..half {
                // f'(0) = ∑ f(low)
                eval_at_0 += poly[i];
                // f'(1) = ∑ f(high)
                eval_at_1 += poly[i + half];
            }

            // check f'(0) + f'(1) = f(r)
            assert_eq!(e, eval_at_0 + eval_at_1);

            trans.update_with_scalar(&eval_at_0);
            trans.update_with_scalar(&eval_at_1);
            debug!("eval_at_0={}", &eval_at_0);
            debug!("eval_at_1={}", &eval_at_1);

            // TODO: temporarily debugging
            // let r = Scalar::from_usize(_rd + 1);
            let r = trans.generate_challenge();
            r_vec.insert(0, r); 
            debug!("r={}", r);
            
            poly.fold_into_half(&r);
            half /= 2;

            let g_poly = [eval_at_0, eval_at_1];
            // reduce the sum
            e = UniPolynomial::evaluate_from_evals(&g_poly, &r, &domain);
            // debug!("g={}", scalar_vector_to_string(&g_poly.evals));
            // debug!("g.coeffs={}", scalar_vector_to_string(&g_poly.coeffs));
            debug!("g[{}]={}", ScalarExt::to_string(&r), ScalarExt::to_string(&e));
            // debug!("reduced sum={}", &e);
            ipoly_vec.push(g_poly.to_vec());
        }

        (r_vec, e, SumcheckProof { 
            name: String::from(name),
            internal_unipolys: ipoly_vec })
    }

    pub fn verify_single(
        claimed_sum: &Scalar,
        num_rounds: usize,
        prf: &SumcheckProof,
        trans: &mut Transcript,
    ) -> (Scalar, Vec<Scalar>) {

        let mut e = *claimed_sum;
        let mut r_vec: Vec<Scalar> = Vec::new();
        let ipoly_vec = &prf.internal_unipolys;
        let domain = [Scalar::zero(), Scalar::one()];

        assert_eq!(num_rounds, ipoly_vec.len());

        for _rd in 0..num_rounds {
            let ipoly = &ipoly_vec[_rd];

            // every ipoly should be a linear polynomial
            assert_eq!(ipoly.len(), 2);

            let eval_at_0 = ipoly[0];
            let eval_at_1 = ipoly[1];

            assert_eq!(e, eval_at_0 + eval_at_1, 
                "sumcheck [{}] failed at round {}", &prf.name, _rd);

            trans.update_with_scalar_vec(ipoly.as_slice());

            // TODO: temporarily debugging
            // let r = Scalar::from_usize(_rd + 1);
            let r = trans.generate_challenge();
            r_vec.insert(0, r);

            debug!("r[{}]={}", _rd, r);

            let eval_at_r = UniPolynomial::evaluate_from_evals(&ipoly, &r, &domain);
            // reduce the sum
            e = eval_at_r
        }
        // (reduced_sum, randomness vector from RO)
       (e, r_vec)
    }

    pub fn prove_product(
        name: &str,
        claimed_sum: &Scalar,
        f: &mut MleEvals,
        g: &mut MleEvals,
        trans: &mut Transcript,
    ) -> (Vec<Scalar>, Scalar, SumcheckProof)
    {
        assert_eq!(f.len(), g.len());
        let mle_size = f.len();
        let num_rounds = f.num_var;
        let domain = (0..=2).map(|i| Scalar::from_usize(i)).collect::<Vec<Scalar>>();

        let mut e = claimed_sum.to_owned();
                
        // r_vec for collecting randomness generated in each round by RO 
        let mut r_vec: Vec<Scalar> = Vec::new();

        // ipoly_vec for collecting uni-polynomials generated in each round
        let mut ipoly_vec: Vec<Vec<Scalar>> = Vec::new();

        let mut half = mle_size / 2;

        debug!("==== sumcheck prove start =====");

        // start sumchecking
        for _rd in 0..num_rounds {

            // g(0), g(1), g(2)
            let mut g_evals: Vec<Scalar> = vec![Scalar::zero(); 3];

            //start folding
            for i in 0..half {

                // TODO: here we only support degree_bound = 3
                //    generalize it to any degree later on, not hard as you can see

                // h(0) = ∑ f(low) * g(low)
                g_evals[0] += f[i] * g[i];
                // h(1) = ∑ f(high) * g(high)
                g_evals[1] += f[half + i] * g[half + i];
                // g(2) = ∑ (-f(low) + 2f(high)) * (-g(low) + 2g(high))
                g_evals[2] += (Scalar::from(2) *f[half + i] - f[i]) * (Scalar::from(2) * g[half + i] - g[i]);
            }
            
            // check f'(0) + f'(1) = f(r)
            assert_eq!(e, g_evals[0] + g_evals[1]);
            println!("rd={}, g_evals={}", _rd, scalar_vector_to_string(&g_evals));

            trans.update_with_scalar_vec(&g_evals);
            let r = trans.generate_challenge();
            r_vec.insert(0, r);

            f.fold_into_half(&r);
            g.fold_into_half(&r);
            half /= 2;

            // reduce the sum
            e = UniPolynomial::evaluate_from_evals(&g_evals, &r, &domain);
            ipoly_vec.push(g_evals);
        }

        debug!("==== sumcheck prove end =====");

        (r_vec, e, SumcheckProof { 
            name: String::from(name),
            internal_unipolys: ipoly_vec })
    }


    // G_func: compute the polynomial G(f_{0,i}, f_{1,i}, ..., f_{m,i}) horizontally
    //     e.g. G(f1(x_vec), f2(x_vec), f3(x_vec), f4(x_vec)) 
    //              = f1(x_vec) * f2(x_vec) * f3(x_vec) + f1(x_vec) * f4(x_vec)
    pub fn prove_cubic<Func>(
        name: &str,
        claimed_sum: &Scalar,
        f_vec: Vec<&MleEvals>,
        G_func: Func,
        degree_bound: usize,
        trans: &mut Transcript,
    ) -> (Vec<Scalar>, Scalar, SumcheckProof)
    where 
        Func: Fn(Vec<Scalar>, usize) -> Scalar,
    {
        assert!(f_vec.len() > 1);
        for f in f_vec.iter() {
            assert_eq!(f.num_var, f_vec[0].num_var)
        }
        let poly_size = f_vec[0].len();
        let num_poly = f_vec.len();
        let mut polys: Vec<MleEvals> = Vec::new();
        for i in 0..num_poly {
            polys.push(f_vec[i].clone())
        }

        let num_rounds = f_vec[0].num_var;
        let domain = (0..=degree_bound).map(|i| Scalar::from_usize(i)).collect::<Vec<Scalar>>();

        let mut e = claimed_sum.to_owned();
            
        // TODO: should add degree bounds checking for G_func(f_vec)
        
        // r_vec for collecting randomness generated in each round by RO 
        let mut r_vec: Vec<Scalar> = Vec::new();

        // ipoly_vec for collecting uni-polynomials generated in each round
        let mut ipoly_vec: Vec<Vec<Scalar>> = Vec::new();

        let mut half = poly_size / 2;

        debug!("==== sumcheck prove start =====");

        // start sumchecking
        for _rd in 0..num_rounds {

            // g(0), g(1), g(2), ..., g(d)
            let mut g_evals: Vec<Scalar> = Vec::new();
            for i in 0..=degree_bound {
                g_evals.push(Scalar::zero());
            }

            //start folding
            for i in 0..half {

                // TODO: here we only support degree_bound = 3
                //    generalize it to any degree later on, not hard as you can see

                // h(0) = ∑ f(low)
                g_evals[0] += G_func((0..num_poly).map(|k| polys[k][i]).collect::<Vec<Scalar>>(), num_poly);
                // h(1) = ∑ f(high)
                g_evals[1] += G_func((0..num_poly).map(|k| polys[k][half + i]).collect(), num_poly);

                // g(2) = ∑ (-f(low) + 2f(high))
                g_evals[2] += G_func((0..num_poly).map(
                    |k| Scalar::from(2) * polys[k][half + i] - polys[k][i]).collect(), num_poly
                );

                // F(3) = ∑ (-2f(low) + 3f(high))
                g_evals[3] += G_func((0..num_poly).map(
                    |k| Scalar::from(3) * polys[k][half + i] - Scalar::from(2) * polys[k][i]).collect(), num_poly
                );
            }
            
            // check f'(0) + f'(1) = f(r)
            assert_eq!(e, g_evals[0] + g_evals[1], "sumcheck failed at round {}", _rd);
            println!("rd={}, g_evals={}", _rd, scalar_vector_to_string(&g_evals));

            trans.update_with_scalar_vec(&g_evals);
            let r = trans.generate_challenge();
            r_vec.insert(0, r);

            for i in 0..num_poly {
                polys[i].fold_into_half(&r);
            }
            half /= 2;
            // println!("poly[0] = {}, poly[1] = {}, poly[2] = {}, poly[3] = {}", polys[0],polys[1],polys[2], polys[3]);

            // reduce the sum
            e = UniPolynomial::evaluate_from_evals(&g_evals, &r, &domain);
            ipoly_vec.push(g_evals);
        }

        debug!("==== sumcheck prove end =====");

        (r_vec, e, SumcheckProof { 
            name: String::from(name),
            internal_unipolys: ipoly_vec })
    }

    // NOTE: verify() does not return boolean, 
    //    but the reduced sum and randomness vector. 
    //    It is only parially verified.
    pub fn verify(
        claimed_sum: &Scalar,
        num_rounds: usize,
        degree_bound: usize,
        prf: &SumcheckProof,
        trans: &mut Transcript,
    ) -> (Scalar, Vec<Scalar>) {

        // TODO: use `log::trace!()` instead of `debug!()`
        debug!("==== sumcheck verify begin =====");

        let mut e = *claimed_sum;
        let mut r_vec: Vec<Scalar> = Vec::new();
        let ipoly_vec = &prf.internal_unipolys;
        let domain = (0..=degree_bound).map(|i| Scalar::from_usize(i)).collect::<Vec<Scalar>>();

        assert_eq!(num_rounds, ipoly_vec.len());

        for _rd in 0..num_rounds {
            let ipoly = &ipoly_vec[_rd];

            // every ipoly's domain should be equal to degree+1
            assert_eq!(ipoly.len(), degree_bound + 1);

            let eval_at_0 = ipoly[0];
            let eval_at_1 = ipoly[1];

            assert_eq!(e, eval_at_0 + eval_at_1, 
                "sumcheck [{}] failed at round {}", &prf.name, _rd);

            trans.update_with_scalar_vec(ipoly.as_slice());
            let r = trans.generate_challenge();
            r_vec.insert(0, r);
            debug!("r[{}]={}", _rd, r);

            let eval_at_r = UniPolynomial::evaluate_from_evals(&ipoly, &r, &domain);
            // reduce the sum
            e = eval_at_r
        }
        // (reduced_sum, randomness vector from RO)
       (e, r_vec)
    }

    pub fn prove_G_polymonial<Func>(
        name: &str,
        claimed_sum: &Scalar,
        f_vec: &[MleEvals],
        G_func: Func,
        degree_bound: usize,
        trans: &mut Transcript,
    ) -> (Vec<Scalar>, Scalar, SumcheckProof)
    where 
        Func: Fn(Vec<Scalar>, usize) -> Scalar,
    {
        assert!(f_vec.len() > 1);
        for f in f_vec.iter() {
            assert_eq!(f.num_var, f_vec[0].num_var)
        }
        let poly_size = f_vec[0].len();
        let num_poly = f_vec.len();
        let mut polys: Vec<MleEvals> = Vec::new();
        for i in 0..num_poly {
            polys.push(f_vec[i].clone())
        }
        let domain = (0..=degree_bound).map(|i| Scalar::from_usize(i)).collect::<Vec<Scalar>>();

        let num_rounds = f_vec[0].num_var;

        let mut e = claimed_sum.to_owned();
            
        // TODO: should add degree bounds checking for G_func(f_vec)
        
        // r_vec for collecting randomness generated in each round by RO 
        let mut r_vec: Vec<Scalar> = Vec::new();

        // ipoly_vec for collecting uni-polynomials generated in each round
        let mut ipoly_vec: Vec<Vec<Scalar>> = Vec::new();

        let mut half = poly_size / 2;

        debug!("==== sumcheck prove start =====");

        // start sumchecking
        for _rd in 0..num_rounds {

            // g(0), g(1), g(2), ..., g(d)
            let mut g_evals: Vec<Scalar> = Vec::new();

            // g(i) = ∑ (g_low * f(low,i) + g_high * f(high,i))
            let mut g_fold_factors_high: Vec<Scalar> = Vec::new();
            let mut g_fold_factors_low: Vec<Scalar> = Vec::new();
            for i in 0..=degree_bound {
                g_evals.push(Scalar::zero());
                g_fold_factors_high.push(Scalar::from_i64(i as i64));
                g_fold_factors_low.push(Scalar::from_i64((i as i64) - 1));
            }

            //start folding
            for i in 0..half {

                // support arbitrary degree bound 
                for d in 0..=degree_bound {

                    // h(d) = ∑ [ g_factor_low * f(low) + g_factor_high * f(high) ]
                    let g_row = (0..num_poly).map(|k| 
                        g_fold_factors_high[d] * polys[k][half + i] // high
                        - g_fold_factors_low[d] * polys[k][i]       // low
                    ).collect::<Vec<Scalar>>();
                    g_evals[d] += G_func(g_row, num_poly); 
                }
            }
            
            // check f'(0) + f'(1) = f(r)
            assert_eq!(e, g_evals[0] + g_evals[1]);
            println!("rd={}, g_evals={}", _rd, scalar_vector_to_string(&g_evals));

            trans.update_with_scalar_vec(&g_evals);
            let r = trans.generate_challenge();
            r_vec.insert(0, r);

            for i in 0..num_poly {
                polys[i].fold_into_half(&r);
            }
            half /= 2;
            // println!("poly[0] = {}, poly[1] = {}, poly[2] = {}, poly[3] = {}", polys[0],polys[1],polys[2], polys[3]);

            // reduce the sum
            e = UniPolynomial::evaluate_from_evals(&g_evals, &r, &domain);
            ipoly_vec.push(g_evals);
            
        }

        debug!("==== sumcheck prove end =====");

        (r_vec, e, SumcheckProof { 
            name: String::from(name),
            internal_unipolys: ipoly_vec })
    }

}


mod tests {
    use super::*;    

    #[test]
    fn test_sumcheck_single_prove_verify_0() {
        init_logger();

        // let rng = &mut ark_std::test_rng();
        // let vs = Scalar::rand_vector(vector_size[i], rng);

        let vs = Scalar::from_usize_vector(&[1,2,3,4]);
        let f = MleEvals::new(&vs);
        let mut tr = Transcript::new_with_name(b"test");

        let num_rounds = f.num_var;
        let sum = vs.iter().sum::<Scalar>();

        let (r_vec, re, prf) = SumcheckSystem::prove_single("test", &sum, &f, &mut tr.clone());

        debug!("r_vec={}", scalar_vector_to_string(&r_vec));
        debug!("reduced_sum={}", ScalarExt::to_string(&re));

        let (re_prime, r_vec_prime) = SumcheckSystem::verify_single(&sum, num_rounds, &prf, &mut tr.clone());
        assert_eq!(re, re_prime);

        assert_eq!(r_vec, r_vec_prime);

        // final verification
        // let rx: Vec<Scalar> = r_vec.into_iter().rev().collect();
        assert_eq!(f.evaluate(&r_vec), re);
    }


    #[test]
    fn test_sumcheck_single_prove_verify() {
        init_logger();

        let rng = &mut ark_std::test_rng();
        let vector_size = [2,4,8,16,32,64,128,256,512,1024];

        for i in 0..vector_size.len() {
            let vs = Scalar::rand_vector(vector_size[i], rng);
 
            // let vs = Scalar::from_usize_vector(&[1,2,3,4]);
            let f = MleEvals::new(&vs);
            let mut tr = Transcript::new_with_name(b"test");

            let num_rounds = f.num_var;
            let sum = vs.iter().sum::<Scalar>();

            let (r_vec, re, prf) = SumcheckSystem::prove_single("test", &sum, &f, &mut tr.clone());

            debug!("r_vec={}", scalar_vector_to_string(&r_vec));
            debug!("reduced_sum={}", ScalarExt::to_string(&re));

            let (re_prime, r_vec_prime) = SumcheckSystem::verify_single(&sum, num_rounds, &prf, &mut tr.clone());
            assert_eq!(re, re_prime);

            assert_eq!(r_vec, r_vec_prime);

            // final verification
            assert_eq!(f.evaluate(&r_vec), re);
        }
    }

    #[test]
    fn test_sumcheck_product_prove_verify() {
        let rng = &mut ark_std::test_rng();
        let mut tr = Transcript::new_with_name(b"test");

        let f_vec = Scalar::from_usize_vector(&[2,2,3,4]);
        let g_vec = Scalar::from_usize_vector(&[3,3,2,4]);
        let mut f = MleEvals::new(&f_vec);
        let mut g = MleEvals::new(&g_vec);

        let sum = f_vec.iter().enumerate().map(
            |(i, v0)| *v0 * g_vec[i]).sum::<Scalar>();

        let (rs, re, prf) = SumcheckSystem::prove_product("test", &sum,
            &mut f.clone(), &mut g.clone(), &mut tr.clone());
        assert_eq!(re, f.evaluate(&rs)*g.evaluate(&rs));

        let (re_prime, rs_prime) = SumcheckSystem::verify(&sum, f.num_var, 2, &prf, &mut tr.clone());
        assert_eq!(re_prime, re);
        assert_eq!(rs_prime, rs);

    }

    #[test]
    fn test_sumcheck_cubic_prove_verify() {
        init_logger();

        let rng = &mut ark_std::test_rng();
        let vector_size = [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024];

        for i in 0..vector_size.len() {

            let f0_vec = Scalar::rand_vector(vector_size[i], rng);
            let f1_vec = Scalar::rand_vector(vector_size[i], rng);
            let f2_vec = Scalar::rand_vector(vector_size[i], rng);
            let f0 = MleEvals::new(&f0_vec);
            let f1 = MleEvals::new(&f1_vec);
            let f2 = MleEvals::new(&f2_vec);

            let tr = Transcript::new_with_name(b"test");

            let G_func = |vs: Vec<Scalar>, size: usize| {
                vs[0] * vs[1] * vs[2]
            };

            let num_rounds = f0.num_var;
            let sum = f0_vec.iter().enumerate().map(
                |(i, v0)| *v0 * f1_vec[i] * f2_vec[i]).sum::<Scalar>();

            debug!("sum={}", sum);

            let (r_vec, re, prf) = SumcheckSystem::prove_cubic("test", &sum,
                vec![&f0, &f1, &f2], &G_func, 3, &mut tr.clone());

            debug!("r_vec={}", scalar_vector_to_string(&r_vec));
            debug!("reduced_sum={}", ScalarExt::to_string(&re));

            let (re_prime, r_vec_prime) = SumcheckSystem::verify(&sum, num_rounds, 3, &prf, &mut tr.clone());
            assert_eq!(re, re_prime);
            assert_eq!(r_vec, r_vec_prime);

            // final verification
            assert_eq!(re, G_func(vec![f0.evaluate(&r_vec), f1.evaluate(&r_vec), f2.evaluate(&r_vec)], 3));
        }
    }

    #[test]
    fn test_sumcheck_cubic_prove_verify_2() {
        init_logger();

        let rng = &mut ark_std::test_rng();
        let vector_size = [8];

        for i in 0..vector_size.len() {

            let f0_vec = Scalar::rand_vector(vector_size[i], rng);
            let f1_vec = Scalar::rand_vector(vector_size[i], rng);
            let f2_vec = Scalar::rand_vector(vector_size[i], rng);
            let f0 = MleEvals::new(&f0_vec);
            let f1 = MleEvals::new(&f1_vec);
            let f2 = MleEvals::new(&f2_vec);

            let tr = Transcript::new_with_name(b"test");

            let G_func = |vs: Vec<Scalar>, size: usize| {
                vs[0] * vs[1] * vs[2]
            };

            let num_rounds = f0.num_var;
            let sum = f0_vec.iter().enumerate().map(
                |(i, v0)| *v0 * f1_vec[i] * f2_vec[i]).sum::<Scalar>();

            debug!("sum={}", sum);

            let (r_vec, re, prf) = SumcheckSystem::prove_cubic("test", &sum,
                vec![&f0, &f1, &f2], &G_func, 3, &mut tr.clone());

            debug!("r_vec={}", scalar_vector_to_string(&r_vec));
            debug!("reduced_sum={}", ScalarExt::to_string(&re));

            let (re_prime, r_vec_prime) = SumcheckSystem::verify(&sum, num_rounds, 3, &prf, &mut tr.clone());
            assert_eq!(re, re_prime);
            assert_eq!(r_vec, r_vec_prime);

            // final verification
            assert_eq!(re, G_func(vec![f0.evaluate(&r_vec), f1.evaluate(&r_vec), f2.evaluate(&r_vec)], 3));
        }
    }

    #[test]
    fn test_sumcheck_G_prove_verify() {
        init_logger();

        let rng = &mut ark_std::test_rng();
        let vector_size = [8];

        for i in 0..vector_size.len() {

            let f0_vec = Scalar::rand_vector(vector_size[i], rng);
            let f1_vec = Scalar::rand_vector(vector_size[i], rng);
            let f2_vec = Scalar::rand_vector(vector_size[i], rng);
            let f0 = MleEvals::new(&f0_vec);
            let f1 = MleEvals::new(&f1_vec);
            let f2 = MleEvals::new(&f2_vec);

            let mut tr = Transcript::new_with_name(b"test");

            let G_func = |vs: Vec<Scalar>, size: usize| {
                vs[0] * vs[1] * vs[2]
            };

            let num_rounds = f0.num_var;
            let sum = f0_vec.iter().enumerate().map(
                |(i, v0)| *v0 * f1_vec[i] * f2_vec[i]).sum::<Scalar>();

            debug!("sum={}", sum);

            let (r_vec, re, prf) = SumcheckSystem::prove_G_polymonial("test", &sum,
                &[f0.clone(), f1.clone(), f2.clone()], &G_func, 3, &mut tr.clone());

            debug!("r_vec={}", scalar_vector_to_string(&r_vec));
            debug!("reduced_sum={}", ScalarExt::to_string(&re));

            let (re_prime, r_vec_prime) = SumcheckSystem::verify(&sum, num_rounds, 3, &prf, &mut tr.clone());
            assert_eq!(re, re_prime);
            assert_eq!(r_vec, r_vec_prime);

            // final verification
            assert_eq!(re, G_func(vec![f0.evaluate(&r_vec), f1.evaluate(&r_vec), f2.evaluate(&r_vec)], 3));
        }
    }

}