use crate::*;
use crate::mle::{EqPolynomial, MLEPolynomial};
use crate::unipoly::UniPolynomial;
use crate::transcript::Transcript;

// TODO: any setup for sumcheck?
pub struct SumcheckSystem { }

// TODO: do we need to store the degree of the polynomial?
pub struct SumcheckProof {
    pub name: String,
    pub internal_unipolys: Vec<UniPolynomial>,
}

impl SumcheckSystem {

    // a simple sumcheck for summarize a vector
    //
    // claimed_sum ?= ∑ f(x_vec)
    // return: 
    //      1. randomness r_vec
    //      2. reduced sum
    //      3. proof

    // NOTE: `name` is useful for debugging, give me a better name pls.
    pub fn prove_single(
        name: &str,
        claimed_sum: &Scalar,
        f: &MLEPolynomial,
        trans: &mut Transcript,
    ) -> (Vec<Scalar>, Scalar, SumcheckProof) {
        let rounds = f.num_var;
        
        // TODO: do we need to truncate `poly`?
        let mut poly = MLEPolynomial::new(&f.evals.clone());
        let mut e = claimed_sum.to_owned();

        // r_vec for collecting randomness generated in each round by RO 
        let mut r_vec: Vec<Scalar> = Vec::new();

        // ipoly_vec for collecting uni-polynomials generated in each round
        let mut ipoly_vec: Vec<UniPolynomial> = Vec::new();

        let mut half = poly.len() / 2;

        for _rd in 0..rounds {

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

            let r = trans.generate_challenge();
            r_vec.push(r);

            poly.fold_into_half(&r);
            half /= 2;

            let g_poly = UniPolynomial::from_evals(&[eval_at_0, eval_at_1], 2);
            // reduce the sum
            e = g_poly.evaluate(&r);
            ipoly_vec.push(g_poly);
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

        assert_eq!(num_rounds, ipoly_vec.len());

        for _rd in 0..num_rounds {
            let ipoly = &ipoly_vec[_rd];

            // every ipoly should be a linear polynomial
            assert_eq!(ipoly.degree(), 1);

            let eval_at_0 = ipoly.evals[0];
            let eval_at_1 = ipoly.evals[1];

            assert_eq!(e, eval_at_0 + eval_at_1, 
                "sumcheck [{}] failed at round {}", &prf.name, _rd);

            trans.update_with_scalar_vec(ipoly.evals.as_slice());
            let r = trans.generate_challenge();
            println!("r[{}]={}", _rd, r);

            let eval_at_r = ipoly.evaluate(&r);
            // reduce the sum
            e = eval_at_r
        }
        // (reduced_sum, randomness vector from RO)
       (e, r_vec)
    }

    // G_func: compute the polynomial G(f_{0,i}, f_{1,i}, ..., f_{m,i}) horizontally
    //     e.g. G(f1(x_vec), f2(x_vec), f3(x_vec), f4(x_vec)) 
    //              = f1(x_vec) * f2(x_vec) * f3(x_vec) + f1(x_vec) * f4(x_vec)
    pub fn prove_cubic<Func>(
        name: &str,
        claimed_sum: &Scalar,
        f_vec: &[MLEPolynomial],
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
        let mut polys: Vec<MLEPolynomial> = Vec::new();
        for i in 0..num_poly {
            polys.push(f_vec[i].clone())
        }

        let num_rounds = f_vec[0].num_var;

        let mut e = claimed_sum.to_owned();

        // TODO: should add degree bounds checking for G_func(f_vec)
        
        // r_vec for collecting randomness generated in each round by RO 
        let mut r_vec: Vec<Scalar> = Vec::new();

        // ipoly_vec for collecting uni-polynomials generated in each round
        let mut ipoly_vec: Vec<UniPolynomial> = Vec::new();

        let mut half = poly_size / 2;

        println!("==== sumcheck prove start =====");

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
            assert_eq!(e, g_evals[0] + g_evals[1]);

            trans.update_with_scalar_vec(&g_evals);
            let r = trans.generate_challenge();
            r_vec.push(r);

            for i in 0..num_poly {
                polys[i].fold_into_half(&r);
            }
            half /= 2;

            let g_poly = UniPolynomial::from_evals(&g_evals, degree_bound + 1);
            // reduce the sum
            e = g_poly.evaluate(&r);
            ipoly_vec.push(g_poly);
            
        }

        println!("==== sumcheck prove end =====");

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

        // TODO: use `log::trace!()` instead of `println!()`
        println!("==== sumcheck verify begin =====");

        let mut e = *claimed_sum;
        let mut r_vec: Vec<Scalar> = Vec::new();
        let ipoly_vec = &prf.internal_unipolys;

        assert_eq!(num_rounds, ipoly_vec.len());

        for _rd in 0..num_rounds {
            let ipoly = &ipoly_vec[_rd];

            // every ipoly's domain should be equal to degree+1
            assert_eq!(ipoly.evals.len(), degree_bound + 1);

            let eval_at_0 = ipoly.evals[0];
            let eval_at_1 = ipoly.evals[1];

            assert_eq!(e, eval_at_0 + eval_at_1, 
                "sumcheck [{}] failed at round {}", &prf.name, _rd);

            trans.update_with_scalar_vec(ipoly.evals.as_slice());
            let r = trans.generate_challenge();
            println!("r[{}]={}", _rd, r);

            let eval_at_r = ipoly.evaluate(&r);
            // reduce the sum
            e = eval_at_r
        }
        // (reduced_sum, randomness vector from RO)
       (e, r_vec)
    }
}


mod tests {
    use super::*;

    #[test]
    fn test_sumcheck_single_prove_verify() {
 
        let vs = Scalar::from_usize_vector(&[1,2,3,4]);
        let f = MLEPolynomial::new(&vs);
        let mut tr = Transcript::new_with_name(b"test");

        let num_rounds = f.num_var;
        let sum = vs.iter().sum::<Scalar>();

        let (r_vec, re, prf) = SumcheckSystem::prove_single("test", &sum, &f, &mut tr.clone());

        println!("r_vec={}", scalar_vector_to_string(&r_vec));
        println!("reduced_sum={}", ScalarExt::to_string(&re));

        let (re_prime, r_vec_prime) = SumcheckSystem::verify_single(&sum, num_rounds, &prf, &mut tr.clone());
        assert_eq!(re, re_prime);
    }

    #[test]
    fn test_sumcheck_cubic_prove_verify() {

        let f0_vec = Scalar::from_usize_vector(&[1,2,3,4]);
        let f1_vec = Scalar::from_usize_vector(&[2,1,2,1]);
        let f2_vec = Scalar::from_usize_vector(&[3,2,2,3]);
        let f0 = MLEPolynomial::new(&f0_vec);
        let f1 = MLEPolynomial::new(&f1_vec);
        let f2 = MLEPolynomial::new(&f2_vec);

        let mut tr = Transcript::new_with_name(b"test");

        let G_func = |vs: Vec<Scalar>, size: usize| {
            vs[0] * vs[1] * vs[2]
        };

        let num_rounds = f0.num_var;
        let sum = f0_vec.iter().enumerate().map(
            |(i, v0)| *v0 * f1_vec[i] * f2_vec[i]).sum::<Scalar>();

        println!("sum={}", sum);

        let (r_vec, re, prf) = SumcheckSystem::prove_cubic("test", &sum, &[f0, f1, f2], &G_func, 3, &mut tr.clone());

        println!("r_vec={}", scalar_vector_to_string(&r_vec));
        println!("reduced_sum={}", ScalarExt::to_string(&re));

        let (re_prime, r_vec_prime) = SumcheckSystem::verify(&sum, num_rounds, 3, &prf, &mut tr.clone());
        assert_eq!(re, re_prime);
    }


}

