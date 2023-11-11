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

        // r_vec for storing randomness generated in each round by RO 
        let mut r_vec: Vec<Scalar> = Vec::new();

        // ipoly_vec for storing uni-polynomials generated in each round
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

            let g_poly = UniPolynomial::from_evals(&[eval_at_0, eval_at_1]);
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
}


mod tests {
    use super::*;

    #[test]
    fn test_sumcheck_prove_verify() {
 
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
}

