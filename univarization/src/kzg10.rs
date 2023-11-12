
use ark_poly::domain;

use crate::*;

use crate::fftunipoly::FftUniPolynomial;
use crate::unipoly::UniPolynomial;
use crate::snark::eval_eq_r;

#[derive(Copy, Clone)]
pub struct StructuralReferenceString {
    secret: Scalar,
    // pub powers: Vec<G2>,
    pub max_degree: usize,
}

#[derive(Clone)]
pub struct KZG10PCS {
    pub srs: StructuralReferenceString,
}

#[derive(Clone)]
pub struct Commitment{
    pub values: Vec<Scalar>,
}

pub struct EvalArgument {
    eval_at_x: Scalar,
}

pub struct DegreeBoundArgument {
    degree: usize,
}

// TODO: mock implementation of KZG10
impl KZG10PCS {

    pub fn setup(max_degree: usize) -> Self {
        // let beta = Scalar::rand(rng);
        let beta = Scalar::from_u64(2);

        let srs = StructuralReferenceString {
            secret: beta,
            max_degree: max_degree,
        };

        KZG10PCS {
            srs: srs,
        }
    }

    pub fn commit(&self, polynomial: &UniPolynomial) -> Commitment {

        assert!(polynomial.degree < self.srs.max_degree);

        let coeffs = &polynomial.coeffs;

        Commitment {
            values: coeffs.clone(),
        }
    }

    pub fn commit_poly(&self, polynomial: &FftUniPolynomial) -> Commitment {

        assert!(polynomial.degree < self.srs.max_degree);

        let coeffs = &polynomial.coeffs;

        Commitment {
            values: coeffs.clone(),
        }
    }

    pub fn commit_evals(&self, evals: &Vec<Scalar>, domain_size: usize) -> Commitment {
        assert!(domain_size.is_power_of_two());
        let poly = FftUniPolynomial::from_evals_fft(&evals, domain_size);
        Commitment {
            values: poly.coeffs.clone(),
        }
    }

    pub fn open(&self, commitment: &Commitment, polynomial: &UniPolynomial) -> bool {
        let coeffs = &polynomial.coeffs;
        let s_vec = &commitment.values;
        coeffs.iter().zip(s_vec.iter())
            .map(| (&c, &s) | c == s).fold(true, |acc, x| acc && x)
    }

    pub fn prove_eval(&self, polynomial: &UniPolynomial, x: &Scalar) -> (Scalar, EvalArgument) {
        let result = polynomial.evaluate(x);
        (result, EvalArgument{eval_at_x: result})
    }

    pub fn verify_eval(&self, commitment: &Commitment, eval_argument: &EvalArgument, x: &Scalar) -> bool {
        let coeffs = &commitment.values;
        let result = UniPolynomial::evaluate_from_coeffs(&coeffs, x);

        result == eval_argument.eval_at_x
    }    

    pub fn prove(&self, polynomial: &FftUniPolynomial, x: &Scalar) -> (Scalar, EvalArgument) {
        let result = polynomial.evaluate(x);
        (result, EvalArgument{eval_at_x: result})
    }

    pub fn verify(&self, commitment: &Commitment, eval_argument: &EvalArgument, x: &Scalar) -> bool {
        let coeffs = &commitment.values;
        let poly = FftUniPolynomial::from_coeffs_fft(&coeffs);
        let result = poly.evaluate(x);

        result == eval_argument.eval_at_x
    }

    pub fn prove_degree_bound(&self, 
        commitment: &Commitment, 
        polynomial: &FftUniPolynomial,
        degree_bound: usize,
    ) -> DegreeBoundArgument {
        DegreeBoundArgument {
            degree: polynomial.degree,
        }
    }

    pub fn verify_degree_bound(&self, 
        commitment: &Commitment, 
        degree_bound: usize,
        deg_argument: &DegreeBoundArgument
    ) -> bool {
        let coeffs = &commitment.values;
        coeffs.len() <= degree_bound 
            && deg_argument.degree < degree_bound
    }
} 

#[derive(Copy, Clone)]
pub struct MultiPCS {
    pub srs: StructuralReferenceString,
}

pub struct MultiCommitment{
    values: Vec<Scalar>,
}

impl MultiCommitment{
    pub fn values(&self) -> Vec<Scalar>{
        self.values.clone()
    }
}

pub struct MultiProof{
    eval: Scalar
}

impl MultiPCS{
    pub fn setup(max_degree: usize) ->  Self{
        // let beta = Scalar::rand(rng);
        let beta = Scalar::from_u64(2);

        let srs = StructuralReferenceString {
            secret: beta,
            max_degree: max_degree,
        };

        Self {
            srs: srs,
        }
    }

    pub fn commit(&self, polynomial: &UniPolynomial) -> MultiCommitment {

        let coeffs = &polynomial.coeffs;

        MultiCommitment {
            values: coeffs.clone(),
        }
    }

    pub fn prove_eval(&self, commit: &MultiCommitment, eval: Scalar) -> MultiProof {
    
        MultiProof {
            eval
        }

    }

    pub fn verify_eval(&self, commit: &MultiCommitment, proof: &MultiProof, r: &Vec<Scalar>) -> bool {
        let values = commit.values.clone();
        assert_eq!(log_2(values.len()), r.len());
        let eval = eval_eq_r(&values, r);

        eval == proof.eval
    }    

}

mod tests {
    use crate::*;
    use super::*;

    #[test]
    fn test_kzg10_commit_open() {
        let coeffs = Scalar::from_usize_vector(&[2, 0, 1]);
        let f_poly = UniPolynomial::from_coeffs(&coeffs, 4);
        let kzg10_sys = KZG10PCS::setup(100);
        let f_cm = kzg10_sys.commit(&f_poly);
        let b = kzg10_sys.open(&f_cm, &f_poly);
        assert!(b);
    }

    #[test]
    fn test_kzg10_eval_prove_verify() {
        
        // f(X) = X^2 + 1
        // domain = 4
        // f(3) = 10

        let coeffs = Scalar::from_usize_vector(&[2, 0, 1]);
        let f_poly = UniPolynomial::from_coeffs(&coeffs, 4);
        let x = Scalar::from(3);

        let kzg10_sys = KZG10PCS::setup(100);
        let f_cm = kzg10_sys.commit(&f_poly);

        let (eval_at_x, eval_prf) = kzg10_sys.prove_eval(&f_poly, &x);
        // println!("eval_at_x={}", ScalarExt::to_string(&eval_at_x));

        assert_eq!(eval_at_x, Scalar::from(19));
        let b = kzg10_sys.verify_eval(&f_cm, &eval_prf, &x);
        assert!(b);
    }
}

