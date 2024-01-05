use crate::*;

use crate::unipoly::UniPolynomial;
use crate::groupsim::*;

use log::{debug, info, warn};

// use ark_poly::domain;
use ark_std::rand::Rng;
use ark_ec::msm::{FixedBaseMSM, VariableBaseMSM};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::ToBytes;
use ark_std::{
    io::{Read, Result as IoResult, Write},
    vec::Vec,
};

#[derive(Clone)]
pub struct SRS {
    // secret: Scalar,
    pub max_degree: usize,
    pub g: G1,
    pub h: G2,
    pub h_tau: G2,
    pub powers_over_G1: Vec<G1>,
    pub powers_over_G2: Vec<G2>,
}

#[derive(Clone)]
pub struct KZG10PCS {
    pub srs: SRS,
}

#[derive(Clone)]
pub struct Commitment {
    pub group_element: G1,
    pub internal_values: Vec<Scalar>,  // for DEBUG (TODO: to be removed)
}

impl Commitment {


    pub fn commit(v: &Scalar) -> Self {
        Commitment {
            group_element: G1::new(*v),
            internal_values: vec![*v],
        }
    }
    pub fn add(&self, rhs: &Self) -> Self {
        let mut cv: Vec<Scalar> = Vec::new();
        let av = &self.internal_values;
        let bv = &rhs.internal_values;
        if av.len() >= bv.len() {
            let mut cv = av.clone();
            for (i, bv) in bv.iter().enumerate() {
                cv[i] += bv;
            }
        } else {
            let mut cv = bv.clone();
            for (i, av) in av.iter().enumerate() {
                cv[i] += av;
            }
        }

        Commitment{
            group_element: self.group_element.add(&rhs.group_element, false),
            internal_values: cv,
        }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let mut cv: Vec<Scalar> = Vec::new();
        let av = &self.internal_values;
        let bv = &rhs.internal_values;

        if av.len() >= bv.len() {
            let mut cv = av.clone();
            for (i, bv) in bv.iter().enumerate() {
                cv[i] -= bv;
            }
        } else {
            let mut cv = bv.clone();
            for (i, av) in av.iter().enumerate() {
                cv[i] -= av;
            }
        }

        Commitment{
            group_element: self.group_element.add(&rhs.group_element, true),
            internal_values: cv}
    }

    pub fn mul_scalar(&self, s: &Scalar) -> Self {
        let mut cv: Vec<Scalar> = Vec::new();
        let av = &self.internal_values;
        for (i, av) in av.iter().enumerate() {
            cv.push((*s) * (*av));            
        }
        Commitment{
            group_element: self.group_element.mul_scalar(s),
            internal_values: cv,
        }
    }
}

#[derive(Clone)]
pub struct EvalArgument {
    pub(crate) commitment: Commitment,
}

#[derive(Clone)]
pub struct DegreeBoundArgument {
    pub(crate) commitment: Commitment,
    degree_bound: usize,
    max_degree: usize,
}

/*
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

    pub fn commit_values(&self, values: &[Scalar]) -> Commitment {
        Commitment {
            values: values.to_vec(),
        }
    }

    pub fn open(&self, commitment: &Commitment, polynomial: &UniPolynomial) -> bool {
        let coeffs = &polynomial.coeffs;
        let s_vec = &commitment.values;
        coeffs.iter().zip(s_vec.iter())
            .map(| (&c, &s) | c == s).fold(true, |acc, x| acc && x)
    }

    pub fn open_with_values(&self, commitment: &Commitment, values: &[Scalar]) -> bool {
        let s_vec = &commitment.values;
        assert_eq!(s_vec.len(), values.len());
        s_vec.iter().zip(values.iter())
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

    pub fn verify(&self, 
        cm: &Commitment, 
        eval_argument: &EvalArgument, 
        x: &Scalar,
        e: &Scalar,
    ) -> bool {
        let coeffs = &cm.values;
        let poly = FftUniPolynomial::from_coeffs_fft(&coeffs);
        let result = poly.evaluate(x);
        result == *e && 
            result == eval_argument.eval_at_x
    }

    // Prove that deg(f) < degree_bound
    // NOTE: strictly less than 
    pub fn prove_degree_bound(&self, 
        commitment: &Commitment, 
        polynomial: &FftUniPolynomial,
        degree_bound: usize,
    ) -> DegreeBoundArgument {
        assert!(polynomial.degree < degree_bound);
        DegreeBoundArgument {
            degree: polynomial.degree,
        }
    }

    // Prove that deg(f) < degree_bound
    // NOTE: strictly less than 
    pub fn prove_degree_bound_2(&self, 
        commitment: &Commitment, 
        polynomial: &unipoly2::UniPolynomial,
        degree_bound: usize,
    ) -> DegreeBoundArgument {
        assert!(polynomial.degree < degree_bound);
        DegreeBoundArgument {
            degree: polynomial.degree,
        }
    }

    // Verify that deg(f) < degree_bound
    // NOTE: strictly less than 
    pub fn verify_degree_bound(&self, 
        commitment: &Commitment, 
        degree_bound: usize,
        deg_argument: &DegreeBoundArgument
    ) -> bool {
        let coeffs = &commitment.values;
        // TODO: trim the leading zeros
        coeffs.len() <= degree_bound 
            && deg_argument.degree < degree_bound
    }
} 
 */

impl ToBytes for DegreeBoundArgument {
    fn write<W: Write>(&self, writer: W) -> Result<(), ark_std::io::Error> {
        self.commitment.group_element.x.write(writer)?;
        Ok(())
    }
}

// TODO: mock implementation of KZG10
impl KZG10PCS {

    pub fn setup<R: Rng>(max_degree: usize, rng: &mut R) -> Self
    {
        debug!("[setup] start to setup...");

        // generate the trapdoor: τ
        let tau = Scalar::rand(rng);

        let g1 = G1::generator();
        let g2 = G2::generator();

        debug!("[setup] generate...ok.");

        let mut powers_of_tau = vec![Scalar::one()];

        let mut cur = tau;
        for _ in 0..max_degree {
            powers_of_tau.push(cur);
            cur *= &tau;
        }

        let powers_of_g1: Vec<G1> = (0..max_degree).map(|i| g1.mul_scalar(&powers_of_tau[i])).collect();
        let powers_of_g2: Vec<G2> = (0..max_degree).map(|i| g2.mul_scalar(&powers_of_tau[i])).collect();

        debug!(
            "[setup] generate powers_of_g1...ok. max_degree = {}",
            max_degree
        );

        let h_tau = g2.mul_scalar(&tau);
        let srs = SRS {
            g: g1,
            h: g2,
            h_tau: h_tau,
            max_degree,
            powers_over_G1: powers_of_g1,
            powers_over_G2: powers_of_g2,
        };
        debug!("[setup] complete");
        Self {
            srs: srs,
        }
    }

    // pub fn commit(&self, polynomial: &UniPolynomial) -> Commitment {

    //     assert!(polynomial.degree < self.srs.max_degree);

    //     let coeffs = &polynomial.coeffs;

    //     Commitment {
    //         values: coeffs.clone(),
    //     }
    // }

    // Commit a polynomial in the form of a vector of coefficients
    pub fn commit_uni_poly(&self, poly: &UniPolynomial) -> Commitment {

        assert!(poly.degree < self.srs.max_degree);

        let coeffs = &poly.coeffs;

        let powers_of_g1 = &self.srs.powers_over_G1;

        let values: Vec<G1> = coeffs.iter().enumerate().map(|(i, c)| powers_of_g1[i].mul_scalar(c)).collect();

        let mut g = G1::identity();
        for i in 0..values.len() {
            g = g.add(&values[i], false);
        }

        Commitment {
            group_element: g,
            internal_values: coeffs.clone(),
        }
    }

    // Commit a polynomial in the form of a vector of evaluations
    // TODO: lagrange basis srs
    // pub fn commit_evals(&self, evals: &Vec<Scalar>, domain_size: usize) -> Commitment {
    //     assert!(domain_size.is_power_of_two());
    //     let poly = FftUniPolynomial::from_evals_fft(&evals, domain_size);
    //     Commitment {
    //         values: poly.coeffs.clone(),
    //     }
    // }

    pub fn commit_values(&self, values: &[Scalar]) -> Commitment {
        assert!(values.len() < self.srs.max_degree);

        let powers_of_g1 = &self.srs.powers_over_G1;

        let cm_vec: Vec<G1> = values.iter().enumerate().map(|(i, c)| powers_of_g1[i].mul_scalar(c)).collect();

        let mut cm = G1::identity();
        for i in 0..values.len() {
            cm = cm.add(&cm_vec[i], false);
        }
        Commitment {
            group_element: cm,
            internal_values: values.to_vec(),
        }
    }

    pub fn open_uni_poly(&self, cm: &Commitment, poly: &UniPolynomial) -> bool {
        let coeffs = &poly.coeffs;
        let s_vec = &cm.internal_values;
        coeffs.iter().zip(s_vec.iter())
            .map(| (&c, &s) | c == s).fold(true, |acc, x| acc && x)
    }

    pub fn open_with_values(&self, cm: &Commitment, values: &[Scalar]) -> bool {
        let s_vec = &cm.internal_values;
        assert_eq!(s_vec.len(), values.len());

        s_vec.iter().zip(values.iter())
            .map(| (&c, &s) | c == s).fold(true, |acc, x| acc && x)
    }

    pub fn prove_eval(&self, poly: &UniPolynomial, u: &Scalar) -> (Scalar, EvalArgument) {
        let v = poly.evaluate(u);
        let (q, r) = poly.sub_scalar(&v).div_by_linear_divisor(u);
        assert_eq!(r, Scalar::zero());
        assert_eq!(q.evaluate(&(*u + Scalar::one())) * (*u + Scalar::one() - u), poly.evaluate(&(*u+Scalar::one())) - v);
        let cm_q = self.commit_uni_poly(&q);
        (v, EvalArgument{ commitment: cm_q })
    }

    // ([f]-v[1]) * 1 = [q] * ([τ] - u[1])
    // ([f] - [v] + u[q]) * [1] = [q] * [τ]
    pub fn verify_eval(&self, cm: &Commitment, u: &Scalar, v: &Scalar, prf: &EvalArgument) -> bool {
        let f_cm = cm.group_element.clone();
        let q_cm = prf.commitment.group_element.clone();
        let v_cm = self.srs.g.mul_scalar(v);
        let uq_cm = q_cm.mul_scalar(u);
        let lhs = pairing(&(f_cm.add(&v_cm, true).add(&uq_cm, false)), &self.srs.h);
        let rhs = pairing(&q_cm, &self.srs.h_tau);
        lhs == rhs
    }

    // pub fn prove(&self, polynomial: &FftUniPolynomial, x: &Scalar) -> (Scalar, EvalArgument) {
    //     let result = polynomial.evaluate(x);
    //     (result, EvalArgument{eval_at_x: result})
    // }

    // pub fn verify(&self, 
    //     cm: &Commitment, 
    //     eval_argument: &EvalArgument, 
    //     x: &Scalar,
    //     e: &Scalar,
    // ) -> bool {
    //     let coeffs = &cm.values;
    //     let poly = FftUniPolynomial::from_coeffs_fft(&coeffs);
    //     let result = poly.evaluate(x);
    //     result == *e && 
    //         result == eval_argument.eval_at_x
    // }

    // Prove that deg(f) < degree_bound
    // ([f(τ)] * [τ^{D-d-1}] = [f * τ^{D-d-1}] * [1]
    // NOTE: strictly less than 
    pub fn prove_degree_bound(&self, 
        f: &UniPolynomial,
        deg_bound: usize,
    ) -> DegreeBoundArgument {
        assert!(f.degree < deg_bound);
        let x_uni = UniPolynomial::from_coeffs(&{
            let mut coe = vec![Scalar::zero(); self.srs.max_degree - deg_bound - 1];
            coe.push(Scalar::one());
            coe
        });
        let fx_uni = f.mul(&x_uni);
        let fx_cm = self.commit_uni_poly(&fx_uni);
        DegreeBoundArgument {
            commitment: fx_cm,
            degree_bound: deg_bound,
            max_degree: self.srs.max_degree,
        }
    }

    // Verify that deg(f) < degree_bound
    // NOTE: strictly less than 
    pub fn verify_degree_bound(&self, 
        f_cm: &Commitment, 
        deg_bound: usize,
        deg_arg: &DegreeBoundArgument
    ) -> bool {
        assert_eq!(deg_arg.max_degree, self.srs.max_degree);

        let x_in_g2 = &self.srs.powers_over_G2[deg_arg.max_degree - deg_bound - 1];
        let fx_cm = &deg_arg.commitment;
        let lhs = pairing(&f_cm.group_element, x_in_g2);
        let rhs = pairing(&fx_cm.group_element, &self.srs.h);
        lhs == rhs
    }

    pub fn prove_eval_and_deg(&self, 
        f: &UniPolynomial,
        u: &Scalar,
        deg_bound: usize,
    ) -> (Scalar, EvalArgument, DegreeBoundArgument) {
        let (v, prf) = self.prove_eval(&f, &u);
        let deg_prf = self.prove_degree_bound(&f, deg_bound);
        (v, prf, deg_prf)
    }

    pub fn verify_eval_and_deg(&self, 
        f_cm: &Commitment, 
        u: &Scalar, 
        v: &Scalar, 
        deg_bound: usize,
        eval_prf: &EvalArgument, 
        deg_prf: &DegreeBoundArgument,
    ) -> bool {
        self.verify_eval(&f_cm, &u, &v, &eval_prf) && 
            self.verify_degree_bound(&f_cm, deg_bound, &deg_prf)
    }

    pub fn check_commitment(&self, cm: &Commitment, poly: &UniPolynomial) -> bool {
        let coeffs = &poly.coeffs;
        let s_vec = &cm.internal_values;
        coeffs.iter().zip(s_vec.iter())
            .map(| (&c, &s) | c == s).fold(true, |acc, x| acc && x)
    }
} 



mod tests {
    use crate::*;
    use super::*;

    #[test]
    fn test_kzg10_commit_open() {
        let mut rng = ark_std::test_rng();

        let coeffs = Scalar::from_usize_vector(&[2, 0, 1]);
        let f = UniPolynomial::from_coeffs(&coeffs);
        let kzg10_pcs = KZG10PCS::setup(100, &mut rng);
        let f_cm = kzg10_pcs.commit_uni_poly(&f);
        let b = kzg10_pcs.open_uni_poly(&f_cm, &f);
        assert!(b);
    }

    #[test]
    fn test_kzg10_eval_prove_verify() {
        let mut rng = ark_std::test_rng();

        // f(X) = 2* X^2 + 1
        // f(3) = 19

        let coeffs = Scalar::from_usize_vector(&[1, 0, 2]);
        let f = UniPolynomial::from_coeffs(&coeffs);
        let u = Scalar::from(3);
        println!("eval_at_0={}", f.evaluate(&(Scalar::from(0))));
        println!("eval_at_1={}", f.evaluate(&(Scalar::from(1))));
        println!("eval_at_2={}", f.evaluate(&(Scalar::from(2))));

        let kzg10_pcs = KZG10PCS::setup(100, &mut rng);
        let f_cm = kzg10_pcs.commit_uni_poly(&f);

        let (eval_at_u, eval_prf) = kzg10_pcs.prove_eval(&f, &u);
        println!("eval_at_u={}", ScalarExt::to_string(&eval_at_u));

        assert_eq!(eval_at_u, Scalar::from(19));
        let b = kzg10_pcs.verify_eval(&f_cm, &u, &eval_at_u, &eval_prf);
        assert!(b);
    }

    #[test]
    fn test_kzg10_degree_bound_prove_verify() {
        let mut rng = ark_std::test_rng();

        // f(X) = 2* X^2 + 1
        // f(3) = 19

        let coeffs = Scalar::from_usize_vector(&[1, 0, 2]);
        let f = UniPolynomial::from_coeffs(&coeffs);

        let kzg10_pcs = KZG10PCS::setup(100, &mut rng);
        let f_cm = kzg10_pcs.commit_uni_poly(&f);

        let deg_prf = kzg10_pcs.prove_degree_bound(&f, 3);
        let b = kzg10_pcs.verify_degree_bound(&f_cm, 3, &deg_prf);
        assert!(b);
    }
}

