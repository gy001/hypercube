use crate::*;
use ark_ff::Zero;
use ark_poly::domain;

pub struct UniPolynomial {
    pub degree: usize,
    pub domain_size: usize,
    pub evals: Vec<Scalar>,
    pub coeffs: Vec<Scalar>,
}

// NOTE: 
//   f(X) = f0 + f1*X + ... + fn*X^n
//   the coeffs vector is [fn, ..., f0]

// NOTE:
//   H = {0, 1, 2, ..., n-1}
//   the evaluation domain is H, i.e., the set of all integers from 0 to n-1
//   and `n` must be a power of 2

impl UniPolynomial {

    // NOTE: the domain_size parameter is important for the G(f0, f1, ..., fn) function
    //    domain_size = degree_bound + 1
    pub fn from_evals(evals: &[Scalar], domain_size: usize) -> Self {
        assert_eq!(evals.len(), domain_size);
        let mut coeffs = UniPolynomial::lagrange_interpolation(evals);
        let degree: usize = {
            let mut deg = evals.len() - 1;
            for c in coeffs.iter() {
                if c.is_zero() {
                    deg -= 1;
                } else {
                    break;
                }
            };
            deg
        };

        UniPolynomial {
            degree: degree,
            domain_size: domain_size,
            evals: evals.to_vec(),
            coeffs: coeffs,
        }
    }

    pub fn from_coeffs(coeffs: &[Scalar], domain_size: usize) -> Self {
        assert!(coeffs.len() <= domain_size);
        assert!(domain_size.is_power_of_two());
        let mut normalized_coeffs = vec![Scalar::zero(); domain_size - coeffs.len()];
        normalized_coeffs.extend(coeffs);
        let evals = UniPolynomial::evaluation(coeffs, domain_size);

        let degree: usize = {
            let mut deg = coeffs.len() - 1;
            for c in coeffs.iter() {
                if c.is_zero() {
                    deg -= 1;
                } else {
                    break;
                }
            };
            deg
        };

        UniPolynomial {
            degree: degree,
            domain_size: domain_size,
            evals: evals,
            coeffs: normalized_coeffs.to_vec(),
        }
    }

    pub fn degree(&self) -> usize {
        self.coeffs.len() - 1
    }

    pub fn coeffs(&self) -> Vec<Scalar> {
        self.coeffs.clone()
    }

    pub fn lagrange_interpolation(evals: &[Scalar]) -> Vec<Scalar> {
        let n = evals.len();
        let mut coeffs = vec![Scalar::zero(); n];

        for i in 0..n {
            let mut c_vec = vec![Scalar::zero(); n];
            c_vec[0] = Scalar::from(1);

            let x_vec: Vec<Scalar> = (0..n)
                .filter(|&k| k != i)
                .map(|i| Scalar::from(i as u64))
                .collect();

            for j in 1..n {
                for k in (0..j).rev() {
                    c_vec[k + 1] = c_vec[k + 1] - c_vec[k] * (x_vec[j - 1]);
                }
            }

            // compute (1/w_i): inversion of barycentric-weights
            let denom = (0..n).filter(|&k| k != i).fold(Scalar::from(1), |acc, k| {
                acc * (Scalar::from(i as u64) - Scalar::from(k as u64))
            });

            for k in 0..n {
                coeffs[k] += evals[i] * c_vec[k] / denom;
            }
        }
        coeffs
    }

    pub fn evaluation(coeffs: &[Scalar], domain_size: usize) -> Vec<Scalar> {
        assert!(domain_size.is_power_of_two());

        let mut evals = vec![Scalar::zero(); domain_size];

        for i in 0..domain_size {
            evals[i] = Self::evaluate_from_coeffs(coeffs, &Scalar::from_usize(i));
        }
        evals
    }

    pub fn barycentric_weights(n: usize) -> Vec<Scalar> {
        let x_vec: Vec<Scalar> = (0..n).map(|i| Scalar::from(i as u64)).collect();
        let mut weights: Vec<Scalar> = vec![Scalar::zero(); n];
        for i in 0..n {
            let xi = x_vec[i];
            let prod = (0..n).fold(Scalar::from(1), |acc, j| {
                acc * if i == j {
                    Scalar::from(1)
                } else {
                    xi - x_vec[j]
                }
            });
            weights[i] = Scalar::from(1) / prod;
        }
        weights
    }

    pub fn evaluate_from_evals(evals: &[Scalar], x: &Scalar) -> Scalar {
        let n = evals.len();

        let mut is_domain = false;
        let mut result = Scalar::from(0);
        for i in 0..n {
            if Scalar::from(i as u64) == *x {
                is_domain = true;
                result = evals[i];
                break;
            } 
        }
        if is_domain {
            result
        } else {
            let weights = UniPolynomial::barycentric_weights(n);
            // assert!(*x != Scalar::from(0));

            let w_vec: Vec<Scalar> = (0..n)
                .map(|i| weights[i] / (*x - Scalar::from(i as u64)))
                .collect();

            let (numinator, denominator) = w_vec.iter().enumerate().fold(
                (Scalar::from(0), Scalar::from(0)),
                |(numinator, denominator), (i, &w)| (numinator + w * evals[i], denominator + w),
            );
            numinator / denominator
        }
    }

    pub fn evaluate_from_coeffs(coeffs: &[Scalar], x: &Scalar) -> Scalar {
        let (acc, _) =
            coeffs
                .iter()
                .rev()
                .fold((Scalar::from(0), Scalar::from(1)), |acc, coeff| {
                    let term: Scalar = acc.0 + acc.1 * coeff;
                    let monomial: Scalar = acc.1 * *x;
                    (term, monomial)
                });
        acc
    }

    pub fn evaluate(&self, x: &Scalar) -> Scalar {
        Self::evaluate_from_coeffs(&self.coeffs, x)
    }
}

mod tests {
    use crate::*;
    use super::UniPolynomial;

    #[test]
    fn test_interpolation() {
        let evals: Vec<Scalar> = Scalar::from_usize_vector(&[2, 3, 2, 3]);
        let coeffs: Vec<Scalar> = UniPolynomial::lagrange_interpolation(&evals);
        for i in 0..4 {
            let eval_at_i = UniPolynomial::evaluate_from_coeffs(&coeffs, &Scalar::from_usize(i));
            assert_eq!(eval_at_i, evals[i], "eval failed at");
        }
    }

    #[test]
    fn test_interpolation_again() {
        let evals: Vec<Scalar> = Scalar::from_usize_vector(&[99, 12, 3, 17, 18, 19, 32, 1]);
        let coeffs: Vec<Scalar> = UniPolynomial::lagrange_interpolation(&evals);
        for i in 0..8 {
            let eval_at_i = UniPolynomial::evaluate_from_coeffs(&coeffs, &Scalar::from_usize(i));
            assert_eq!(eval_at_i, evals[i], "eval failed at");
        }
    }

    #[test]
    fn test_interp_eval_degree_16_rep_1000() {

        let rng = &mut ark_std::test_rng();

        for i in 0..1000 {
            let evals: Vec<Scalar> = Scalar::rand_vector(16, rng);

            let coeffs: Vec<Scalar> = UniPolynomial::lagrange_interpolation(&evals);
    
            let rand = Scalar::rand(rng);
    
            let eval_at_rand = UniPolynomial::evaluate_from_coeffs(&coeffs, &rand);
            let eval_at_rand_prime = UniPolynomial::evaluate_from_evals(&evals, &rand);

            assert_eq!(eval_at_rand, eval_at_rand_prime, "test failed in round {}", i);
        }

    }

    #[test]
    fn test_interp_eval_degree_128_rep_10() {

        let rng = &mut ark_std::test_rng();

        for i in 0..10 {
            let evals: Vec<Scalar> = Scalar::rand_vector(128, rng);

            let coeffs: Vec<Scalar> = UniPolynomial::lagrange_interpolation(&evals);
    
            let rand = Scalar::rand(rng);
    
            let eval_at_rand = UniPolynomial::evaluate_from_coeffs(&coeffs, &rand);
            let eval_at_rand_prime = UniPolynomial::evaluate_from_evals(&evals, &rand);

            assert_eq!(eval_at_rand, eval_at_rand_prime, "test failed in round {}", i);
        }
    }

    #[test]
    fn test_new_from_evals() {
        // f(X) = X + 1
        let domain_size = 8;
        let evals: Vec<Scalar> = Scalar::from_usize_vector(&[1, 2, 3, 4, 5, 6, 7, 8]);
        let f = UniPolynomial::from_evals(&evals, 8);

        assert_eq!(f.degree, 1);
        assert_eq!(f.coeffs[7], Scalar::from(1));
        assert_eq!(f.coeffs[6], Scalar::from(1));
    }

    #[test]
    fn test_new_from_coeffs() {
        // f(X) = X^2 + 1
        let domain_size = 8;
        let coeffs: Vec<Scalar> = Scalar::from_usize_vector(&[0, 0, 0, 0, 0, 1, 0, 1]);
        let f = UniPolynomial::from_coeffs(&coeffs, 8);

        assert_eq!(f.degree, 2);
        assert_eq!(f.evals[7], Scalar::from(50));
        assert_eq!(f.evals[6], Scalar::from(37));
        assert_eq!(f.evals[0], Scalar::from(1));

        // let rng = &mut ark_std::test_rng();
        // let x = Scalar::rand(rng);
    }

    #[test]
    fn test_new_from_coeffs_again() {
        // f(X) = X^2 + 1
        let domain_size = 8;
        let coeffs: Vec<Scalar> = Scalar::from_usize_vector(&[2, 0, 1]);
        let f = UniPolynomial::from_coeffs(&coeffs, 8);

        assert_eq!(f.degree, 2);
        println!("f.evals={}", scalar_vector_to_string(&f.evals));
        println!("f.coeffs={}", scalar_vector_to_string(&f.coeffs));

        // let rng = &mut ark_std::test_rng();
        // let x = Scalar::rand(rng);
    }

}
