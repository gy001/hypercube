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

// fft/ifft polynomials over smooth domain (multiplicative subgroup)

// NOTE: 
//   f(X) = f0 + f1*X + ... + fn*X^n
//   the coeffs vector is [f0, ..., fn]

// NOTE:
//   H = {1, w, w^2, ..., w^{n-1}}
//   the evaluation domain is H, i.e., multiplicative subgroup of Fp
//   and `n` must be a power of 2

impl UniPolynomial {

    pub fn from_coeffs_fft(coeffs: &[Scalar], domain_size: usize) -> Self {
        assert!(coeffs.len() <= domain_size);
        assert!(domain_size.is_power_of_two());
        let mut padded_zeros = vec![Scalar::zero(); domain_size - coeffs.len()];
        let mut coeffs = coeffs.to_vec();
        coeffs.extend(padded_zeros);
        let coeffs0 = coeffs.clone();

        Self::ntt_evals_from_coeffs(&mut coeffs, log_2(domain_size));
        let evals = coeffs;
    
        let degree: usize = {
            let mut deg = coeffs0.len() - 1;
            for c in coeffs0.iter().rev() {
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
                coeffs: coeffs0,
        }
    }

    pub fn from_evals_fft(evals: &[Scalar], domain_size: usize) -> Self {
        assert_eq!(evals.len(), domain_size);
        assert!(domain_size.is_power_of_two());
        let mut evals = evals.to_vec();
        let evals0 = evals.clone();

        Self::ntt_coeffs_from_evals(&mut evals, log_2(domain_size));
        let coeffs = evals;
    
        let degree: usize = {
            let mut deg = coeffs.len() - 1;
            for c in coeffs.iter().rev() {
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
                evals: evals0,
                coeffs: coeffs,
        }
    }

    pub fn multiplicative_generator() -> Scalar {
        Scalar::multiplicative_generator()
    }

    // Compute the nth-omega from g^{(p-1)/2^k} 
    pub fn get_root_of_unity(k_log_size: usize) -> Scalar {
        let g = Scalar::multiplicative_generator();
        let order = -Scalar::one();
        let cofactor = order / Scalar::from((2 as u64).pow(k_log_size as u32));
        let omega = g.pow(cofactor.into_repr());
        assert_eq!(g.pow(order.into_repr()), Scalar::one());

        // double check
        // let omega_pow_k = omega.pow(&[k_log_size as u64,0,0,0]);
        // assert_eq!(omega_pow_k, Scalar::one());

        omega
    }

    // Compute the domain from omega
    pub fn fft_domain(k_log_size: usize) -> Vec<Scalar> {
        let omega = Self::get_root_of_unity(k_log_size);
        let size = (2 as u64).pow(k_log_size as u32) as usize;
        let mut domain = vec![Scalar::one(); size];
        for i in 1..size {
            domain[i] = omega * domain[i-1];
        }
        domain
    }

    pub fn ifft_domain(k_log_size: usize) -> Vec<Scalar> {
        let omega = Self::get_root_of_unity(k_log_size);
        let omega_inv = omega.inverse().unwrap();

        let size = (2 as u64).pow(k_log_size as u32) as usize;
        let mut domain = vec![Scalar::one(); size];
        for i in 1..size {
            domain[i] = omega_inv * domain[i-1];
        }
        domain
    }

    fn ntt_core(coeffs: &mut Vec<Scalar>, omega: &Scalar, k_log_size: usize) {
        let len = coeffs.len();
        let domain_size = (2 as u64).pow(k_log_size as u32) as usize;

        assert_eq!(len, domain_size);

        // bit-reversing
        for k in 0..domain_size {
            let k_rev = bit_reverse(k, k_log_size);
            if k < k_rev {
                coeffs.swap(k, k_rev);
            }
        }

        let mut sep = 1;
        for _ in 0..k_log_size {
            let mut w = Scalar::one();
            for j in 0..sep {
                for i in (0..domain_size).step_by(2*sep) {
                    let l = i + j;
                    let r = i + j + sep;
                    let tmp = coeffs[r] * w;
                    coeffs[r] = coeffs[l] - tmp;
                    coeffs[l] = coeffs[l] + tmp;
                }
                w = w * omega.exp(domain_size / (2*sep));
            }
            sep *= 2;
        }
    }

    pub fn ntt_evals_from_coeffs(coeffs: &mut Vec<Scalar>, k_log_size: usize) {
        let omega = Self::get_root_of_unity(k_log_size);
        Self::ntt_core(coeffs, &omega, k_log_size);
    }

    pub fn ntt_coeffs_from_evals(evals: &mut Vec<Scalar>, k_log_size: usize) {
        let omega = Self::get_root_of_unity(k_log_size);
        let omega_inv = omega.inverse().unwrap();
        let domain_size: u64 = (2 as u64).pow(k_log_size as u32);
        let domain_size_inv = Scalar::from(domain_size).inverse().unwrap();
        Self::ntt_core(evals, &omega_inv, k_log_size);
        evals.iter_mut().for_each(|e| *e = *e * domain_size_inv);
    }

    // compute evaluations in O(n^2)
    pub fn ntt_evals_from_coeffs_slow(coeffs: &Vec<Scalar>, k_log_size: usize) -> Vec<Scalar>{
        let len = coeffs.len();
        let domain_size = (2 as u64).pow(k_log_size as u32) as usize;
        assert_eq!(len, domain_size);

        // Compute domain = {omega^i}
        let domain = Self::fft_domain(k_log_size);
        
        // initialize evals to zero
        let mut evals = vec![Scalar::zero(); domain_size];

        for i in 0..domain_size {
            let mut acc = Scalar::zero();
            for j in 0..domain_size {
                let omega_pow_ij = domain[i].pow(&[j as u64,0,0,0]);
                acc = acc + coeffs[j] * omega_pow_ij;
            }
            evals[i] = acc;
        }
        evals
    }

    pub fn division(dividend: &[Scalar], divisor: &[Scalar]) -> (Vec<Scalar>, Vec<Scalar>) {
        let mut quotient = vec![Scalar::zero(); dividend.len() - divisor.len() + 1];
        let mut remainder = dividend.to_vec();
    
        for i in (0..quotient.len()).rev() {
            quotient[i] = remainder[i + divisor.len() - 1] / divisor[divisor.len() - 1];
            for j in 0..divisor.len() {
                remainder[i + j] -= quotient[i] * divisor[j];
            }
        }
    
        // Remove leading zeros from remainder
        while remainder.len() > 1 && remainder[remainder.len() - 1] == Scalar::zero() {
            remainder.pop();
        }
    
        (quotient, remainder)
    }

}

mod tests {
    use crate::*;
    use super::*;

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
    }

    #[test]
    fn test_get_root_of_unity_8() {
        let omega = UniPolynomial::get_root_of_unity(3);
        let mut acc = Scalar::one();
        for i in 0..16 {
            acc = acc * omega;
            println!("omega_{}={}", i, ScalarExt::to_string(&acc));
        }

        println!("omega^2={}", ScalarExt::to_string(&(omega*omega)));

        let mut p = scalar_modulus();
        p.div2();
        p.div2();
        p.div2();
        let omega_prime = Scalar::multiplicative_generator().pow(p);
        println!("omega_prime={}", ScalarExt::to_string(&omega_prime));
        let mut acc = Scalar::one();
        for i in 0..8 {
            acc = omega_prime * acc;
            println!("omega_prime_pow_{}={}", i, ScalarExt::to_string(&acc));
        }

    }   


    #[test]
    fn test_get_root_of_unity_16() {
        let omega = UniPolynomial::get_root_of_unity(4);
        println!("omega={}", ScalarExt::to_string(&omega));
        for i in 0..=16 {
            println!("omega_pow_{}={}", i, ScalarExt::to_string(&omega.pow(&[i as u64,0,0,0])));
        }
    }

    #[test]
    fn test_get_root_of_unity_1m() {
        let omega = UniPolynomial::get_root_of_unity(20);
        println!("omega={}", ScalarExt::to_string(&omega));
        let omega_pow_1m = omega.pow(&[(2 as u64).pow(20),0,0,0]);
        println!("omega_pow_1m={}", ScalarExt::to_string(&omega_pow_1m));
    }

    #[test]
    fn test_ntt_evals_from_coeffs_naive() {
        let mut coeffs = Scalar::from_usize_vector(&[0,1,0,0]);
        println!("origin coeffs={}", scalar_vector_to_string(&coeffs));
        UniPolynomial::ntt_evals_from_coeffs(&mut coeffs, 2);        
        println!("evals={}", scalar_vector_to_string(&coeffs));
    }

    #[test] 
    fn test_ntt_evals_from_coeffs() {
        let mut coeffs = Scalar::from_usize_vector(&[1,2,3,4,5,6,7,8]);
        let k = 3;
        let evals = UniPolynomial::ntt_evals_from_coeffs_slow(&coeffs, k);
        UniPolynomial::ntt_evals_from_coeffs(&mut coeffs, k);
        assert_eq!(coeffs, evals);
    }

    #[test]
    fn test_fft_domain() {
        let domain = UniPolynomial::fft_domain(3);
        println!("domain={}", scalar_vector_to_string(&domain));
        
        let len = domain.len();
        let omega = domain[1];
        for i in 0..=len {
            println!("omega_pow_{}={}", i, ScalarExt::to_string(&omega.pow(&[i as u64,0,0,0])));
        }

        let mut acc = Scalar::one();
        for i in 0..8 {
            acc = acc * omega;
            println!("omega_{}={}", i, ScalarExt::to_string(&acc));
        }

        assert_eq!(acc, Scalar::one());
    }

    #[test] 
    fn test_ntt_core() {
        let mut coeffs = Scalar::from_usize_vector(&[1,2,3,4,5,6,7,8]);
        let k = 3;
        let coeffs0 = coeffs.clone();
        println!("coeffs={}", scalar_vector_to_string(&coeffs));

        UniPolynomial::ntt_evals_from_coeffs(&mut coeffs, k);
        println!("evals={}", scalar_vector_to_string(&coeffs));

        UniPolynomial::ntt_coeffs_from_evals(&mut coeffs, k);
        println!("coeffs={}", scalar_vector_to_string(&coeffs));

        assert_eq!(coeffs, coeffs0);
    }

    #[test]
    fn test_division() {
        let dividend = vec![5, 3, 2, 1].into_iter().map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let divisor = vec![2, 1].into_iter().map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let (quotient, remainder) = UniPolynomial::division(&dividend, &divisor);
        println!("quotient={}", scalar_vector_to_string(&quotient));
        println!("remainder={}", scalar_vector_to_string(&remainder));

        assert_eq!(quotient, vec![Scalar::from(3), Scalar::from(0), Scalar::from(1)]);
        assert_eq!(remainder, vec![Scalar::from(-1)]);
    }

    #[test]
    fn test_division_2() {
        let dividend = vec![3, 0, 1].into_iter().map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let divisor = vec![1, 1].into_iter().map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let (quotient, remainder) = UniPolynomial::division(&dividend, &divisor);
        println!("quotient={}", scalar_vector_to_string(&quotient));
        println!("remainder={}", scalar_vector_to_string(&remainder));
        
        assert_eq!(quotient, vec![Scalar::from(-1), Scalar::from(1)]);
        assert_eq!(remainder, vec![Scalar::from(4)]);
    }
}
