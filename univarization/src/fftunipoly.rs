
use crate::*;

// fft/ifft polynomials over smooth domain (multiplicative subgroup)

#[derive(Debug, Clone)]
pub struct FftUniPolynomial {
    pub degree: usize,
    pub coeffs: Vec<Scalar>,
}

// NOTE: 
//   f(X) = f0 + f1*X + ... + fn*X^n
//   the coeffs vector is [f0, ..., fn]

// NOTE:
//   H = {1, w, w^2, ..., w^{n-1}}
//   the evaluation domain is H, i.e., multiplicative subgroup of Fp
//   and `n` must be a power of 2
impl FftUniPolynomial {

    pub fn zero_polynomial() -> Self {
        Self {
            degree: 0,
            coeffs: vec![Scalar::zero()],
        }
    }

    pub fn is_zero(&self) -> bool {
        self.degree == 0 && self.coeffs[0].is_zero()
    }

    pub fn from_coeffs_fft(coeffs: &[Scalar]) -> Self {
        // assert!(coeffs.len() <= domain_size);
        // assert!(domain_size.is_power_of_two());
        // let mut padded_zeros = vec![Scalar::zero(); domain_size - coeffs.len()];
        // let mut coeffs = coeffs.to_vec();
        // coeffs.extend(padded_zeros);
        let mut coeffs = coeffs.to_vec();

        // Self::ntt_evals_from_coeffs(&mut coeffs, log_2(domain_size));
        // let evals = coeffs;
            
        // Remove leading zeros from result
        while coeffs.len() > 1 && coeffs[coeffs.len() - 1] == Scalar::zero() {
            coeffs.pop();
        }
    
        Self {
            degree: coeffs.len() - 1,
            coeffs: coeffs,
        }
    }

    pub fn from_evals_fft(evals: &[Scalar], domain_size: usize) -> Self {
        assert_eq!(evals.len(), domain_size);
        assert!(domain_size.is_power_of_two());
        let mut evals = evals.to_vec();

        let mut coeffs = Self::ntt_coeffs_from_evals(&evals, log_2(domain_size));
    
        // let degree: usize = {
        //     let mut deg = coeffs.len() - 1;
        //     for c in coeffs.iter().rev() {
        //         if c.is_zero() && deg > 0 {
        //             deg -= 1;
        //         } else {
        //             break;
        //         }
        //     };
        //     deg
        // };

        // Remove leading zeros from result
        while coeffs.len() > 1 && coeffs[coeffs.len() - 1] == Scalar::zero() {
            coeffs.pop();
        }

        Self {
                degree: coeffs.len()-1,
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

    pub fn vanishing_polynomial(domain_size: usize) -> Self {
        assert!(domain_size.is_power_of_two());

        let mut coeffs = vec![Scalar::zero(); domain_size + 1];
        coeffs[0] = -Scalar::one();
        coeffs[domain_size] = Scalar::one();
        Self { 
            degree: domain_size,
            coeffs: coeffs,
        }
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

    pub fn ntt_evals_from_coeffs(coeffs: &[Scalar], k_log_size: usize) -> Vec<Scalar> {
        let mut coeffs = coeffs.to_vec();
        let omega = Self::get_root_of_unity(k_log_size);
        Self::ntt_core(&mut coeffs, &omega, k_log_size);
        coeffs
    }

    pub fn ntt_coeffs_from_evals(evals: &[Scalar], k_log_size: usize) -> Vec<Scalar> {

        let mut evals = evals.to_vec();
        let omega = Self::get_root_of_unity(k_log_size);
        let omega_inv = omega.inverse().unwrap();
        let domain_size: u64 = (2 as u64).pow(k_log_size as u32);
        let domain_size_inv = Scalar::from(domain_size).inverse().unwrap();
        Self::ntt_core(&mut evals, &omega_inv, k_log_size);
        evals.iter_mut().for_each(|e| *e = *e * domain_size_inv);
        evals
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

    pub fn evaluate(&self, x: &Scalar) -> Scalar {
        let mut acc = Scalar::zero();
        for i in 0..=self.degree {
            acc = acc + self.coeffs[i] * x.pow(&[i as u64,0,0,0]);
        }
        acc
    }

    pub fn evaluations(&self) -> Vec<Scalar> {
        let mut coeffs = self.coeffs.clone();
        let domain_size = if coeffs.len().is_power_of_two() {
            coeffs.len()
        } else {
            coeffs.len().next_power_of_two()
        };

        let zeros = vec![Scalar::zero(); domain_size - coeffs.len()];
        coeffs.extend(zeros);

        Self::ntt_evals_from_coeffs(&mut coeffs, log_2(domain_size))
    }

    pub fn evaluations_over_domain(&self, domain_size: usize) -> Vec<Scalar> {

        let domain = Self::fft_domain(log_2(domain_size));
        domain.iter().map(|w| self.evaluate(w)).collect()
    }

    fn multiplication(poly1: &[Scalar], poly2: &[Scalar]) -> Vec<Scalar> {
        let mut result = vec![Scalar::zero(); poly1.len() + poly2.len() - 1];
    
        for i in 0..poly1.len() {
            for j in 0..poly2.len() {
                result[i + j] += poly1[i] * poly2[j];
            }
        }
    
        result
    }

    pub fn multiply(&self, poly2: &Self) -> Self {

        let coeffs_1 = &self.coeffs;
        let coeffs_2 = &poly2.coeffs;
        let mut coeffs_m = Self::multiplication(coeffs_1, coeffs_2);

        let degree = &self.degree + &poly2.degree;

        Self {
            degree: degree,
            coeffs: coeffs_m,
        }
    }

    // support addition and subtraction
    // f1.add(&f2, false) = f1 + f2
    // f1.add(&f2, true) = f1 - f2

    pub fn add(&self, poly2: &Self, neg: bool) -> Self {

        let len1 = self.coeffs.len();
        let len2 = poly2.coeffs.len();
        let len_a = std::cmp::max(self.coeffs.len(), poly2.coeffs.len());
        let mut coeffs_a = vec![Scalar::zero(); len_a];

        for i in 0..coeffs_a.len() {
            let coeff1 = if i < len1 { self.coeffs[i] } else { Scalar::zero() };
            let coeff2 = if i < len2 { poly2.coeffs[i] } else { Scalar::zero() };
            if neg {
                coeffs_a[i] = coeff1 - coeff2;
            } else {
                coeffs_a[i] = coeff1 + coeff2;
            }
        }

        // Remove leading zeros from result
        while coeffs_a.len() > 1 && coeffs_a[coeffs_a.len() - 1] == Scalar::zero() {
            coeffs_a.pop();
        }

        let mut degree_a = std::cmp::max(self.degree, poly2.degree);
        let mut idx = degree_a;
        println!("coeffs_a={}", scalar_vector_to_string(&coeffs_a));

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }

    pub fn add_constant(&self, v: &Scalar, neg: bool) -> Self {

        let len1 = self.coeffs.len();
        let len_a = std::cmp::max(self.coeffs.len(), 1);
        let mut coeffs_a = self.coeffs.clone();

        if neg {
            coeffs_a[0] -= v;
        } else {
            coeffs_a[0] += v;
        }

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }

    pub fn mul_constant(&self, a: &Scalar) -> Self {

        let mut coeffs_a = self.coeffs.clone();

        for i in 0..coeffs_a.len() {
            coeffs_a[i] *= a;
        }

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }

    pub fn shift(&self, a: &Scalar) -> Self {

        let mut coeffs_a = self.coeffs.clone();

        let mut acc = Scalar::one();
        for i in 0..coeffs_a.len() {
            coeffs_a[i] *= acc;
            acc *= a;
        }

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }

    fn division(dividend: &[Scalar], divisor: &[Scalar]) -> (Vec<Scalar>, Vec<Scalar>) {
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

    // only support division in the same domain_size
    pub fn div(&self, divisor_poly: &Self) -> (Self, Self) {
        assert!(divisor_poly.degree > 0);

        let mut dividend = self.coeffs.clone();
        dividend.truncate(self.degree + 1);
        let mut divisor = divisor_poly.coeffs.clone();
        divisor.truncate(divisor_poly.degree + 1);

        let (quotient, remainder) = Self::division(&dividend, &divisor);

        let quotient_degree = self.degree - divisor_poly.degree;
        assert_eq!(quotient_degree, quotient.len()-1);

        (Self {
            degree: quotient_degree,
            coeffs: quotient,
        },
        Self {
            degree: remainder.len() - 1,
            coeffs: remainder,
        })
    }

}

mod tests {
    use crate::{*, mle::EqPolynomial};
    use super::*;

    #[test]
    fn test_get_root_of_unity_8() {
        let omega = FftUniPolynomial::get_root_of_unity(3);
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
        let omega = FftUniPolynomial::get_root_of_unity(4);
        println!("omega={}", ScalarExt::to_string(&omega));
        for i in 0..=16 {
            println!("omega_pow_{}={}", i, ScalarExt::to_string(&omega.pow(&[i as u64,0,0,0])));
        }
    }

    #[test]
    fn test_get_root_of_unity_1m() {
        let omega = FftUniPolynomial::get_root_of_unity(20);
        println!("omega={}", ScalarExt::to_string(&omega));
        let omega_pow_1m = omega.pow(&[(2 as u64).pow(20),0,0,0]);
        println!("omega_pow_1m={}", ScalarExt::to_string(&omega_pow_1m));
    }

    #[test]
    fn test_ntt_evals_from_coeffs_naive() {
        let mut coeffs = Scalar::from_usize_vector(&[0,1,0,0]);
        println!("origin coeffs={}", scalar_vector_to_string(&coeffs));
        FftUniPolynomial::ntt_evals_from_coeffs(&mut coeffs, 2);        
        println!("evals={}", scalar_vector_to_string(&coeffs));
    }

    #[test] 
    fn test_ntt_evals_from_coeffs() {
        let mut coeffs = Scalar::from_usize_vector(&[1,2,3,4,5,6,7,8]);
        let k = 3;
        let evals1 = FftUniPolynomial::ntt_evals_from_coeffs_slow(&coeffs, k);
        let evals2 = FftUniPolynomial::ntt_evals_from_coeffs(&mut coeffs, k);
        assert_eq!(evals1, evals2);
    }

    #[test]
    fn test_fft_domain() {
        let domain = FftUniPolynomial::fft_domain(3);
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

        FftUniPolynomial::ntt_evals_from_coeffs(&mut coeffs, k);
        println!("evals={}", scalar_vector_to_string(&coeffs));

        FftUniPolynomial::ntt_coeffs_from_evals(&mut coeffs, k);
        println!("coeffs={}", scalar_vector_to_string(&coeffs));

        assert_eq!(coeffs, coeffs0);
    }

    #[test] 
    fn test_ntt_core_2() {
        let mut evals = Scalar::from_usize_vector(&[0,0,0,0,5,6,7,8]);
        let k = 3;
        let evals0 = evals.clone();
        println!("evals0={}", scalar_vector_to_string(&evals0));
        let coeffs = FftUniPolynomial::ntt_coeffs_from_evals(&evals, k);
        println!("coeffs={}", scalar_vector_to_string(&coeffs));

        let evals1 = FftUniPolynomial::ntt_evals_from_coeffs(&coeffs, k);
        println!("evals1={}", scalar_vector_to_string(&evals1));


        // assert_eq!(coeffs, coeffs0);
    }

    #[test]
    fn test_division() {
        let dividend = vec![5, 3, 2, 1].into_iter().map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let divisor = vec![2, 1].into_iter().map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let (quotient, remainder) = FftUniPolynomial::division(&dividend, &divisor);
        println!("quotient={}", scalar_vector_to_string(&quotient));
        println!("remainder={}", scalar_vector_to_string(&remainder));

        // assert_eq!(quotient, vec![Scalar::from(2), Scalar::from(1)]);
        // assert_eq!(remainder, vec![Scalar::from(1)]);
    }

    #[test]
    fn test_division_2() {
        let dividend = vec![3, 0, 1].into_iter().map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let divisor = vec![1, 1].into_iter().map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let (quotient, remainder) = FftUniPolynomial::division(&dividend, &divisor);
        println!("quotient={}", scalar_vector_to_string(&quotient));
        println!("remainder={}", scalar_vector_to_string(&remainder));
        
        // assert_eq!(quotient, vec![Scalar::from(2), Scalar::from(1)]);
        // assert_eq!(remainder, vec![Scalar::from(1)]);
    }

    #[test]
    fn test_multiply() {
        let f1 = Scalar::from_i64_vector(&vec![1, 2]);
        let f2 = Scalar::from_i64_vector(&vec![-1, 2]);

        let f1_poly = FftUniPolynomial::from_coeffs_fft(&f1);
        let f2_poly = FftUniPolynomial::from_coeffs_fft(&f2);

        let f3_poly = f1_poly.multiply(&f2_poly);
        println!("f3_evals={}", scalar_vector_to_string(&f3_poly.evaluations()));
        println!("f3_coeffs={}", scalar_vector_to_string(&f3_poly.coeffs));
        assert_eq!(f3_poly.coeffs, Scalar::from_i64_vector(&vec![-1, 0, 4]));
        assert_eq!(f3_poly.degree, 2);
    }

    #[test]
    fn test_multiply_2() {
        let f1 = Scalar::from_i64_vector(&vec![1, 0, 1]);
        let f2 = Scalar::from_i64_vector(&vec![-1, 0, 1]);

        let f1_poly = FftUniPolynomial::from_coeffs_fft(&f1);
        let f2_poly = FftUniPolynomial::from_coeffs_fft(&f2);

        let f3_poly = f1_poly.multiply(&f2_poly);
        println!("f3_evals={}", scalar_vector_to_string(&f3_poly.evaluations()));
        println!("f3_coeffs={}", scalar_vector_to_string(&f3_poly.coeffs));
        // assert_eq!(f3_poly.coeffs, Scalar::from_i64_vector(&vec![-1, 0, 4, 0]));
        assert_eq!(f3_poly.degree, 4);
    }

    #[test]
    fn test_add_0() {
        let f1 = Scalar::from_i64_vector(&vec![1, 0, 1]);
        let f2 = Scalar::from_i64_vector(&vec![-1, 0, 1]);

        let f1_poly = FftUniPolynomial::from_coeffs_fft(&f1);
        let f2_poly = FftUniPolynomial::from_coeffs_fft(&f2);

        let f3_poly = f1_poly.add(&f2_poly, false);
        println!("f3_evals={}", scalar_vector_to_string(&f3_poly.evaluations()));
        println!("f3_coeffs={}", scalar_vector_to_string(&f3_poly.coeffs));

        println!("f1.degree={}", f1_poly.degree);
        println!("f2.degree={}", f2_poly.degree);
        // assert_eq!(f3_poly.coeffs, Scalar::from_i64_vector(&vec![-1, 0, 4, 0]));
        assert_eq!(f3_poly.degree, 2);

        let f4_poly = f1_poly.add(&f2_poly, true);
        println!("f4_evals={}", scalar_vector_to_string(&f3_poly.evaluations()));
        println!("f4_coeffs={}", scalar_vector_to_string(&f3_poly.coeffs));
        assert_eq!(f4_poly.degree, 0);
    }

    #[test]
    fn test_vanishing_polynomial() {
        let z_poly = FftUniPolynomial::vanishing_polynomial(4);
        println!("z_poly.coeffs={}", scalar_vector_to_string(&z_poly.coeffs));
        println!("z_poly.evals={}", scalar_vector_to_string(&z_poly.evaluations()));
    }

    #[test]
    fn test_shift() {
        let f_vec = Scalar::from_i64_vector(&vec![1, 2, 3, 4]);
        let f_poly = FftUniPolynomial::from_evals_fft(&f_vec, 4);
        let omega = FftUniPolynomial::get_root_of_unity(2);
        let f_prime_poly = f_poly.shift(&omega);
        println!("f_prime_poly.evals={}", scalar_vector_to_string(&f_prime_poly.evaluations()));

    }

    #[test]
    fn test_div() { // test for logup

        let rng = &mut ark_std::test_rng();
        let n: usize = 3;
        let x_vec = Scalar::from_i64_vector(&vec![1, 2, 3]);
        let c_vec = EqPolynomial::new(&x_vec).evals_over_hypercube();
        println!("c_vec={}", scalar_vector_to_string(&c_vec));

        let c_poly = FftUniPolynomial::from_evals_fft(&c_vec, 8);
        println!("c_poly.evals={}", scalar_vector_to_string(&c_poly.evaluations()));
        let zH_poly = FftUniPolynomial::vanishing_polynomial(8);
        let (s0_poly, r_poly) = zH_poly.div(&FftUniPolynomial::vanishing_polynomial(1));
        println!("s0_poly.coeffs={}", scalar_vector_to_string(&s0_poly.coeffs));
        println!("r_poly.coeffs={}", scalar_vector_to_string(&r_poly.coeffs));
        println!("s0_poly.evals={}", scalar_vector_to_string(&s0_poly.evaluations()));

        let f0_poly = c_poly.add_constant(&c_vec[0], true);
        println!("f1_poly.evals={}", scalar_vector_to_string(&f0_poly.evaluations()));
        let p_poly = s0_poly.multiply(&f0_poly);
        println!("p_poly.evals={}", scalar_vector_to_string(&p_poly.evaluations_over_domain(8)));

        let (q0_poly, r0_poly) = p_poly.div(&zH_poly);
        println!("r0_poly.coeffs={}", scalar_vector_to_string(&r0_poly.coeffs));
        let zeta = Scalar::rand(rng);
        assert_eq!(p_poly.evaluate(&zeta), q0_poly.evaluate(&zeta) * zH_poly.evaluate(&zeta));

        let mut k: usize = 1;
        let domain_k = (2 as u32).pow(k as u32) as usize;
        let omega_1 = FftUniPolynomial::get_root_of_unity(k);
        let f1_poly = c_poly.mul_constant(&x_vec[k-1]).add(&c_poly.shift(&omega_1).mul_constant(&(Scalar::one() - x_vec[k-1])), true);
        println!("f1_poly.evals={}", scalar_vector_to_string(&f1_poly.evaluations()));
        // println!("f1_left.evals={}", scalar_vector_to_string(&c_poly.mul_constant(&x_vec[k-1]).evaluations()));
        // println!("f1_right.evals={}", scalar_vector_to_string(&c_poly.shift(&omega_1).mul_constant(&(Scalar::one() - x_vec[k-1])).evaluations()));
        let p1_poly = s0_poly.multiply(&f1_poly);
        println!("p1_poly.evals={}", scalar_vector_to_string(&p1_poly.evaluations_over_domain(8)));
        // println!("c-shift4.evals={}", scalar_vector_to_string(&c_poly.shift(&omega_1).evaluations_over_domain(8)));

        let (s1_poly, _) = zH_poly.div(&FftUniPolynomial::vanishing_polynomial(domain_k));
        println!("s1_poly.evals={}", scalar_vector_to_string(&s1_poly.evaluations()));
        k = 2;
        let domain_k = (2 as u32).pow(k as u32) as usize;
        let omega_2 = FftUniPolynomial::get_root_of_unity(k);
        let f2_poly = c_poly.mul_constant(&x_vec[k-1]).add(&c_poly.shift(&omega_2).mul_constant(&(Scalar::one() - x_vec[k-1])), true);
        let p2_poly = s1_poly.multiply(&f2_poly);
        println!("p2_poly.evals={}", scalar_vector_to_string(&p2_poly.evaluations_over_domain(8)));

        let (s2_poly, _) = zH_poly.div(&FftUniPolynomial::vanishing_polynomial(domain_k));
        println!("s2_poly.evals={}", scalar_vector_to_string(&s2_poly.evaluations()));
        k = 3;
        let domain_k = (2 as u32).pow(k as u32) as usize;
        let omega_2 = FftUniPolynomial::get_root_of_unity(k);
        let f3_poly = c_poly.mul_constant(&x_vec[k-1]).add(&c_poly.shift(&omega_2).mul_constant(&(Scalar::one() - x_vec[k-1])), true);
        let p3_poly = s1_poly.multiply(&f3_poly);
        println!("p3_poly.evals={}", scalar_vector_to_string(&p3_poly.evaluations_over_domain(8)));
    }

    #[test]
    fn test_add_1() { // test univariate sumcheck
        let a = Scalar::from_i64_vector(&vec![1, 2, 3, 4]);
        let b = Scalar::from_i64_vector(&vec![2, 3, 1, 2]);

        // sum = 19
        let inner_prod: Scalar = (0..a.len()).map(|i| a[i] * b[i]).sum();

        println!("inner_prod={}", ScalarExt::to_string(&inner_prod));


        let a_poly = FftUniPolynomial::from_evals_fft(&a, 4);
        let b_poly = FftUniPolynomial::from_evals_fft(&b, 4);

        let ab_prod = a_poly.multiply(&b_poly);
        println!("ab_prod.evals={}", scalar_vector_to_string(&ab_prod.evaluations()));
        println!("ab_prod.coeffs={}", scalar_vector_to_string(&ab_prod.coeffs));
        println!("ab_prod.degree={}", ab_prod.degree);

        let z_poly = FftUniPolynomial::vanishing_polynomial(4);
        println!("z_poly.coeffs={}", scalar_vector_to_string(&z_poly.coeffs));
        println!("z_poly.degree={}", z_poly.degree);


        // let f1_poly = UniPolynomial::from_evals_fft(&f1, 4);
        // let f2_poly = UniPolynomial::from_evals_fft(&f2, 4);

        // let f3_poly = f1_poly.add(&f2_poly, false);
        // println!("f3_evals={}", scalar_vector_to_string(&f3_poly.evals));
        // println!("f3_coeffs={}", scalar_vector_to_string(&f3_poly.coeffs));

        // println!("f1.degree={}", f1_poly.degree);
        // println!("f2.degree={}", f2_poly.degree);
        // // assert_eq!(f3_poly.coeffs, Scalar::from_i64_vector(&vec![-1, 0, 4, 0]));
        // assert_eq!(f3_poly.degree, 2);
        // assert_eq!(f3_poly.domain_size, 4);

        // let f4_poly = f1_poly.add(&f2_poly, true);
        // println!("f4_evals={}", scalar_vector_to_string(&f3_poly.evals));
        // println!("f4_coeffs={}", scalar_vector_to_string(&f3_poly.coeffs));
        // assert_eq!(f4_poly.degree, 0);
        // assert_eq!(f4_poly.domain_size, 4);
    }
}
