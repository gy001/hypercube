#![allow(non_snake_case)]

use crate::*;
use crate::bits::*;
use std::iter;

/// # Module Description
/// 
/// 
/// 
/// # Example: 
///   f(X) = f0 + f1*X + ... + f{n-1}*X^{n-1}
///   the coeffs vector is [f0, f1, ..., f{n-1}]

/// # Note: 
///   H = {0, 1, 2, ..., n-1}
///   the evaluation domain is H, i.e., the set of all integers from 0 to n-1


// TODO: to use HashMap of sparse coefficients internally?
//   It will be harder to shift coefficients in this case.


/// A univariate polynomial over a prime field Fp in dense form.
/// The polynomial is denoted as a vector of coefficients
/// ordered by ascending degree.
/// The degree of the polynomial is (coeffs.len() - 1), and the
/// leading coefficient is coeffs[coeffs.len() - 1].
/// 
/// TODO: zero polynomial's degree should be minus-infinity
#[derive(Debug, PartialEq, Clone)]
pub struct UniPolynomial {
    pub degree: usize,
    pub coeffs: Vec<Scalar>,
}

impl Display for UniPolynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UniPolynomial(degree={})", self.degree);
        let mut str = "".to_string();
        for i in 0..self.coeffs.len() {
            let c = self.coeffs[i];
            if c == Scalar::zero() {
                continue;
            } else {
                // str.push_str(&format!("{}*x^{}", ScalarExt::to_string(&c), i));
                str.push_str(&format!("{}", ScalarExt::to_string(&c)));
            }
            // str.push_str(" + ");
            str.push_str(" , ");
        }
        str.pop();
        str.pop();
        str.pop();
        write!(f, "={}", str)
    }
}


impl UniPolynomial {

    /// Returns the primitive multiplicative generator of the Field.
    fn multiplicative_generator() -> Scalar {
        Scalar::multiplicative_generator()
    }

    /// Compute the nth-root of unity from `g^{(p-1)/2^k}`
    /// where 
    ///   - g: the primitive multiplicative generator of the field
    ///   - p: the modulus of the field
    ///   - k: the log size of the domain, `n = 2^k`
    pub fn get_root_of_unity(k_log_size: usize) -> Scalar {
        let g = Scalar::multiplicative_generator();
        let order = -Scalar::one();
        let cofactor = order / Scalar::from_usize(pow_2(k_log_size));
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

    pub fn vanishing_polynomial_fft(domain_size: usize) -> Self {
        assert!(domain_size.is_power_of_two());

        let mut coeffs = vec![Scalar::zero(); domain_size + 1];
        coeffs[0] = -Scalar::one();
        coeffs[domain_size] = Scalar::one();
        Self { 
            degree: domain_size,
            coeffs: coeffs,
        }
    }

    /// Compute barcycentric weights in O(n^2)
    /// 
    /// # Arguments
    /// 
    /// - `domain`: a domain of any size n
    /// 
    /// # Return
    /// 
    /// - `weights`: a vector of weights of size n
    /// 
    pub fn barycentric_weights(domain: &[Scalar]) -> Vec<Scalar> {
        let domain_size = domain.len();
        let mut weights: Vec<Scalar> = vec![Scalar::zero(); domain_size];
        for i in 0..domain_size {
            let xi = domain[i];
            let prod = (0..domain_size).fold(Scalar::from(1), |acc, j| {
                acc * if i == j {
                    Scalar::from(1)
                } else {
                    xi - domain[j]
                }
            });
            weights[i] = Scalar::from(1) / prod;
        }
        weights
    }

}

impl UniPolynomial {

    // NOTE: letting deg(f_zero) == 0 is harmless
    pub fn zero() -> Self {
        Self {
            degree: 0,
            coeffs: vec![Scalar::zero()],
        }
    }

    pub fn is_zero(&self) -> bool {
        self.degree == 0 && self.coeffs[0].is_zero()
    }

    pub fn from_coeffs(coeffs: &[Scalar]) -> Self {
        let mut coeffs = coeffs.to_vec();

        // Remove leading zeros
        remove_leading_zeros(&mut coeffs);
    
        Self {
            degree: coeffs.len() - 1,
            coeffs: coeffs,
        }
    }

    pub fn from_evals(evals: &[Scalar]) -> Self {
        let domain_size = evals.len();
        assert!(domain_size.is_power_of_two());

        let mut evals = evals.to_vec();

        let mut coeffs = Self::ntt_coeffs_from_evals(&evals, log_2(domain_size));

        // Remove leading zeros from result
        remove_leading_zeros(&mut coeffs);

        Self {
                degree: coeffs.len()-1,
                coeffs: coeffs,
        }
    }

    // compute NTT in O(n log n)
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

    // Compute evaluations from coefficients in O(n log n)
    pub fn ntt_evals_from_coeffs(coeffs: &[Scalar], k_log_size: usize) -> Vec<Scalar> {
        let mut coeffs = coeffs.to_vec();
        let omega = Self::get_root_of_unity(k_log_size);
        Self::ntt_core(&mut coeffs, &omega, k_log_size);
        coeffs
    }

    // Compute evaluations from coefficients in O(n log n)
    pub fn ntt_coeffs_from_evals(evals: &[Scalar], k_log_size: usize) -> Vec<Scalar> {

        let mut evals = evals.to_vec();
        let omega = Self::get_root_of_unity(k_log_size);
        let omega_inv = omega.inverse().unwrap();
        let domain_size = pow_2(k_log_size);
        let domain_size_inv = Scalar::from_usize(domain_size).inverse().unwrap();
        Self::ntt_core(&mut evals, &omega_inv, k_log_size);
        evals.iter_mut().for_each(|e| *e = *e * domain_size_inv);
        evals
    }

    // compute evaluations in O(n^2)
    pub fn ntt_evals_from_coeffs_slow(coeffs: &Vec<Scalar>, k_log_size: usize) -> Vec<Scalar>{
        let len = coeffs.len();
        let domain_size = pow_2(k_log_size);
        assert_eq!(len, domain_size);

        // Compute domain = {omega^i}
        let domain = Self::fft_domain(k_log_size);
        
        // Initialize evals to zero
        let mut evals = vec![Scalar::zero(); domain_size];

        for i in 0..domain_size {
            let mut acc = Scalar::zero();
            for j in 0..domain_size {
                let omega_pow_ij = domain[i].exp(j);
                acc = acc + coeffs[j] * omega_pow_ij;
            }
            evals[i] = acc;
        }
        evals
    }

    pub fn degree(&self) -> usize {
        self.coeffs.len() - 1
    }

    pub fn coefficients(&self) -> Vec<Scalar> {
        self.coeffs.clone()
    }

    pub fn evaluations(&self, domain: &[Scalar]) -> Vec<Scalar> {
        Self::compute_evals_from_coeffs_slow(&self.coeffs, domain)
    }

    pub fn evaluations_fft(&self, domain_log_size: usize) -> Vec<Scalar> {
        Self::compute_evals_from_coeffs_slow(&self.coeffs, &Self::fft_domain(domain_log_size))
    }

    /// Compute subproduct tree in O(M(n) * log(n)) time, where O(M(n)) is the 
    /// asymptotic complexity of multiplication, and equal to O(nlog(n)) if using
    /// FFT-based fast multiplication.
    /// 
    /// Return a vector of levels, each level is a vector of polynomials,
    /// and each polynomial is a vector of coefficients.
    fn contruct_subproduct_tree(domain: &[Scalar]) -> Vec<Vec<Vec<Scalar>>> {
        let n = domain.len();
        assert!(n.is_power_of_two());

        let mut tree = Vec::new();
        let mut level = Vec::new();
        for u in domain.iter() {
            level.push(vec![-*u, Scalar::one()]);
        }
        tree.push(level.clone());

        for k in 0..log_2(n) {
            let mut new_level = Vec::new();
            for i in 0..(n >> (k + 1)) {
                let left = &level[2*i];
                let right = &level[2*i+1];
                let poly = Self::multiplication(left, right);
                new_level.push(poly);
            }
            tree.push(new_level.clone());
            level = new_level;
        }
        assert_eq!(tree.len(), log_2(n)+1);

        // for i in 0..tree.len() {
        //     println!("tree[{}]=", i);
        //     let level = &tree[i];
        //     for j in 0..level.len() {
        //         println!("tree[{}][{}]={}", i, j, scalar_vector_to_string(&level[j]));
        //     }
        // }

        tree
    }

    /// Compute f(X) = ∑i c_i * z(X) / (X - u_i) in O(M(n) * log(n)) time
    /// 
    /// The algorithm is the core of fast interpolation, 
    /// from Modern Computer Algebra, Algorithm 10.9, "Linear Combination for linear moduli".
    /// 
    /// # Arguments 
    /// 
    /// - k: `log(n)`
    /// - base: the base index of the subproduct tree
    /// - c: a vector of coefficients of size n
    /// - u: a vector of points of size n
    /// 
    /// return: a polynomial in coefficients
    /// 
    /// # Example 
    /// 
    /// TODO: I use this alg. to compute `z'(X)`. Is there 
    /// any faster algorithm? It is mentioned in [TAB20] that `z'(X)`
    /// can be computed in O(n) time.
    /// 
    fn linear_combination_linear_moduli_fix(
        tree: &Vec<Vec<Vec<Scalar>>>, 
        k: usize, 
        base: usize, 
        c: &[Scalar], 
        u: &[Scalar],
    ) -> Vec<Scalar> {
        let n = u.len();

        // println!("lc_fix> k={}, base={}, n={}", k, base, n);
        // println!("c={}", scalar_vector_to_string(&c.to_vec()));
        // println!("u={}", scalar_vector_to_string(&u.to_vec()));

        if k == 0 {
            assert_eq!(c.len(), 1);
            assert_eq!(u.len(), 1);
            return vec![c[0]];
        }

        assert!(n.is_power_of_two());
        assert_eq!(n, pow_2(k));


        let node0 = &tree[k-1][2*base + 0];
        let node1 = &tree[k-1][2*base + 1];

        let (c0, c1) = c.split_at(n/2);
        let (u0, u1) = u.split_at(n/2);

        let r0 = Self::linear_combination_linear_moduli_fix(&tree, k-1, 2*base + 0, c0, u0);
        let r1 = Self::linear_combination_linear_moduli_fix(&tree, k-1, 2*base + 1, c1, u1);
        
        UniPolynomial::addition(UniPolynomial::naive_multiplication(&node1, &r0), 
            UniPolynomial::naive_multiplication(&node0, &r1))
    }

    /// Polynomial interpolation in O(M(n) * log(n)) time.
    /// If O(M(n)) is O(nlog(n)) by using fast polynomial multiplication, 
    /// then the asymtotics is O(nlog^2(n)).
    /// 
    /// # Arguments
    /// 
    /// - evals: a vector of evaluations of size n
    /// - domain: a domain of size n, n must be a power of 2
    /// 
    /// # Return
    /// 
    /// - a polynomial (coefficients) of degree (n-1)
    /// 
    pub fn compute_coeffs_from_evals_fast_2(evals: &[Scalar], domain: &[Scalar]) -> Vec<Scalar> {
        let n = domain.len();
        assert!(n.is_power_of_two());
        assert_eq!(evals.len(), n);

        // 1. building up subproduct tree

        let tree = Self::contruct_subproduct_tree(domain);

        // 2. construct a polynomial with linear moduli
        
        let f_derivative = Self::linear_combination_linear_moduli_fix(&tree, 
            log_2(n), 0, &vec![Scalar::one(); n], domain);
        // println!("f_derivative={}", scalar_vector_to_string(&f_derivative));

        let f_derivative_at_u =  Self::eval_rec(&tree, log_2(n), 0, &f_derivative, domain);

        // println!("f_derivative_at_u={}", scalar_vector_to_string(&f_derivative_at_u));

        let mut bary_centric_weights: Vec<Scalar> = f_derivative_at_u.iter().map(|e| e.inverse().unwrap()).collect();
        // println!("bary_centric_weights={}", scalar_vector_to_string(&bary_centric_weights));
        // println!("bary_centric_weights2={}", scalar_vector_to_string(&UniPolynomial::barycentric_weights(domain)));

        bary_centric_weights.iter_mut().enumerate().for_each(|(i, w)| *w = *w * evals[i]);

        // println!("before linear_combination_linear_moduli_fix");
        let f = Self::linear_combination_linear_moduli_fix(&tree, log_2(n), 0, &bary_centric_weights, domain);


        // {
        //     let z_poly = UniPolynomial::from_coeffs(&tree[log_2(n)][0]);
        //     println!("z_poly={}", scalar_vector_to_string(&z_poly.coeffs));
        //     let mut g = Self::zero();
        //     for i in 0..n {
        //         let (gi, _) = z_poly.div_by_linear_divisor(&domain[i]);
        //         g = Self::add(&g, &gi, false);
        //     }
        //     println!("g={}", scalar_vector_to_string(&g.coeffs));
        // }

        f

    }


    fn eval_rec(tree: &Vec<Vec<Vec<Scalar>>>, k: usize, base: usize, f: &[Scalar], u:&[Scalar]) -> Vec<Scalar> {
        let n = u.len();
        // println!("eval_rec> k={}, base={}, n={}", k, base, n);
        // println!("f={}", scalar_vector_to_string(&f.to_vec()));
        // println!("u={}", scalar_vector_to_string(&u.to_vec()));
        
        if k == 0 {
            return f.to_vec();
        }

        // println!("division> k-1={}, left={}, right={}, n={}", k-1, base+0, base+1, n);
        let (q0, r0) = Self::division(f, &tree[k-1][2*base + 0]);
        let (q1, r1) = Self::division(f, &tree[k-1][2*base + 1]);

        let (u0, u1) = u.split_at(n/2);
        // println!("u0={}", scalar_vector_to_string(&u0.to_vec()));
        // println!("u1={}", scalar_vector_to_string(&u1.to_vec()));
        let mut rs0: Vec<Scalar> = Self::eval_rec(tree, k-1, base * 2 + 0, &r0, &u0);
        let mut rs1: Vec<Scalar> = Self::eval_rec(tree, k-1, base * 2 + 1, &r1, &u1);
        rs0.append(&mut rs1);
        rs0
    }

    /// Polynomial evaluation in O(nlog^2(n)), or multiple points evaluation
    /// It assumes using O(nlog(n)) fast multiplication (TODO: to implement).
    /// 
    /// # Arguments
    /// 
    /// - `coeffs`: a polynomial (coefficients) of degree (n-1)
    /// - `domain`: a domain of size n, n must be a power of 2
    /// 
    /// # Return
    /// 
    /// - `evals`:  a vector of evaluations of size n
    /// 
    pub fn compute_evals_from_coeffs_fast(coeffs: &[Scalar], domain: &[Scalar]) -> Vec<Scalar> {
        let n = domain.len();
        assert!(n.is_power_of_two());
        assert_eq!(coeffs.len(), n);

        // 1. building up subproduct tree
        let tree = Self::contruct_subproduct_tree(domain);
        // 2. compute evaluations from subproduct tree

        let evals = Self::eval_rec(&tree, log_2(n), 0, coeffs, domain);

        evals
    }

/*
    /// Compute evaluations 
    pub fn compute_evals_from_coeffs_fast_alt(coeffs: &[Scalar], points: &[Scalar]) -> Vec<Scalar> {
        if points.len() == 1 {
            return vec![Self::evaluate_from_coeffs(coeffs, &points[0])];
        }
    
        println!("fast2> f={}", scalar_vector_to_string(&coeffs.to_vec()));
        println!("fast2> u={}", scalar_vector_to_string(&points.to_vec()));

        let mid = points.len() / 2;
        let (points_left, points_right) = points.split_at(mid);
    
        let mut poly_left = UniPolynomial::from_coeffs(&coeffs);
        let mut poly_right = UniPolynomial::from_coeffs(&coeffs);
    

        let poly_l_coeffs = {
            let mut quo_l = poly_left.clone();
            let mut rem_left = {
                let mut rem_vec = Vec::new();
                for &point in points_left {
                    let (quo, rem) = quo_l.div_by_linear_divisor(&point);
                    println!("quo_l: {}", quo);  
                    rem_vec.push(rem);
                    println!("rem_l: {}", rem);  
                    quo_l = quo
               }
               rem_vec
            };
    
            println!("rem={}", scalar_vector_to_string(&rem_left.to_vec()));
        
            let mut coeffs = vec![Scalar::zero(); mid];
            let rem = rem_left.pop().unwrap();
            coeffs[0] += rem;
            rem_left.iter().rev().enumerate().for_each(|(i, rem)| {
                println!("coeffs={}", scalar_vector_to_string(&coeffs));
                println!("coeffs={}", scalar_vector_to_string(&coeffs));
                println!("p[{}]={}", i, points_left[i]);
                for j in (0..mid).rev() {
                    if j > 0 { 
                        coeffs[j] = coeffs[j-1] - coeffs[j] * points_left[i]
                    } else {
                        coeffs[j] = Scalar::zero() - coeffs[j] * points_left[i]
                    };
                }
                coeffs[0] += rem;
                println!("coeffs={}", scalar_vector_to_string(&coeffs));
            });
            coeffs
        };

        let poly_r_coeffs = {
            let mut quo_r = poly_right.clone();
            let mut rem_r = {
                let mut rem_vec = Vec::new();
                for &point in points_right {
                    let (quo, rem) = quo_r.div_by_linear_divisor(&point);
                    println!("quo_l: {}", quo);  
                    rem_vec.push(rem);
                    println!("rem_l: {}", rem);  
                    quo_r = quo
               }
               rem_vec
            };
    
            println!("rem={}", scalar_vector_to_string(&rem_r.to_vec()));
        
            let mut coeffs = vec![Scalar::zero(); mid];
            let rem = rem_r.pop().unwrap();
            coeffs[0] += rem;
            rem_r.iter().rev().enumerate().for_each(|(i, rem)| {
                println!("coeffs={}", scalar_vector_to_string(&coeffs));
                println!("coeffs={}", scalar_vector_to_string(&coeffs));
                println!("p[{}]={}", i, points_right[i]);
                for j in (0..mid).rev() {
                    if j > 0 { 
                        coeffs[j] = coeffs[j-1] - coeffs[j] * points_right[i]
                    } else {
                        coeffs[j] = Scalar::zero() - coeffs[j] * points_right[i]
                    };
                }
                coeffs[0] += rem;
                println!("coeffs={}", scalar_vector_to_string(&coeffs));
            });
            coeffs
        };

        println!("poly_r_coeffs={}", scalar_vector_to_string(&poly_r_coeffs.to_vec()));
    
        let mut results_left = Self::compute_evals_from_coeffs_fast_alt(&poly_l_coeffs, points_left);
        let mut results_right = Self::compute_evals_from_coeffs_fast_alt(&poly_r_coeffs, points_right);
    
        results_left.append(&mut results_right);
        results_left
    }
  */


    /// Returns the coefficients of the vanishing polynomial over a domain.
    fn vanishing_polynomial(domain: &[Scalar]) -> Vec<Scalar> {
        let mut coeffs = vec![Scalar::zero(); domain.len() + 1];
        coeffs[0] = Scalar::one();
        for i in 0..domain.len()  {
            for j in (0..=(i+1)).rev() {
                if j > 0 { 
                    coeffs[j] = coeffs[j-1] - coeffs[j] * domain[i]
                } else {
                    coeffs[j] = Scalar::zero() - coeffs[j] * domain[i]
                };
            }
            // println!("coeffs={}", scalar_vector_to_string(&coeffs));
        }
        coeffs
    }

    /// Compute interpolation in O(n^2)
    /// 
    /// f(X) = u_0 * L_0(X) + u_1 * L_1(X) + u_2 * L_2(X) + ... + u_{n-1} * L_{n-1}(X)
    /// 
    /// L_i(X) = c_i * z(X)/ (X-u_i)
    /// 
    /// where 
    ///     z(X) = (X-u_0) * (X-u_1) * ... * (X-u_{n-1})
    ///     c_i = 1 / z'(u_i)
    /// 
    pub fn compute_coeffs_from_evals_slow(evals: &[Scalar], domain: &[Scalar]) -> Vec<Scalar> {
        assert_eq!(evals.len(), domain.len());

        let n = evals.len();
        let mut coeffs = vec![Scalar::zero(); n];

        // compute bary centric weights in O(n^2);
        let w_rec = Self::barycentric_weights(domain);

        // compute z(X) in O(n^2)
        let vanishing_poly = Self::vanishing_polynomial(domain);

        for i in 0..n {

            let (mut z_div, rem) = Self::division_by_linear_divisor(&vanishing_poly, &domain[i]);
            assert_eq!(rem, Scalar::zero());

            z_div.iter_mut().for_each(|e| *e = *e * w_rec[i]);
            z_div.iter_mut().for_each(|e| *e = *e * evals[i]);

            coeffs.iter_mut().enumerate().for_each(|(j, c)| *c = *c + z_div[j]);
        }
        coeffs
    }

    /// Compute interpolation in O(n^3)
    /// 
    /// f(X) = u_0 * L_0(X) + u_1 * L_1(X) + u_2 * L_2(X) + ... + u_{n-1} * L_{n-1}(X)
    /// 
    /// L_i(X) = ∏_{j<>i} (X - u_i) / ∏_{j<>i} (u_j - u_i)
    pub fn compute_coeffs_from_evals_slow_slow(evals: &[Scalar], domain: &[Scalar]) -> Vec<Scalar> {
        assert_eq!(evals.len(), domain.len());

        let n = evals.len();
        let mut coeffs = vec![Scalar::zero(); n];

        for i in 0..n {
            let mut c_vec = vec![Scalar::zero(); n];
            c_vec[0] = Scalar::from(1);

            // x_vec = [x_0, x_1, ..., x_{i-1}, x_{i+1}, ..., x_{n-1}]
            let x_vec: Vec<Scalar> = (0..n)
                .filter(|&k| k != i)
                .map(|j| domain[j])
                .collect();

            for j in 1..n {
                for k in (0..=j).rev() {
                    let tmp = if k == 0 {Scalar::zero()} else {c_vec[k - 1]};
                    c_vec[k] = tmp - c_vec[k] * (x_vec[j - 1]);
                }
            }

            // compute (1/w_i): inversion of barycentric-weights
            let denom = (0..n).filter(|&k| k != i).fold(Scalar::from(1), |acc, k| {
                acc * (domain[i] - domain[k])
            });

            for k in 0..n {
                coeffs[k] += evals[i] * c_vec[k] / denom;
            }
        }
        coeffs
    }

    /// Polynomial multiple points evaluation in O(n^2)
    /// 
    /// # Arguments
    /// 
    /// - `coeffs`: a polynomial (coefficients) of degree (n-1)
    /// - `domain`: a domain of size n, n must be a power of 2
    /// 
    /// # Return
    /// - `evals`:  a vector of evaluations of size n
    /// 
    pub fn compute_evals_from_coeffs_slow(coeffs: &[Scalar], domain: &[Scalar]) -> Vec<Scalar> {
        let domain_size = domain.len();
        assert!(domain_size.is_power_of_two());
        // TODO: uncomment this line?
        // assert!(coeffs.len() <= domain_size);

        let mut evals = vec![Scalar::zero(); domain_size];

        for i in 0..domain_size {
            evals[i] = Self::evaluate_from_coeffs(coeffs, &domain[i]);
        }
        evals
    }

    // Compute f(X) from [e0, e1, ..., e{n-1}] over D in O(n)
    //   f(X) = numinator / denominator
    //   w[i] = weights[i] * / (X - domain[i])
    //   numerator   = ∑ w[i] * e[i]
    //   denominator = ∑ w[i]
    pub fn evaluate_from_evals(evals: &[Scalar], x: &Scalar, domain: &[Scalar]) -> Scalar {
        let domain_size = domain.len();
        assert_eq!(domain_size, evals.len());

        if let Some(idx) = domain.iter().position(|&y| *x == y) {
            evals[idx]
        } else {
            let weights = UniPolynomial::barycentric_weights(domain);
            let w_vec: Vec<Scalar> = (0..domain_size)
                .map(|i| weights[i] / (*x - domain[i]))
                .collect();

            let (numerator, denominator) = w_vec.iter().enumerate().fold(
                (Scalar::from(0), Scalar::from(0)),
                |(numerator, denominator), (i, &w)| (numerator + w * evals[i], denominator + w),
            );
            numerator / denominator
        }
    }

    // Compute f(X) from [f0, f1, f2, ..., fd] in O(n) (Horner's method)
    //   f(x) = f0 + x*(f1 + x*(f2 + ... + x*fd)...))
    //
    // For more information on Horner's method, 
    //   refer to: https://en.wikipedia.org/wiki/Horner%27s_method
    // 
    pub fn evaluate_from_coeffs(coeffs: &[Scalar], x: &Scalar) -> Scalar {
        coeffs
            .iter().rev()
            .fold(Scalar::from(0), |acc, coeff| (acc * *x + coeff))
    }

    // Compute f(X) from [f0, f1, f2, ..., fd] in O(n)
    //   with 2n field multiplications
    pub fn evaluate_from_coeffs_alt(coeffs: &[Scalar], x: &Scalar) -> Scalar {
        let (acc, _) =
            coeffs
                .iter()
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

impl UniPolynomial {

    fn addition(coeffs0: Vec<Scalar>, coeffs1: Vec<Scalar>) -> Vec<Scalar> {
        let len0 = coeffs0.len();
        let len1 = coeffs1.len();
        let len = if len0 < len1 {len1} else {len0};
        let mut c = vec![Scalar::zero(); len];

        for i in 0..len {
            let c0 = if i < len0 { coeffs0[i] } else { Scalar::zero() };
            let c1 = if i < len1 { coeffs1[i] } else { Scalar::zero() };
            c[i] = c0 + c1;
        }
        c
    }

    // fn subtract(coeffs0: Vec<Scalar>, coeffs1: Vec<Scalar>) -> Vec<Scalar> {
    //     let len0 = coeffs0.len();
    //     let len1 = coeffs1.len();
    //     let len = if len0 < len1 {len1} else {len0};
    //     let mut c = vec![Scalar::zero(); len];

    //     for i in 0..len {
    //         let c0 = if i < len0 { coeffs0[i] } else { Scalar::zero() };
    //         let c1 = if i < len1 { coeffs1[i] } else { Scalar::zero() };
    //         c[i] = c0 + c1;
    //     }
    //     c
    // }

    /// Compute polynomials addition and subtraction
    /// f1.add(&f2, false) = f1 + f2
    /// f1.add(&f2, true) = f1 - f2
    pub fn add(&self, poly2: &Self) -> Self {

        let len1 = self.coeffs.len();
        let len2 = poly2.coeffs.len();
        let len_a = std::cmp::max(self.coeffs.len(), poly2.coeffs.len());
        let mut coeffs_a = vec![Scalar::zero(); len_a];

        for i in 0..coeffs_a.len() {
            let coeff1 = if i < len1 { self.coeffs[i] } else { Scalar::zero() };
            let coeff2 = if i < len2 { poly2.coeffs[i] } else { Scalar::zero() };
            coeffs_a[i] = coeff1 + coeff2;
        }

        remove_leading_zeros(&mut coeffs_a);

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }

    /// Compute polynomials addition and subtraction
    /// f1.add(&f2, false) = f1 + f2
    /// f1.add(&f2, true) = f1 - f2
    pub fn sub(&self, poly2: &Self) -> Self {

        let len1 = self.coeffs.len();
        let len2 = poly2.coeffs.len();
        let len_a = std::cmp::max(self.coeffs.len(), poly2.coeffs.len());
        let mut coeffs_a = vec![Scalar::zero(); len_a];

        for i in 0..coeffs_a.len() {
            let coeff1 = if i < len1 { self.coeffs[i] } else { Scalar::zero() };
            let coeff2 = if i < len2 { poly2.coeffs[i] } else { Scalar::zero() };
            coeffs_a[i] = coeff1 - coeff2;
        }

        remove_leading_zeros(&mut coeffs_a);

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }

    pub fn add_inplace(&mut self, poly2: &Self) {

        let len1 = self.coeffs.len();
        let len2 = poly2.coeffs.len();
        let mut len = len1;
        if len1 < len2 {
            self.coeffs.resize(len2, Scalar::zero());
            len = len2;
        }

        for i in 0..poly2.coeffs.len() {
                self.coeffs[i] += poly2.coeffs[i];
        }

        remove_leading_zeros(&mut self.coeffs);

        self.degree = self.coeffs.len() - 1;
    }

    pub fn sub_inplace(&mut self, poly2: &Self) {

        let len1 = self.coeffs.len();
        let len2 = poly2.coeffs.len();
        let mut len = len1;
        if len1 < len2 {
            self.coeffs.resize(len2, Scalar::zero());
            len = len2;
        } 

        for i in 0..poly2.coeffs.len() {
                self.coeffs[i] -= poly2.coeffs[i];
        }

        remove_leading_zeros(&mut self.coeffs);

        self.degree = self.coeffs.len() - 1;

    }

    // TODO: to implement fast poly multiplication
    //  1. Karatsuba multiplication  ✅
    //  2. Schonhage Strassen multiplication O(n * logn * loglogn) 🛴

    /// Compute polynomial multiplication in O(n^{1.6}) using Karatsuba multiplication
    /// 
    /// @param a: a polynomial (coefficients) of degree (n-1)
    /// @param b: a polynomial (coefficients) of degree (n-1)
    /// return: a polynomial (coefficients) of degree 2n-1
    /// 
    /// NOTE: a and b are padded zeros to 2^k size
    fn karatsuba_multiplication(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
        let al = a.len();
        let bl = b.len();
        let n = std::cmp::max(al, bl).next_power_of_two();
        let mut a = a.to_vec();
        a.extend(iter::repeat(Scalar::zero()).take(n - al));
        let mut b = b.to_vec();
        b.extend(iter::repeat(Scalar::zero()).take(n - bl));
        Self::karatsuba_fixpoint(&a, &b)
    }

    fn karatsuba_fixpoint(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
        let n = a.len();
        if n <= 1 {
            return vec![a[0] * b[0]];
        }
        println!("n={}, a={}", n, scalar_vector_to_string(&a.to_vec()));
        println!("n={}, b={}", n, scalar_vector_to_string(&b.to_vec()));

        let mid = n / 2;

        let a_low = &a[0..mid];
        let a_high = &a[mid..];
        let b_low = &b[0..mid];
        let b_high = &b[mid..];

        let p1 = Self::karatsuba_fixpoint(a_low, b_low);
        println!("n={}, p1={}", n, scalar_vector_to_string(&p1));
        let p2 = Self::karatsuba_fixpoint(a_high, b_high);
        println!("n={}, p2={}", n, scalar_vector_to_string(&p2));

        let a_low_high = a_low.iter().zip(a_high).map(|(a, b)| *a + b).collect::<Vec<_>>();
        let b_low_high = b_low.iter().zip(b_high).map(|(a, b)| *a + b).collect::<Vec<_>>();
        let p3 = Self::karatsuba_fixpoint(&a_low_high, &b_low_high);
        println!("n={}, p3={}", n, scalar_vector_to_string(&p3));

        let mut result = vec![Scalar::zero(); 2*n];
        for i in 0..p1.len() {
            result[i] += p1[i];
            result[i + n] += p2[i];
        }
        for i in 0..p3.len() {
            result[i + mid] += p3[i] - p1[i] - p2[i];
        }
        println!("n={}, result={}", n, scalar_vector_to_string(&result));
        result
    }

    /// Compute polynomial multilication naively in O(n^2)
    fn naive_multiplication(coeffs0: &[Scalar], coeffs1: &[Scalar]) -> Vec<Scalar> {

        let mut c =vec![Scalar::zero(); coeffs0.len() + coeffs1.len() - 1];
        
        for i in 0..coeffs0.len() {
            for j in 0..coeffs1.len() {
                c[i + j] += coeffs0[i] * coeffs1[j];
            }
        }
        c
    }

    /// Compute polynomial multilication wrapper
    pub fn multiplication(coeffs0: &[Scalar], coeffs1: &[Scalar]) -> Vec<Scalar> {
        // TODO: to select different multiplication algs based 
        // on the degree of polynomials.
        Self::naive_multiplication(coeffs0, coeffs1)
    }

    pub fn mul(&self, poly2: &Self) -> Self {

        let coeffs_1 = &self.coeffs;
        let coeffs_2 = &poly2.coeffs;
        let mut coeffs_m =vec![Scalar::zero(); coeffs_1.len() + coeffs_2.len() - 1];
        
        for i in 0..coeffs_1.len() {
            for j in 0..coeffs_2.len() {
                coeffs_m[i + j] += coeffs_1[i] * coeffs_2[j];
            }
        }

        let degree = &self.degree + &poly2.degree;

        Self {
            degree: degree,
            coeffs: coeffs_m,
        }
    }

    //TODO: add mul_inplace()

    pub fn add_scalar(&self, v: &Scalar) -> Self {

        let mut coeffs_a = self.coeffs.clone();

        coeffs_a[0] += v;

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }

    pub fn sub_scalar(&self, v: &Scalar) -> Self {

        let mut coeffs_a = self.coeffs.clone();

        coeffs_a[0] -= v;

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }

    pub fn mul_scalar(&self, a: &Scalar) -> Self {

        let mut coeffs_a = self.coeffs.clone();

        for i in 0..coeffs_a.len() {
            coeffs_a[i] *= a;
        }

        Self {
            degree: coeffs_a.len() - 1,
            coeffs: coeffs_a,
        }
    }


    fn division_by_linear_divisor(coeffs: &[Scalar], d: &Scalar) -> (Vec<Scalar>, Scalar) {
        assert!(coeffs.len() > 1);

        let coeffs = coeffs.to_vec();
        let (q, r) = coeffs
            .iter().enumerate().rev()
            .fold((Vec::new(), Scalar::from(0)), |(mut quo, mut rem), (i, coeff)| {
                rem = rem * *d + coeff;
                if i > 0 {quo.insert(0, rem)};
                (quo, rem)
            });
        (q, r)
    }

    /// Divide a polynomial by a linear divisor in O(n)
    ///     
    ///   `(q(X), r) = f(X) / (X-d)`
    ///
    /// For more information on Ruffini's Rule, 
    ///   refer to https://mathworld.wolfram.com/RuffinisRule.html
    /// 
    pub fn div_by_linear_divisor(&self, d: &Scalar) -> (Self, Scalar) {
        assert!(self.degree > 0);
        let (q, r) = Self::division_by_linear_divisor(&self.coeffs, d);
        (Self {
            degree: self.degree - 1,
            coeffs: q,
        }, r)
    }

    // TODO: https://en.wikipedia.org/wiki/Synthetic_division
    fn division(dividend: &[Scalar], divisor: &[Scalar]) -> (Vec<Scalar>, Vec<Scalar>) {

        // Important: if dividend.len() < divisor.len(), then the quotient is zero and 
        // the remainder is the dividend.
        if dividend.len() < divisor.len() {
            return (vec![Scalar::zero()], dividend.to_vec());
        }

        let mut quotient = vec![Scalar::zero(); dividend.len() - divisor.len() + 1];
        let mut remainder = dividend.to_vec();
    
        for i in (0..quotient.len()).rev() {
            quotient[i] = remainder[i + divisor.len() - 1] / divisor[divisor.len() - 1];
            for j in 0..divisor.len() {
                remainder[i + j] -= quotient[i] * divisor[j];
            }
        }
    
        // Remove leading zeros
        while remainder.len() > 1 && remainder[remainder.len() - 1] == Scalar::zero() {
            remainder.pop();
        }
    
        (quotient, remainder)
    }

    // Compute long division in O(n^2)
    pub fn div(&self, divisor_poly: &Self) -> (Self, Self) {
        assert!(divisor_poly.degree > 0);

        let mut dividend = self.coeffs.clone();
        let mut divisor = divisor_poly.coeffs.clone();

        let mut quotient = vec![Scalar::zero(); dividend.len() - divisor.len() + 1];
        let mut remainder = dividend.to_vec();
    
        for i in (0..quotient.len()).rev() {
            quotient[i] = remainder[i + divisor.len() - 1] / divisor[divisor.len() - 1];
            for j in 0..divisor.len() {
                remainder[i + j] -= quotient[i] * divisor[j];
            }
        }
    
        // Remove leading zeros
        while remainder.len() > 1 && remainder[remainder.len() - 1] == Scalar::zero() {
            remainder.pop();
        }

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

    /// Compute f(a*X) in O(n)
    ///  f(a*X) = f0 + f1*(a*X) + f2*(a*X)^2 + ... + fd*(a*X)^d
    ///         = f0 + (f1*a)X + (f2*a^2)X^2 + ... + (fd*a^d)X^d
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
}

use std::rc::Rc;

struct Node {
    poly: Vec<Scalar>,
    left: Option<Rc<Node>>,
    right: Option<Rc<Node>>,
}

impl UniPolynomial {

    /// Compute subproduct tree in O(M(n) * log(n)) time, where O(M(n)) is the 
    /// asymptotic complexity of multiplication, and equal to O(nlog(n)) if using
    /// FFT-based fast multiplication.
    /// 
    /// NOTE: `n` does NOT need to be a power of 2.
    /// 
    /// # Arguments 
    /// 
    /// - `domain`: a domain of any size n
    /// 
    /// # Returns 
    /// 
    /// - A binary tree 
    fn contruct_subproduct_tree_fix(domain: &[Scalar]) -> Node {
        let n = domain.len();
        // assert!(n.is_power_of_two());

        if domain.len() == 1 {
            Node {
                poly: vec![-domain[0], Scalar::one()],
                left: None,
                right: None,
            }
        } else {
            let mid = if n % 2 == 0 {n/2} else {n/2 + 1};
            let (left, right) = domain.split_at(mid);
            // println!("l={}", scalar_vector_to_string(&left.to_vec()));
            // println!("r={}", scalar_vector_to_string(&right.to_vec()));

            let left_node = Self::contruct_subproduct_tree_fix(left);
            let right_node = Self::contruct_subproduct_tree_fix(right);
            let poly = Self::multiplication(&left_node.poly, &right_node.poly);
            // println!("node={}", scalar_vector_to_string(&poly));
            Node {
                poly: poly,
                left: Some(Rc::new(left_node)),
                right: Some(Rc::new(right_node)),
            }
        }
    }

    /// Compute evaluations going down the subproduct tree
    /// from Modern Computer Algebra, Algorithm 10.5, page 298
    ///
    /// # Arguments
    /// 
    /// - `tree`: a subproduct tree of `(X-u0)(X-u1)\cdots (X-u{n-1})`
    /// - `f`: a polynomial (coefficients) of any degree greater than zero
    /// - `u`: a domain of any size n
    /// 
    /// # Returns
    /// 
    /// - evaluations of `f`` at `(u0, u1, ..., u{n-1})`
    /// 
    fn compute_eval_fix(tree: &Node, f: &[Scalar], u:&[Scalar]) -> Vec<Scalar> {
        assert!(f.len() > 0);
        let n = u.len();
        // println!("compute_eval_fix> k={}, base={}, n={}", k, base, n);
        // println!("compute_eval_fix> f={}", scalar_vector_to_string(&f.to_vec()));
        // println!("compute_eval_fix> u={}", scalar_vector_to_string(&u.to_vec()));
        
        if f.len() == 1 {
            return f.to_vec();
        }

        if tree.left.is_none() &&  tree.right.is_none(){
            panic!("compute_eval_fix> tree is a leaf node");
        }

        let node_l = tree.left.as_ref().unwrap();
        let node_r = tree.right.as_ref().unwrap();
        // println!("compute_eval_fix> node_l={}, node_r={}", 
        //     scalar_vector_to_string(&node_l.poly),
        //     scalar_vector_to_string(&node_r.poly));

        // println!("division> k-1={}, left={}, right={}, n={}", k-1, base+0, base+1, n);
        let (_, r0) = Self::division(f, &node_l.poly);
        let (_, r1) = Self::division(f, &node_r.poly);
        // println!("compute_eval_fix> r0={}", scalar_vector_to_string(&r0));
        // println!("compute_eval_fix> r1={}", scalar_vector_to_string(&r1));

        let mid = if n % 2 == 0 {n/2} else {n/2 + 1};
        let (u_l, u_r) = u.split_at(mid);
        // println!("compute_eval_fix> u0={}", scalar_vector_to_string(&u_l.to_vec()));
        // println!("compute_eval_fix> u1={}", scalar_vector_to_string(&u_r.to_vec()));
        let mut rs_l: Vec<Scalar> = Self::compute_eval_fix(node_l, &r0, &u_l);
        let mut rs_r: Vec<Scalar> = Self::compute_eval_fix(node_r, &r1, &u_r);
        // println!("compute_eval_fix> rs_l={}", scalar_vector_to_string(&rs_l));
        // println!("compute_eval_fix> rs_r={}", scalar_vector_to_string(&rs_r));

        rs_l.append(&mut rs_r);
        rs_l
    }

    /// Compute f(X) = ∑i c_i * z(X) / (X - u_i) in O(M(n) * log(n)) time
    /// 
    /// The algorithm is the core of fast interpolation, 
    /// from Modern Computer Algebra, Algorithm 10.9, "Linear Combination for linear moduli".
    /// 
    /// # Arguments 
    /// 
    /// - k: `log(n)`
    /// - base: the base index of the subproduct tree
    /// - c: a vector of coefficients of size n
    /// - u: a vector of points of size n
    /// 
    /// return: a polynomial in coefficients
    /// 
    ///  
    /// TODO: I use this alg. to compute `z'(X)`. Is there 
    /// any faster algorithm? It is mentioned in [TAB20] that `z'(X)`
    /// can be computed in O(n) time.
    fn compute_linear_combination_linear_moduli_fix(
        tree: &Node, 
        c: &[Scalar], 
        u: &[Scalar],
    ) -> Vec<Scalar> {
        let n = u.len();
        assert_eq!(c.len(), u.len());
        // println!("lc_fix> k={}, base={}, n={}", k, base, n);
        // println!("c={}", scalar_vector_to_string(&c.to_vec()));
        // println!("u={}", scalar_vector_to_string(&u.to_vec()));

        if n == 1 {
            return vec![c[0]];
        }

        let node_l = tree.left.as_ref().unwrap();
        let node_r = tree.right.as_ref().unwrap();

        let mid = if n % 2 == 0 {n/2} else {n/2 + 1};
        let (c0, c1) = c.split_at(mid);
        let (u0, u1) = u.split_at(mid);

        let r0 = Self::compute_linear_combination_linear_moduli_fix(&node_l, c0, u0);
        let r1 = Self::compute_linear_combination_linear_moduli_fix(&node_r, c1, u1);
        
        UniPolynomial::addition(UniPolynomial::naive_multiplication(&node_r.poly, &r0), 
            UniPolynomial::naive_multiplication(&node_l.poly, &r1))
    }


    /// Compute barcycentric weights in O(M(n)log n)
    pub fn barycentric_weights_fast(domain: &[Scalar]) -> Vec<Scalar> {
        let n = domain.len();
        let tree = Self::contruct_subproduct_tree_fix(domain);
        let z_derivative = UniPolynomial::compute_linear_combination_linear_moduli_fix(
            &tree, &vec![Scalar::one(); n], &domain);
        let z_derivative_at_u = UniPolynomial::compute_eval_fix(
                &tree, &z_derivative, &domain);
        let ws: Vec<Scalar> = z_derivative_at_u.iter().map(
            |e| e.inverse().unwrap()).collect();
        ws
    }

    /// Polynomial interpolation in O(M(n) * log(n)) time.
    /// If O(M(n)) is O(nlog(n)) by using fast polynomial multiplication, 
    /// then the asymtotics is O(nlog^2(n)).
    /// from Modern Computer Algebra, Algorithm 10.11, page 301
    /// 
    /// # Arguments
    /// 
    /// - evals: a vector of evaluations of size n
    /// - domain: a domain of any size n
    /// 
    /// # Return
    /// 
    /// - a polynomial (coefficients) of degree (n-1)
    pub fn compute_coeffs_from_evals_fast(evals: &[Scalar], domain: &[Scalar]) -> Vec<Scalar> {
        let n = domain.len();
        assert_eq!(evals.len(), n);

        // 1. building up subproduct tree

        let tree = Self::contruct_subproduct_tree_fix(domain);

        // 2. construct a polynomial with linear moduli
        
        let z_derivative = Self::compute_linear_combination_linear_moduli_fix(&tree, 
            &vec![Scalar::one(); n], domain);

        // 3. compute barycentric weights

        let z_derivative_at_u =  Self::compute_eval_fix(&tree, &z_derivative, domain);
        let mut ws: Vec<Scalar> = z_derivative_at_u.iter().map(|e| e.inverse().unwrap()).collect();

        ws.iter_mut().enumerate().for_each(|(i, w)| *w = *w * evals[i]);

        // 4. compute barycentric weights
        let f = Self::compute_linear_combination_linear_moduli_fix(&tree, &ws, domain);

        f

    }


}

fn remove_leading_zeros(coeffs: &mut Vec<Scalar>) {
    while coeffs.len() > 1 && coeffs[coeffs.len() - 1] == Scalar::zero() {
        coeffs.pop();
    }
}

fn append_leading_zeros(coeffs: &mut Vec<Scalar>, degree: usize) {
    let len = coeffs.len();
    if len < degree + 1 {
        coeffs.extend(iter::repeat(Scalar::zero()).take(degree + 1 - len));
    }
}

fn pad_zeros_to_power_of_two(coeffs: &mut Vec<Scalar>) {
    let len = coeffs.len();
    let n = len.next_power_of_two();
    if len < n {
        coeffs.extend(iter::repeat(Scalar::zero()).take(n - len));
    }
}

mod tests {
    use crate::*;
    use super::*;

    #[test]
    fn test_omega() {
        let order = -Scalar::one();

        let domain_size = 8;
        let cofactor = order / Scalar::from_usize(domain_size);
        let omega = order.pow(cofactor.into_repr());
        let omega_pow_8 = omega.pow(&[8,0,0,0]);
        assert_eq!(omega_pow_8, Scalar::one());
    }

    #[test]
    fn test_get_root_of_unity_8() {
        let domain_size = 8;
        let omega = UniPolynomial::get_root_of_unity(3);
        assert_eq!(omega.exp(8), Scalar::one());

        let omega_prime = Scalar::multiplicative_generator().pow(
            (-Scalar::one() / Scalar::from_usize(domain_size)).into_repr());
        assert_eq!(omega, omega_prime);
    }

    #[test]
    fn test_get_root_of_unity_128() {
        let domain_size = 128;
        let omega = UniPolynomial::get_root_of_unity(log_2(128));
        assert_eq!(omega.exp(128), Scalar::one());

        let omega_prime = Scalar::multiplicative_generator().pow(
            (-Scalar::one() / Scalar::from_usize(domain_size)).into_repr());
        assert_eq!(omega, omega_prime);
    }

    #[test]
    fn test_fft_domain() {
        let k = 5;
        let domain = UniPolynomial::fft_domain(k);
        // println!("domain={}", scalar_vector_to_string(&domain));
        
        let len = domain.len();
        let omega = domain[1];

        assert_eq!(domain[0], Scalar::one());

        for i in 1..len {
            assert_eq!(domain[i-1] * omega, domain[i]);
        }

        assert_eq!(domain[len-1] * omega, Scalar::one());
    }

    #[test]
    fn test_ntt_evals_from_coeffs_naive() {
        let rng = &mut ark_std::test_rng();
        let k = 5;

        let mut coeffs = Scalar::rand_vector(pow_2(k), rng);

        let fft_domain = UniPolynomial::fft_domain(k);

        let evals = UniPolynomial::ntt_evals_from_coeffs(&mut coeffs, k);        
        
        let zeta = Scalar::rand(rng);
        let eval1 = UniPolynomial::evaluate_from_evals(&evals, &zeta, &fft_domain);
        let eval2 = UniPolynomial::evaluate_from_coeffs(&coeffs, &zeta);
        assert_eq!(eval1, eval2);
    }

    #[test] 
    fn test_ntt_evals_from_coeffs() {
        let rng = &mut ark_std::test_rng();
        let k = 5;

        let mut coeffs = Scalar::rand_vector(pow_2(k), rng);

        let evals1 = UniPolynomial::ntt_evals_from_coeffs_slow(&coeffs, k);
        let evals2 = UniPolynomial::ntt_evals_from_coeffs(&coeffs, k);
        assert_eq!(evals1, evals2);
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
    fn test_ntt_core_2() {
        let mut evals = Scalar::from_usize_vector(&[0,0,0,0,5,6,7,8]);
        let k = 3;
        let evals0 = evals.clone();
        println!("evals0={}", scalar_vector_to_string(&evals0));
        let coeffs = UniPolynomial::ntt_coeffs_from_evals(&evals, k);
        println!("coeffs={}", scalar_vector_to_string(&coeffs));

        let evals1 = UniPolynomial::ntt_evals_from_coeffs(&coeffs, k);
        println!("evals1={}", scalar_vector_to_string(&evals1));


        // assert_eq!(coeffs, coeffs0);
    }

    #[test]
    fn test_evaluate_from_coeffs() {
        let coeffs = ScalarExt::from_usize_vector(&[2,3,2,4,1]);
        let x = Scalar::from(2);
        let result = UniPolynomial::evaluate_from_coeffs(&coeffs, &x);
        assert_eq!(result, Scalar::from(64));
    }

    #[test]
    fn test_evaluate_from_coeffs_alt() {
        let rng = &mut ark_std::test_rng();
        let coeffs = ScalarExt::from_usize_vector(&[2,3,2,4,1]);
        let x = Scalar::rand(rng);
        let result = UniPolynomial::evaluate_from_coeffs(&coeffs, &x);
        let result2 = UniPolynomial::evaluate_from_coeffs_alt(&coeffs, &x);
        assert_eq!(result, result2);
    }

    #[test]
    fn test_div_linear_divisor() {
        let coeffs = vec![Scalar::from(2), Scalar::from(3), Scalar::from(4)];
        let polynomial = UniPolynomial::from_coeffs(&coeffs);
        let divisor = Scalar::from(1);
        let (q, r) = polynomial.div_by_linear_divisor(&divisor);
        println!("quotient_poly={}, remainder={}", scalar_vector_to_string(&q.coeffs), r);
        // assert_eq!(result, vec![Scalar::from(10), Scalar::from(7)]);
    }

    #[test]
    fn test_mul() {
        // f1(X) = 2X + 1
        // f2(X) = 2X - 1
        let f1 = Scalar::from_i64_vector(&vec![1, 2]);
        let f2 = Scalar::from_i64_vector(&vec![-1, 2]);

        let f1_poly = UniPolynomial::from_coeffs(&f1);
        let f2_poly = UniPolynomial::from_coeffs(&f2);

        // f3(X) = f1(X) * f2(X) = 4X^2 - 1
        let f3_poly = f1_poly.mul(&f2_poly);
        assert_eq!(f3_poly.coeffs, Scalar::from_i64_vector(&vec![-1, 0, 4]));
        assert_eq!(f3_poly.degree, 2);
    }

    #[test]
    fn test_division() {
        // f1(X) = X^3 + 2X^2 + 3X + 5
        // f2(X) = X + 2
        let f1 = ScalarExt::from_i64_vector(&[5, 3, 2, 1]);
        let f2 = ScalarExt::from_i64_vector(&[2, 1]);
        let f1_poly = UniPolynomial::from_coeffs(&f1);
        let f2_poly = UniPolynomial::from_coeffs(&f2);
        // q(X) = X^2 + 3
        // r(X) = -1
        let (q_poly, r_poly) = UniPolynomial::div(&f1_poly, &f2_poly);

        assert_eq!(q_poly.coeffs, Scalar::from_i64_vector(&[3, 0, 1]));
        assert_eq!(r_poly.coeffs, Scalar::from_i64_vector(&[-1]));

        let f3_poly = f2_poly.mul(&q_poly).add(&r_poly);
        assert_eq!(f1_poly.coeffs, f3_poly.coeffs);
        assert_eq!(f1_poly.degree, f3_poly.degree);
    }

    #[test]
    fn test_division_2() {
        let f1 = ScalarExt::from_i64_vector(&[3, 0, 1]);
        let f2 = ScalarExt::from_i64_vector(&[1, 1]);
        let f1_poly = UniPolynomial::from_coeffs(&f1);
        let f2_poly = UniPolynomial::from_coeffs(&f2); 
        let (q_poly, r_poly) = UniPolynomial::div(&f1_poly, &f2_poly);
        println!("q_poly={}", scalar_vector_to_string(&q_poly.coeffs));
        println!("r_poly={}", scalar_vector_to_string(&r_poly.coeffs));
        
        assert_eq!(q_poly.coeffs, vec![Scalar::from(-1), Scalar::from(1)]);
        assert_eq!(r_poly.coeffs, vec![Scalar::from(4)]);
    }

    #[test]
    fn test_vanishing_polynomial() {

        // f(X) = (X-1)(X-2)(X-3)(X-4)
        let domain = vec![Scalar::from(1), Scalar::from(2), Scalar::from(3), Scalar::from(4)];
        let result1 = UniPolynomial::vanishing_polynomial(&domain);
        let tree = UniPolynomial::contruct_subproduct_tree(&domain);
        let result2: Vec<Scalar> = tree[tree.len()-1][0].clone();
        assert_eq!(result1, result2);
        // The result should be 
        // f(X) = 24 - 50x + 35x^2 - 10x^3 + x^4 
        assert_eq!(result1, ScalarExt::from_i64_vector(&vec![24, -50, 35, -10, 1]));
    }

    #[test]
    fn test_evaluations_simple() {

        // f(X) = X^3 + 3X^2 - X + 1
        let coeffs = vec![Scalar::from(1), -Scalar::from(1), Scalar::from(3), Scalar::from(1)];
        let domain = vec![Scalar::from(0), Scalar::from(1), Scalar::from(2), Scalar::from(3)];

        let evals = vec![Scalar::from(1), Scalar::from(4), Scalar::from(19), Scalar::from(52)];

        let result1 = UniPolynomial::compute_evals_from_coeffs_fast(&coeffs, &domain);
        let result2 = UniPolynomial::compute_evals_from_coeffs_slow(&coeffs, &domain);
        
        assert_eq!(result1, result2);
        assert_eq!(result1, evals);

        // evals = [1, 4, 19, 52] = [0x01, 0x04, 0x13, 0x34]
        println!("result1={}", scalar_vector_to_string(&result1));
    }

    #[test]
    fn test_evaluations_random() {

        let rng = &mut ark_std::test_rng();
        let coeffs = Scalar::rand_vector(512, rng);
        let domain = Scalar::rand_vector(512, rng);

        let result1 = UniPolynomial::compute_evals_from_coeffs_fast(&coeffs, &domain);
        let result2 = UniPolynomial::compute_evals_from_coeffs_slow(&coeffs, &domain);
        
        assert_eq!(result1, result2);

        // evals = [1, 4, 19, 52] = [0x01, 0x04, 0x13, 0x34]
        println!("result1={}", scalar_vector_to_string(&result1));
    }


    #[test]
    fn test_karatsuba() {
        let a = ScalarExt::from_usize_vector(&vec![1, 2, 3, 4]); // Represents 1 + 2x + 3x^2 + 4x^3
        let b = ScalarExt::from_usize_vector(&vec![5, 6, 7, 8]); // Represents 5 + 6x + 7x^2 + 8x^3

        let result = UniPolynomial::karatsuba_multiplication(&a, &b);

        let c: Vec<Scalar> = ScalarExt::from_usize_vector(&vec![5, 16, 34, 60, 61, 44, 24]);
        // The result should be 5 + 16x + 34x^2 + 60x^3 + 61x^4 + 44x^5 + 24x^6
        let result2 = UniPolynomial::from_coeffs(&a).mul(&UniPolynomial::from_coeffs(&b)).coeffs;
        println!("result2={}", scalar_vector_to_string(&result2));
        // assert_eq!(result, c);
    }

    #[test]
    fn test_interpolation_simple() {
        // f(X) = [(0,1), (1,4), (2, 19), (3, 52)]
        // f(X) = X^3 + 3X^2 - X + 1

        let evals: Vec<Scalar> = Scalar::from_usize_vector(&[1, 4, 19, 52]);
        let H: Vec<Scalar> = Scalar::from_usize_vector(&[0, 1, 2, 3]);
        let result1: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_fast(&evals, &H);
        let coeffs = Scalar::from_i64_vector(&[1, -1, 3, 1]);
        
        let result2: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow(&evals, &H);
        let result3: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow_slow(&evals, &H);
        assert_eq!(result1, coeffs);
        assert_eq!(result2, coeffs);
        assert_eq!(result3, coeffs);
        // println!("coeffs={}", scalar_vector_to_string(&result1));
     }

     #[test]
     fn test_interpolation_evaluation() {
        let coeffs: Vec<Scalar> = ScalarExt::from_i64_vector(&vec![2,3,4,4,3,2,3,7]);
        let H: Vec<Scalar> = Scalar::from_usize_vector(&[0, 2, 3, 4, 5, 6, 7, 8]);
        let evals = UniPolynomial::compute_evals_from_coeffs_fast(&coeffs, &H);

        let result1: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_fast(&evals, &H);
        let result2: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow(&evals, &H);
        let result3: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow_slow(&evals, &H);
        // println!("result1={}", scalar_vector_to_string(&result1));
        // println!("result2={}", scalar_vector_to_string(&result2));
        assert_eq!(result1, coeffs);
        assert_eq!(result1, result2);
        assert_eq!(result1, result3);

      }

     #[test]
     fn test_interpolation_random() {
        let rng = &mut ark_std::test_rng();
        let evals: Vec<Scalar> = Scalar::rand_vector(64, rng);
        let H: Vec<Scalar> = Scalar::rand_vector(64, rng);

        let result1: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_fast(&evals, &H);
        let result2: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow(&evals, &H);
        let result3: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow_slow(&evals, &H);
        assert_eq!(result1, result2);
        assert_eq!(result1, result3);
      }

     #[test]
     fn test_interpolation_random_512() {
        let rng = &mut ark_std::test_rng();
        let evals: Vec<Scalar> = Scalar::rand_vector(1024, rng);
        let H: Vec<Scalar> = Scalar::rand_vector(1024, rng);

        let result1: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_fast(&evals, &H);
        let result2: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow(&evals, &H);
        assert_eq!(result1, result2);

        // NOTE: too slow to run
        // let result3: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow_slow(&evals, &H);
        // assert_eq!(result1, result3);
      }

    // #[test]
    // fn test_interpolation_again() {
    //     let evals: Vec<Scalar> = Scalar::from_usize_vector(&[99, 12, 3, 17, 18, 19, 32, 1]);
    //     let coeffs: Vec<Scalar> = UniPolynomial::lagrange_interpolation(&evals);
    //     for i in 0..8 {
    //         let eval_at_i = UniPolynomial::evaluate_from_coeffs(&coeffs, &Scalar::from_usize(i));
    //         assert_eq!(eval_at_i, evals[i], "eval failed at {}", i);
    //     }
    // }

    // #[test]
    // fn test_compute_coeffs_from_evals() {
    //     let evals: Vec<Scalar> = Scalar::from_usize_vector(&[99, 12, 3, 17, 18, 19, 32, 1]);
    //     let coeffs: Vec<Scalar> = UniPolynomial::lagrange_interpolation(&evals);
    //     let coeffs2: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals(&evals);
    //     println!("coeffs={}", scalar_vector_to_string(&coeffs));
    //     println!("coeffs2={}", scalar_vector_to_string(&coeffs2));
    //     for i in 0..evals.len() {
    //         let eval_at_i = UniPolynomial::evaluate_from_coeffs(&coeffs2, &Scalar::from_usize(i));
    //         assert_eq!(evals[i], eval_at_i, "test failed at {}", i);
    //     }

    // }

    // #[test]
    // fn test_evaluate_from_evals() {
    //     let rng = &mut ark_std::test_rng();
    //     let evals: Vec<Scalar> = Scalar::from_usize_vector(&[99, 12, 3, 17, 18, 19, 32, 1]);
    //     for i in 0..evals.len() {
    //         let eval_at_i = UniPolynomial::evaluate_from_evals(&evals, &Scalar::from_usize(i));
    //         assert_eq!(evals[i], eval_at_i, "test failed at {}", i);
    //     }

    //     let coeffs: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals(&evals);
    //     let zeta = Scalar::rand(rng);
    //     let eval_at_zeta_coeffs = UniPolynomial::evaluate_from_coeffs(&coeffs, &zeta);
    //     let eval_at_zeta_evals = UniPolynomial::evaluate_from_evals(&evals, &zeta);

    //     assert_eq!(eval_at_zeta_coeffs, eval_at_zeta_evals, "test failed at {}", zeta);
    // }

    // #[test]
    // fn test_interp_eval_degree_16_rep_1000() {

    //     let rng = &mut ark_std::test_rng();

    //     for i in 0..1000 {
    //         let evals: Vec<Scalar> = Scalar::rand_vector(16, rng);

    //         let coeffs: Vec<Scalar> = UniPolynomial::lagrange_interpolation(&evals);
    
    //         let rand = Scalar::rand(rng);
    
    //         let eval_at_rand = UniPolynomial::evaluate_from_coeffs(&coeffs, &rand);
    //         let eval_at_rand_prime = UniPolynomial::evaluate_from_evals(&evals, &rand);

    //         assert_eq!(eval_at_rand, eval_at_rand_prime, "test failed in round {}", i);
    //     }

    // }

    // #[test]
    // fn test_interp_eval_degree_128_rep_10() {

    //     let rng = &mut ark_std::test_rng();

    //     for i in 0..10 {
    //         let evals: Vec<Scalar> = Scalar::rand_vector(128, rng);

    //         let coeffs: Vec<Scalar> = UniPolynomial::lagrange_interpolation(&evals);
    
    //         let rand = Scalar::rand(rng);
    
    //         let eval_at_rand = UniPolynomial::evaluate_from_coeffs(&coeffs, &rand);
    //         let eval_at_rand_prime = UniPolynomial::evaluate_from_evals(&evals, &rand);

    //         assert_eq!(eval_at_rand, eval_at_rand_prime, "test failed in round {}", i);
    //     }
    // }

    // #[test]
    // fn test_new_from_evals() {
    //     // f(X) = X + 1
    //     let domain_size = 8;
    //     let evals: Vec<Scalar> = Scalar::from_usize_vector(&[1, 2, 3, 4, 5, 6, 7, 8]);
    //     let f = UniPolynomial::from_evals(&evals, 8);

    //     assert_eq!(f.degree, 1);
    //     assert_eq!(f.coeffs[7], Scalar::from(1));
    //     assert_eq!(f.coeffs[6], Scalar::from(1));
    // }

    // #[test]
    // fn test_new_from_coeffs() {
    //     // f(X) = X^2 + 1
    //     let domain_size = 8;
    //     let coeffs: Vec<Scalar> = Scalar::from_usize_vector(&[0, 0, 0, 0, 0, 1, 0, 1]);
    //     let f = UniPolynomial::from_coeffs(&coeffs, 8);

    //     assert_eq!(f.degree, 2);
    //     assert_eq!(f.evals[7], Scalar::from(50));
    //     assert_eq!(f.evals[6], Scalar::from(37));
    //     assert_eq!(f.evals[0], Scalar::from(1));
    // }

    // #[test]
    // fn test_new_from_coeffs_again() {
    //     // f(X) = X^2 + 1
    //     let domain_size = 8;
    //     let coeffs: Vec<Scalar> = Scalar::from_usize_vector(&[2, 0, 1]);
    //     let f = UniPolynomial::from_coeffs(&coeffs, 8);

    //     assert_eq!(f.degree, 2);
    //     println!("f.evals={}", scalar_vector_to_string(&f.evals));
    //     println!("f.coeffs={}", scalar_vector_to_string(&f.coeffs));
    // }

    #[test]
    fn test_contruct_subproduct_tree_fix() {
        let domain = vec![Scalar::from(1), Scalar::from(2), Scalar::from(3), Scalar::from(4)];
        let tree = UniPolynomial::contruct_subproduct_tree_fix(&domain);

        // The expected result is based on the actual behavior of your function
        // Here we assume the function returns a Node with a polynomial [-4, 1] for simplicity
        let expected_result = {
            let mut f = UniPolynomial::from_coeffs(&[Scalar::one()]);
            for u in domain.iter() {
                f = f.mul(&UniPolynomial::from_coeffs(&[-*u, Scalar::one()]));
            }
            f
        };

        assert_eq!(tree.poly, expected_result.coeffs);
    }

    #[test]
    fn test_compute_eval_fix() {
        let domain = vec![Scalar::from(0), Scalar::from(1), Scalar::from(2), Scalar::from(3), Scalar::from(4)];
        let tree = UniPolynomial::contruct_subproduct_tree_fix(&domain);

        let f = vec![Scalar::from(1), Scalar::from(0), Scalar::from(0), Scalar::from(1)];
        let evals = UniPolynomial::compute_eval_fix(&tree, &f, &domain);
        println!("evals={}", scalar_vector_to_string(&evals));

        let evals_expected: Vec<Scalar> = {
            let f_uni = UniPolynomial::from_coeffs(&f);
            domain.iter().map(|u| {
                f_uni.evaluate(u)
            }).collect()
        };
        println!("evals_expected={}", scalar_vector_to_string(&evals_expected));

        assert_eq!(evals, evals_expected);
    }

    #[test]
    fn test_compute_eval_fix2() {
        let domain = vec![Scalar::from(1), Scalar::from(2), Scalar::from(3)];
        let tree = UniPolynomial::contruct_subproduct_tree_fix(&domain);

        let f = vec![Scalar::from(5), Scalar::from(1), Scalar::from(5), Scalar::from(1), Scalar::from(5), Scalar::from(1)];
        let evals = UniPolynomial::compute_eval_fix(&tree, &f, &domain);
        println!("evals={}", scalar_vector_to_string(&evals));

        let evals_expected: Vec<Scalar> = {
            let f_uni = UniPolynomial::from_coeffs(&f);
            domain.iter().map(|u| {
                f_uni.evaluate(u)
            }).collect()
        };
        println!("evals_expected={}", scalar_vector_to_string(&evals_expected));

        assert_eq!(evals, evals_expected);
    }

    #[test]
    fn test_compute_linear_combination_linear_moduli_fix() {
        let domain = vec![
            Scalar::from(0), Scalar::from(1), 
            Scalar::from(2), Scalar::from(3), 
            Scalar::from(4)
        ];

        let n = domain.len();
        let tree = UniPolynomial::contruct_subproduct_tree_fix(&domain);

        let f = vec![Scalar::from(1), Scalar::from(0), Scalar::from(0), Scalar::from(1)];

        let f_derivative = UniPolynomial::compute_linear_combination_linear_moduli_fix(
            &tree, &vec![Scalar::one(); n], &domain);
        let f_derivative_at_u = UniPolynomial::compute_eval_fix(
            &tree, &f_derivative, &domain);
        let bary_centric_weights: Vec<Scalar> = f_derivative_at_u.iter().map(|e| e.inverse().unwrap()).collect();

        let ws = UniPolynomial::barycentric_weights(&domain);

        assert_eq!(bary_centric_weights, ws);
    }

    #[test]
    fn test_compute_coefficients_random() {
       let rng = &mut ark_std::test_rng();
       let evals: Vec<Scalar> = Scalar::rand_vector(65, rng);
       let H: Vec<Scalar> = Scalar::rand_vector(65, rng);

       let result1: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_fast(&evals, &H);
       let result2: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow(&evals, &H);
       let result3: Vec<Scalar> = UniPolynomial::compute_coeffs_from_evals_slow_slow(&evals, &H);
       assert_eq!(result1, result2);
       assert_eq!(result1, result3);
     }

}
