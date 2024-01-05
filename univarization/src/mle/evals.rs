use core::ops::Index;
use core::fmt::Display;
use core::fmt;
use std::ops::IndexMut;
use core::cmp::min;
use log::debug;
use std::collections::HashMap;

use crate::*;
use crate::mle::*;
use crate::mle::coeffs_sparse::*;

/// MLE Polynomial with (non-sparse) evaluations over hypercube.
#[derive(Debug, Clone)]
pub struct MleEvals {
    pub evals: Vec<Scalar>, // Hello, hypercube!
    pub num_var: usize,
}

impl Display for MleEvals {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let terms: Vec<String> = self
            .evals
            .iter()
            .enumerate()
            .map(|(i, term)| {
                format!("\n{}:{}", i, ScalarExt::to_string(term))
            })
            .collect();

        write!(f, "Polynomial.evals[{}]", terms.join(","))
    }
}

impl MleEvals {

    pub fn new(vs: &[Scalar]) -> Self {
        let vs_len = vs.len();
        let mut evals = vs.to_vec();
        let full_len = vs_len.next_power_of_two();

        let num_var = log_2(full_len);

        let padded_len = full_len - vs_len;
        let padded_vec = vec![Scalar::zero(); padded_len];

        evals.extend(padded_vec);

        Self {
            num_var: num_var,
            evals: evals,
        }
    }

    pub fn len(&self) -> usize {
        self.evals.len()
    }

    pub fn lift_vars(&self, prepend_num_var: usize) -> Self {
        let new_evals = (0..pow_2(self.num_var+prepend_num_var)).enumerate().map(
            |(k, _v)| {
                let k_high = k >> prepend_num_var;
                self.evals[k_high]
            }
        ).collect();

        Self {
            num_var: self.num_var + prepend_num_var,
            evals: new_evals,
        }
    }

    pub fn expand_vars(&self, append_num_var: usize) -> Self {
        let new_evals = (0..pow_2(self.num_var+append_num_var)).enumerate().map(
            |(k, _v)| {
                let k_low = k & (pow_2(self.num_var) - 1);
                self.evals[k_low]
            }
        ).collect();

        Self {
            num_var: self.num_var + append_num_var,
            evals: new_evals,
        }
    }

    // Fold the space from N-dim to (N-1)-dim
    // Partial evaluation at (Xn = r), and turns the MLE
    // from f(X0, X1, ..., Xn) to f(X0, X1, ..., X{n-1})
    pub fn fold_into_half(&mut self, rho: &Scalar) {
        let half = self.len() / 2;
        for i in 0..half {
            self.evals[i] = (Scalar::one() - rho) * self.evals[i] 
                + *rho * self.evals[i + half];
        }
        self.num_var -= 1;
        self.evals.truncate(half);
    }

    /// Partial evaluate f(X0, X1, ..., X{n-1}) at 
    /// 
    /// ```
    ///     (X{n-k}, X{n-k+1}, ..., X{n-1} = (r{n-k}, r{n-k+1})), 
    /// ```
    /// and return f(X0, X1, ..., X{n-k-1})
    ///
    /// NOTE: the length of `rs` might greater than num_var, if so,
    ///   the right most chunk of `rs` are chosen
    pub fn partial_evaluate(&self, rs: &[Scalar]) -> Self {
        let num_var = self.num_var;
        let mut evals = self.evals.clone();
        let num_round = min(num_var, rs.len());
        let mut half = self.len() / 2;
        let rho_vec: Vec<Scalar>= rs.iter().cloned().rev().take(num_round).collect();
        for rd in 0..num_round {
            for i in 0..half {
                evals[i] = (Scalar::one() - rho_vec[rd]) * evals[i] 
                + rho_vec[rd] * evals[i + half];
            }
            half = half/2;
        };
        evals.truncate(pow_2(num_var - num_round));
        Self {
            num_var: num_var - num_round,
            evals: evals,
        }
    }

    // Evaluate the polynomial at the point: (Xn,...,X1,X0) in O(n)
    pub fn evaluate(&self, rs: &[Scalar]) -> Scalar {
        assert_eq!(rs.len(), self.num_var);

        // chi is lagrange polynomials evaluated at rs
        let chi_vec = EqPolynomial::new(&rs.to_vec()).evals_over_hypercube();

        assert_eq!(chi_vec.len(), self.evals.len());
        (0..self.evals.len()).map(| i | chi_vec[i] * self.evals[i]).sum()
    }



    // Evaluate the polynomial at r with coefficients in O(n)
    // TODO: add check for the length of rs.
    // TODO: change the order of rs, so that it is consistent with (X0, X1, ..., Xn)
    pub fn evaluate_from_coeffs(coeffs: &[Scalar], rs: &[Scalar]) -> Scalar {
        assert!(coeffs.len().is_power_of_two());

        let mut evals = coeffs.to_vec();
        let mut rs = rs.to_vec();
        let num_rounds = log_2(evals.len());
        let mut half = evals.len();

        for _i in 0..num_rounds {
            half =  half / 2;
            let r = rs.pop().unwrap(); // TODO: let r = rs[i]
            for j in 0..half {
                evals[j] = evals[j*2] + r * evals[j*2+1];
            }
            evals.truncate(half);
        }
        evals[0]
    }

    /// Divide the polynomial at the point: `[X_0, X_1, ..., X_{n-1}]` in O(N) (Linear!)
    /// 
    /// Reference: Algorithm 8 in Appendix B, [XZZPS18] 
    ///              "Libra: Succinct Zero-Knowledge Proofs with Optimal Prover Computation"
    /// 
    /// Returns `[q_0, q_1, ..., q_{n-1}]` where q_i is a MLE as `q_i(X0, X1, ..., X_{i-1})`.
    #[allow(dead_code)]
    pub fn decompose_by_div(poly: &MleEvals, point: &[Scalar]) -> Vec<MleEvals> {
        let mut r = poly.evals.clone();
        let mut quotients: Vec<MleEvals> = vec![];
        let num_var = poly.num_var;
        for i in (0..num_var).rev() {
            let mut q = vec![Scalar::zero(); pow_2(i)];
            for j in 0..pow_2(i) {
                q[j] = r[j + pow_2(i)] - r[j];
                r[j] = r[j] * (Scalar::one() - point[i]) + r[j + pow_2(i)] * point[i];
            }
            quotients.insert(0, MleEvals {
                num_var: i,
                evals: q,
            });
        }
        quotients
    }

    pub fn to_coeffs(&self) -> Vec<Scalar> {
        compute_coeffs_from_evals(&self.evals)
    }

    pub fn from_coeffs(coeffs: &[Scalar], num_var: usize) -> Self {
        assert!(pow_2(num_var)>=coeffs.len());
        let evals = compute_evals_from_coeffs(num_var, coeffs);
        Self {
            num_var: num_var,
            evals: evals,
        }
    }
}

impl Index<usize> for MleEvals {
    type Output = Scalar;

    // TODO: inline
    fn index(&self, index: usize) -> &Self::Output {
        &(self.evals[index])
    }
}


#[cfg(test)]
#[allow(dead_code)]
#[allow(unused)]
#[allow(non_snake_case)]
mod tests {
    use crate::unipoly::UniPolynomial;

    use super::*;

    #[test]
    fn test_is_valid() {
        // give me a test case for is_valid():
        let coeffs = vec![
                    (0b101, Scalar::from(2)),
                    (0b010, Scalar::from(3)),
                    (0b001, Scalar::from(4)),
                    (0b100, Scalar::from(9)),
        ];
        let num_var = 3;
        let f_mle = MleCoeffs::new(coeffs.clone(), num_var);
        assert!(f_mle.is_valid());
        
        let g_mle = MleCoeffs::new(coeffs.clone(), 2);
        assert!(!g_mle.is_valid());
    }
    
    #[test]
    fn test_eq_evals_over_hypercube() {
        init_logger();

        let vs = Scalar::from_usize_vector(&[1,2,3]);
        let eq = EqPolynomial::new(&vs);
        let evals = eq.evals_over_hypercube();
        let evals_prime = eq.evals_over_hypercube_slow();
        assert_eq!(evals, evals_prime);
        debug!("evals={}", scalar_vector_to_string(&evals));
    }

    #[test]
    fn test_mle_evals_evaluate() {
        init_logger();

        // f(X0, X1) = [2, 3, 4, 5]
        // f(X0, X1) = 2 + X0 + 2X1
        let vs = Scalar::from_usize_vector(&[2,3,4,5]);
        let mle = MleEvals::new(&vs);
        debug!("mle.coeffs={}", scalar_vector_to_string(&mle.to_coeffs()));

        // f(2, 3) = 2 + 2 + 2*3 = 10
        let r = Scalar::from_usize_vector(&[2,3]);
        let e = mle.evaluate(&r);
        assert_eq!(e, Scalar::from(10));
    }

    #[test]
    fn test_partial_evaluate() {
        init_logger();

        // f(X0, X1, X2) = 1 + X0 + 2X1 + 4X2
        let mle = MleEvals {
            num_var: 3,
            evals: vec![Scalar::from(1), Scalar::from(2), Scalar::from(3), Scalar::from(4), 
                        Scalar::from(5), Scalar::from(6), Scalar::from(7), Scalar::from(8)],
        };
        let coeffs = mle.to_coeffs();
        debug!("mle.coeffs={}", scalar_vector_to_string(&coeffs));
        assert_eq!(&coeffs, &ScalarExt::from_i64_vector(&vec![1,1,2,0,4,0,0,0]));
        let rs = vec![Scalar::from(1), Scalar::from(2)];

        // f(X0, 1, 2) = 11 + X0
        let mle_1_2 = mle.partial_evaluate(&rs);
        assert_eq!(mle_1_2.num_var, 1);
        assert_eq!(mle_1_2.evals, vec![Scalar::from(11), Scalar::from(12)]);

        // f(X0, X1, 2) = 9 + X0 + 2X1 = g(X0, X1)
        let mle_2 = mle.partial_evaluate(&[Scalar::from(2)]);
        assert_eq!(mle_2.num_var, 2);
        assert_eq!(mle_2.evals, vec![Scalar::from(9), Scalar::from(10),Scalar::from(11),Scalar::from(12)]);

        // g(X0, 1) = ?
        let mle_2_1 = mle_2.partial_evaluate(&[Scalar::from(1)]);
        assert_eq!(mle_2_1.evals, mle_1_2.evals);
    }

    #[test]
    fn test_partial_evaluate_2() {
        
        // f() = 5
        let mle = MleEvals {
            num_var: 0,
            evals: vec![Scalar::from(5)],
        };
        let rs = vec![Scalar::from(1), Scalar::from(2)];

        // f(1,2) = f() = 5
        let mle_1 = mle.partial_evaluate(&rs);
        assert_eq!(mle_1.num_var, 0);
        assert_eq!(mle_1.evals, vec![Scalar::from(5)]);
    }

    #[test]
    fn test_partial_evaluate_3() {
        let mle = MleEvals {
            num_var: 3,
            evals: vec![Scalar::from(1), Scalar::from(2), Scalar::from(3), Scalar::from(4), 
                        Scalar::from(5), Scalar::from(6), Scalar::from(7), Scalar::from(8)],
        };
        // the actual rs = [-1, 1, 2]
        let rs = vec![Scalar::from(3), Scalar::from(-1), Scalar::from(1), Scalar::from(2)];

        let mle_1 = mle.partial_evaluate(&rs);
        assert_eq!(mle_1.num_var, 0);

        let eval = mle.evaluate(rs.split_at(1).1);
        assert_eq!(mle_1.evals, vec![Scalar::from(10)]);
        assert_eq!(eval, Scalar::from(10));
    }


    #[test]
    fn test_compute_coeffs_from_evals() {
        init_logger();

        let evals = ScalarExt::from_usize_vector(&vec![1, 2, 3, 4, 5, 6, 7, 8]);
        let coeffs: Vec<Scalar> = ScalarExt::from_i64_vector(&vec![1, 1, 2, 0, 4, 0, 0, 0]);
        let result = compute_coeffs_from_evals(&evals);
        assert_eq!(&coeffs, &result);
        debug!("mle.coeffs={}", scalar_vector_to_string(&result));
    }

    #[test]
    fn test_compute_evals_from_coeffs() {
        init_logger();

        let coeffs: Vec<Scalar> = ScalarExt::from_i64_vector(&vec![1, 1, 2, 0, 4, 0, 0, 0]);
        let evals: Vec<Scalar> = ScalarExt::from_usize_vector(&vec![1, 2, 3, 4, 5, 6, 7, 8]);
        let result = compute_evals_from_coeffs(3, &coeffs);
        assert_eq!(&evals, &result);
        debug!("mle.evals={}", scalar_vector_to_string(&result));
    }

    #[test]
    fn test_coeffs_evals_random() {
        init_logger();
        let rng = &mut ark_std::test_rng();
        let n = 20;
        let N = pow_2(n);
        let coeffs: Vec<Scalar> = ScalarExt::rand_vector(N, rng);
        let evals = compute_evals_from_coeffs(n, &coeffs);
        let coeffs_prime = compute_coeffs_from_evals(&evals);
        assert_eq!(&coeffs, &coeffs_prime);
    }

}