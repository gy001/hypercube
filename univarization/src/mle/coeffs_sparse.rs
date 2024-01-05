use crate::*;
use crate::bits::*;
use crate::mle::*;

/// MLE Polynomial in the (sparse) coefficients form
///
/// NOTE: We use a HashMap to store the non-zero coefficients of the polynomial
/// in terms of the sparse form. The keys of the HashMap represent the
/// exponents of the variables, and the values represent the corresponding
/// coefficients.
#[derive(Clone, Debug, PartialEq)]
pub struct MleCoeffs {
    coeffs: HashMap<usize, Scalar>,
    num_var: usize,
}

/// A divisor is a pair of (var-index, constant)
/// d = x_k - u_k = (k, u_k)
type Divisor = (usize, Scalar);

impl Display for MleCoeffs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut str = format!("MleCoeffs(num_var={})", self.num_var).to_string();
        for i in 0..pow_2(self.num_var) {
            if self.coeffs.contains_key(&i) {
                let c = self.coeffs.get(&i).unwrap();
                // if c.is_zero() {
                //     continue;
                // }
                str.push_str(&format!("{}*", ScalarExt::to_string(c)));
                for (j, b) in bits_BE(i, self.num_var).iter().rev().enumerate() {
                    if *b {
                        let s = format!("x_{}*", j);
                        str.push_str(if *b { &s } else { "" });
                    }
                }
                str.pop();
                str.push_str(" + ");
            }
        }
        str.pop();
        str.pop();
        str.pop();
        write!(f, "{}", str)
    }
}

impl MleCoeffs {

    pub fn new(coeffs: Vec<(usize, Scalar)>, num_var: usize) -> Self {
        Self {
            coeffs: coeffs.into_iter().collect(),
            num_var: num_var,
        }
    }

    pub fn from_coeffs(coeffs: &Vec<Scalar>, num_var: usize) -> Self {
        let mut coeffs_map: HashMap<usize, Scalar> = HashMap::new();
        for (i, c) in coeffs.iter().enumerate() {
            if !c.is_zero() {
                coeffs_map.insert(i, *c);
            }
        }
        Self {
            num_var: num_var,
            coeffs: coeffs_map,
        }
    }

    pub fn num_var(&self) -> usize {
        self.num_var
    }

    /// Check if the ordinal of any monomial < 2^{num_var}
    ///  e.g.   
    ///        X0X1 = b11    <  2^2  (valid for f(X0,X1))
    ///        X0X3  = b1001  <  2^4 (valid for f(X0,X1,X2,X3))
    ///        X1X2  = b110   >= 2^2 (invalid for f(X0,X1))
    ///        X2    = b100   >= 2^2 (invalid for f(X0,X1))
    pub fn is_valid(&self) -> bool {
        let n = self.num_var;
        let mut rs = true;
            for (k, _v) in self.coeffs.clone().iter() {
                if *k >= pow_2(n) {
                    rs = false;
                    break;
                }
            }
        rs
    }

    /// Extend the number of variables by delta
    /// 
    /// ```
    /// f(X0, X1) -> f(X0, X1, X2)
    /// ```
    /// 
    /// NOTE: succeed always
    pub fn expand_vars(&mut self, delta: usize) {
        assert!(delta > 0);
        self.num_var += delta;
    }

    /// Shrink the number of variables by delta
    // TODO: return failure if shrinking failed instead of panic
    fn exclude_var(&mut self, idx_var: usize) {
        assert!(idx_var < self.num_var);

        let num_bits = self.num_var;
        let mut bits = vec![false; num_bits];
        bits[idx_var] = true;
        println!("bits={:?}", bits);
        let mut new_coeffs = HashMap::new();
        for (k, v) in self.coeffs.clone().iter() {
            println!("k={}, v={}", k, v);
            let mut k_bits = bits_LE(*k, num_bits);
            println!("k_bits={:?}", k_bits);

            assert!(bits_nand(&k_bits, &bits));
            k_bits.remove(idx_var);
            let new_k = bits_LE_to_integer(&k_bits);
            new_coeffs.insert(new_k, *v);
        }
        self.num_var = num_bits - 1;
        self.coeffs = new_coeffs;
    }

    /// Lift the number of variables by delta
    pub fn lift_vars(&mut self, delta: usize) {
        assert!(delta > 0);
        let n = self.num_var;
        let mut coeffs: HashMap<usize, Scalar> = HashMap::new();
        for (t, c) in self.coeffs.clone().iter() {
            coeffs.insert(t * pow_2(delta), *c);
        }
        self.coeffs = coeffs;
        self.num_var = n + delta;
    }

    /// Turn a divisor into a MLE polynomial
    pub fn from_divisor(num_var: usize, div: &Divisor) -> Self {
        let (var, coeff) = div;
        let coeffs: HashMap<usize, Scalar> = vec![(pow_2(*var), Scalar::one()), (0, -*coeff)]
            .into_iter()
            .collect();
        Self {
            num_var: num_var,
            coeffs: coeffs,
        }
    }

}

impl MleCoeffs {

    /// Compute the addition of two MLE polynomials
    pub fn add(&self, mle: &Self) -> Self {
        // assert_eq!(self.num_var, mle.num_var);
        let num_var = if self.num_var > mle.num_var {
            self.num_var
        } else {
            mle.num_var
        };

        let mut coeffs = self.coeffs.clone();
        for (var, coeff) in mle.coeffs.iter() {
            if let Some(c) = coeffs.get_mut(var) {
                if (*c + coeff).is_zero() {
                    coeffs.remove(var);
                } else {
                    *c += coeff;
                }
            } else {
                coeffs.insert(*var, *coeff);
            }
        }
        Self {
            num_var: num_var,
            coeffs: coeffs,
        }
    }

    /// Compute the multiplication of two MLE polynomials,
    /// whose variables should be disjoint to each other,
    /// otherwise, the degree of the some variable will be greater than 1
    /// 
    /// NOTE: the two MLEs' `num_var` should be expanded to the same number beforehand
    pub fn mul(&self, mle: &Self) -> Self {
        // IMPORTANT: the two MLEs should have the same num_var
        assert!(self.num_var == mle.num_var); 

        let mut coeffs: HashMap<usize, Scalar> = HashMap::new();

        // Expand the variables range to the maximum
        let num_var = self.num_var;
        for (var1, coeff1) in self.coeffs.iter() {
            for (var2, coeff2) in mle.coeffs.iter() {
                // check if the two monomials are disjoint
                assert!(bits_nand(&bits_BE(*var1, num_var), &bits_BE(*var2, num_var)));

                // multiply the two monomials
                let var = var1 + var2;

                // multiply the coefficients
                let coeff = *coeff1 * coeff2;
                *coeffs.entry(var).or_insert(Scalar::zero()) += coeff;
            }
        }

        Self {
            coeffs: coeffs,
            num_var: self.num_var,
        }
    }

    /// Compute the multiplication of two MLE polynomials,
    /// whose variables are treated as disjoint sets and concatenated together.
    /// In this way, there will no variable conflict.
    /// 
    /// NOTE: please choose correct `mul()` for your case.
    pub fn mul_disjoint(&self, mle: &Self) -> Self {
        let n1 = self.num_var;
        let n2 = mle.num_var;
        let mut mle1 = self.clone();
        mle1.expand_vars(n2);
        let mut mle2 = mle.clone();
        mle2.lift_vars(n1);

        let mut coeffs: HashMap<usize, Scalar> = HashMap::new();

        // Expand the variables range to the maximum
        let num_var = n1+n2;
        for (var1, coeff1) in mle1.coeffs.iter() {
            for (var2, coeff2) in mle2.coeffs.iter() {
                // check if the two monomials are disjoint
                assert!(bits_nand(&bits_BE(*var1, num_var), &bits_BE(*var2, num_var)));

                // multiply the two monomials
                let var = var1 + var2;

                // multiply the coefficients
                let coeff = *coeff1 * coeff2;
                *coeffs.entry(var).or_insert(Scalar::zero()) += coeff;
            }
        }

        Self {
            coeffs: coeffs,
            num_var: num_var,
        }
    }


    /// Compute the division of two MLE polynomials. The second MLE has
    /// only one variable that is the right most variable of the first MLE.
    /// 
    /// NOTE: the values of `num_var` of the quotient and remainder 
    ///    are decreased by 1, as the dividend polynomial is *multi-linear*.
    fn div_by_linear_divisor(&self, divisor: &Scalar) -> (Self, Self) {
        let mut quotient: HashMap<usize, Scalar> = HashMap::new();
        let mut remainder: HashMap<usize, Scalar> = HashMap::new();

        let var = self.num_var - 1;
        for (monomial, coeff) in self.coeffs.iter() {
            if pow_2(var) & monomial == 0 {
                // Case: the var is not in the monomial
                *remainder.entry(*monomial).or_insert(Scalar::zero()) += *coeff;
            } else {
                // Case: the var is in the monomial
                let monomial_div = monomial - pow_2(var);
                *quotient.entry(monomial_div).or_insert(Scalar::zero()) += coeff;
                *remainder.entry(monomial_div).or_insert(Scalar::zero()) += *coeff * divisor;
            }
        }
        (
            Self {
                num_var: self.num_var - 1,
                coeffs: quotient,
            },
            Self {
                num_var: self.num_var - 1,
                coeffs: remainder,
            },
        )
    }

    // TODO: The following function, which divides a divisor whose variable 
    // is in the middle, might be useless. Remove it.

    /// Compute the division of two MLE polynomials. The second MLE has
    /// only one variable, which can be any variable.
    /// 
    /// The results are still two MLE polynomials, a 
    /// quotient and a remainder.
    /// 
    /// NOTE: the values of `num_var` of the quotient and remainder 
    ///    are decreased by 1, as the dividend polynomial is *multi-linear*.
    #[allow(dead_code)]
    fn div_by_any_linear_divisor(&self, divisor: &Divisor) -> (Self, Self) {
        let mut quotient: HashMap<usize, Scalar> = HashMap::new();
        let mut remainder: HashMap<usize, Scalar> = HashMap::new();
        let (var, cnst) = divisor;

        assert!(var < &self.num_var);

        for (monomial, coeff) in self.coeffs.iter() {
            if pow_2(*var) & monomial == 0 {
                // Case: the var is not in the monomial
                *remainder.entry(*monomial).or_insert(Scalar::zero()) += *coeff;
            } else {
                // Case: the var is in the monomial
                let monomial_div = monomial - pow_2(*var);
                *quotient.entry(monomial_div).or_insert(Scalar::zero()) += coeff;
                *remainder.entry(monomial_div).or_insert(Scalar::zero()) += *coeff * cnst;
            }
        }
        let mut quo = Self {
            num_var: self.num_var,
            coeffs: quotient,
        };
        let mut rem = Self {
            num_var: self.num_var,
            coeffs: remainder,
        };
        
        quo.exclude_var(*var);
        rem.exclude_var(*var);
        
        (quo, rem)
    }

    /// Trim all zero coefficients in the MLE polynomial to make it more sparse.
    pub fn trim(&mut self) {
        for (k, v) in self.coeffs.clone().iter() {
            if v.is_zero() {
                self.coeffs.remove(k);
            }
        }
    }

    /// Evaluate at the point: `(X_0, X_1, ..., X_{n-1})`
    pub fn evaluate(&self, point: &[Scalar]) -> Scalar {
        assert!(self.num_var <= point.len());

        let mut sum = Scalar::zero();
        for (var, coeff) in self.coeffs.iter() {
            let mut prod = *coeff;

            for (i, b) in bits_LE(*var, self.num_var).iter().enumerate() {
                if *b {
                    prod *= point[i];
                }
            }
            sum += prod;
        }
        sum
    }

    /// Compute partial evaluation from the right-most variable at (X{n_1} = r).
    /// 
    /// If `f(X_0, X_1, ..., X_{n-1})`, then compute 
    /// 
    /// ```
    /// g(X_0, X_1,...,X_{n-2}) = f(X_0, X_1,...,X_{n-2}, r)
    /// ```
    /// 
    /// where `r` is the folding factor.
    /// 
    /// NOTE: the partial evaluations is done from the right most variable.
    /// 
    pub fn partial_evaluate(&self, r: Scalar) -> Self {
        let mut coeffs_prime = HashMap::new();
        for (var, coeff) in self.coeffs.iter() {
            let half = pow_2(self.num_var-1);
            if var >= &half {
                *coeffs_prime.entry(*var - half).or_insert(Scalar::zero()) += r * *coeff;
            } else {
                *coeffs_prime.entry(*var).or_insert(Scalar::zero()) += *coeff;
            }
        }
        Self {
            num_var: self.num_var - 1,
            coeffs: coeffs_prime,
        }
    }

    /// Compute the entire coefficients of the MLE polynomial in the non-sparse form
    pub fn coefficients(&self) -> Vec<Scalar> {
        let mut coeffs = vec![Scalar::zero(); pow_2(self.num_var)];
        for (var, coeff) in self.coeffs.iter() {
            coeffs[*var] = *coeff;
        }
        coeffs
    }

    /// Compute all evaluations over hypercube.
    pub fn evaluations(&self) -> Vec<Scalar> {
        compute_evals_from_coeffs(self.num_var, &self.coefficients())
    }

    /// According to the univariate polynomial remainder theorem, we have
    ///
    /// ```
    ///     f(X) - f(u) = (X - u) * q(X)
    /// ```
    /// where `q(X)` is the quotient polynomial.
    /// 
    /// Correspondingly, we have a similar theorem for multivariate polynomials
    /// 
    /// ```
    ///    f(X_0, X_1, ..., X_{n-1}) - f(u_0, u_1, ..., u_{n-1}) =
    /// 
    ///      + (X_{n-1} - u_{n-1}) * q_{n-1}(X_0, X_1, ..., X_{n-2}) 
    ///      ... 
    ///      + (X_1     - u_1)     * q_1    (X_0)
    ///      + (X_0     - u_0      * q_0    ()    
    ///                              ^^^^^^^^^^ q_0 is a constant polynomial
    /// ```
    /// For more information, refer to [PST13]: https://eprint.iacr.org/2011/587
    ///

    /// Decompose the MLE polynomial at the point: `[u0, u1, ..., u_{n-1}]`
    /// The first approach is straightforward, i.e. divide the MLE repeatedly
    /// Returns `[q_0, q_1, ..., q_{n-1}]` where `q_i` is like `q_i(X0, X1, ..., X{i-1})`
    pub fn decompose_by_division(&self, point: &[Scalar]) -> Vec<MleCoeffs> {
        let mut quotients: Vec<MleCoeffs> = vec![];
        let mut coeffs = self.coeffs.clone();
        let v = self.evaluate(point);
        *coeffs.entry(0).or_insert(Scalar::zero()) -= v;
        let mut mle = MleCoeffs {
            num_var: self.num_var,
            coeffs: coeffs,
        };

        for i in (0..self.num_var).rev() {
            let (q, mut r) = mle.div_by_linear_divisor(&point[i]);
            quotients.insert(0, q);
            r.trim();
            mle = r;
        }
        quotients
    }

    /// The second approach is to use the folding technique.
    /// 
    /// Observe that, the quotient MLE polynomial (when divisor is (X_{n-1} - u_{n-1})) 
    /// is actually the higher part of the MLE coefficients. We fold the MLE 
    /// coefficients from `X_{n-1}` all the way to `X_0`, and conveniently store the higher part 
    /// as the quotient polynomial at each folding step. The final coefficent folded 
    /// is the remainder of the division, and interestingly, it is exactly the evaluation of 
    /// `f(u_0, u_1, ..., u_{n-1})` according to Ruffini's rule.

    /// Alternative approach to decompose the MLE into the quotients
    /// Returns `[q_0, q_1, ..., q_n-1]` where `q_i(X_0, X_1, ..., X_{i-1})`.
    pub fn decompose_by_division_alt(&self, point: &[Scalar]) -> Vec<MleCoeffs> {
        assert_eq!(point.len(), self.num_var);
        let mut coeffs = self.coeffs.clone();
        let mut quotients: Vec<MleCoeffs> = vec![];
        let mut num_var = self.num_var;

        for u in point.iter().rev() {
            num_var = num_var - 1;

            let mut quo_coeffs = HashMap::new();
            let half = pow_2(num_var);

            let mut coeffs_prime = HashMap::new();
            for (var, coeff) in coeffs.iter() {
                if var >= &half {
                    *coeffs_prime.entry(*var - half).or_insert(Scalar::zero()) += *coeff * u;
                    quo_coeffs.insert(*var - half, *coeff);
                } else {
                    *coeffs_prime.entry(*var).or_insert(Scalar::zero()) += *coeff;
                }
            }
            coeffs = coeffs_prime;

            quotients.insert(0,  MleCoeffs{
                num_var: num_var,
                coeffs: quo_coeffs,
            });
        };
        quotients
    }

    /// The third approach also uses the folding technique over 
    /// the sparse coefficients represented by a HashMap.
    pub fn decompose_by_division_alt_alt(&self, point: &[Scalar]) -> Vec<MleCoeffs> {
        assert_eq!(point.len(), self.num_var);

        let mut quotients: Vec<MleCoeffs> = vec![];
        let mut coeffs = self.coefficients();
        let mut num_var = self.num_var;

        // Iterate over the point vector in reverse order
        for p in point.iter().rev() {
            num_var = num_var - 1;
            let mut quo_coeffs = vec![Scalar::zero(); pow_2(num_var)];
            let half = pow_2(num_var);
            for j in 0..half {
                quo_coeffs[j] = coeffs[j + half];
                let prod = *p * coeffs[j + half];
                coeffs[j] += prod;
            }
            coeffs.truncate(half);
            let mut q_k = MleCoeffs{
                num_var: num_var,
                coeffs: quo_coeffs.into_iter().enumerate().collect(),
            };
            q_k.trim();
            quotients.insert(0, q_k);
        };
        quotients
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mle::evals::*;

    #[test]
    fn test_mle_coeffs_evaluate() {
        let coeffs = vec![
            (0b101, Scalar::from(2)),
            (0b010, Scalar::from(3)),
            (0b001, Scalar::from(4)),
        ].into_iter().collect();
        let num_var = 3;
        let poly = MleCoeffs{
            num_var: num_var,
            coeffs: coeffs, 
        };

        // Test evaluation at different points
        let point = vec![Scalar::from(1), Scalar::from(0), Scalar::from(1)];
        assert_eq!(poly.evaluate(&point), Scalar::from(6));

        let point = vec![Scalar::from(1), Scalar::from(1), Scalar::from(0)];
        assert_eq!(poly.evaluate(&point), Scalar::from(7));

        let point = vec![Scalar::from(0), Scalar::from(1), Scalar::from(1)];
        assert_eq!(poly.evaluate(&point), Scalar::from(3));

        let point = vec![Scalar::from(1), Scalar::from(1), Scalar::from(1)];
        assert_eq!(poly.evaluate(&point), Scalar::from(9));

        let point = vec![Scalar::from(2), Scalar::from(2), Scalar::from(2)];
        assert_eq!(poly.evaluate(&point), Scalar::from(22));
    }

    #[test]
    fn test_mle_add() {
        let poly1 = MleCoeffs {
            num_var: 2,
            coeffs: vec![
                (0b00, Scalar::from(1)),
                (0b01, Scalar::from(2)),
                (0b10, Scalar::from(3)),
                (0b11, Scalar::from(4)),
            ]
            .into_iter()
            .collect(),
        };
        let poly2 = MleCoeffs {
            num_var: 2,
            coeffs: vec![
                (0b00, Scalar::from(1)),
                (0b01, Scalar::from(2)),
                (0b10, Scalar::from(3)),
                (0b11, Scalar::from(4)),
            ]
            .into_iter()
            .collect(),
        };
        println!("poly1={}", &poly1);
        println!("poly2={}", &poly2);

        let poly3 = poly1.add(&poly2);
        println!("poly3={}", &poly3);
    }

    #[test]
    fn test_mle_mul_2() {
    // p1 = 2 + 2*x_0 + 3*x0*x1
    // p2 = x_2 - 1
    // p3 = p1 * p2 = (-2) - 2*x_0 - 3*x_0*x_1 + 2*x_2 + 2*x_0x_2 + 3*x_0*x_1*x_2
        let poly1 = MleCoeffs {
        num_var: 3,
        coeffs: vec![
            (0b00, Scalar::from(2)),
            (0b01, Scalar::from(2)),
            (0b11, Scalar::from(3)),
        ]
        .into_iter()
        .collect(),
    };
    let poly2 = MleCoeffs {
        num_var: 3,
        coeffs: vec![(0b00, -Scalar::from(1)), (0b100, Scalar::from(1))]
            .into_iter()
            .collect(),
    };

    let poly3 = poly1.mul(&poly2);
    assert_eq!(
        poly3,
        MleCoeffs {
            num_var: 3,
            coeffs: vec![
                (0b000, -Scalar::from(2)),
                (0b001, -Scalar::from(2)),
                (0b011, -Scalar::from(3)),
                (0b100, Scalar::from(2)),
                (0b101, Scalar::from(2)),
                (0b111, Scalar::from(3))
            ]
            .into_iter()
            .collect(),
        }
    );
    println!("poly3={}", &poly3);
}

    #[test]
    fn test_mle_mul() {
        // p1 = 2 + 2*x_0
        // p2 = 1 + 3*x_1
        // p3 = p1 * p2 = 2 + 2*x_0 + 6*x_1 + 6*x_0*x_1
        let poly1 = MleCoeffs {
            num_var: 2,
            coeffs: vec![(0b00, Scalar::from(2)), (0b01, Scalar::from(2))]
                .into_iter()
                .collect(),
        };
        let poly2 = MleCoeffs {
            num_var: 2,
            coeffs: vec![(0b00, Scalar::from(1)), (0b10, Scalar::from(3))]
                .into_iter()
                .collect(),
        };
        println!("poly1={}", &poly1);
        println!("poly2={}", &poly2);

        let poly3 = poly1.mul(&poly2);
        println!("poly3={}", &poly3);
    }

    #[test]
    fn test_mle_div_1() {
        init_logger();
        // p1 = 2 + 2X0 + 3X0X1
        // p2 = X0 - 1
        // p3 = p1 / p2 = (3X0, 2 + 5X0)
        let p1 = MleCoeffs {
            num_var: 2,
            coeffs: vec![
                (0b00, Scalar::from(2)),
                (0b01, Scalar::from(2)),
                (0b11, Scalar::from(3)),
            ]
            .into_iter()
            .collect(),
        };
        let d2: Divisor = (0, Scalar::from(1));
        let p2 = MleCoeffs::from_divisor(1, &d2);
        let p3 = MleCoeffs {
            num_var: 2,
            coeffs: vec![(0b00, -Scalar::from(1)), (0b01, Scalar::from(1))]
                .into_iter()
                .collect(),
        };
        let (quo, rem) = p1.div_by_linear_divisor(&Scalar::from(1));
        assert_eq!(&quo.coefficients(), &ScalarExt::from_i64_vector(&vec![0, 3]));
        assert_eq!(&rem.coefficients(), &ScalarExt::from_i64_vector(&vec![2, 5]));
        debug!("quo={}", scalar_vector_to_string(&quo.coefficients()));
        debug!("rem={}", scalar_vector_to_string(&rem.coefficients()));

        // p4 = quo * p2 + rem
        let p4 = quo.mul_disjoint(&p2).add(&rem);
        assert_eq!(p4, p1);
    }

    #[test]
    fn test_mle_div_2() {
        // p1 = -1 + X0X1X2
        // p2 = X0 - 1
        // (quo, rem) = p1 / p2 = (X1X2, X1X2-1)
        let p1 = MleCoeffs {
            num_var: 3,
            coeffs: vec![(0b000, -Scalar::from(1)), (0b111, Scalar::from(1))]
                .into_iter()
                .collect(),
        };
        let p3 = MleCoeffs {
            num_var: 2,
            coeffs: vec![(0b11, Scalar::from(1))]
                .into_iter()
                .collect(),
        };
        let p4 = MleCoeffs {
            num_var: 2,
            coeffs: vec![(0b00, -Scalar::from(1)), (0b11, Scalar::from(1))]
                .into_iter()
                .collect(),
        };
        let d2: Divisor = (0, Scalar::from(1));
        let (mut quo, mut rem) = p1.div_by_any_linear_divisor(&d2);

        assert_eq!(p3, quo);
        assert_eq!(p4, rem);

        let p5 = quo.mul_disjoint(&MleCoeffs::from_divisor(1, &d2)).add(&rem);
        
        assert_eq!(p1, p5);
        println!("quo={}", &quo);
        println!("rem={}", &rem);
        println!(
            "prod0={}",
            &quo.mul_disjoint(&MleCoeffs::from_divisor(3, &d2))
        );
    }


    #[test]
    fn test_decompose() {
        let mut rng = ark_std::test_rng();

        // Create a MLE instance with coefficients
        let coeffs = vec![
            (0b101, Scalar::from(2)),
            (0b010, Scalar::from(3)),
            (0b001, Scalar::from(4)),
        ];
        let num_var = 3;
        let mle = MleCoeffs::new(coeffs, num_var);

        // f(X0, X1, X2) = 2*X0X2 + 3*X1 + 4*X0

        // Test compute_quotients at different points
        let point = vec![Scalar::from(1), Scalar::from(0), Scalar::from(1)];
        let quotients1 = mle.decompose_by_division(&point);

        assert_eq!(quotients1.len(), 3);
        assert_eq!(quotients1[2].coeffs, vec![(0b001, Scalar::from(2))].into_iter().collect());
        assert_eq!(quotients1[1].coeffs, vec![(0b000, Scalar::from(3))].into_iter().collect());
        assert_eq!(quotients1[0].coeffs, vec![(0b000, Scalar::from(6))].into_iter().collect());

        println!("quotients1[0]={}", quotients1[0]);
        println!("quotients1[1]={}", quotients1[1]);
        println!("quotients1[2]={}", quotients1[2]);

        // challenge: zeta = (rand, rand, rand)
        let zeta = vec![Scalar::rand(&mut rng), Scalar::rand(&mut rng), Scalar::rand(&mut rng)];

        // check f(zeta) - f(point) = ∑ q_i(zeta) * (zeta[i] - point[i])
        let eval = mle.evaluate(&zeta) - mle.evaluate(&point);
        let eval_prime = quotients1.iter().enumerate().map(|(i, poly)| poly.evaluate(&zeta) * (zeta[i] - point[i])).sum::<Scalar>();
        assert_eq!(eval, eval_prime);

        // compare with other two approaches
        let quotients_alt = mle.decompose_by_division_alt(&point);
        assert_eq!(quotients_alt.len(), 3);
        let eval_prime = quotients_alt.iter().enumerate().map(|(i, poly)| poly.evaluate(&zeta) * (zeta[i] - point[i])).sum::<Scalar>();

        let quotients_alt2 = mle.decompose_by_division_alt_alt(&point);
        let eval_prime2 = quotients_alt2.iter().enumerate().map(|(i, poly)| poly.evaluate(&zeta) * (zeta[i] - point[i])).sum::<Scalar>();
        assert_eq!(eval, eval_prime2);
    }

    #[test]
    fn test_decompose_alt() {
        let mut rng = ark_std::test_rng();

        // Create a MLE instance with coefficients
        let coeffs = vec![
            (0b101, Scalar::from(2)),
            (0b010, Scalar::from(3)),
            (0b001, Scalar::from(4)),
        ];
        let num_var = 3;
        let mle = MleCoeffs::new(coeffs, num_var);

        // f(X0, X1, X2) = 2*X0X2 + 3*X1 + 4*X0

        // Test compute_quotients at different points
        let point = vec![Scalar::rand(&mut rng), Scalar::rand(&mut rng), Scalar::rand(&mut rng)];

        let eval = mle.evaluate(&point);
        println!("eval={}", ScalarExt::to_string(&eval));

        let quotients_1 = mle.decompose_by_division(&point);
        let quotients_2 = mle.decompose_by_division_alt(&point);
        let quotients_3 = mle.decompose_by_division_alt_alt(&point);
        assert_eq!(quotients_2.len(), 3);
        assert_eq!(quotients_3.len(), 3);
        println!("q0={}", &quotients_1[0]);

        for i in 0..num_var {
            assert_eq!(quotients_2[i].num_var, i);
            assert_eq!(quotients_3[i].num_var, i);
        }

        // challenge: zeta = (rand, rand, rand)
        let zeta = vec![Scalar::rand(&mut rng), Scalar::rand(&mut rng), Scalar::rand(&mut rng)];

        for i in 0..num_var {
            let qe1 = quotients_1[i].evaluate(&zeta);
            let qe2 = quotients_2[i].evaluate(&zeta);
            let qe3 = quotients_3[i].evaluate(&zeta);
            assert_eq!(qe1, qe2);
            assert_eq!(qe1, qe3);
        }
        let eval = mle.evaluate(&zeta) - mle.evaluate(&point);
        let eval_2 = quotients_2.iter().enumerate().map(
            |(i, qi)| qi.evaluate(&zeta) * (zeta[i] - point[i])
        ).sum::<Scalar>();
        assert_eq!(eval, eval_2);

        let eval_3 = quotients_3.iter().enumerate().map(
            |(i, qi)| qi.evaluate(&zeta) * (zeta[i] - point[i])
        ).sum::<Scalar>();
        assert_eq!(eval, eval_3);
    }

    #[test]
    fn test_compute_quotients() {
        let mut rng = ark_std::test_rng();

        // Create a MLE instance with coefficients
        let coeffs = vec![
            (0b101, Scalar::from(2)),
            (0b010, Scalar::from(3)),
            (0b001, Scalar::from(4)),
        ];
        let num_var = 3;
        let poly = MleCoeffs::new(coeffs, num_var);

        // f(X0, X1, X2) = 2*X0X2 + 3*X1 + 4*X0

        // Test compute_quotients at different points
        let point1 = vec![Scalar::from(1), Scalar::from(0), Scalar::from(1)];
        let quotients1 = poly.decompose_by_division(&point1);

        assert_eq!(quotients1.len(), 3);
        assert_eq!(quotients1[2].coeffs, vec![(0b001, Scalar::from(2))].into_iter().collect());
        assert_eq!(quotients1[1].coeffs, vec![(0b000, Scalar::from(3))].into_iter().collect());
        assert_eq!(quotients1[0].coeffs, vec![(0b000, Scalar::from(6))].into_iter().collect());

        println!("quotients1[0]={}", quotients1[0]);
        println!("quotients1[1]={}", quotients1[1]);
        println!("quotients1[2]={}", quotients1[2]);

        // challenge point 2: (rand, rand, rand)
        let zeta = vec![Scalar::rand(&mut rng), Scalar::rand(&mut rng), Scalar::rand(&mut rng)];

        let eval = poly.evaluate(&zeta) - poly.evaluate(&point1);
        let eval_prime = quotients1.iter().enumerate().map(|(i, poly)| poly.evaluate(&zeta) * (zeta[i] - point1[i])).sum::<Scalar>();
        assert_eq!(eval, eval_prime);

        let quotients_alt = poly.decompose_by_division_alt(&point1);
        assert_eq!(quotients_alt.len(), 3);
        let eval_prime = quotients_alt.iter().enumerate().map(|(i, poly)| poly.evaluate(&zeta) * (zeta[i] - point1[i])).sum::<Scalar>();

        let quotients_alt2 = poly.decompose_by_division_alt_alt(&point1);
        let eval_prime2 = quotients_alt2.iter().enumerate().map(|(i, poly)| poly.evaluate(&zeta) * (zeta[i] - point1[i])).sum::<Scalar>();
        assert_eq!(eval, eval_prime2);

    }

    #[test]
    fn test_decompose_alt_2() {
        let mut rng = ark_std::test_rng();

        // Create a MLE instance with coefficients
        let coeffs = vec![
            (0b101, Scalar::from(2)),
            (0b010, Scalar::from(3)),
            (0b001, Scalar::from(4)),
        ];
        let num_var = 3;
        let poly = MleCoeffs::new(coeffs, num_var);

        // f(X0, X1, X2) = 2*X0X2 + 3*X1 + 4*X0

        // Test compute_quotients at different points
        let point1 = vec![Scalar::rand(&mut rng), Scalar::rand(&mut rng), Scalar::rand(&mut rng)];

        let quotients_alt = poly.decompose_by_division_alt(&point1);
        assert_eq!(quotients_alt.len(), 3);
        
        for i in 0..num_var {
            assert_eq!(quotients_alt[i].num_var, i);
        }

        // challenge point 2: (rand, rand, rand)
        let zeta = vec![Scalar::rand(&mut rng), Scalar::rand(&mut rng), Scalar::rand(&mut rng)];
        let eval = poly.evaluate(&zeta) - poly.evaluate(&point1);
        let eval_prime = quotients_alt.iter().enumerate().map(
            |(i, poly)| poly.evaluate(&zeta) * (zeta[i] - point1[i])
        ).sum::<Scalar>();

        assert_eq!(eval, eval_prime);
    }

    #[test]
    fn test_compute_quotients_mle() {
        // Create a MLE instance with coefficients
        let coeffs = vec![
            (0b101, Scalar::from(2)),
            (0b010, Scalar::from(3)),
            (0b001, Scalar::from(4)),
        ];
        let num_var = 3;
        let poly = MleCoeffs::new(coeffs, num_var);

        // f(X0, X1, X2) = 2*X0X2 + 3*X1 + 4*X0

        let coeffs_full = poly.coefficients();
        let evals = compute_evals_from_coeffs(num_var, &coeffs_full);
        let poly_evals = MleEvals {
            num_var: num_var,
            evals: evals,
        };

        // Test compute_quotients at different points
        let point1 = vec![Scalar::from(1), Scalar::from(0), Scalar::from(1)];
        let quotients1 = poly.decompose_by_division(&point1);

        println!("quotients1[0]={}", quotients1[0]);
        println!("quotients1[1]={}", quotients1[1]);
        println!("quotients1[2]={}", quotients1[2]);

        let quotients_alt = MleEvals::decompose_by_div(&poly_evals, &point1);
        println!("quotients_alt[0]={}", quotients_alt[0]);
        println!("quotients_alt[1]={}", quotients_alt[1]);
        println!("quotients_alt[2]={}", quotients_alt[2]);

        // challenge point 2: (rand, rand, rand)
        let zeta = vec![Scalar::from(5), Scalar::from(2), Scalar::from(3)];
        // let zeta = vec![Scalar::rand(&mut rng), Scalar::rand(&mut rng), Scalar::rand(&mut rng)];
        for i in 0..num_var {
            assert_eq!(quotients1[i].evaluate(&zeta), quotients_alt[i].evaluate(&zeta[0..i]));
        }
    }


    #[test]
    fn test_mle_coeffs_new() {
        let coeffs = vec![(0, Scalar::one()), (1, Scalar::one())];
        let mle = MleCoeffs::new(coeffs, 2);
        assert_eq!(mle.coeffs.len(), 2);
        assert_eq!(mle.num_var, 2);
    }

    #[test]
    fn test_mle_coeffs_from_coeffs() {
        let coeffs = vec![Scalar::one(), Scalar::one()];
        let mle = MleCoeffs::from_coeffs(&coeffs, 2);
        assert_eq!(mle.coeffs.len(), 2);
        assert_eq!(mle.num_var, 2);
    }

    #[test]
    fn test_mle_coeffs_is_valid() {
        let coeffs = vec![(0, Scalar::one()), (1, Scalar::one())];
        let mle = MleCoeffs::new(coeffs, 2);
        assert_eq!(mle.is_valid(), true);

        let coeffs = vec![(0, Scalar::one()), (1, Scalar::one()), (2, Scalar::one())];
        let mle = MleCoeffs::new(coeffs, 1);
        assert_eq!(mle.is_valid(), false);
    }

    #[test]
    fn test_mle_coeffs_expand_vars() {
        let coeffs = vec![(0, Scalar::one()), (1, Scalar::one())];
        let mut mle = MleCoeffs::new(coeffs, 2);
        mle.expand_vars(1);
        assert_eq!(mle.num_var, 3);
    }

    #[test]
    fn test_mle_coeffs_lift_vars() {
        let coeffs = vec![(0, Scalar::one()), (1, Scalar::one())];
        let mut mle = MleCoeffs::new(coeffs, 2);
        mle.lift_vars(1);
        assert_eq!(mle.num_var, 3);
    }

    #[test]
    fn test_mle_coeffs_trim() {
        let coeffs = vec![(0, Scalar::one()), (1, Scalar::one())];
        let mut mle = MleCoeffs::new(coeffs, 2);
        mle.trim();
        assert_eq!(mle.coeffs.len(), 2);
    }
}