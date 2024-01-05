use crate::*;
use crate::mle::*;
use crate::mle::evals::*;

use core::ops::{IndexMut, Index};
use std::collections::HashMap;
use core::cmp::max;

#[derive(Debug, Clone)]
pub struct MleEvalsSparse {
    pub sparse_evals: HashMap<usize, Scalar>,
    pub num_var: usize,
    zero: Scalar,
}

impl MleEvalsSparse {

    pub fn new(vs: &HashMap<usize, Scalar>, num_var: usize) -> Self {
        let vs_len = vs.len();
        vs.iter().for_each(|(&k, &v)| {
            assert!(k < pow_2(num_var));
        });

        Self {
            num_var: num_var,
            sparse_evals: vs.clone(),
            zero: Scalar::zero(),
        }
    }

    pub fn from_evals(mle: &MleEvals) -> Self {
        let mut sparse_evals = HashMap::new();
        for (k, v) in mle.evals.iter().enumerate() {
            if !v.is_zero() {
                sparse_evals.insert(k, *v);
            }
        }
        Self {
            num_var: mle.num_var,
            sparse_evals: sparse_evals,
            zero: Scalar::zero(),
        }
    }

    pub fn to_evals(&self) -> MleEvals {
        let mut evals = vec![Scalar::zero(); pow_2(self.num_var)];
        for (k, v) in self.sparse_evals.iter() {
            evals[*k] = *v;
        }
        MleEvals {
            num_var: self.num_var,
            evals: evals,
        }
    }

    pub fn lift_vars(&mut self, prepend_num_var: usize) {
        let mut vs = HashMap::new();
        self.sparse_evals.iter().for_each(|(k, v)| {
            let mut k_prime = *k;
            k_prime <<= prepend_num_var;
            for i in 0..pow_2(prepend_num_var) {
                vs.insert(k_prime + i, *v);
            }
        });
        self.num_var += prepend_num_var;
        self.sparse_evals = vs;
    }

    pub fn expand_vars(&mut self, append_num_var: usize) {
        let mut vs = HashMap::new();
        self.sparse_evals.iter().for_each(|(k, v)| {
            let mut k_prime = *k;
            for i in 0..pow_2(append_num_var) {
                vs.insert(k_prime + (i<<append_num_var), *v);
            }
        });
        self.num_var += append_num_var;
        self.sparse_evals = vs;
    }

    pub fn len(&self) -> usize {
        pow_2(self.num_var)
    }

    // TODO: refractor the code to avoid code duplication
    pub fn fold_into_half(&mut self, rho: &Scalar) {
        let half = self.len() / 2;
        let mut new_sparse_evals = self.sparse_evals.clone();
        for (&k, v) in self.sparse_evals.iter() {
            if k >= half {
                let k_prime = k - half;
                let low = new_sparse_evals.entry(k_prime).or_insert(Scalar::zero());
                let high = v;
                let u = (Scalar::one() - rho) * *low + *rho * *high;
                if u != Scalar::zero() {
                    *low = u;
                } else {
                    new_sparse_evals.remove(&k_prime);
                }
                new_sparse_evals.remove(&k);
            } else {
                if self.sparse_evals.get(&(k + half)) == None {
                    *new_sparse_evals.entry(k).or_insert(Scalar::zero()) *= Scalar::one() - rho;
                }
            }
        }
        self.num_var -= 1;
        self.sparse_evals = new_sparse_evals;
    }

    pub fn partial_evaluate(&self, rs: &[Scalar]) -> Self {
        let num_var = self.num_var;
        let mut mle = self.clone();
        let num_rounds = 
            if num_var >= rs.len() {
                rs.len()
            } else {
                num_var
            };
        rs.iter().rev().take(num_rounds).for_each(|r| {
            mle.fold_into_half(r);
        });
        mle
    }

    pub fn partial_evaluate_in_place(&mut self, rs: &[Scalar]) -> usize {
        let num_var = self.num_var;
        if num_var == 0 {
            return 0;
        } else if num_var >= rs.len() {
            for r in rs.iter().rev() {
                self.fold_into_half(r);
            }
            return rs.len();
        } else if num_var < rs.len() {
            for r in rs.iter().rev().take(num_var) {
                self.fold_into_half(r);
            }
            return num_var;
        } else {
            unreachable!();
        }
    }

    // Evaluate the polynomial at the point: (X0, X1, ..., Xn) in O(n)
    pub fn evaluate(&self, rs: &[Scalar]) -> Scalar {
        assert_eq!(rs.len(), self.num_var);

        // chi is lagrange polynomials evaluated at rs
        let chi_vec = EqPolynomial::new(&rs.to_vec()).evals_over_hypercube();

        let mut sum = Scalar::zero();
        for (k, v) in self.sparse_evals.iter() {
            sum += chi_vec[*k] * v;
        }
        sum
    }
}

impl Index<usize> for MleEvalsSparse {
    type Output = Scalar;

    // TODO: inline
    fn index(&self, index: usize) -> &Self::Output {
        self.sparse_evals.get(&index).unwrap_or(&self.zero)
    }
}

impl IndexMut<usize> for MleEvalsSparse {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.sparse_evals.entry(index).or_insert(self.zero)
    }
}

impl MleEvalsSparse {

    // Concat two MLEs into one MLE with one more variable
    //   f(X0, X1, ..., X{n+1}) = 
    //       (1 - X{n+1}}) * f1(X0, X1, ..., Xn) + X{n+1} * f2(X0, X1, ..., Xn)
    // NOTE: If the num_vars of f1 and f2 are not the same, then 
    // the smaller one is padded with zeros. 
    
    pub fn append(&self, other: &Self) -> Self {
        let num_var = max(self.num_var, other.num_var);
        let mut sparse_evals = self.sparse_evals.clone();
        let half = pow_2(num_var);
        for (k, v) in other.sparse_evals.iter() {
            let en = sparse_evals.entry(*k + half).or_insert(Scalar::zero());
            *en += *v;
        }

        Self {
            sparse_evals: sparse_evals,
            num_var: num_var + 1,
            zero: Scalar::zero(),
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut sparse_evals = self.sparse_evals.clone();
        for (k, v) in other.sparse_evals.iter() {
            let en = sparse_evals.entry(*k).or_insert(Scalar::zero());
            *en += *v;
        }

        Self {
            sparse_evals: sparse_evals,
            num_var: self.num_var,
            zero: Scalar::zero(),
        }
    }

    pub fn mul_scalar(&self, scalar: &Scalar) -> Self {
        let mut sparse_evals = self.sparse_evals.clone();
        for (k, v) in sparse_evals.iter_mut() {
            *v *= *scalar;
        }

        Self {
            sparse_evals: sparse_evals,
            num_var: self.num_var,
            zero: Scalar::zero(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    
    #[test]
    fn test_to_from_evals() {
        let hs = HashMap::from(
            [
                (0b1 + 0b1 * pow_2(1) + 0b0 * pow_2(2), Scalar::one()), // 0b011 -> 1
                (0b0 + 0b1 * pow_2(1) + 0b1 * pow_2(2), Scalar::one()) // 0b110 -> 1
            ]);
        for (k, v) in hs.iter() {
            println!("hs: k={}, v={}", k, v);
        }

        let mut mle = MleEvalsSparse::new(&hs, 1+1+1);
        println!("eval={}", mle.evaluate(&[Scalar::from(1), Scalar::from(1), Scalar::from(0)]));
        println!("eval={}", mle.evaluate(&[Scalar::from(0), Scalar::from(1), Scalar::from(1)]));

        let mut evals = vec![Scalar::zero(); pow_2(mle.num_var)];
        for (k, v) in mle.sparse_evals.iter() {
            println!("k={}, v={}", k, v);
            evals[*k] = *v;
        }
        println!("evals={}", scalar_vector_to_string(&evals));

        let mle2 = mle.to_evals();
        println!("mle2={}", scalar_vector_to_string(&mle2.evals));

        let mle3 = MleEvalsSparse::from_evals(&mle2);
        for (k, v) in mle3.sparse_evals.iter() {
            println!("mle3: k={}, v={}", k, v);
        }
    }

    #[test]
    fn test_lift_vars() {
        let hs = HashMap::from(
            [
                (0b1 + 0b1 * pow_2(1) + 0b0 * pow_2(2), Scalar::one()), // 0b011 -> 1
                (0b0 + 0b1 * pow_2(1) + 0b1 * pow_2(2), Scalar::one()) // 0b110 -> 1
            ]);
        let mut mle = MleEvalsSparse::new(&hs, 3);
        mle.lift_vars(2);

        assert_eq!(mle.to_evals().evals[0b01100], Scalar::one());
        assert_eq!(mle.to_evals().evals[0b11000], Scalar::one());
        assert_eq!(mle.to_evals().evals[0b00000], Scalar::zero());
        assert_eq!(mle.to_evals().evals[0b00110], Scalar::zero());
        assert_eq!(mle.to_evals().evals[0b00011], Scalar::zero());
    }

    #[test]
    fn test_expand_vars() {
        let hs = HashMap::from(
            [
                (0b1 + 0b1 * pow_2(1) + 0b0 * pow_2(2), Scalar::one()), // 0b011 -> 1
                (0b0 + 0b1 * pow_2(1) + 0b1 * pow_2(2), Scalar::one()) // 0b110 -> 1
            ]);
        let mut mle = MleEvalsSparse::new(&hs, 3);
        mle.expand_vars(2);
        
        assert_eq!(mle.to_evals().evals[0b01100], Scalar::one());
        assert_eq!(mle.to_evals().evals[0b11000], Scalar::one());
        assert_eq!(mle.to_evals().evals[0b00000], Scalar::zero());
        assert_eq!(mle.to_evals().evals[0b00110], Scalar::zero());
        assert_eq!(mle.to_evals().evals[0b00011], Scalar::zero());
    }

    #[test]
    fn test_fold() {

        let mut rng = ark_std::test_rng();

        let hs = HashMap::from(
            [
                (0b0 + 0b0 * pow_2(1) + 0b0 * pow_2(2), Scalar::two()), // 0b011 -> 1
                (0b1 + 0b1 * pow_2(1) + 0b0 * pow_2(2), Scalar::one()), // 0b011 -> 1
                (0b0 + 0b1 * pow_2(1) + 0b1 * pow_2(2), Scalar::one()), // 0b110 -> 1
                (0b0 + 0b1 * pow_2(1) + 0b0 * pow_2(2), Scalar::from(9)), // 0b010 -> 1
                (0b0 + 0b1 * pow_2(1) + 0b0 * pow_2(2), Scalar::from(9)) // 0b010 -> 1
            ]);
        let mut mle = MleEvalsSparse::new(&hs, 3);
        let mut mle_evals = mle.to_evals();

        // sample a folding factor
        let rho = Scalar::rand(&mut rng);

        // fold two identical mles
        mle.fold_into_half(&rho);
        mle_evals.fold_into_half(&rho);

        // test the equality of two folded mles
        let rs = Scalar::rand_vector(2, &mut rng);
        assert_eq!(mle.evaluate(&rs), mle_evals.evaluate(&rs));
    }

    #[test]
    fn test_fold_2() {

        let mut rng = ark_std::test_rng();

        // Assume H(4) = 1, H(0) = 2, if rho = 2, then
        //    (1-2) * H(0) + 2 * H(4) = 0
        // TEST: the keys of both H(0) and H(4) shall be removed
        let hs = HashMap::from(
            [
                (0b0 + 0b0 * pow_2(1) + 0b0 * pow_2(2), Scalar::two()), // 0b000 -> 2
                (0b1 + 0b1 * pow_2(1) + 0b0 * pow_2(2), Scalar::one()), // 0b011 -> 1
                (0b0 + 0b1 * pow_2(1) + 0b1 * pow_2(2), Scalar::one()), // 0b110 -> 1
                (0b0 + 0b1 * pow_2(1) + 0b0 * pow_2(2), Scalar::from(9)), // 0b010 -> 1
                (0b0 + 0b0 * pow_2(1) + 0b1 * pow_2(2), Scalar::from(1)) // 0b010 -> 1
            ]);
        let mut mle = MleEvalsSparse::new(&hs, 3);
        let mut mle_evals = mle.to_evals();
        
        // use a specific folding factor
        let rho = Scalar::from(2);

        // fold the two mles
        mle.fold_into_half(&rho);
        mle_evals.fold_into_half(&rho);

        // test equality
        let rs = Scalar::rand_vector(2, &mut rng);
        assert_eq!(mle.evaluate(&rs), mle_evals.evaluate(&rs));
    }

    #[test]
    fn test_partial_evaluate() {

        let rng = &mut ark_std::test_rng();

        let mut evals = vec![Scalar::zero(); 8];
        evals[0b011] = Scalar::rand(rng);
        evals[0b110] = Scalar::rand(rng);

        let rs = Scalar::rand_vector(3, rng);

        let mle = MleEvals::new(&evals);
        let e = mle.evaluate(&rs);        

        println!("e={}", e);

        let hs = HashMap::from(
            [
                (0b1 + 0b1 * pow_2(1) + 0b0 * pow_2(2), evals[0b011]), // 0b011 -> r1
                (0b0 + 0b1 * pow_2(1) + 0b1 * pow_2(2), evals[0b110]) // 0b110 -> r2
            ]);

        let mut mle2 = MleEvalsSparse::new(&hs, 3);

        mle2.partial_evaluate(&rs);
        println!("mle2={}", mle2.to_evals());
        let mle3 = mle.partial_evaluate(&rs);
        println!("mle3={}", mle3);
    }

    #[test]
    fn test_add() {
        let mut sparse_evals1 = HashMap::new();
        sparse_evals1.insert(1, Scalar::from(2));
        sparse_evals1.insert(2, Scalar::from(8));
        let mle1 = MleEvalsSparse {
            sparse_evals: sparse_evals1,
            num_var: 2,
            zero: Scalar::zero(),
        };

        let mut sparse_evals2 = HashMap::new();
        sparse_evals2.insert(1, Scalar::from(3));
        sparse_evals2.insert(3, Scalar::from(5));
        let mle2 = MleEvalsSparse {
            sparse_evals: sparse_evals2,
            num_var: 2,
            zero: Scalar::zero(),
        };

        let result = mle1.add(&mle2);
        assert_eq!(result.sparse_evals.get(&1), Some(&Scalar::from(5)));
        assert_eq!(result.sparse_evals.get(&2), Some(&Scalar::from(8)));
        assert_eq!(result.sparse_evals.get(&3), Some(&Scalar::from(5)));
        assert_eq!(result.sparse_evals.get(&0), None);
    }

    #[test]
    fn test_mul_scalar() {
        let mut sparse_evals = HashMap::new();
        sparse_evals.insert(1, Scalar::from(2));
        sparse_evals.insert(2, Scalar::from(4));
        let mle = MleEvalsSparse {
            sparse_evals: sparse_evals,
            num_var: 2,
            zero: Scalar::zero(),
        };

        let scalar = Scalar::from(10);
        let result = mle.mul_scalar(&scalar);
        assert_eq!(result.sparse_evals.get(&1), Some(&Scalar::from(20)));
        assert_eq!(result.sparse_evals.get(&2), Some(&Scalar::from(40)));
        assert_eq!(result.sparse_evals.get(&0), None);
    }



}