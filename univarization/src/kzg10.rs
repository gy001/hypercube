use crate::*;

use crate::groupsim::*;
use crate::unipoly::UniPolynomial;

use log::{debug, info, warn};

// use ark_poly::domain;
use ark_std::rand::Rng;
// use ark_ec::msm::{FixedBaseMSM, VariableBaseMSM};
// use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::ToBytes;
use ark_std::{io::Write, vec::Vec};

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
    pub internal_values: Vec<Scalar>, // for DEBUG (TODO: to be removed)
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

        Commitment {
            group_element: self.group_element.add(&rhs.group_element),
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

        Commitment {
            group_element: self.group_element.sub(&rhs.group_element),
            internal_values: cv,
        }
    }

    pub fn mul_scalar(&self, s: &Scalar) -> Self {
        let mut cv: Vec<Scalar> = Vec::new();
        let av = &self.internal_values;
        for (i, av) in av.iter().enumerate() {
            cv.push((*s) * (*av));
        }
        Commitment {
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
    pub fn setup<R: Rng>(max_degree: usize, rng: &mut R) -> Self {
        debug!("[setup] start to setup...");

        // generate the trapdoor: τ
        let tau = Scalar::rand(rng);

        let g1 = G1::generator();
        let g2 = G2::generator();

        debug!("[setup] generate...ok.");

        let mut powers_of_tau = vec![Scalar::one()];

        let mut cur = tau;
        for _ in 0..=max_degree {
            powers_of_tau.push(cur);
            cur *= &tau;
        }

        let powers_of_g1: Vec<G1> = (0..max_degree)
            .map(|i| g1.mul_scalar(&powers_of_tau[i]))
            .collect();
        let powers_of_g2: Vec<G2> = (0..max_degree)
            .map(|i| g2.mul_scalar(&powers_of_tau[i]))
            .collect();

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
        Self { srs: srs }
    }

    // pub fn commit(&self, polynomial: &UniPolynomial) -> Commitment {

    //     assert!(polynomial.degree < self.srs.max_degree);

    //     let coeffs = &polynomial.coeffs;

    //     Commitment {
    //         values: coeffs.clone(),
    //     }
    // }

    /// Commit a polynomial in the form of a vector of coefficients
    pub fn commit_uni_poly(&self, poly: &UniPolynomial) -> Commitment {
        assert!(poly.degree < self.srs.max_degree);

        let coeffs = &poly.coeffs;

        let powers_of_g1 = &self.srs.powers_over_G1;

        let values: Vec<G1> = coeffs
            .iter()
            .enumerate()
            .map(|(i, c)| powers_of_g1[i].mul_scalar(c))
            .collect();

        let mut g = G1::identity();
        for i in 0..values.len() {
            g = g.add(&values[i]);
        }

        Commitment {
            group_element: g,
            internal_values: coeffs.clone(),
        }
    }

    pub fn open_uni_poly(&self, cm: &Commitment, poly: &UniPolynomial) -> bool {
        let coeffs = &poly.coeffs;
        let powers_of_g1 = &self.srs.powers_over_G1;
        let g = coeffs
            .iter()
            .zip(powers_of_g1.iter())
            .map(|(c, g)| g.mul_scalar(c))
            .fold(G1::identity(), |acc, x| acc.add(&x));
        g == cm.group_element
    }

    /// Commit a polynomial in the form of a vector of evaluations
    pub fn commit_poly_evals(&self, srs: &[G1], evals: &[Scalar], log_size: usize) -> Commitment {
        let domain_size = pow_2(log_size);
        assert_eq!(evals.len(), domain_size);
        assert_eq!(srs.len(), domain_size);

        let mut g = G1::identity();
        for i in 0..evals.len() {
            g = g.add(&srs[i].mul_scalar(&evals[i]));
        }
        Commitment {
            group_element: g,
            internal_values: evals.to_vec(),
        }
    }

    pub fn commit_values(&self, values: &[Scalar]) -> Commitment {
        assert!(values.len() < self.srs.max_degree);

        let powers_of_g1 = &self.srs.powers_over_G1;

        let cm_vec: Vec<G1> = values
            .iter()
            .enumerate()
            .map(|(i, c)| powers_of_g1[i].mul_scalar(c))
            .collect();

        let mut cm = G1::identity();
        for i in 0..values.len() {
            cm = cm.add(&cm_vec[i]);
        }
        Commitment {
            group_element: cm,
            internal_values: values.to_vec(),
        }
    }

    pub fn open_with_values(&self, cm: &Commitment, values: &[Scalar]) -> bool {
        let s_vec = &cm.internal_values;
        assert_eq!(s_vec.len(), values.len());

        s_vec
            .iter()
            .zip(values.iter())
            .map(|(&c, &s)| c == s)
            .fold(true, |acc, x| acc && x)
    }

    pub fn prove_eval(&self, poly: &UniPolynomial, u: &Scalar) -> (Scalar, EvalArgument) {
        let v = poly.evaluate(u);
        let (q, r) = poly.sub_scalar(&v).div_by_linear_divisor(u);
        assert_eq!(r, Scalar::zero());
        assert_eq!(
            q.evaluate(&(*u + Scalar::one())) * (*u + Scalar::one() - u),
            poly.evaluate(&(*u + Scalar::one())) - v
        );
        let cm_q = self.commit_uni_poly(&q);
        (v, EvalArgument { commitment: cm_q })
    }

    // ([f]-v[1]) * 1 = [q] * ([τ] - u[1])
    // ([f] - [v] + u[q]) * [1] = [q] * [τ]
    pub fn verify_eval(&self, cm: &Commitment, u: &Scalar, v: &Scalar, prf: &EvalArgument) -> bool {
        let f_cm = cm.group_element.clone();
        let q_cm = prf.commitment.group_element.clone();
        let v_cm = self.srs.g.mul_scalar(v);
        let uq_cm = q_cm.mul_scalar(u);
        let lhs = pairing(&(f_cm.sub(&v_cm).add(&uq_cm)), &self.srs.h);
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
    pub fn prove_degree_bound(&self, f: &UniPolynomial, deg_bound: usize) -> DegreeBoundArgument {
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
    pub fn verify_degree_bound(
        &self,
        f_cm: &Commitment,
        deg_bound: usize,
        deg_arg: &DegreeBoundArgument,
    ) -> bool {
        assert_eq!(deg_arg.max_degree, self.srs.max_degree);

        let x_in_g2 = &self.srs.powers_over_G2[deg_arg.max_degree - deg_bound - 1];
        let fx_cm = &deg_arg.commitment;
        let lhs = pairing(&f_cm.group_element, x_in_g2);
        let rhs = pairing(&fx_cm.group_element, &self.srs.h);
        lhs == rhs
    }

    pub fn prove_eval_and_deg(
        &self,
        f: &UniPolynomial,
        u: &Scalar,
        deg_bound: usize,
    ) -> (Scalar, EvalArgument, DegreeBoundArgument) {
        let (v, prf) = self.prove_eval(&f, &u);
        let deg_prf = self.prove_degree_bound(&f, deg_bound);
        (v, prf, deg_prf)
    }

    pub fn verify_eval_and_deg(
        &self,
        f_cm: &Commitment,
        u: &Scalar,
        v: &Scalar,
        deg_bound: usize,
        eval_prf: &EvalArgument,
        deg_prf: &DegreeBoundArgument,
    ) -> bool {
        self.verify_eval(&f_cm, &u, &v, &eval_prf)
            && self.verify_degree_bound(&f_cm, deg_bound, &deg_prf)
    }

    pub fn check_commitment(&self, cm: &Commitment, poly: &UniPolynomial) -> bool {
        let coeffs = &poly.coeffs;
        let s_vec = &cm.internal_values;
        coeffs
            .iter()
            .zip(s_vec.iter())
            .map(|(&c, &s)| c == s)
            .fold(true, |acc, x| acc && x)
    }
}

impl KZG10PCS {

    /// core algorithm for FFT and iFFT over group G1
    /// 
    /// # Arguments
    /// - `gs`: the vector of group elements to be transformed
    /// - `omega`: the root of unity
    /// - `log_size`: the log of the size of the domain
    /// 
    /// # Return
    /// - mutated `gs`
    /// 
    fn _fft_over_group(gs: &mut Vec<G1>, omega: &Scalar, log_size: usize) {
        let n = pow_2(log_size);
        assert_eq!(gs.len(), n);
        assert!(n.is_power_of_two());

        let n_inv = Scalar::from_usize(n).inverse().unwrap();

        // bit-reversing
        for k in 0..n {
            let k_rev = crate::bits::bit_reverse(k, log_size);
            if k < k_rev {
                gs.swap(k, k_rev);
            }
        }

        let mut sep = 1;
        for _ in 0..log_size {
            let mut w = Scalar::one();
            for j in 0..sep {
                for i in (0..n).step_by(2 * sep) {
                    let l = i + j;
                    let r = i + j + sep;
                    let tmp = gs[r].mul_scalar(&w);
                    gs[r] = gs[l].sub(&tmp);
                    gs[l] = gs[l].add(&tmp);
                }
                w = w * omega.exp(n / (2 * sep));
            }
            sep *= 2;
        }
    }

    pub fn compute_interpolation_over_group(evals_over_group: &[G1], log_size: usize) -> Vec<G1> {
        let n = pow_2(log_size);
        assert_eq!(evals_over_group.len(), n);
        assert!(n.is_power_of_two());
        let mut coeffs_over_group = evals_over_group.to_vec();

        let omega = UniPolynomial::get_root_of_unity(log_size)
            .inverse()
            .unwrap();
        let n_inv = Scalar::from_usize(n).inverse().unwrap();

        Self::_fft_over_group(&mut coeffs_over_group, &omega, log_size);
        coeffs_over_group
            .iter_mut()
            .for_each(|e| *e = e.mul_scalar(&n_inv));
        coeffs_over_group
    }

    pub fn compute_evaluation_over_group(coeffs_over_group: &[G1], log_size: usize) -> Vec<G1> {
        let n = pow_2(log_size);
        assert_eq!(coeffs_over_group.len(), n);
        assert!(n.is_power_of_two());
        let mut evals_over_group = coeffs_over_group.to_vec();

        let omega = UniPolynomial::get_root_of_unity(log_size);

        Self::_fft_over_group(&mut evals_over_group, &omega, log_size);
        evals_over_group
    }

    /// Compute the h polynomial over group G1.
    /// 
    /// # Arguments
    /// 
    /// - `f`: the polynomial to be computed,  len(f) = 2^k
    /// - `gs`: the powers of tau SRS, gs = {[1], [τ], [τ^2], ..., [τ^{n-1}]}, n=2^k
    /// 
    /// # Return
    /// 
    /// - `h`: the (coeffients of) polynomial `h(Y)` over group G1
    /// 
    /// The h polynomial is similar to the quotient polynomial `f(X)/(X-u)`, except that
    /// the latter is over the field `Fp` while the former is over the group `G1`.
    /// 
    /// ```
    ///   h(X) = h_0 + h_1*X + h_2*X^2 ... + h_{d-1}*X^{d-1}
    ///        = f(X) / (X-u)
    /// 
    ///   where d = deg(f) 
    /// ``` 
    /// 
    /// For any polynomial `f` has the following property: 
    /// WLOG, we assume that `f(X) = f_0 + f_1 * X + f_2 * X^2`.
    /// 
    /// ```
    ///  f(X) - f(u)
    ///   
    ///  = [1, X, X^2] * | f_2, f_1, f_0 | * | u^2 |
    ///                  | 0  , f_2, f_1 |   | u   | 
    ///                  | 0  , 0  , f_2 |   | 1   |
    ///   
    ///  = [1, u, u^2] * | f_2, f_1, f_0 | * | X^2 |
    ///                  | 0  , f_2, f_1 |   | X   | 
    ///                  | 0  , 0  , f_2 |   | 1   |
    /// ``` 
    /// Therefore, 
    /// 
    ///  we compute a polynomial `h(Y)` over group `G1` such that
    ///     
    /// ```
    ///     h(Y)= (1, Y, Y^2) * (h_0, h_1, h_2)
    /// 
    /// where 
    ///    |  h_0  |  = | h_2, h_1, h_0 | * | [τ^2] |
    ///    |  h_1  |    | 0  , h_2, h_1 |   | [τ]   | 
    ///    |  h_2  |    | 0  , 0  , h_2 |   | [1]   |  
    /// ```
    /// 
    /// Here `h(Y)` (in coeffient form) can be used to compute any commitment 
    /// of quotient corresponding to `(f(X)-f(Y))/(X-Y)`.
    /// 
    fn compute_h(f: &[Scalar], gs: &[G1]) -> Vec<G1> {
        let n = f.len();
        assert!(n.is_power_of_two());

        let s = log_2(n);
        let domain_2n = UniPolynomial::fft_domain(s + 1);

        // g_ext = [τ^{n-1}, τ^{n-2}, ..., τ, 1, 0, 0, ..., 0]
        let g_vec = {
            let mut g = gs.to_vec();
            g.reverse();
            // g = [τ^{n-1}], [τ^{n-2}], ..., [τ], [1]]
            g.extend(vec![G1::identity(); n]);
            g
        };
        let y_ext = Self::compute_evaluation_over_group(&g_vec, s + 1);

        let f_ext = {
            let mut f_ext = vec![Scalar::zero(); n];
            f_ext.extend(f);
            f_ext
        };

        let v_ext = UniPolynomial::ntt_evals_from_coeffs(&f_ext, s + 1);

        let u_ext = {
            let mut u_ext = Vec::new();
            for i in 0..2 * n {
                u_ext.push(y_ext[i].mul_scalar(&(v_ext[i] * domain_2n[i])));
            }
            u_ext
        };

        let h_ext = Self::compute_interpolation_over_group(&u_ext, s + 1);

        let h = h_ext[0..n].to_vec();

        h
    }

    /// Compute all commitments to the quotient polynomials `{[q_i(τ)]}` in O(N * log(N)) time.
    /// A quotient polynomial is defined as `f(X)/(X-w)`. Cached quotients `{q_i(X)} `are the quotient
    /// polynomials over a pre-defined domain `H=(w_0, w_1, ..., w_{n-1})`. Here we require
    /// that `H` is a smooth multiplicative subgroup of `Fp`.
    ///
    /// NOTE: The commitment of `q_i(X)` is over `G1`.
    ///
    /// The precomputed quotient polynomials are used to build optimized lookup arguments
    /// or (zk)SNARKs. See more details [TAB+20], [FK23], [CQ](CQ paper), Caulk(+) papers.
    ///  
    /// ```
    ///    q_i(X) = f(X) / (X - ω_i),  where ω_i = ω^{i},  H = ⟨ω⟩
    ///    
    ///    [q_i(τ)]_1 = [f(τ)]_1 * [1 / (X - ω_i)]_1
    /// ```
    /// # Arguments
    ///
    /// - `f`: the polynomial to be committed,  deg(f) < 2^k <= srs.max_degree
    ///
    /// # Return
    ///
    /// - `q_vec`: the vector of commitments to the quotient polynomials
    ///
    pub fn compute_cached_quotients(&self, f: &UniPolynomial) -> Vec<G1> {
        let n = if f.degree.is_power_of_two() {
            f.degree
        } else {
            f.degree.next_power_of_two()
        };
        assert!(self.srs.max_degree >= n);

        let mut f_vec = f.coeffs.clone();
        f_vec.remove(0);
        f_vec.extend(vec![Scalar::zero(); n - f.degree]);

        let h_vec = Self::compute_h(&f_vec, &self.srs.powers_over_G1[..n]);
        let q_vec = Self::compute_evaluation_over_group(&h_vec, log_2(n));

        q_vec
    }

    /// Compute the lagrange basis in O(N^2) time
    ///
    ///  ```
    ///    SRS_PowerOfTau = [1], [τ], [τ^2], ..., [τ^{N-1}]
    ///    SRS_Lagrange = [L_0(τ), L_1(τ), ..., L_{N-1}(τ)]
    ///  ```
    ///
    /// ```
    ///
    ///  SRS_Lagrange =
    ///
    ///   |  1 ,   1 ,     1 ,         ... ,  1         |     | [1]       |
    ///   |  1 ,   ω ,     ω^2,        ... , ω^{N-1}    |     | [τ]       |
    ///   |  1 ,  ω^2 ,    ω^4,        ... , ω^{2(N-1)} |   * | [τ^2]     |
    ///   |  1 ,  ω^3 ,    ω^6,        ... , ω^{3(N-1)} |     | [τ^3]     |
    ///   | ...,  ... ,    ...,        ... , ...        |     |  ...      |
    ///   |  1 ,  ω^{N-1}, ω^{2(N-1)}, ... , ω^{(N-1)(N-1)} | | [τ^{N-1}] |
    /// ```
    ///
    /// # Arguments
    /// - `n`: the size of the lagrange basis, n=2^k
    /// - `gs`: the powers of tau SRS, i.e., [tau^i] for i=0,1,...,n-1
    ///
    /// # Return
    /// - `lagrange_basis`: the lagrange basis SRS
    ///
    pub fn compute_lagrange_bases_slow(n: usize, gs: &Vec<G1>) -> Vec<G1> {
        let mut lagrange_basis = vec![];
        assert!(gs.len() >= n);

        let omega = UniPolynomial::get_root_of_unity(log_2(n))
            .inverse()
            .unwrap();
        let inv_factor = Scalar::from(n as u64).inverse().unwrap();

        let mut row_omega = Scalar::one();
        for i in 0..n {
            let mut col_omega = Scalar::one();
            let mut g = G1::identity();
            for j in 0..n {
                g = g.add(&gs[j].mul_scalar(&col_omega));
                col_omega *= &row_omega;
            }
            lagrange_basis.push(g.mul_scalar(&inv_factor));
            row_omega *= &omega;
        }
        lagrange_basis
    }

    /// Compute the lagrange basis in O(N * log(N)) time
    pub fn compute_lagrange_bases_fft(n: usize, gs: &[G1]) -> Vec<G1> {
        let len = gs.len();
        assert!(len >= n);
        assert!(n.is_power_of_two());
        let log_size = log_2(n);
        let omega = UniPolynomial::get_root_of_unity(log_size)
            .inverse()
            .unwrap();
        let n_inv = Scalar::from_usize(n).inverse().unwrap();

        let mut lagrange_bases = gs[..n].to_vec();
        // bit-reversing
        for k in 0..n {
            let k_rev = crate::bits::bit_reverse(k, log_size);
            if k < k_rev {
                lagrange_bases.swap(k, k_rev);
            }
        }

        let mut sep = 1;
        for _ in 0..log_size {
            let mut w = Scalar::one();
            for j in 0..sep {
                for i in (0..n).step_by(2 * sep) {
                    let l = i + j;
                    let r = i + j + sep;
                    let tmp = lagrange_bases[r].mul_scalar(&w);
                    lagrange_bases[r] = lagrange_bases[l].sub(&tmp);
                    lagrange_bases[l] = lagrange_bases[l].add(&tmp);
                }
                w = w * omega.exp(n / (2 * sep));
            }
            sep *= 2;
        }
        lagrange_bases
            .iter_mut()
            .for_each(|e| *e = e.mul_scalar(&n_inv));
        lagrange_bases
    }
}

mod tests {
    use super::*;
    use crate::*;

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

        let coeffs = Scalar::from_i64_vector(&[1, 0, 2]);
        let f = UniPolynomial::from_coeffs(&coeffs);

        let kzg10_pcs = KZG10PCS::setup(100, &mut rng);
        let f_cm = kzg10_pcs.commit_uni_poly(&f);

        let deg_prf = kzg10_pcs.prove_degree_bound(&f, 3);
        let b = kzg10_pcs.verify_degree_bound(&f_cm, 3, &deg_prf);
        assert!(b);
    }

    #[test]
    fn test_commit_poly_evals() {
        let mut rng = ark_std::test_rng();
        let max_degree = 80;

        let n = 64;

        let kzg10_pcs = KZG10PCS::setup(max_degree, &mut rng);
        let lagrange_bases = KZG10PCS::compute_lagrange_bases_fft(n, &kzg10_pcs.srs.powers_over_G1);
        println!("lagrange_bases.len()={}", lagrange_bases.len());
        let f_coeffs = Scalar::rand_vector(n, &mut rng);
        let f = UniPolynomial::from_coeffs(&f_coeffs);
        let f_evals = f.evaluations_fft(log_2(n));
        let f_cm = kzg10_pcs.commit_poly_evals(&lagrange_bases, &f_evals, log_2(n));
        let f_cm_2 = kzg10_pcs.commit_uni_poly(&f);
        println!(
            "f_cm.group_element={}",
            ScalarExt::to_string(&f_cm.group_element.x)
        );
        println!(
            "f_cm_2.group_element={}",
            ScalarExt::to_string(&f_cm_2.group_element.x)
        );
        let verified = kzg10_pcs.open_uni_poly(&f_cm, &f);
        assert_eq!(verified, true);
    }

    #[test]
    pub fn test_compute_h() {
        //
        let kzg10 = KZG10PCS::setup(4, &mut ark_std::test_rng());
        // let gs = &kzg10.srs.powers_over_G1;

        let gs: Vec<G1> = ScalarExt::from_i64_vector(&[1, 2, 4, 8])
            .into_iter()
            .map(|v| G1 { x: v })
            .collect();

        let f: Vec<Scalar> = ScalarExt::from_i64_vector(&[9, -2, 1, -3, 1]);

        let f_remove_0th_coeff = {
            let mut f = f.clone();
            f.remove(0);
            f
        };

        let gs = KZG10PCS::compute_h(&f_remove_0th_coeff, &gs);
        for g in gs.iter() {
            println!("{}", ScalarExt::to_string(&g.x));
        }
    }

    #[test]
    pub fn test_compute_lagrange_bases_slow() {
        let kzg10 = KZG10PCS::setup(4, &mut ark_std::test_rng());
        let n = 4;

        let f = UniPolynomial::from_coeffs(&Scalar::from_usize_vector(&[1, 0, 2, 1]));
        let f_cm = kzg10.commit_uni_poly(&f);
        let gs = &kzg10.srs.powers_over_G1;

        let lagranges = KZG10PCS::compute_lagrange_bases_slow(n, gs);

        let f_evals = UniPolynomial::ntt_evals_from_coeffs(&f.coeffs, log_2(n));
        let f_cm_2 = {
            let mut g = G1::identity();
            for i in 0..n {
                g = g.add(&&lagranges[i].mul_scalar(&f_evals[i]));
            }
            g
        };
        assert_eq!(f_cm.group_element, f_cm_2);
    }

    #[test]
    pub fn test_compute_lagrange_bases_fft() {
        let kzg10 = KZG10PCS::setup(4, &mut ark_std::test_rng());
        let n = 4;

        let lagranges = KZG10PCS::compute_lagrange_bases_slow(n, &kzg10.srs.powers_over_G1);
        let lagranges_fft = KZG10PCS::compute_lagrange_bases_fft(n, &kzg10.srs.powers_over_G1);
        assert_eq!(lagranges, lagranges_fft);
    }

    #[test]
    pub fn group_fft() {
        let n = 4;
        let s = log_2(n);
        let d = Scalar::from(2);

        let monomial_bases = {
            let mut g = Vec::new();
            let mut elem = Scalar::one();
            for _ in 0..n {
                g.push(elem);
                elem *= d;
            }
            g.reverse();
            g
        };

        let lagrange_bases = UniPolynomial::ntt_coeffs_from_evals(&monomial_bases, s);

        let coeffs = Scalar::from_usize_vector(&[1, 0, 2, 1]);
        let evals = UniPolynomial::ntt_evals_from_coeffs(&coeffs, s);

        let f_cm = coeffs
            .iter()
            .zip(monomial_bases.iter())
            .map(|(c, b)| *b * c)
            .fold(Scalar::zero(), |acc, x| acc + x);
        let f_cm_alt = evals
            .iter()
            .zip(lagrange_bases.iter())
            .map(|(c, b)| *b * c)
            .fold(Scalar::zero(), |acc, x| acc + x);
        assert_eq!(f_cm, f_cm_alt);
    }

    #[test]
    fn test_compute_cached_quotients() {
        let mut rng = ark_std::test_rng();
        let degree = 104;
        // let coeffs = Scalar::from_i64_vector(&[1, -2, 1]);

        let coeffs = Scalar::rand_vector(degree, &mut rng);

        let f = UniPolynomial::from_coeffs(&coeffs);

        let kzg10_pcs = KZG10PCS::setup(degree.next_power_of_two(), &mut rng);

        println!("max_degree={}", kzg10_pcs.srs.max_degree);

        let f_cm = kzg10_pcs.commit_uni_poly(&f);
        let q_cm_vec = kzg10_pcs.compute_cached_quotients(&f);
        let domain = UniPolynomial::fft_domain(log_2(q_cm_vec.len()));
        for (q_cm, omega) in q_cm_vec.iter().zip(domain.iter()) {
            let b = kzg10_pcs.verify_eval(
                &f_cm,
                &omega,
                &f.evaluate(&omega),
                &EvalArgument {
                    commitment: Commitment {
                        group_element: q_cm.clone(),
                        internal_values: vec![],
                    },
                },
            );
            assert!(b);
        }
    }
}
