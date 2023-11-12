use core::fmt::Display;
use core::fmt;

use ark_bn254::Fr;
use ark_bn254::FrParameters;
use ark_std::{vec::Vec, One, Zero, UniformRand};
// use ark_std::rand::Rng;
use ark_ff::{Field, PrimeField, FftField, FftParameters, FpParameters, BigInteger, BigInteger256, ToBytes};
use ark_std::rand::Rng;

use env_logger::Env;

pub type Scalar = Fr;
pub type G1 = <ark_ec::models::bn::Bn<ark_bn254::Parameters> as ark_ec::PairingEngine>::G1Affine;
pub type G2 = <ark_ec::models::bn::Bn<ark_bn254::Parameters> as ark_ec::PairingEngine>::G2Affine;

pub mod unipoly;
pub mod kzg10; // TODO: mock implementation of KZG10
pub mod mle;
pub mod gemini;
pub mod sumcheck;
pub mod transcript;
<<<<<<< HEAD
pub mod unisumcheck;
pub mod fftunipoly;
=======
>>>>>>> 0925ef6918170daba4d9ffc4d25ec8be99e05855

// Initialize the logger
pub fn init_logger() {
    let env = Env::default()
        .filter_or("RUST_LOG", "debug"); // Set the default log level here

    env_logger::Builder::from_env(env)
        .format_timestamp(None) // Customize the log format if needed
        .try_init();
}

pub fn log_2(n: usize) -> usize {
    assert_ne!(n, 0);

    if n.is_power_of_two() {
      (1usize.leading_zeros() - n.leading_zeros()) as usize
    } else {
      (0usize.leading_zeros() - n.leading_zeros()) as usize
    }
}

pub fn pow_2(n: usize) -> usize {
    assert_ne!(n, 0);
    let p = (2 as u32).pow(n as u32);
    p as usize
}

// NOTE: 6 = (1, 1, 0), big-endian
pub fn bits(i: usize, num_bits: usize) -> Vec<bool> {
    (0..num_bits)
      .map(|shift_amount| ((i & (1 << (num_bits - shift_amount - 1))) > 0))
      .collect::<Vec<bool>>()
}

// NOTE: (1, 1, 0) = 6, big-endian
pub fn bits_to_integer(bits: Vec<bool>) -> usize {
    let bits: Vec<usize> = bits.iter().map(|b| if *b {1} else {0}).collect();
    bits.into_iter().fold(0, |acc, b| acc * 2 + b)
}

pub fn bit_reverse(i: usize, k_log: usize) -> usize {
    let mut i_bits = bits(i, k_log);
    i_bits.reverse();
    let i_reversed = bits_to_integer(i_bits);
    i_reversed
}

pub fn scalar_from_bits(i: usize, num_bits: usize) -> Vec<Scalar> {
    bits(i, num_bits).iter().map(| &b | if b {Scalar::one()} else {Scalar::zero()}).collect()
}

pub fn scalar_modulus_half() -> Scalar{
    let mut b = FrParameters::MODULUS;
    b.div2();
    Scalar::from(b)
}

pub fn scalar_modulus() -> BigInteger256 {
    FrParameters::MODULUS
}

// impl Display for ScalarExt {

// }

pub trait ScalarExt: Sized + Copy + Zero + One + Eq + std::fmt::Debug + Display {
    fn from_u64(i: u64) -> Self;

    fn from_i64(i: i64) -> Self;

    // fn one() -> Self;
    fn two() -> Self;

    fn from_i64_vector(v: &[i64]) -> Vec<Self>;

    fn from_usize(v: usize) -> Self;

    fn from_usize_vector(v: &[usize]) -> Vec<Self>;

    fn rand_vector<R: Rng>(n: usize, rng: &mut R) -> Vec<Self>;

    fn to_string(&self) -> String;

    fn to_bytes(&self) -> Vec<u8>;

    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = ScalarExt::to_string(self);
        write!(f, "{}", str)
    }

    fn exp(&self, exp: usize) -> Self;
}

impl ScalarExt for Scalar {

    fn from_u64(i: u64) -> Self {
        Scalar::from(i as u64)
    }

    fn from_i64(i: i64) -> Self {
        Scalar::from(i as i64)
    }

    // fn one() -> Self {
    //     Scalar::from(1 as u64)
    // }

    fn two() -> Self {
        Scalar::from(2 as u64)

    }

    fn from_i64_vector(v: &[i64]) -> Vec<Self> {
        v.iter().map(| &n | Scalar::from(n as i64)).collect()
    }


    fn from_usize(v: usize) -> Self{
        Scalar::from(v as u64)
    }

    fn from_usize_vector(v: &[usize]) -> Vec<Self> {
        v.iter().map(| &n | Scalar::from(n as u64)).collect()
    }

    fn rand_vector<R: Rng>(n: usize, rng: &mut R) -> Vec<Self> {
        (0..n).map(| _ | Fr::rand(rng)).collect()
    }

    fn to_string(&self) -> String{
        let mut str = "".to_string();
        if self > &scalar_modulus_half() {
            str.push_str(&(Scalar::zero() - self).into_repr().to_string());
            str.push_str("-*");
        } else {
            str.push_str(&self.into_repr().to_string());
        }
        str
    }   

    fn to_bytes(&self) -> Vec<u8> {
        let mut value = [0u8; 32];
        let _ = self.into_repr().to_bytes_be().write(value.as_mut());
        value.to_vec()
    }

    fn exp(&self, exp: usize) -> Self {
        let mut res = Scalar::one();
        let mut base = self.clone();
        assert_eq!(exp, (exp as u64) as usize);
        self.pow(&[exp as u64, 0, 0, 0])
    }
}

pub fn scalar_vector_to_string(v_vec: &Vec<Scalar>) -> String {
    let mut str = "[".to_string();
    for (i, v) in v_vec.iter().enumerate() {
        str.push_str(&format!("{}:", i));
        str.push_str(&ScalarExt::to_string(v));
        str.push_str(",\n");
    }
    str.push_str("]\n");
    str
}

mod tests {
    // use ark_ff::{PrimeField, FftParameters, FpParameters, BigInteger, BigInteger256};
    use super::*;
    use ark_ff::{BigInteger, BigInteger256, FpParameters, PrimeField, FftParameters};
    use ark_bn254::FrParameters;
    #[test]
    fn test_scalar_field() {
        let a = (Scalar::from(0 as u32) - Scalar::from(1 as u32)).into_repr();
        let bigint_two = BigInteger256::from(2);
        let mut b = FrParameters::MODULUS;
        println!("b={}", b);
        b.div2();
        println!("a={}", a);
        println!("b/2={}", b);
        if a < b {
            println!("a<b");
        } else {
            println!("a>=b");
        }
    }


    #[test]
    fn test_omega() {
        let g = Scalar::multiplicative_generator();
        let order = -Scalar::one();
        println!("g={}", ScalarExt::to_string(&g));
        let cofactor = order / Scalar::from((2 as u64).pow(3));
        let omega = order.pow(cofactor.into_repr());
        println!("omega={}", ScalarExt::to_string(&omega));
        let omega_pow_8 = omega.pow(&[8,0,0,0]);
        println!("omega_pow_8={}", ScalarExt::to_string(&omega_pow_8));
    }

    #[test]
    fn test_polynomial_fft() {
        let evals: Vec<Scalar> = Scalar::from_usize_vector(&[1, 2, 3, 4, 5, 6, 7, 8]);

    }

    #[test]
    fn test_bits_to_integer() {
        let bs = bits(6, 3);
        assert_eq!(bits_to_integer(bs), 6);
    }

    #[test]
    fn test_bit_reverse() {
        let i_bits = bit_reverse(6, 3);
        assert_eq!(i_bits, 3);
    }
}