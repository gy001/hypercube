use core::fmt::Display;
use core::fmt;

use ark_bn254::Fr;
use ark_bn254::FrParameters;
use ark_ec::group;
use ark_std::{vec::Vec, One, Zero, UniformRand};
// use ark_std::rand::Rng;
use ark_ff::{Field, PrimeField, FftField, FftParameters, FpParameters, BigInteger, BigInteger256, ToBytes};
use ark_std::rand::Rng;

use env_logger::Env;

pub type Scalar = Fr;
// pub type G1 = <ark_ec::models::bn::Bn<ark_bn254::Parameters> as ark_ec::PairingEngine>::G1Affine;
// pub type G2 = <ark_ec::models::bn::Bn<ark_bn254::Parameters> as ark_ec::PairingEngine>::G2Affine;
// pub type G1Projective = <ark_ec::models::bn::Bn<ark_bn254::Parameters> as ark_ec::PairingEngine>::G1Projective;
// pub type G2Projective = <ark_ec::models::bn::Bn<ark_bn254::Parameters> as ark_ec::PairingEngine>::G2Projective;

pub type G1 = groupsim::G1;
pub type G2 = groupsim::G2;
pub type GT = groupsim::GT;

pub mod groupsim;
pub mod bits;
pub mod unipoly;
pub mod kzg10; // TODO: mock implementation of KZG10
pub mod mle;
pub mod sumcheck;
pub mod transcript;

pub mod unisumcheck;

pub mod zeromorph;
pub mod ph23_pcs;
pub mod bcho_pcs;

pub mod snark;

pub mod fk20;

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
    // assert_ne!(n, 0);
    let p = (2 as u32).pow(n as u32);
    p as usize
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
    use super::*;
    #[test]
    fn test_scalar_field() {
        let a = (Scalar::from(0 as u32) - Scalar::from(1 as u32)).into_repr();
        let _bigint_two = BigInteger256::from(2);
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

}