use ark_bn254::Fr;
use ark_bn254::FrParameters;
use ark_std::{vec::Vec, One, Zero, UniformRand};
// use ark_std::rand::Rng;
use ark_ff::{PrimeField, FftParameters, FpParameters, BigInteger, BigInteger256};

use ark_std::rand::Rng;

pub type Scalar = Fr;
pub type G1 = <ark_ec::models::bn::Bn<ark_bn254::Parameters> as ark_ec::PairingEngine>::G1Affine;
pub type G2 = <ark_ec::models::bn::Bn<ark_bn254::Parameters> as ark_ec::PairingEngine>::G2Affine;

pub mod unipoly;
pub mod kzg10; // TODO: mock implementation of KZG10
pub mod mle;

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

pub fn bits(i: usize, num_bits: usize) -> Vec<bool> {
    (0..num_bits)
      .map(|shift_amount| ((i & (1 << (num_bits - shift_amount - 1))) > 0))
      .collect::<Vec<bool>>()
}

pub fn scalar_from_bits(i: usize, num_bits: usize) -> Vec<Scalar> {
    bits(i, num_bits).iter().map(| &b | if b {Scalar::one()} else {Scalar::zero()}).collect()
}

pub fn scalar_modulus_half() -> Scalar{
    let mut b = FrParameters::MODULUS;
    b.div2();
    Scalar::from(b)
}

pub trait ScalarExt: Sized + Copy + Zero + One + Eq + std::fmt::Debug {
    fn from_u64(i: u64) -> Self;

    // fn one() -> Self;
    fn two() -> Self;

    fn from_usize(v: usize) -> Self;

    fn from_usize_vector(v: &[usize]) -> Vec<Self>;

    fn rand_vector<R: Rng>(n: usize, rng: &mut R) -> Vec<Self>;

    fn to_string(&self) -> String;

}

impl ScalarExt for Scalar {
    fn from_u64(i: u64) -> Self {
        Scalar::from(i as u64)
    }

    // fn one() -> Self {
    //     Scalar::from(1 as u64)
    // }

    fn two() -> Self {
        Scalar::from(2 as u64)

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
}