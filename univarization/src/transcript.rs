#![allow(non_snake_case)]

use crate::*;
use sha3::{Digest, Keccak256};

#[derive(Debug, Clone)]
pub struct Transcript {
    //uint256 constant FR_MASK = 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    //here just represent the highest byte 0x1f
    pub FR_MASK: u8,
    pub DST_0: [u8; 4],
    pub DST_1: [u8; 4],
    pub DST_CHALLENGE: [u8; 4],

    pub state_0: [u8; 32],
    pub state_1: [u8; 32],
    pub challenge_counter: u32,
}

impl Transcript {

    pub fn new() -> Self {
        Transcript {
            FR_MASK: 0x1f,
            DST_0: [0u8; 4],
            DST_1: [0u8, 0u8, 0u8, 1u8],
            DST_CHALLENGE: [0u8, 0u8, 0u8, 2u8],
            state_0: [0u8; 32],
            state_1: [0u8; 32],
            challenge_counter: 0,
        }
    }

    pub fn new_with_name(name: &[u8]) -> Self {
        let mut res = Transcript::new();
        res.update_with_u256(&name);
        res
    }

    pub fn update_with_u256(&mut self, value: impl AsRef<[u8]>) {
        let old_state_0: [u8; 32] = self.state_0.clone();

        let mut hasher = Keccak256::new();
        hasher.update(&self.DST_0);
        hasher.update(&old_state_0);
        hasher.update(&self.state_1);
        hasher.update(&value);
        self.state_0 = <[u8; 32]>::from(hasher.finalize_reset());

        hasher.update(&self.DST_1);
        hasher.update(&old_state_0);
        hasher.update(&self.state_1);
        hasher.update(&value);
        self.state_1 = <[u8; 32]>::from(hasher.finalize_reset());
    }

    pub fn update_with_scalar(&mut self, a: &Scalar) {
        let a_bytes = a.to_bytes();
        self.update_with_u256(a_bytes);
    }

    pub fn update_with_g1(&mut self, a: &G1) {
        let a_bytes = a.x.to_bytes();
        self.update_with_u256(a_bytes);
    }

    pub fn update_with_g2(&mut self, a: &G2) {
        let a_bytes = a.x.to_bytes();
        self.update_with_u256(a_bytes);
    }

    pub fn update_with_scalar_vec(&mut self, a_vec: &[Scalar]) {
        for a in a_vec.iter() {
            self.update_with_u256(a.to_bytes());
        }
    }

    fn change_u32_to_bytes(&value: &u32) -> [u8; 4] {
        let musk = 0x000f as u32;
        let mut res = [0u8; 4];
        let mut val = value.clone();
        for i in 0..4 {
            res[4 - i - 1] = (val & musk) as u8;
            val >>= 8;
        }
        res
    }

    pub fn generate_challenge(&mut self) -> Scalar {
        let mut hasher = Keccak256::new();
        hasher.update(&self.DST_CHALLENGE);
        hasher.update(&self.state_0);
        hasher.update(&self.state_1);
        let cc = Transcript::change_u32_to_bytes(&self.challenge_counter);
        hasher.update(cc);
        let mut query = <[u8; 32]>::from(hasher.finalize_reset());

        self.challenge_counter += 1;
        query[0] = self.FR_MASK & query[0];
        Scalar::from_be_bytes_mod_order(&query)
    }

    pub fn generate_challenge_vector(&mut self, size: usize) -> Vec<Scalar> {
        let mut c_vec = vec![Scalar::zero(); size];
        for i in 0..size {
            c_vec[i] = self.generate_challenge();
        }
        c_vec
    }
}

mod tests {
    use super::*;

    #[test]
    fn test_transcript_update() {
        let mut tr = Transcript::new();
        tr.update_with_scalar(&Scalar::from(0));
        tr.update_with_scalar(&Scalar::from(1));
        let alpha = tr.generate_challenge();
        println!("alpha={}", ScalarExt::to_string(&alpha));

        tr.update_with_u256([1,2,3,4,5]);
        let beta = tr.generate_challenge();
        println!("beta={}", ScalarExt::to_string(&beta));

        let gamma_vec = tr.generate_challenge_vector(2);
        println!("gamma={}", scalar_vector_to_string(&gamma_vec));
    }   
}


