use crate::*;

#[derive(Debug, PartialEq, Clone)]
pub struct G1 {
    pub(crate) x: Scalar,
}

#[derive(Debug, PartialEq, Clone)]
pub struct G2 {
    pub(crate) x: Scalar,
}

#[derive(Debug, PartialEq, Clone)]
pub struct GT {
    pub(crate) x: Scalar, 
}

impl G1 {
    pub fn new(x: Scalar) -> Self {
        G1 { x: x }
    }

    pub fn identity() -> Self{
        G1::new(Scalar::zero())
    }

    pub fn generator() -> Self{
        G1::new(Scalar::one())
    }

    pub fn add(&self, other: &G1) -> G1 {
            G1::new(self.x + other.x)
    }

    pub fn sub(&self, other: &G1) -> G1 {
        G1::new(self.x - other.x)
    }

    // pub fn add(&self, other: &G1, neg: bool) -> G1 {
    //     if neg {
    //         G1::new(self.x - other.x)
    //     } else {
    //         G1::new(self.x + other.x)
    //     }
    // }

    pub fn mul_int(&self, i: i64) -> G1 {
        G1::new(self.x * Scalar::from_i64(i))
    }

    pub fn mul_scalar(&self, s: &Scalar) -> G1 {
        G1::new(self.x * s)
    }
}

impl G2 {
    pub fn new(x: Scalar) -> Self {
        G2 { x: x }
    }

    pub fn identity() -> Self{
        G2::new(Scalar::zero())
    }

    pub fn generator() -> Self{
        G2::new(Scalar::one())
    }

    pub fn add(&self, other: &G2, neg: bool) -> G2 {
        if neg {
            G2::new(self.x - other.x)
        } else {
            G2::new(self.x + other.x)
        }
    }

    pub fn mul_int(&self, i: i64) -> G2 {
        G2::new(self.x * Scalar::from_i64(i))
    }

    pub fn mul_scalar(&self, s: &Scalar) -> G2 {
        G2::new(self.x * s)
    }
}

impl GT {
    pub fn new(x: Scalar) -> Self {
        GT { x: x }
    }

    pub fn add(&self, other: &GT) -> GT {
        GT::new(self.x + other.x)
    }
}

pub fn pairing(g1: &G1, g2: &G2) -> GT {
    GT::new(g1.x * g2.x)
}