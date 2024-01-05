use crate::*;


pub fn bits_nand(a: &Vec<bool>, b: &Vec<bool>) -> bool {
    a.iter().zip(b.iter()).all(|(a, b)| !(*a && *b))
}


// NOTE: 6 = (1, 1, 0), big-endian
pub fn bits_BE(i: usize, num_bits: usize) -> Vec<bool> {
    (0..num_bits)
      .map(|shift_amount| ((i & (1 << (num_bits - shift_amount - 1))) > 0))
      .collect::<Vec<bool>>()
}

pub fn bits_LE(n: usize, num_bits: usize) -> Vec<bool> {
    let mut bits = bits_BE(n, num_bits);
    bits.reverse();
    bits
}


// NOTE: (1, 1, 0) = 6, big-endian
pub fn bits_BE_to_integer(bits: &[bool]) -> usize {
    let bits: Vec<usize> = bits.iter().map(|b| if *b {1} else {0}).collect();
    bits.into_iter().fold(0, |acc, b| acc * 2 + b)
}

// NOTE: (1, 1, 0) = 3, little-endian
pub fn bits_LE_to_integer(bits: &[bool]) -> usize {
    let bits: Vec<usize> = bits.iter().map(|b| if *b {1} else {0}).collect();
    bits.into_iter().rev().fold(0, |acc, b| acc * 2 + b)
}

pub fn uint_LE_concat_3(g: usize, g_bits: usize, x: usize, x_bits: usize, y: usize, y_bits: usize) -> usize {
    assert!(g < pow_2(g_bits));
    assert!(x < pow_2(x_bits));
    assert!(y < pow_2(y_bits));
    g +  (x << g_bits) + (y << (g_bits + x_bits))
}

pub fn uint_LE_split_3(gxy: usize, g_bits: usize, x_bits: usize, y_bits: usize) -> (usize, usize, usize) {
    let xy = gxy >> g_bits;
    let g = gxy - (xy << g_bits);
    let y = xy >> x_bits;
    let x = xy - (y << x_bits);
    (g, x, y)
}

pub fn bit_reverse(i: usize, k_log: usize) -> usize {
    let i_bits = bits_LE(i, k_log);
    let i_reversed = bits_BE_to_integer(&i_bits);
    i_reversed
}

pub fn scalar_from_bits_BE(i: usize, num_bits: usize) -> Vec<Scalar> {
    bits_BE(i, num_bits).iter().map(| &b | if b {Scalar::one()} else {Scalar::zero()}).collect()
}

pub fn scalar_from_bits_LE(i: usize, num_bits: usize) -> Vec<Scalar> {
    bits_LE(i, num_bits).iter().map(| &b | if b {Scalar::one()} else {Scalar::zero()}).collect()
}

pub fn bits_BE_to_scalar(bits: Vec<bool>) -> Scalar {
    let i = bits_BE_to_integer(&bits);
    Scalar::from(i as i64)
}

pub fn bits_LE_to_scalar(bits: Vec<bool>) -> Scalar {
    let i = bits_LE_to_integer(&bits);
    Scalar::from(i as i64)
}





#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_bits_nand() {
        assert_eq!(bits_nand(&vec![true, true], &vec![true, true]), false);
        assert_eq!(bits_nand(&vec![true, true], &vec![true, false]), false);
        assert_eq!(bits_nand(&vec![true, true], &vec![false, true]), false);
        assert_eq!(bits_nand(&vec![true, true], &vec![false, false]), true);
        assert_eq!(bits_nand(&vec![true, false], &vec![true, true]), false);
        assert_eq!(bits_nand(&vec![true, false], &vec![true, false]), false);
        assert_eq!(bits_nand(&vec![true, false], &vec![false, true]), true);
        assert_eq!(bits_nand(&vec![true, false], &vec![false, false]), true);
        assert_eq!(bits_nand(&vec![false, true], &vec![true, true]), false);
        assert_eq!(bits_nand(&vec![false, true], &vec![true, false]), true);
        assert_eq!(bits_nand(&vec![false, true], &vec![false, true]), false);
        assert_eq!(bits_nand(&vec![false, true], &vec![false, false]), true);
        assert_eq!(bits_nand(&vec![false, false], &vec![true, true]), true);
        assert_eq!(bits_nand(&vec![false, false], &vec![true, false]), true);
        assert_eq!(bits_nand(&vec![false, false], &vec![false, true]), true);
        assert_eq!(bits_nand(&vec![false, false], &vec![false, false]), true);
    }


    #[test]
    fn test_bits_to_integer() {
        let bs = bits_BE(6, 3);
        assert_eq!(bits_BE_to_integer(&bs), 6);
    }

    #[test]
    fn test_bit_reverse() {
        let i_bits = bit_reverse(6, 3);
        assert_eq!(i_bits, 3);
    }

    #[test]
    fn test_uint_LE_concat_3_and_split_3() {
        let g = 2;
        let g_bits = 2;
        let x = 3;
        let x_bits = 2;
        let y = 4;
        let y_bits = 3;

        let concat = uint_LE_concat_3(g, g_bits, x, x_bits, y, y_bits);
        let (g_res, x_res, y_res) = uint_LE_split_3(concat, g_bits, x_bits, y_bits);
        assert_eq!(g, g_res);
        assert_eq!(x, x_res);
        assert_eq!(y, y_res);
    }
}