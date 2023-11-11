# Hello, Hypercube!

### Motivation

This is a project as part of ZK Hack Istanbul 2023. The goal is to implement cryptographic primitives to reduce a Zk-Snark circuit into a univariate polynomial eventually. We call it "Hello, Hypercube!" because a multilinear polynomial can be represented as points on a Boolean hypercube and reduced through evaluations on it partial sum (using sumcheck).

### Ovewview

![Overview](./img/univarization.png)

The above diagram shows the outline of this project. Starting from the top level, we have a ZK proving system (a simplified version of Spartan is implemented here). The proving system can be represented as a multilinear polynomial. We can think of the multilinear polynomial as a Boolean hypercube. For example, if the polynomial is of form f(x_1, x_2, x_3), then the hypercube is of dimension 3. We can think of f as following:
```
f(0, 0, 0) = v_0
f(0, 0, 1) = v_1
f(0, 1, 0) = v_2
f(0, 1, 1) = v_3
f(1, 0, 0) = v_4
f(1, 0, 1) = v_5
f(1, 1, 0) = v_6
f(1, 1, 1) = v_7
```
where v_i is the value of the polynomial at the point (x_1, x_2, x_3) = (i_1, i_2, i_3). Point v_i is each a vertex of the hypercube. We can then evaluate over the hypercube to get the partial sums from the sumcheck protocol. 

After the sumcheck protocol, we have reduced the polynomial to a simpler form where it is a polynomial dependent on the verifier's randomness during sumcheck. We want to further reduce this to a univariate polynomial. Three ways that have been mentioned in literature are Logup+, [Gemini](https://eprint.iacr.org/2022/420.pdf) and [ZeroMorph](https://eprint.iacr.org/2023/917.pdf). These are used in combination with polynomial commitment schemes such as KZG10. 

### Running the code

```
cd univarization
cargo test
```