use ark_ff::Zero;
use ark_std::log2;
use kzg10::Commitment;

use crate::*;
use crate::transcript::Transcript;
use crate::sumcheck::{SumcheckSystem, SumcheckProof};
use crate::mle::{*, evals::*};
use crate::ph23_pcs::{MlePCSystem, EvalArgument as phEvalArgument};

#[derive(Clone)]
pub struct Instance{
    pub a_matrix: Vec<Vec<Scalar>>,
    pub b_matrix: Vec<Vec<Scalar>>,
    pub c_matrix: Vec<Vec<Scalar>>, // m * m
    pub io: Vec<Scalar>,
    pub m: usize, // m
}

impl Instance {
    fn new(a_matrix: Vec<Vec<Scalar>>, b_matrix: Vec<Vec<Scalar>>, c_matrix: Vec<Vec<Scalar>>, m: usize, io: Vec<Scalar>)-> Self{
        let s = log_2(m);
        assert_eq!(pow_2(s), m);
        assert_eq!(io.len() + 1, m/2);
        assert_eq!(a_matrix.len(), m);
        assert_eq!(b_matrix.len(), m);
        assert_eq!(c_matrix.len(), m);
        //TODO: check each row

        Self{
            a_matrix,
            b_matrix,
            c_matrix,
            m,
            io
        }
    }

    pub fn eval_matrix_a(&self, input: &Vec<Scalar>) -> Vec<Scalar> {
        eval_matrix(&self.a_matrix, input)
    }

    pub fn eval_matrix_b(&self, input: &Vec<Scalar>) -> Vec<Scalar> {
        eval_matrix(&self.b_matrix, input)
    }

    pub fn eval_matrix_c(&self, input: &Vec<Scalar>) -> Vec<Scalar> {
        eval_matrix(&self.c_matrix, input)
    }
}


#[derive(Clone)]
pub struct ProveKey{
    pub instance: Instance,
    pub params: MlePCSystem,
}

impl ProveKey {
    fn new(params: MlePCSystem, instance: Instance) -> Self {
        Self {
            params, instance
        }
    }
}

#[derive(Clone)]
pub struct VerifyKey{
    pub instance: Instance,
    pub params: MlePCSystem,
}

impl VerifyKey {
    fn new(params: MlePCSystem, instance: Instance) -> Self {
        Self {
            params, instance
        }
    }
}

#[derive(Clone)]
pub struct KeyPair{
    pub prove_key: ProveKey,
    pub verify_key: VerifyKey,
}

impl KeyPair{
    pub fn generate(params: MlePCSystem, instance: Instance) -> Self {
        Self{
            prove_key: ProveKey::new(params.clone(), instance.clone()),
            verify_key: VerifyKey::new(params, instance)
        }
    }

    pub fn prove_key(&self) -> ProveKey {
        self.prove_key.clone()
    }

    pub fn verify_key(&self) -> VerifyKey {
        self.verify_key.clone()
    }
}

pub struct MatrixEncode{
    pub comm_a: Commitment,
    pub comm_b: Commitment,
    pub comm_c: Commitment,
}

pub struct MatrixEncodeProof {
    pub ea: Scalar,
    pub eb: Scalar,
    pub ec: Scalar,
    pub evala: phEvalArgument,
    pub evalb: phEvalArgument,
    pub evalc: phEvalArgument,
}

impl MatrixEncode {
    pub fn commit(matrix_a: &Vec<Vec<Scalar>>, matrix_b: &Vec<Vec<Scalar>>, matrix_c: &Vec<Vec<Scalar>>) -> Self{
        let mut matrix_a = matrix_a.clone();
        let mut matrix_b = matrix_b.clone();
        let mut matrix_c = matrix_c.clone();

        let pcs = MlePCSystem::setup();

        let mut vec_a = Vec::new();
        let mut vec_b = Vec::new();
        let mut vec_c = Vec::new();
        for i in 0..matrix_a.len() {
            vec_a.append(&mut matrix_a[i]);
            vec_b.append(&mut matrix_b[i]);
            vec_c.append(&mut matrix_c[i]);
        }
        let poly_a = MleEvals::new(vec_a.as_slice());
        let poly_b = MleEvals::new(vec_b.as_slice());
        let poly_c = MleEvals::new(vec_c.as_slice());

        Self{
            comm_a: pcs.commit(&poly_a),
            comm_b: pcs.commit(&poly_b),
            comm_c: pcs.commit(&poly_c),
        }
        
    }
}

pub struct SumcheckRound1Proof{
    pub va: Scalar,
    pub vb: Scalar,
    pub vc: Scalar,
    pub value: Scalar,
    pub sumcheckproof: SumcheckProof,
}

impl SumcheckRound1Proof{
    
    pub fn generate_proof(value_a: &Vec<Scalar>, value_b: &Vec<Scalar>, value_c: &Vec<Scalar>, eq_values: &Vec<Scalar>, tr: &mut Transcript) -> (Vec<Scalar>, Scalar, SumcheckProof) {
        assert_eq!(value_a.len(), value_b.len());
        assert_eq!(value_a.len(), value_c.len());
        assert_eq!(value_a.len(), eq_values.len());

        let claim = Scalar::zero();
        let poly_a = MleEvals::new(value_a.as_slice());
        let poly_b = MleEvals::new(value_b.as_slice());
        let poly_c = MleEvals::new(value_c.as_slice());
        let poly_eq = MleEvals::new(eq_values.as_slice());
        
        let g_func  = |vs: Vec<Scalar>, _| {
            vs[3] * (vs[0] * vs[1] - vs[2])
        };
        SumcheckSystem::prove_cubic("sumcheck #1", &claim, vec![&poly_a, &poly_b, &poly_c, &poly_eq], g_func ,3, tr)
    }

    pub fn verify(&self, num_rounds: usize, tr: &mut Transcript) -> (Scalar, Vec<Scalar>) {
        let claim = Scalar::zero();
        SumcheckSystem::verify(&claim, num_rounds, 3, &self.sumcheckproof, tr)
    }
}

pub struct SumcheckRound2Proof {

    pub value: Scalar,
    pub sumcheckproof: SumcheckProof,
    
}

impl SumcheckRound2Proof{
    pub fn generate_proof(claim: Scalar, values: &Vec<Scalar>, input: &Vec<Scalar>, tr: &mut Transcript) ->(Vec<Scalar>, Scalar, SumcheckProof) {
        let poly = MleEvals::new(values.as_slice());
        let poly_z = MleEvals::new(input.as_slice());

        let g_func  = |vs: Vec<Scalar>, _| {
            vs[1] * vs[0]
        };
        SumcheckSystem::prove_cubic("sumcheck #2", &claim, vec![&poly, &poly_z], g_func , 3, tr)
    }

    pub fn verify(&self, claim: &Scalar, num_rounds: usize, tr: &mut Transcript) -> (Scalar, Vec<Scalar>){
        SumcheckSystem::verify(claim, num_rounds,3, &self.sumcheckproof, tr)
    }
}

pub struct SNARKProof {
    pub v: Scalar,
    pub wit_comm: Commitment,
    pub proof1: SumcheckRound1Proof,
    pub proof2: SumcheckRound2Proof,
    pub ew: Scalar, // proof for witness commitment
    pub evalw: phEvalArgument,// proof for witness commitment
    pub ma: Scalar,
    pub mb: Scalar,
    pub mc: Scalar,
    pub eproof: MatrixEncodeProof,
}

impl SNARKProof{

    pub fn generate_proof(params: &MlePCSystem, prove_key: &ProveKey, public: &[Scalar], witness: &[Scalar], encode: &MatrixEncode) -> Self{

        let mut tr = Transcript::new_with_name(b"snark proof");
        tr.update_with_scalar_vec(&public);
        // TODO: transcript adds more stuffs
        let s = log_2(prove_key.instance.m);
        let mut input = vec![Scalar::one()];
        input.append(&mut public.to_vec());
        input.append(&mut witness.to_vec());

        assert_eq!(prove_key.instance.m/2, witness.len());
        assert_eq!(prove_key.instance.m, input.len());

        // step 1. PC.Commit(pp, w)
        let wit_poly = MleEvals::new(witness);
        let wit_comm = params.commit(&wit_poly);
        tr.update_with_g1(&wit_comm.group_element);

        // step 2. generate tau
        let tau = tr.generate_challenge_vector(s);
        
        // let tau_eq_2 = eval_eq_array(&tau);
        // change to:
        let tau_eq = EqPolynomial::new(&tau).evals_over_hypercube();

        // step 3~5: sumcheck #1
        let value_a = prove_key.instance.eval_matrix_a(&input);
        let value_b = prove_key.instance.eval_matrix_b(&input);
        let value_c = prove_key.instance.eval_matrix_c(&input);

        {// double check
            for i in 0..value_a.len() {
                let v = value_a[i] * value_b[i] - value_c[i];
                assert_eq!(v, Scalar::zero());
            }
        }

        let (rx, eval_x, sumcheckproof1) = SumcheckRound1Proof::generate_proof(&value_a, &value_b, &value_c, &tau_eq, &mut tr);

        // step 6: eval_x = (va * vb - vc) * eq(rx, tau)
        // let va = eval_eq_r(&value_a, &rx);
        // let vb = eval_eq_r(&value_b, &rx);
        // let vc = eval_eq_r(&value_c, &rx);
        // let vr = eval_eq_r(&tau_eq, &rx);
        let va = MleEvals::new(value_a.as_slice()).evaluate(&rx);
        let vb = MleEvals::new(value_b.as_slice()).evaluate(&rx);
        let vc = MleEvals::new(value_c.as_slice()).evaluate(&rx);
        let vr = MleEvals::new(&tau_eq).evaluate(&rx);
        assert_eq!(eval_x, (va * vb - vc) * vr);

        let proof1 = SumcheckRound1Proof{
            va,
            vb,
            vc,
            sumcheckproof: sumcheckproof1,
            value: eval_x,
        };

        // step 8: generate ra, rb, rc
        let ra = tr.generate_challenge();
        let rb = tr.generate_challenge();
        let rc = tr.generate_challenge();

        // step 9: generate claim2 = ra * xa + rb * xb + rc * xc
        let claim2 = ra * proof1.va + rb * proof1.vb + rc * proof1.vc;

        // step 10~11: sumcheck #2
        let rx_eq = EqPolynomial::new(&rx).evals_over_hypercube();
        let eval_a = eval_matrix_col(&rx_eq, &prove_key.instance.a_matrix);
        let eval_b = eval_matrix_col(&rx_eq, &prove_key.instance.b_matrix);
        let eval_c = eval_matrix_col(&rx_eq, &prove_key.instance.c_matrix);
        let evals = eval_a.iter().zip(eval_b.iter().zip(eval_c.iter())).map(|(va, (vb, vc))|{
            ra * va + rb * vb + rc * vc
        }).collect();

        let (ry, eval_y, sumcheckproof2) = SumcheckRound2Proof::generate_proof(claim2, &evals, &input, &mut tr);
        
        let proof2 = SumcheckRound2Proof{
            sumcheckproof: sumcheckproof2,
            value: eval_y,
        };

        // step 12: v = w(ry[1..])
        // let v = eval_eq_r(&witness.to_vec(), &ry[1..].to_vec());
        let v = MleEvals::new(witness).evaluate(&ry[1..].to_vec());
        tr.update_with_scalar(&v);
        
        // step 13: proof commit(w)
        let (ew, evalw) = params.prove_plain(&wit_comm, &wit_poly, &ry[1..], &mut tr);
        tr.update_with_scalar(&ew);
        // tr.update_with_scalar(&evalw);

        let ry_eq = EqPolynomial::new(&ry).evals_over_hypercube();
        let ma = eval_matrix_row_col(&prove_key.instance.a_matrix, &rx_eq, &ry_eq);
        let mb = eval_matrix_row_col(&prove_key.instance.b_matrix, &rx_eq, &ry_eq);
        let mc = eval_matrix_row_col(&prove_key.instance.c_matrix, &rx_eq, &ry_eq);

        let mut matrix_a = prove_key.instance.a_matrix.clone();
        let mut matrix_b = prove_key.instance.b_matrix.clone();
        let mut matrix_c = prove_key.instance.c_matrix.clone();

        let mut vec_a = Vec::new();
        let mut vec_b = Vec::new();
        let mut vec_c = Vec::new();
        for i in 0..matrix_a.len() {
            vec_a.append(&mut matrix_a[i]);
            vec_b.append(&mut matrix_b[i]);
            vec_c.append(&mut matrix_c[i]);
        }
        let poly_a = MleEvals::new(vec_a.as_slice());
        let poly_b = MleEvals::new(vec_b.as_slice());
        let poly_c = MleEvals::new(vec_c.as_slice());
        let mut rs = rx.clone();
        let mut ry = ry.clone();
        rs.append(&mut ry);

        let (ea, evala) = params.prove_plain(&encode.comm_a, &poly_a,&rs, &mut tr);
        let (eb, evalb) = params.prove_plain(&encode.comm_b, &poly_b,&rs, &mut tr);
        let (ec, evalc) = params.prove_plain(&encode.comm_c, &poly_c,&rs, &mut tr);
        let eproof = MatrixEncodeProof{
            ea,
            eb,
            ec,
            evala,
            evalb,
            evalc,
        };

        println!("test...final");
        Self {
            v,
            wit_comm,
            proof1,
            proof2,
            ew,
            evalw,
            ma,
            mb,
            mc,
            eproof,
        }
    }

    pub fn verify(&self, params: &MlePCSystem, verify_key: &VerifyKey, public: &[Scalar], encode: &MatrixEncode) -> bool{
        let mut tr = Transcript::new_with_name(b"snark proof");

        // TODO: SHOULD feed ABC matrices into transcript
        tr.update_with_scalar_vec(&public);
        tr.update_with_g1(&self.wit_comm.group_element);

        let s = log_2(verify_key.instance.m);

        // step 2. generate tau
        let tau =tr.generate_challenge_vector(s);
        let tau_eq = EqPolynomial::new(&tau);
        
        // step 4~5: sumcheck #1
        let (eval_x, rx) = self.proof1.verify(s, &mut tr);
        let eq_eval = tau_eq.evaluate(&rx);
        
        // step 7: verify ex = (va * vb - vc)* eq(rx, tau)
        let rhs = (self.proof1.va * self.proof1.vb - self.proof1.vc) * eq_eval;
        let result1 = eval_x == rhs;
        println!("result1 = {}", result1);
        
        // step 8: generate ra, rb, rc
        let ra = tr.generate_challenge();
        let rb = tr.generate_challenge();
        let rc = tr.generate_challenge();

        // step 9: generate claim2 = ra * xa + rb * xb + rc * xc
        let claim2 = ra * self.proof1.va + rb * self.proof1.vb + rc * self.proof1.vc;

        // step 10~11: sumcheck #2
        let  (eval_y, ry) = self.proof2.verify(&claim2, s, &mut tr);

        // step 12
        tr.update_with_scalar(&self.v);

        // step 13~14: verify commit(w)
        let result3 = params.verify_plain(&self.wit_comm, &ry[1..], &self.ew, &self.evalw, &mut tr);
        println!("result3 = {}", result3);
        tr.update_with_scalar(&self.ew);

        // step 15: vz = (1-ry[0])w(ry[1..]) + ry[0]input(ry[1..])
        let mut input = vec![Scalar::one()];
        input.append(&mut public.to_vec());
        let vio = MleEvals::new(&input).evaluate(&ry[1..]);
        let vz = (Scalar::one() - ry[0]) * vio + ry[0] * self.v;
        
        // step 16: v1 = A(rx, ry), v2 = B(rx, ry), v3 = C(rx, ry)
        let result2 = eval_y == (ra * self.ma + rb * self.mb + rc * self.mc) * vz;
        println!("result2 = {}", result2);

        let mut rs = rx.clone();
        let mut ry = ry.clone();
        rs.append(&mut ry);
        let rea = params.verify_plain(&encode.comm_a, &rs.as_slice(), &self.eproof.ea, &self.eproof.evala, &mut tr);
        let reb = params.verify_plain(&encode.comm_b, &rs.as_slice(), &self.eproof.eb, &self.eproof.evalb, &mut tr);
        let rec = params.verify_plain(&encode.comm_c, &rs.as_slice(), &self.eproof.ec, &self.eproof.evalc, &mut tr);
        
        println!("rea  = {}, reb = {}, rec = {}", rea, reb, rec);

        rea && reb && rec
    }
}

// fn eval_eq_array(tau: &Vec<Scalar>) -> Vec<Scalar>{
//     let base: usize = 2;
//     let len = tau.len();
//     let pow_len = base.pow(len as u32);

//     let mut evals: Vec<Scalar> = vec![Scalar::one(); pow_len];
//     let mut size = 1;
//     for i in 0..len {
//         let scalar = tau[len - i - 1];
//         for j in 0..size {
//             evals[size + j] = scalar * &evals[j]; // eval * scalar
//             evals[j] = (Scalar::one() - &scalar) * &evals[j]; // eval * (1- scalar)
//         }
//         size *= 2;
//     }
//     evals
// }

// \prod (1-tau[i])(1-values[i]) + tau[i] * values[i]
// fn eval_eq(tau: &Vec<Scalar>, values: &Vec<Scalar>) -> Scalar {
//     assert_eq!(tau.len(), values.len());
//     tau.iter().zip(values.iter()).map(|(&a,&b)| a * b + (Scalar::one() - a) * (Scalar::one() - b)).product()
// }


// pub fn eval_eq_r(values: &Vec<Scalar>, r: &Vec<Scalar>) -> Scalar {
    
//     let m = values.len();
//     let rm = r.len();
//     assert_eq!(log2(m), rm as u32);

//     values.iter().zip(eval_eq_array(r).iter()).map(|(&v, &r)| v * r).sum()
// }

/// compute vector * matrix 
fn eval_matrix_col(rx_eq: &Vec<Scalar>, matrix: &Vec<Vec<Scalar>>) -> Vec<Scalar> {
    assert_eq!(rx_eq.len(), matrix.len());
    let m = rx_eq.len();
    let mut evals = vec![Scalar::zero(); m];
    for i in 0..m {
        for j in 0..m {
            evals[j] += rx_eq[i]* matrix[i][j];
        }
    }
    evals
}

fn eval_matrix_row_col(matrix: &Vec<Vec<Scalar>>, rx_eq: &Vec<Scalar>, ry_eq: &Vec<Scalar>) -> Scalar {

    assert_eq!(matrix.len(), rx_eq.len());

    matrix.iter().zip(rx_eq.iter()).map(|(row, rx)|{
        row.iter().zip(ry_eq.iter()).map(|(&v, &ry)| v * rx * ry).sum::<Scalar>()
    }).sum()  
}

/// compute matrix * vector 
fn eval_matrix(matrix: &Vec<Vec<Scalar>>, values: &Vec<Scalar>) -> Vec<Scalar> {
    matrix.iter().map(|coeffs|{
        assert_eq!(coeffs.len(), values.len());
        coeffs.iter().zip(values.iter()).map(|(&coeff, &value)| coeff * value).sum()
    }).collect()
}


mod tests {
    use crate::*;
    use super::*;

    #[test]
    fn test_snark() {
        // input: 1, 2, 2, 
        // witness: 2, 8, 7, 12
        let max_degree = 8;
        let params = MlePCSystem::setup();
        // a * b = c
        // (b + c) * d = e
        // - a + e = f
        // f * d = g + 2
        // b * 1 = d
        // 4 * d = e
        let a_matrix = vec![
            vec![Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()], 
            vec![Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero() - Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::one().double().double(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::one(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero() - Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero()],
        ];
        let b_matrix = vec![
            vec![Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
        ];
        let c_matrix = vec![
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero()],
            vec![Scalar::one().double(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one()],
            vec![Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::zero(), Scalar::one()],
        ];
        let encode = MatrixEncode::commit(&a_matrix, &b_matrix, &c_matrix);
        let public = vec![Scalar::one(), Scalar::one().double(), Scalar::one().double()];
        let witness = vec![Scalar::from_u64(2), Scalar::from_u64(8), Scalar::from_u64(7), Scalar::from_u64(12)];
        let instance = Instance::new(a_matrix, b_matrix, c_matrix, 8, public.clone());
        let keypair = KeyPair::generate(params.clone(), instance);
        let proof = SNARKProof::generate_proof(&params, &keypair.prove_key, &public.as_slice(), &witness.as_slice(), &encode);
        let result = proof.verify(&params, &keypair.verify_key, &public.as_slice(), &encode);
        println!("result = {}", result);

    }

}