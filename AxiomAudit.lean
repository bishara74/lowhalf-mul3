import LowHalfMul3

/-! Axiom audit for the 3 x 3 low-half multiplier development.

Every proved theorem of `LowHalfMul3.Target`, `LowHalfMul3.Upper` and
`LowHalfMul3.Derivative` is listed here with its axiom closure. `Challenge.lean` is a separate statement
environment and is deliberately not imported: its single theorem is a `sorry`.
-/

open UnrestrictedBooleanMul.LowHalfMul3

-- Target: the ANF of the three coordinates and the 64-input check.
#check @eval_lowMul3_zero
#print axioms eval_lowMul3_zero
#check @eval_lowMul3_one
#print axioms eval_lowMul3_one
#check @eval_lowMul3_two
#print axioms eval_lowMul3_two
#check @lowMul3_eval
#print axioms lowMul3_eval

-- Upper: the six-gate circuit.
#check @leftFactor_five
#print axioms leftFactor_five
#check @rightFactor_five
#print axioms rightFactor_five
#check @circuit_gate
#print axioms circuit_gate
#check @z0_eq
#print axioms z0_eq
#check @z1_eq
#print axioms z1_eq
#check @z2_eq
#print axioms z2_eq
#check @circuit_computes
#print axioms circuit_computes
#check @upper
#print axioms upper

-- Derivative: Lemma 8 of lambda4_proof.tex.
#check @DegreeLE.mul
#print axioms DegreeLE.mul
#check @degreeLE_one_of_mem_affine
#print axioms degreeLE_one_of_mem_affine
#check @anf_mul_self
#print axioms anf_mul_self
#check @coeff_lowMul3_two_carry
#print axioms coeff_lowMul3_two_carry
#check @derivative_lemma
#print axioms derivative_lemma
#check @deriv_lowMul3_two_dirA2
#print axioms deriv_lowMul3_two_dirA2
#check @deriv_lowMul3_two_dirB2
#print axioms deriv_lowMul3_two_dirB2
#check @deriv_lowMul3_two_dirA2B2
#print axioms deriv_lowMul3_two_dirA2B2
#check @derivative_lemma_dirA2
#print axioms derivative_lemma_dirA2
#check @derivative_lemma_dirB2
#print axioms derivative_lemma_dirB2
#check @derivative_lemma_dirA2B2
#print axioms derivative_lemma_dirA2B2
