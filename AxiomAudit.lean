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

-- Reduction: MC = 6 from the single exclusion of five gates.
#check @mc_eq_six_of_no_five
#print axioms mc_eq_six_of_no_five

-- NormalForm: Lemma 1.
#check @exists_move_linear_gate_left
#print axioms exists_move_linear_gate_left
#check @coeff_a0b0
#print axioms coeff_a0b0
#check @a0b0_not_mem_affine
#print axioms a0b0_not_mem_affine
#check @exists_g0_normal
#print axioms exists_g0_normal
#check @exists_linear_prefix
#print axioms exists_linear_prefix
#check @normal_form
#print axioms normal_form
#check @normal_form_five
#print axioms normal_form_five

-- LambdaFive: the case lambda = 5.
#check @finalWire_le_degreeTwo
#print axioms finalWire_le_degreeTwo
#check @not_degreeLE_two_lowMul3_two
#print axioms not_degreeLE_two_lowMul3_two
#check @no_all_linear_circuit
#print axioms no_all_linear_circuit
#check @not_lambda_five
#print axioms not_lambda_five

-- Contraction: pi2, iota, V4, the bridge lemma, Lemma 8 in paper form.
#check @iota_add_dir
#print axioms iota_add_dir
#check @iota_dirA2B2
#print axioms iota_dirA2B2
#check @lhs_expand
#print axioms lhs_expand
#check @pi2_eq_sum
#print axioms pi2_eq_sum
#check @rhs_expand
#print axioms rhs_expand
#check @deriv_add_deriv_zero_eq_of_termwise
#print axioms deriv_add_deriv_zero_eq_of_termwise
#check @termwise_dirA2
#print axioms termwise_dirA2
#check @termwise_dirB2
#print axioms termwise_dirB2
#check @termwise_dirA2B2
#print axioms termwise_dirA2B2
#check @deriv_add_deriv_zero_eq
#print axioms deriv_add_deriv_zero_eq
#check @constDeriv_iff_iota_pi2_eq_zero
#print axioms constDeriv_iff_iota_pi2_eq_zero
#check @derivative_lemma_paper
#print axioms derivative_lemma_paper

-- LemmaTwo: Lemma 2.
#check @anf_eq_sum_monomials
#print axioms anf_eq_sum_monomials
#check @monomial_empty
#print axioms monomial_empty
#check @mem_affine_of_degreeLE_two_of_pi2_eq_zero
#print axioms mem_affine_of_degreeLE_two_of_pi2_eq_zero
#check @pi2_eq_zero_of_mem_affine
#print axioms pi2_eq_zero_of_mem_affine
#check @span_prefix_le_degreeTwo
#print axioms span_prefix_le_degreeTwo
#check @wireSpace_eq_V4
#print axioms wireSpace_eq_V4

-- Assembly: the lambda = 4 reduction and the case split.
#check @lambdaCase_five
#print axioms lambdaCase_five
#check @starFree_instance_of_iota
#print axioms starFree_instance_of_iota
#check @degreeLE_two_lowMul3_one
#print axioms degreeLE_two_lowMul3_one
#check @gateQ_le_quadSpan
#print axioms gateQ_le_quadSpan
#check @finalWire_five_eq
#print axioms finalWire_five_eq
#check @lambdaCase_four_of_starFree
#print axioms lambdaCase_four_of_starFree
#check @not_hasCircuit_five_of_cases
#print axioms not_hasCircuit_five_of_cases
#check @mc_eq_six_of_remaining_cases
#print axioms mc_eq_six_of_remaining_cases

-- CrossPart: Lemma 4 (kernel) and Lemma 6.
#check @iota_dirA2_apply
#print axioms iota_dirA2_apply
#check @iota_dirB2_apply
#print axioms iota_dirB2_apply
#check @pi2_symm
#print axioms pi2_symm
#check @phi_eq_zero_iff
#print axioms phi_eq_zero_iff
#check @pi2_lowMul3_two
#print axioms pi2_lowMul3_two
#check @phi_q2
#print axioms phi_q2
#check @lemma6_finite
#print axioms lemma6_finite
#check @lemma6
#print axioms lemma6

-- The open statements, printed in full.
#print LambdaCase
#print StarFree
