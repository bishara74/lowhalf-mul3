import LowHalfMul3

/-! Axiom audit for the 3 x 3 low-half multiplier development.

Every proved theorem listed below is printed with its axiom closure; the expected
closure is `[propext, Classical.choice, Quot.sound]`. The listed theorems come from
all modules of the library:

* `LowHalfMul3.Target`
* `LowHalfMul3.Upper`
* `LowHalfMul3.Derivative`
* `LowHalfMul3.Reduction`
* `LowHalfMul3.NormalForm`
* `LowHalfMul3.LambdaFive`
* `LowHalfMul3.Contraction`
* `LowHalfMul3.LemmaTwo`
* `LowHalfMul3.Assembly`
* `LowHalfMul3.CrossPart`
* `LowHalfMul3.Product`
* `LowHalfMul3.LineDerivative`
* `LowHalfMul3.LemmaThree`
* `LowHalfMul3.Types`
* `LowHalfMul3.MainTheorem`
* `LowHalfMul3.LambdaThree`
* `LowHalfMul3.Coset`
* `LowHalfMul3.LemmaA`
* `LowHalfMul3.LemmaC`

The main results are `upper`, `mc_eq_six_of_no_five`, `normal_form_five`,
`lambdaCase_five`, `starFree` / `lambdaCase_four`, `b3Claim`, `badClaim`,
`lambdaCase_three` and `mc_eq_six_of_lambda_one_two`. Helper lemmas that are not
listed are covered by the closures of the listed results that use them. The statements still open
(`LambdaCase`, used for `λ = 1, 2`) are printed in full at the end.
`Challenge.lean` is a separate statement environment and is deliberately not
imported: its single theorem is a `sorry`.
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

-- Product: the product-coefficient layer.
#check @eval_affine
#print axioms eval_affine
#check @sel_eq_mobius_termwise
#print axioms sel_eq_mobius_termwise
#check @pi2_eq_mobius
#print axioms pi2_eq_mobius
#check @pi2_mul_affine
#print axioms pi2_mul_affine
#check @pi2_a0b0
#print axioms pi2_a0b0
#check @pi2_lowMul3_one
#print axioms pi2_lowMul3_one

-- LineDerivative (Lemma 8') and LemmaThree (Lemma 3 instances).
#check @eval_linANF
#print axioms eval_linANF
#check @deriv_add
#print axioms deriv_add
#check @deriv_mul
#print axioms deriv_mul
#check @not_degreeLE_three_of_star
#print axioms not_degreeLE_three_of_star
#check @line_core
#print axioms line_core
#check @PaperPair.deriv_z2
#print axioms PaperPair.deriv_z2
#check @line_finite_b0
#print axioms line_finite_b0
#check @line_finite_a0
#print axioms line_finite_a0
#check @line_finite_a0b0
#print axioms line_finite_a0b0
#check @PaperPair.fin
#print axioms PaperPair.fin
#check @deriv_line_of_mem
#print axioms deriv_line_of_mem
#check @starFree_of_goodDir
#print axioms starFree_of_goodDir
#check @wedge_comm
#print axioms wedge_comm
#check @wedge_self
#print axioms wedge_self
#check @pf_wedge
#print axioms pf_wedge
#check @allPfZero_wedge
#print axioms allPfZero_wedge
#check @Z1form_eq_lit
#print axioms Z1form_eq_lit
#check @Z1form_add_P0form_eq_lit
#print axioms Z1form_add_P0form_eq_lit
#check @wedge_ne_Z
#print axioms wedge_ne_Z
#check @lemma3_finite_Z1
#print axioms lemma3_finite_Z1
#check @lemma3_finite_Z1P0
#print axioms lemma3_finite_Z1P0
#check @lemma3
#print axioms lemma3

-- Types (Lemma 11).
#check @wedge_lincomb
#print axioms wedge_lincomb
#check @types_finite
#print axioms types_finite
#check @types
#print axioms types
#check @phi_eq_zero_of_rows
#print axioms phi_eq_zero_of_rows
#check @rows_v
#print axioms rows_v
#check @rows_full
#print axioms rows_full
#check @phi_of_NFzero
#print axioms phi_of_NFzero
#check @gamma_v
#print axioms gamma_v
#check @gamma_full
#print axioms gamma_full
#check @iota_dirA2_v
#print axioms iota_dirA2_v
#check @iota_dirB2_v
#print axioms iota_dirB2_v
#check @iota_dirA2B2_v
#print axioms iota_dirA2B2_v

-- MainTheorem (Theorem 12, StarFree).
#check @goodDir_of_gens
#print axioms goodDir_of_gens
#check @goodDir_kill
#print axioms goodDir_kill
#check @goodDir_caseA
#print axioms goodDir_caseA
#check @iota_P0
#print axioms iota_P0
#check @phi_P0
#print axioms phi_P0
#check @Z_rows
#print axioms Z_rows
#check @phi_Z
#print axioms phi_Z
#check @row_sum
#print axioms row_sum
#check @zeroFull_finite
#print axioms zeroFull_finite
#check @zeroFull
#print axioms zeroFull
#check @twoFull
#print axioms twoFull
#check @triple_core
#print axioms triple_core
#check @none_false
#print axioms none_false
#check @single_false
#print axioms single_false
#check @pair_zero
#print axioms pair_zero
#check @decomposition_cases
#print axioms decomposition_cases
#check @goodDir_main
#print axioms goodDir_main
#check @starFree
#print axioms starFree
#check @lambdaCase_four
#print axioms lambdaCase_four
#check @not_hasCircuit_five_of_lambda_cases
#print axioms not_hasCircuit_five_of_lambda_cases
#check @mc_eq_six_of_lambda_cases
#print axioms mc_eq_six_of_lambda_cases

-- LambdaThree: LambdaCase 3 from BadClaim and B3Claim (phase 5).
#check @iota_Z1
#print axioms iota_Z1
#check @goodDir_sup_Z1
#print axioms goodDir_sup_Z1
#check @z1_mem_V4_sup
#print axioms z1_mem_V4_sup
#check @noPlace_of_goodDir
#print axioms noPlace_of_goodDir
#check @not_degreeLE_two_z2_add_z1
#print axioms not_degreeLE_two_z2_add_z1
#check @not_mem_sup_of_noPlace
#print axioms not_mem_sup_of_noPlace
#check @flow
#print axioms flow
#check @f2_swap3
#print axioms f2_swap3
#check @phi_of_Z1_mem
#print axioms phi_of_Z1_mem
#check @gateQ_three
#print axioms gateQ_three
#check @wireSpace_four_eq
#print axioms wireSpace_four_eq
#check @lambdaCase_three_of
#print axioms lambdaCase_three_of
#check @mc_eq_six_of_claims
#print axioms mc_eq_six_of_claims

-- Coset: the general coset lemma (B3a + B3b), B3Claim (phase 6).
#check @cp_lin4
#print axioms cp_lin4
#check @carry_mobius_termwise
#print axioms carry_mobius_termwise
#check @cp_one_eq_coeff
#print axioms cp_one_eq_coeff
#check @cp_one_eq_zero_of_deg3
#print axioms cp_one_eq_zero_of_deg3
#check @cp_z2
#print axioms cp_z2
#check @z2_shiftA
#print axioms z2_shiftA
#check @z2_shiftB
#print axioms z2_shiftB
#check @fin_E1
#print axioms fin_E1
#check @gram_finite
#print axioms gram_finite
#check @fin_rank
#print axioms fin_rank
#check @coset_B3a
#print axioms coset_B3a
#check @fin_mu1
#print axioms fin_mu1
#check @fin_mu0
#print axioms fin_mu0
#check @fin_D
#print axioms fin_D
#check @fin_Dcases
#print axioms fin_Dcases
#check @fin_onept
#print axioms fin_onept
#check @fin_case3
#print axioms fin_case3
#check @coset_B3b
#print axioms coset_B3b
#check @fin_00
#print axioms fin_00
#check @fin_10
#print axioms fin_10
#check @fin_01
#print axioms fin_01
#check @fin_11
#print axioms fin_11
#check @coset_obstruction
#print axioms coset_obstruction
#check @coset_z2_not_mem
#print axioms coset_z2_not_mem
#check @cosetBase_V4
#print axioms cosetBase_V4
#check @b3Claim
#print axioms b3Claim
#check @lambdaCase_three_of_badClaim
#print axioms lambdaCase_three_of_badClaim
#check @mc_eq_six_of_badClaim
#print axioms mc_eq_six_of_badClaim

-- LemmaA: Lemma A for spaces without a good direction (phase 6).
#check @bridge_all
#print axioms bridge_all
#check @iota_wedge
#print axioms iota_wedge
#check @affine_vanish
#print axioms affine_vanish
#check @wedge_of_contractions
#print axioms wedge_of_contractions
#check @pi2_wedge_of_vanish
#print axioms pi2_wedge_of_vanish
#check @z1_place_vanish
#print axioms z1_place_vanish
#check @goodDir_mono
#print axioms goodDir_mono
#check @noPlace_z1_of_genDir
#print axioms noPlace_z1_of_genDir
#check @uDir_of_kill
#print axioms uDir_of_kill
#check @kill_v_fin
#print axioms kill_v_fin
#check @kill_vv_fin
#print axioms kill_vv_fin
#check @goodDir_zero1
#print axioms goodDir_zero1
#check @goodDir_sameV
#print axioms goodDir_sameV
#check @uDir_vv
#print axioms uDir_vv
#check @uDir_full
#print axioms uDir_full
#check @goodDir_or_uDir
#print axioms goodDir_or_uDir
#check @noPlace_z1_bad
#print axioms noPlace_z1_bad

-- LemmaC: Lemma C for spaces without a good direction; BadClaim; LambdaCase 3 (phase 6).
#check @genDir_of_uDir
#print axioms genDir_of_uDir
#check @uDir_of_bad
#print axioms uDir_of_bad
#check @T3_quad
#print axioms T3_quad
#check @T3_affine
#print axioms T3_affine
#check @T3_congr
#print axioms T3_congr
#check @T3_Dz2_a
#print axioms T3_Dz2_a
#check @T3_Dz2_b
#print axioms T3_Dz2_b
#check @fin_pt
#print axioms fin_pt
#check @noPlace_z2_of_uDir
#print axioms noPlace_z2_of_uDir
#check @noPlace_z2_bad
#print axioms noPlace_z2_bad
#check @noPlace_z21_bad
#print axioms noPlace_z21_bad
#check @badClaim
#print axioms badClaim
#check @lambdaCase_three
#print axioms lambdaCase_three
#check @mc_eq_six_of_lambda_one_two
#print axioms mc_eq_six_of_lambda_one_two

-- The open statements, printed in full.
#print BadClaim
#print B3Claim
#print CosetBase
#print GenDir
#print UDir
#print NoPlace
#print Q3span
#print LambdaCase
#print StarFree
