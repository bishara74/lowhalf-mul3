module

public import LowHalfMul3.LambdaOneTail

@[expose] public section

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

open scoped BigOperators

local notation "⟪" p "⟫" => singleton p

theorem termL_unit_of_small_or_absent (i : Fin 6) (t : Finset (Fin 6)) (x : Vec)
    (h : t.card ≤ 1 ∨ i ∉ t) : termL (unitVec i) t x = 0 := by
  by_cases hi : i ∈ t
  · have ht := h.resolve_right (not_not_intro hi)
    have he : t = {i} := by
      ext j
      simp only [Finset.mem_singleton]
      exact ⟨fun hj => Finset.card_le_one.mp ht j hj i hi, fun hj => hj ▸ hi⟩
    rw [he]
    rcases f2_eq_zero_or_one (x i) with hx | hx <;>
      simp [termL, unitVec, hx, CharTwo.add_self_eq_zero]
  · have hshift (y : Vec) : (∏ j ∈ t, (y j + unitVec i j)) = ∏ j ∈ t, y j := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [unitVec, hji]
    have hz : (∏ j ∈ t, ((0 : F₂) + unitVec i j)) = ∏ _j ∈ t, (0 : F₂) :=
      hshift (0 : Vec)
    rw [termL, hshift x, hz, CharTwo.add_self_eq_zero, zero_add]
    exact CharTwo.add_self_eq_zero _

theorem core_const_deriv {p : A6} (hp : CoreHi p) (i : Fin 6) (hi : i = 2 ∨ i = 5)
    (x : Vec) : deriv (unitVec i) (eval p) x = deriv (unitVec i) (eval p) 0 := by
  apply f2_eq_of_add_eq_zero
  rw [lhs_expand]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases h : 2 ≤ m.vars.card ∧ i ∈ m.vars
  · have hm : (2 : Fin 6) ∈ m.vars ∨ (5 : Fin 6) ∈ m.vars := by
      rcases hi with rfl | rfl
      · exact Or.inl h.2
      · exact Or.inr h.2
    rw [hp m h.1 hm, zero_mul]
  · have hc : m.vars.card ≤ 1 ∨ i ∉ m.vars := by
      by_cases hm : 2 ≤ m.vars.card
      · exact Or.inr fun hn => h ⟨hm, hn⟩
      · exact Or.inl (by omega)
    rw [termL_unit_of_small_or_absent i m.vars x hc, mul_zero]

theorem coreHi_extGate_of_core_any (d : F₂) {l b : Vec}
    (hl2 : l 2 = 0) (hl5 : l 5 = 0) (hb2 : b 2 = 0) (hb5 : b 5 = 0) :
    CoreHi (ExtGate d l b) := by
  intro m _ hm
  obtain ⟨t⟩ := m
  have hb (i : Fin 6) (h : i = 2 ∨ i = 5) : b i = 0 := by
    rcases h with rfl | rfl <;> assumption
  have hl (i : Fin 6) (h : i = 2 ∨ i = 5) : l i = 0 := by
    rcases h with rfl | rfl <;> assumption
  obtain ⟨e, he, het⟩ : ∃ e : Fin 6, (e = 2 ∨ e = 5) ∧ e ∈ t := by
    rcases hm with hm | hm
    · exact ⟨2, Or.inl rfl, hm⟩
    · exact ⟨5, Or.inr rfl, hm⟩
  have he0 : e ∉ ({0, 3} : Finset (Fin 6)) := by
    rcases he with rfl | rfl <;> decide
  have hm1 : (P0 * linANF b).coeff ⟨t⟩ = 0 := by
    rw [p0_mul_linANF]
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply,
      coeff_monomial, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · have hei : e = i := by
        have hmem := Finset.mem_union.mp (h.symm ▸ het)
        exact Finset.mem_singleton.mp (hmem.resolve_left he0)
      subst i
      rw [hb e he, zero_mul]
    · rw [mul_zero]
  have hm2 : (linANF l * linANF b).coeff ⟨t⟩ = 0 := by
    simp only [linANF, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      X, monomial_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_smul_apply, coeff_monomial, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · have hmem := Finset.mem_union.mp (h.symm ▸ het)
      rcases hmem with hi | hj
      · simp only [← Finset.mem_singleton.mp hi, hl e he, zero_mul, mul_zero]
      · simp only [← Finset.mem_singleton.mp hj, hb e he, zero_mul, mul_zero]
    · rw [mul_zero, mul_zero]
  rw [ExtGate, add_mul, smul_mul_assoc]
  simp [hm1, hm2]

theorem coreHi_extGate_of_core {l b : Vec}
    (hl2 : l 2 = 0) (hl5 : l 5 = 0) (hb2 : b 2 = 0) (hb5 : b 5 = 0) :
    CoreHi (ExtGate 1 l b) :=
  coreHi_extGate_of_core_any 1 hl2 hl5 hb2 hb5

theorem xlow_mul_p0 (i : Fin 6) (hi : i = 0 ∨ i = 3) : X i * P0 = P0 := by
  rcases hi with rfl | rfl <;> rw [p0_monomial, X, monomial_mul] <;>
    congr 1 <;> decide

theorem degree_xlow_mul_extGate (i : Fin 6) (hi : i = 0 ∨ i = 3) (l b : Vec) :
    DegreeLE 3 (X i * ExtGate 1 l b) := by
  rw [extGate_one, add_mul, mul_add, ← mul_assoc (X i) P0, xlow_mul_p0 i hi]
  exact (p0_degree.mul (degreeLE_one_of_mem_affine (linANF_mem_affine b))).add
    ((degreeLE_one_of_mem_affine (X_mem_affine i)).mul
      ((degreeLE_one_of_mem_affine (linANF_mem_affine l)).mul
        (degreeLE_one_of_mem_affine (linANF_mem_affine b))))

theorem cosetBase_S0 : CosetBase (V4 S0) := by
  apply cosetBase_V4
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have hP : Phi P0form = 0 := by
    change (iota dirA2 P0form, iota dirB2 P0form) = 0
    rw [iota_P0_gen dirA2 (by rfl) (by rfl), iota_P0_gen dirB2 (by rfl) (by rfl)]
    rfl
  have hZ : Phi Z1form = 0 := by
    change (iota dirA2 Z1form, iota dirB2 Z1form) = 0
    rw [iota_Z1 (Or.inl ⟨rfl, rfl⟩), iota_Z1 (Or.inr (Or.inl ⟨rfl, rfl⟩))]
    rfl
  simp [hP, hZ]

theorem cosetBase_plusZ1_core {l b : Vec} (hc : CoreHi (ExtGate 1 l b)) :
    CosetBase (PlusZ1 (ExtGate 1 l b)) := by
  let c := ExtGate 1 l b
  have hA := cosetBase_S0
  have aff : affine 6 ≤ PlusZ1 c := (affine_le_V4 S0).trans le_sup_left
  refine ⟨aff, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp x
    obtain ⟨a, ha, t, rfl⟩ := mem_extend.mp hp
    have hc' := core_const_deriv hc 2 (Or.inl rfl) x
    rw [show unitVec 2 = dirA2 by funext i; fin_cases i <;> rfl] at hc'
    change deriv dirA2 (eval c) x = deriv dirA2 (eval c) 0 at hc'
    rw [deriv_add, deriv_add, hA.derivA a ha x]
    have he (y : Vec) : deriv dirA2 (eval (t • c)) y = t * deriv dirA2 (eval c) y := by
      simp [deriv, mul_add]
    rw [he, he, hc']
  · intro p hp x
    obtain ⟨a, ha, t, rfl⟩ := mem_extend.mp hp
    have hc' := core_const_deriv hc 5 (Or.inr rfl) x
    rw [show unitVec 5 = dirB2 by funext i; fin_cases i <;> rfl] at hc'
    change deriv dirB2 (eval c) x = deriv dirB2 (eval c) 0 at hc'
    rw [deriv_add, deriv_add, hA.derivB a ha x]
    have he (y : Vec) : deriv dirB2 (eval (t • c)) y = t * deriv dirB2 (eval c) y := by
      simp [deriv, mul_add]
    rw [he, he, hc']
  · intro p hp
    obtain ⟨a, ha, t, rfl⟩ := mem_extend.mp hp
    exact cp_one_eq_zero_of_deg3 ((ha.1.mono (by omega)).add ((first_degree l b).smul t))
  · intro p hp
    obtain ⟨a, ha, t, rfl⟩ := mem_extend.mp hp
    have h : DegreeLE 3 (X (0 : Fin 6) * (a + t • c)) := by
      rw [mul_add, mul_smul_comm]
      exact ((degreeLE_one_of_mem_affine (X_mem_affine 0)).mul ha.1).add
        ((degree_xlow_mul_extGate 0 (Or.inl rfl) l b).smul t)
    simpa [cp, one6, mul_comm] using cp_one_eq_zero_of_deg3 h
  · intro p hp
    obtain ⟨a, ha, t, rfl⟩ := mem_extend.mp hp
    have h : DegreeLE 3 (X (3 : Fin 6) * (a + t • c)) := by
      rw [mul_add, mul_smul_comm]
      exact ((degreeLE_one_of_mem_affine (X_mem_affine 3)).mul ha.1).add
        ((degree_xlow_mul_extGate 3 (Or.inr rfl) l b).smul t)
    simpa [cp, one6, mul_comm] using cp_one_eq_zero_of_deg3 h

theorem core_noNextZ2 {l b : Vec} (hc : CoreHi (ExtGate 1 l b)) {f h : A6}
    (hf : f ∈ PlusZ1 (ExtGate 1 l b)) (hh : h ∈ PlusZ1 (ExtGate 1 l b)) :
    NoNextZ2 (PlusZ1 (ExtGate 1 l b) ⊔ ⟪f * h⟫) :=
  noNextZ2_of_cosetBase (cosetBase_plusZ1_core hc) hf hh

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
