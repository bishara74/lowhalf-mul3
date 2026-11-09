module

public import LowHalfMul3.LastFactor

@[expose] public section

/-! The last-gate feedback case and the complete `TwoClaim`. -/

namespace UnrestrictedBooleanMul.LowHalfMul3

noncomputable section

open LambdaOne

private theorem noncore_of_phi {l r : Vec} (hP : Phi (wedge l r) ≠ 0) :
    ¬ CoreHi (ExtGate 0 l r) := by
  intro h
  have hπ : pi2 (ExtGate 0 l r) = wedge l r := by rw [extGate_zero, pi2_linANF_mul]
  apply hP
  rw [← hπ]
  apply (phi_eq_zero_iff (pi2_symm _)).mpr
  intro i j hij
  by_cases he : i = j
  · subst j
    exact pi2_diag _ i
  simp only [pi2_apply, he, ↓reduceIte]
  apply h
  · change 2 ≤ ({i, j} : Finset (Fin 6)).card
    rw [Finset.card_pair_eq_two_iff.mpr he]
  · change (2 : Fin 6) ∈ ({i, j} : Finset (Fin 6)) ∨
      (5 : Fin 6) ∈ ({i, j} : Finset (Fin 6))
    rcases hij with rfl | rfl | rfl | rfl <;> simp

private theorem lastFactor_two_mod {l r : Vec} (hP : Phi (wedge l r) ≠ 0) {k R : A6}
    (hk : k ∈ V4 (Slr l r)) (hR : R + z2 ∈ V4 (Slr l r)) (hfix : k * R = R) :
    ModLow k 1 := by
  have hspace := (quadratic_space_eq l r).2
  have hk' : k ∈ PlusZ1 (ExtGate 0 l r) := by rwa [hspace]
  have hR' : R + z2 ∈ PlusZ1 (ExtGate 0 l r) := by rwa [hspace]
  have hc := noncore_of_phi hP
  have hoff (v : Vec) (h : v 2 = 1 ∨ v 5 = 1) : OffLowSpan v := by
    rcases h with h | h
    · exact ⟨2, by norm_num, by norm_num, h⟩
    · exact ⟨5, by norm_num, by norm_num, h⟩
  rcases ext_coord_of_phi hP with hl | hr
  · have he : ExtGate 0 r l = ExtGate 0 l r := by
      rw [extGate_zero, extGate_zero, mul_comm]
    apply lastFactorLowIdeal (d := 0) (l := r) (b := l) (hoff l hl) _ _ _ hfix
    · rwa [he]
    · rwa [he]
    · rwa [he]
  · exact lastFactorLowIdeal (hoff r hr) hc hk' hR' hfix

/-- In the quadratic case the modular conclusion gives the two possible factors. -/
theorem lastFactor_two {l r : Vec} (hP : Phi (wedge l r) ≠ 0) {k R : A6}
    (hk : k ∈ V4 (Slr l r)) (hR : R + z2 ∈ V4 (Slr l r)) (hfix : k * R = R) :
    k = 1 ∨ k = 1 + P0 := by
  have hmod := lastFactor_two_mod hP hk hR hfix
  have hd := (degreeLE_one_of_mem_affine (one_mem_affine 6)).mono (by omega : 1 ≤ 2)
  obtain ⟨c, hc⟩ := quadratic_inLowIdeal (hk.1.add hd) hmod
  have he : k = c • P0 + 1 := by rw [← hc, add_cancel_right]
  rcases f2_eq_zero_or_one c with rfl | rfl
  · exact Or.inl (by simpa only [zero_smul, zero_add] using he)
  · exact Or.inr (by simpa only [one_smul, add_comm P0] using he)

/-- **Form (b)** of the last gate in Proposition `onehigh`. -/
theorem formB {l r : Vec} (hP : Phi (wedge l r) ≠ 0) {f h k F : A6}
    (hf : f ∈ V4 (Qlr l r)) (hh : h ∈ V4 (Qlr l r))
    (hk : k ∈ V4 (Slr l r)) (hF : F ∈ V4 (Slr l r))
    (hpos : k * (f * h + F) + z2 ∈ V4 (Slr l r)) : False := by
  let R := k * (f * h + F)
  have hfix : k * R = R := by dsimp only [R]; rw [← mul_assoc, anf_mul_self]
  have hmod := lastFactor_two_mod hP hk hpos hfix
  apply feedbackNoPlaceModLow (v := R + z2) hf hh hF hpos
  apply modLow_iff.mpr
  intro x hx
  have hke : eval k x = 1 := by
    simpa only [eval_one'] using (modLow_iff.mp hmod) x hx
  have hZ : eval z2 x = eval q2 x := (modLow_iff.mp z2_mod_q2) x hx
  have hRx : eval R x = eval (f * h) x + eval F x := by
    simp only [R, eval_mul' k, eval_add', hke, one_mul]
  simp only [eval_add', ← hZ, hRx]
  symm
  calc
    _ = eval (f * h) x + ((eval z2 x + eval z2 x) + (eval F x + eval F x)) := by ac_rfl
    _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]

/-- Proposition `onehigh` for a wedge outside the core. -/
theorem twoClaim : TwoClaim := by
  intro l r hP f h hf hh
  have hle : V4 (Qlr l r) ≤ V4 (Slr l r) := V4_mono le_sup_left
  refine ⟨z2_not_mem_S_sup (hle hf) (hle hh), ?_⟩
  intro F H hF hH hpos
  have h1 : (1 : A6) ∈ V4 (Slr l r) := affine_le_V4 _ (one_mem_affine 6)
  rcases feedbackNormal h1 hF hH hpos with ⟨U, V, hU, hV, hUV⟩ | ⟨k, G, hk, hG, hkg⟩
  · rcases mem_sup_span_cases hUV with h0 | h1
    · exact formA_zero hU hV h0
    · apply formA_one_of_phi hP hU hV (hle hf) (hle hh)
      have he : U * V + f * h + z2 = f * h + (U * V + z2) := by ac_rfl
      rwa [he]
  · exact formB hP hf hh hk hG hkg

end

end UnrestrictedBooleanMul.LowHalfMul3
