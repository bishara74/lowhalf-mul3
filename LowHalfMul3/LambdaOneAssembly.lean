module

public import LowHalfMul3.LambdaOneCore

@[expose] public section

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

local notation "⟪" p "⟫" => singleton p

theorem noncore_noNextZ2 {l b : Vec} (hb : OffLowSpan b)
    (hc : ¬ CoreHi (ExtGate 1 l b))
    (hpair : ∀ F : Fin 4 → A6, (∀ i, F i ∈ PlusZ1 (ExtGate 1 l b)) →
      F 0 * F 1 + F 2 * F 3 + z2 ∉ PlusZ1 (ExtGate 1 l b))
    (hLast : LastFactorLowIdeal) (hMod : FeedbackNoPlaceModLow) (hNormal : FeedbackNormal)
    {f h : A6} (hf : f ∈ Base (ExtGate 1 l b)) (hh : h ∈ Base (ExtGate 1 l b)) :
    NoNextZ2 (PlusZ1 (ExtGate 1 l b) ⊔ ⟪f * h⟫) := by
  let c := ExtGate 1 l b
  let A := PlusZ1 c
  let g := f * h
  have hBA : Base c ≤ A := by
    change Base c ≤ PlusZ1 c
    rw [plusZ1_eq]
    exact le_sup_left
  have noPair (F H J K : A6) (hF : F ∈ A) (hH : H ∈ A) (hJ : J ∈ A) (hK : K ∈ A) :
      F * H + J * K + z2 ∉ A := by
    have hm : ∀ i : Fin 4, (![F, H, J, K] : Fin 4 → A6) i ∈ A := by
      intro i
      fin_cases i <;> assumption
    exact hpair ![F, H, J, K] hm
  have noOrdinary (F H : A6) (hF : F ∈ A) (hH : H ∈ A) :
      F * H + z2 ∉ A ⊔ ⟪g⟫ := by
    intro hp
    rcases mem_sup_span_cases hp with h0 | h1
    · exact noPair F H 0 0 hF hH A.zero_mem A.zero_mem (by simpa only [zero_mul, add_zero])
    · apply noPair F H f h hF hH (hBA hf) (hBA hh)
      simpa only [g, add_left_comm, add_assoc, add_comm] using h1
  constructor
  · simpa only [zero_mul, zero_add] using noOrdinary 0 0 A.zero_mem A.zero_mem
  · intro F H hF hH hp
    have h1 : (1 : A6) ∈ A := hBA (Submodule.mem_sup_left
      (affine_le_V4 Q0 (one_mem_affine 6)))
    rcases hNormal h1 hF hH hp with hord | hfb
    · obtain ⟨F', H', hF', hH', hP'⟩ := hord
      exact noOrdinary F' H' hF' hH' hP'
    · obtain ⟨k, F', hk, hF', hv⟩ := hfb
      let R := k * (g + F')
      let v := R + z2
      have hfix : k * R = R := by
        change k * (k * (g + F')) = k * (g + F')
        rw [← mul_assoc, anf_mul_self]
      have hmodk : ModLow k 1 := hLast hb hc hk hv hfix
      obtain ⟨f', hf', hmf⟩ := (substitute_c_modLow l b).1 f hf
      obtain ⟨h', hh', hmh⟩ := (substitute_c_modLow l b).1 h hh
      obtain ⟨F'', hF'', hmF⟩ := (substitute_c_modLow l b).2 F' hF'
      obtain ⟨v', hv', hmv⟩ := (substitute_c_modLow l b).2 v hv
      apply hMod hf' hh' hF'' hv'
      apply modLow_iff.mpr
      intro x hx
      have he := modLow_iff.mp hmv x hx
      change eval (k * (f*h + F') + z2) x = eval v' x at he
      rw [eval_add', eval_mul', modLow_iff.mp hmodk x hx, eval_one', one_mul,
        eval_add', eval_mul', modLow_iff.mp hmf x hx, modLow_iff.mp hmh x hx,
        modLow_iff.mp hmF x hx, modLow_iff.mp z2_mod_q2 x hx] at he
      simp only [eval_mul', eval_add']
      rw [← he]
      simp only [add_assoc, add_left_comm, add_comm, CharTwo.add_self_eq_zero, zero_add]

theorem cubic_tail_contradiction {l b : Vec} (hb : OffLowSpan b)
    (hEarly : ∀ {f h : A6}, f ∈ Base (ExtGate 1 l b) → h ∈ Base (ExtGate 1 l b) →
      z1 ∈ Base (ExtGate 1 l b) ⊔ ⟪f*h⟫ → CoreHi (ExtGate 1 l b))
    (hLate : ∀ {f h : A6}, f ∈ Base (ExtGate 1 l b) → h ∈ Base (ExtGate 1 l b) →
      ¬ CoreHi (ExtGate 1 l b) → NoNextZ2 (PlusZ1 (ExtGate 1 l b) ⊔ ⟪f*h⟫))
    {f h F H K L : A6} (hf : f ∈ Base (ExtGate 1 l b)) (hh : h ∈ Base (ExtGate 1 l b))
    (hF : F ∈ Base (ExtGate 1 l b) ⊔ ⟪f*h⟫) (hH : H ∈ Base (ExtGate 1 l b) ⊔ ⟪f*h⟫)
    (hK : K ∈ (Base (ExtGate 1 l b) ⊔ ⟪f*h⟫) ⊔ ⟪F*H⟫)
    (hL : L ∈ (Base (ExtGate 1 l b) ⊔ ⟪f*h⟫) ⊔ ⟪F*H⟫)
    (h1 : z1 ∈ ((Base (ExtGate 1 l b) ⊔ ⟪f*h⟫) ⊔ ⟪F*H⟫) ⊔ ⟪K*L⟫)
    (h2 : z2 ∈ ((Base (ExtGate 1 l b) ⊔ ⟪f*h⟫) ⊔ ⟪F*H⟫) ⊔ ⟪K*L⟫) : False := by
  have h1B : z1 ∉ Base (ExtGate 1 l b) := by
    intro hz
    rcases mem_sup_span_cases hz with hz | hz
    · have hle := V4_mono (show Q0 ≤ Qlr 0 0 by rw [qlr_eq]; exact le_sup_left)
      exact z1_not_mem_V4_two 0 0 (hle hz)
    · have hd := degreeLE_two_lowMul3_one.add hz.1
      rw [add_comm (ExtGate 1 l b), add_cancel_left] at hd
      exact (first_cubic_iff l b).mpr hb hd
  refine tail_contradiction (plusZ1_eq _) h1B hf hh hF hH hK hL h1 h2 ?_ ?_
  · exact fun he => cosetBase_plusZ1_core (hEarly hf hh he)
  · by_cases hc : CoreHi (ExtGate 1 l b)
    · have hle : Base (ExtGate 1 l b) ≤ PlusZ1 (ExtGate 1 l b) := by
        rw [plusZ1_eq]
        exact le_sup_left
      exact core_noNextZ2 hc (hle hf) (hle hh)
    · exact hLate hf hh hc

theorem lambdaCase_one_of_branches (hTwo : TwoClaim)
    (hEarly : ∀ {l b : Vec}, OffLowSpan b → ∀ {f h : A6},
      f ∈ Base (ExtGate 1 l b) → h ∈ Base (ExtGate 1 l b) →
      z1 ∈ Base (ExtGate 1 l b) ⊔ ⟪f*h⟫ → CoreHi (ExtGate 1 l b))
    (hLate : ∀ {l b : Vec}, OffLowSpan b → ∀ {f h : A6},
      f ∈ Base (ExtGate 1 l b) → h ∈ Base (ExtGate 1 l b) →
      ¬ CoreHi (ExtGate 1 l b) → NoNextZ2 (PlusZ1 (ExtGate 1 l b) ⊔ ⟪f*h⟫)) :
    LambdaCase 1 := by
  intro D hD h0 _ _ hlam
  have h1w := wireSpace_one_eq D h0
  have h2w : wireSpace D.gate 2 = Base (D.left 1 * D.right 1) := by
    show wireSpace D.gate (1 + 1) = _
    rw [N4.wireSpace_succ D.gate (by decide), h1w, D.gate_eq, Base]
    rfl
  have hn : ¬ IsLinearGate D 1 := fun h => by
    have := (hlam 1).mpr h
    exact (by decide : ¬ ((1 : Fin 5).val < 1)) this
  obtain ⟨l, b, hc⟩ := first_normal_form (h1w ▸ D.left_mem 1) (h1w ▸ D.right_mem 1) hn
  set B := Base (D.left 1 * D.right 1)
  set f := D.left 2
  set h := D.right 2
  set F := D.left 3
  set H := D.right 3
  set K := D.left 4
  set L := D.right 4
  have h3w : wireSpace D.gate 3 = B ⊔ ⟪f*h⟫ := by
    rw [wireSpace_three_eq, h2w, D.gate_eq]
  have h4w : wireSpace D.gate 4 = (B ⊔ ⟪f*h⟫) ⊔ ⟪F*H⟫ := by
    rw [wireSpace_four_eq, h3w, D.gate_eq]
  have h5w : D.finalWire = ((B ⊔ ⟪f*h⟫) ⊔ ⟪F*H⟫) ⊔ ⟪K*L⟫ := by
    rw [finalWire_five_eq, h4w, D.gate_eq]
  have hf := h2w ▸ D.left_mem 2
  have hh := h2w ▸ D.right_mem 2
  have hF := h3w ▸ D.left_mem 3
  have hH := h3w ▸ D.right_mem 3
  have hK := h4w ▸ D.left_mem 4
  have hL := h4w ▸ D.right_mem 4
  have hz1 := h5w ▸ hD 1
  have hz2 := h5w ▸ hD 2
  by_cases hb : OffLowSpan b
  · have he : B = Base (ExtGate 1 l b) := extend_eq_of_add_mem hc
    rw [he] at hf hh hF hH hK hL hz1 hz2
    exact cubic_tail_contradiction hb (hEarly hb) (hLate hb) hf hh hF hH hK hL hz1 hz2
  · have hd : DegreeLE 2 (D.left 1 * D.right 1) := by
      have he : DegreeLE 2 (ExtGate 1 l b) := by
        by_contra hn
        exact hb ((first_cubic_iff l b).mp hn)
      have hc' := hc.1.add he
      rwa [add_cancel_right] at hc'
    have hle := quadratic_first_le hc hd
    have hle3 := sup_le_sup_right hle (⟪f*h⟫)
    have hle4 := sup_le_sup_right hle3 (⟪F*H⟫)
    have hle5 := sup_le_sup_right hle4 (⟪K*L⟫)
    exact twoTail_of_twoClaim hTwo l b (hle hf) (hle hh) (hle3 hF) (hle3 hH)
      (hle4 hK) (hle4 hL) (hle5 hz1) (hle5 hz2)

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
