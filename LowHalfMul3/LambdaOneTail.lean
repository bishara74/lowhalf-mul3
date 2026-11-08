module

public import LowHalfMul3.LambdaOneBase
public import LowHalfMul3.LambdaTwo

@[expose] public section

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

local notation "⟪" p "⟫" => singleton p

theorem mem_add_iff {W : Submodule F₂ A6} {p q : A6} (hq : q ∈ W) :
    p + q ∈ W ↔ p ∈ W := by
  constructor
  · intro h
    simpa only [add_cancel_right] using W.add_mem h hq
  · exact fun h => W.add_mem h hq

theorem noNextZ2_of_cosetBase {A : Submodule F₂ A6} (hA : CosetBase A)
    {f h : A6} (hf : f ∈ A) (hh : h ∈ A) : NoNextZ2 (A ⊔ ⟪f * h⟫) :=
  ⟨coset_z2_not_mem hA hf hh, fun _ _ hF hH => coset_obstruction hA hf hh hF hH⟩

theorem noNextZ2_after {W : Submodule F₂ A6} {f h : A6} (hw : NoNextZ2 W)
    (hf : f ∈ W) (hh : h ∈ W) : z2 ∉ W ⊔ ⟪f * h⟫ :=
  not_mem_after_product hw.1 hw.2 hf hh

theorem noNextZ21_after {W : Submodule F₂ A6} {f h : A6} (hw : NoNextZ2 W)
    (hz1 : z1 ∈ W) (hf : f ∈ W) (hh : h ∈ W) :
    z2 + z1 ∉ W ⊔ ⟪f * h⟫ := by
  apply not_mem_after_product _ _ hf hh
  · exact fun h => hw.1 ((mem_add_iff hz1).mp h)
  · intro F H hF hH hh'
    exact hw.2 F H hF hH ((mem_add_iff hz1).mp (by simpa only [add_assoc] using hh'))

set_option maxHeartbeats 600000 in
/-- Three products beyond a base with neither output yet freely available. -/
theorem tail_contradiction {B A : Submodule F₂ A6} (hA : A = B ⊔ ⟪z1⟫)
    (h1B : z1 ∉ B) {f h F H K L : A6} (hf : f ∈ B) (hh : h ∈ B)
    (hF : F ∈ B ⊔ ⟪f * h⟫) (hH : H ∈ B ⊔ ⟪f * h⟫)
    (hK : K ∈ (B ⊔ ⟪f * h⟫) ⊔ ⟪F * H⟫)
    (hL : L ∈ (B ⊔ ⟪f * h⟫) ⊔ ⟪F * H⟫)
    (h1 : z1 ∈ ((B ⊔ ⟪f * h⟫) ⊔ ⟪F * H⟫) ⊔ ⟪K * L⟫)
    (h2 : z2 ∈ ((B ⊔ ⟪f * h⟫) ⊔ ⟪F * H⟫) ⊔ ⟪K * L⟫)
    (hearly : z1 ∈ B ⊔ ⟪f * h⟫ → CosetBase A)
    (hlate : NoNextZ2 (A ⊔ ⟪f * h⟫)) : False := by
  let W3 := B ⊔ ⟪f*h⟫
  let W4 := W3 ⊔ ⟪F*H⟫
  change F ∈ W3 at hF
  change H ∈ W3 at hH
  change K ∈ W4 at hK
  change L ∈ W4 at hL
  change z1 ∈ W4 ⊔ ⟪K*L⟫ at h1
  change z2 ∈ W4 ⊔ ⟪K*L⟫ at h2
  by_cases h1early : z1 ∈ W3
  · have heq : W3 = A := by
      change B ⊔ ⟪f*h⟫ = A
      rw [hA]
      exact extend_eq_of_add_mem ((mem_sup_span_cases h1early).resolve_left h1B)
    have heq4 : W4 = A ⊔ ⟪F*H⟫ := congrArg (· ⊔ ⟪F*H⟫) heq
    exact noNextZ2_after
      (noNextZ2_of_cosetBase (hearly h1early) (heq ▸ hF) (heq ▸ hH))
      (heq4 ▸ hK) (heq4 ▸ hL) (heq4 ▸ h2)
  · let W := A ⊔ ⟪f*h⟫
    have hBA : B ≤ A := by rw [hA]; exact le_sup_left
    have hBW : W3 ≤ W := sup_le_sup_right hBA _
    have h1A : z1 ∈ A := by
      rw [hA]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have h1W : z1 ∈ W := Submodule.mem_sup_left h1A
    have hw4 : W4 ≤ W ⊔ ⟪F*H⟫ := sup_le_sup_right hBW _
    have h2no : z2 ∉ W4 := fun p => noNextZ2_after hlate (hBW hF) (hBW hH) (hw4 p)
    have h21no : z2 + z1 ∉ W4 := fun p => noNextZ21_after hlate h1W (hBW hF) (hBW hH) (hw4 p)
    have h1at4 : z1 ∈ W4 := by
      rcases mem_sup_span_cases (W := W4) (p := K*L) h1 with h | h
      · exact h
      · rcases mem_sup_span_cases (W := W4) (p := K*L) h2 with h' | h'
        · exact (h2no h').elim
        · apply (h21no _).elim
          have hh' := W4.add_mem h' h
          rw [add_add_add_comm, anf_add_self, zero_add] at hh'
          exact hh'
    have heq : W4 = W := by
      change W3 ⊔ ⟪F*H⟫ = A ⊔ ⟪f*h⟫
      have hh' : F*H + z1 ∈ W3 :=
        (mem_sup_span_cases (W := W3) (p := F*H) h1at4).resolve_left h1early
      rw [extend_eq_of_add_mem hh']
      change (B ⊔ ⟪f*h⟫) ⊔ ⟪z1⟫ = A ⊔ ⟪f*h⟫
      rw [hA, sup_right_comm]
    have hKW : K ∈ W := heq ▸ hK
    have hLW : L ∈ W := heq ▸ hL
    have h2W : z2 ∈ W ⊔ ⟪K*L⟫ := heq ▸ h2
    exact noNextZ2_after hlate hKW hLW h2W

theorem twoTail_of_twoClaim (hTwo : TwoClaim) (l b : Vec) {f h F H K L : A6}
    (hf : f ∈ V4 (Qlr l b)) (hh : h ∈ V4 (Qlr l b))
    (hF : F ∈ V4 (Qlr l b) ⊔ ⟪f * h⟫) (hH : H ∈ V4 (Qlr l b) ⊔ ⟪f * h⟫)
    (hK : K ∈ (V4 (Qlr l b) ⊔ ⟪f * h⟫) ⊔ ⟪F * H⟫)
    (hL : L ∈ (V4 (Qlr l b) ⊔ ⟪f * h⟫) ⊔ ⟪F * H⟫)
    (h1 : z1 ∈ ((V4 (Qlr l b) ⊔ ⟪f * h⟫) ⊔ ⟪F * H⟫) ⊔ ⟪K * L⟫)
    (h2 : z2 ∈ ((V4 (Qlr l b) ⊔ ⟪f * h⟫) ⊔ ⟪F * H⟫) ⊔ ⟪K * L⟫) : False := by
  have hS : V4 (Slr l b) = V4 (Qlr l b) ⊔ ⟪z1⟫ := by
    rw [Slr, ← pi2_lowMul3_one, mem_V4_sup_singleton degreeLE_two_lowMul3_one]
  refine tail_contradiction hS (z1_not_mem_V4_two l b) hf hh hF hH hK hL h1 h2 ?_ ?_
  · intro hz
    by_cases hP : Phi (wedge l b) = 0
    · exact cosetBase_V4 (phi_S_two hP)
    · exact (noPlace_z1_two hP _ _ hf hh
        ((mem_sup_span_cases hz).resolve_left (z1_not_mem_V4_two l b))).elim
  · by_cases hP : Phi (wedge l b) = 0
    · exact oneHigh_of_phi (phi_S_two hP) _ _ hf hh
    · exact hTwo _ _ hP _ _ hf hh

theorem eval_p0 (x : Vec) : eval P0 x = x 0 * x 3 := by
  change eval (aVar 3 0 * bVar 3 0) x = _
  rw [← lowMul3_zero_eq_a0b0, eval_lowMul3_zero]

theorem lowIdeal_iff_offFibers {p : A6} :
    InLowIdeal p ↔ ∀ x : Vec, x 0 * x 3 = 0 → eval p x = 0 := by
  constructor
  · intro h x hx
    have he := congrArg (fun v : A6 => eval v x) h
    change eval (P0 * p) x = eval p x at he
    rw [eval_mul', eval_p0, hx, zero_mul] at he
    exact he.symm
  · intro h
    apply eval_injective 6
    funext x
    change eval (P0 * p) x = eval p x
    rw [eval_mul', eval_p0]
    rcases f2_eq_zero_or_one (x 0 * x 3) with hx | hx
    · simp only [hx, zero_mul, h x hx]
    · simp only [hx, one_mul]

theorem modLow_iff {p q : A6} :
    ModLow p q ↔ ∀ x : Vec, x 0 * x 3 = 0 → eval p x = eval q x := by
  rw [ModLow, lowIdeal_iff_offFibers]
  constructor
  · intro h x hx
    apply f2_eq_of_add_eq_zero
    simpa only [eval_add'] using h x hx
  · intro h x hx
    rw [eval_add', h x hx, CharTwo.add_self_eq_zero]

theorem substitute_c_modLow (l b : Vec) :
    (∀ p ∈ Base (ExtGate 1 l b), ∃ p' ∈ V4 (Qlr l b), ModLow p p') ∧
    (∀ p ∈ PlusZ1 (ExtGate 1 l b), ∃ p' ∈ V4 (Slr l b), ModLow p p') := by
  have step (W : Submodule F₂ A6) {p : A6}
      (hp : p ∈ W ⊔ ⟪ExtGate 1 l b⟫) :
      ∃ p' ∈ W ⊔ ⟪ExtGate 0 l b⟫, ModLow p p' := by
    obtain ⟨a, ha, t, rfl⟩ := mem_extend.mp hp
    refine ⟨a + t • ExtGate 0 l b, mem_extend.mpr ⟨a, ha, t, rfl⟩, modLow_iff.mpr ?_⟩
    intro x hx
    have hp0 : eval P0 x = 0 := (eval_p0 x).trans hx
    simp only [extGate_zero, extGate_one, eval_add', eval_smul', eval_mul', hp0, zero_add]
  constructor
  · intro p hp
    rw [← (quadratic_space_eq l b).1]
    exact step (V4 Q0) hp
  · intro p hp
    rw [← (quadratic_space_eq l b).2]
    exact step (V4 S0) hp

theorem z2_mod_q2 : ModLow z2 q2 := by
  apply modLow_iff.mpr
  intro x hx
  rw [eval_lowMul3_two]
  change _ = eval ((X (0 : Fin 6) * X 5 + X 1 * X 4 + X 2 * X 3) : A6) x
  simp only [eval_add', eval_mul', eval_X]
  -- The four-variable carry contains the two low variables.
  have hcarry : x 0 * x 1 * x 3 * x 4 = 0 := by
    rw [mul_right_comm (x 0) (x 1) (x 3), hx, zero_mul, zero_mul]
  rw [hcarry, add_zero]

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
