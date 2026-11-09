module

public import LowHalfMul3.LambdaOneTail
public import LowHalfMul3.LemmaA

@[expose] public section

/-!
# Quadratic extraction modulo the low-bit ideal

After a change of factors, one factor is affine. On a level set of that
factor, the quadratic representative differs from an available function by a
quadratic supported on the low-bit ideal. A constant second difference
determines this last correction, and Lemma W extracts the remaining wedge.
-/

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

private theorem restore_correction {Q : Submodule F₂ TwoForm6} {R C : A6}
    (hC : pi2 C ∈ Q)
    (h : ∃ π ∈ Q, ∃ a b : Vec, pi2 (R + C) = π + wedge a b) :
    ∃ π ∈ Q, ∃ a b : Vec, pi2 R = π + wedge a b := by
  obtain ⟨π, hπ, a, b, he⟩ := h
  refine ⟨π + pi2 C, Q.add_mem hπ hC, a, b, ?_⟩
  calc
    pi2 R = pi2 (R + C) + pi2 C := by rw [map_add, add_assoc, tf_add_self, add_zero]
    _ = _ := by rw [he]; ac_rfl

/-- On a plane preserved by independent low-bit flips, a quadratic vanishing
off the low-bit ideal is a scalar multiple of the low product on the plane. -/
private theorem low_product_on_plane {G : A6} (hG : DegreeLE 2 G) {a e d : Vec} {α : F₂}
    (he : dotv a e = 0) (hd : dotv a d = 0)
    (he0 : e 0 = 1) (hd0 : d 0 = 0) (hd3 : d 3 = 1)
    (hvan : ∀ x : Vec, dotv a x = α → x 0 * x 3 = 0 → eval G x = 0) :
    ∃ c : F₂, ∀ x : Vec, dotv a x = α → eval G x = c * (x 0 * x 3) := by
  let c := dotv (iota e (pi2 G)) d
  have hdiff (x : Vec) : deriv d (deriv e (eval G)) x = c := by
    change deriv e (eval G) (x + d) + deriv e (eval G) x = c
    rw [bridge_all e G hG (x + d), bridge_all e G hG x, dotv_add_right]
    let u := deriv e (eval G) 0
    let v := dotv (iota e (pi2 G)) x
    change (u + (v + c)) + (u + v) = c
    rw [show (u + (v + c)) + (u + v) = (u + u) + (v + v) + c by ac_rfl]
    simp only [CharTwo.add_self_eq_zero, zero_add]
  refine ⟨c, fun x hx => ?_⟩
  rcases f2_eq_zero_or_one (x 0 * x 3) with h0 | h1
  · rw [hvan x hx h0, h0, mul_zero]
  · have hx0 : x 0 = 1 := (f2_eq_zero_or_one (x 0)).resolve_left
        (fun h => by simp [h] at h1)
    have hx3 : x 3 = 1 := (f2_eq_zero_or_one (x 3)).resolve_left
        (fun h => by simp [h] at h1)
    have hxe : dotv a (x + e) = α := by rw [dotv_add_right, hx, he, add_zero]
    have hxd : dotv a (x + d) = α := by rw [dotv_add_right, hx, hd, add_zero]
    have hxde : dotv a (x + d + e) = α := by rw [dotv_add_right, hxd, he, add_zero]
    have zxe : (x + e) 0 * (x + e) 3 = 0 := by
      simp [Pi.add_apply, hx0, he0, CharTwo.add_self_eq_zero]
    have zxd : (x + d) 0 * (x + d) 3 = 0 := by
      simp [Pi.add_apply, hx3, hd3, CharTwo.add_self_eq_zero]
    have zxde : (x + d + e) 0 * (x + d + e) 3 = 0 := by
      simp [Pi.add_apply, hx0, hd0, he0, CharTwo.add_self_eq_zero]
    have h := hdiff x
    change (eval G (x + d + e) + eval G (x + d)) + (eval G (x + e) + eval G x) = c at h
    simpa only [hvan _ hxde zxde, hvan _ hxd zxd, hvan _ hxe zxe, h1, zero_add, mul_one]
      using h

private theorem extract_affine_right {Q : Submodule F₂ TwoForm6} (hP : P0form ∈ Q)
    {F B R : A6} (hF : F ∈ V4 Q) (hB : B ∈ affine 6) (hR : DegreeLE 2 R)
    (hm : ModLow (F * B) R) : ∃ π ∈ Q, ∃ a b : Vec, pi2 R = π + wedge a b := by
  let a := lin B
  have hp : P0 ∈ V4 Q := ⟨p0_degree, by rwa [pi2_a0b0]⟩
  have product_on_plane (α : F₂) (x : Vec) (hx : dotv a x = α)
      (hx0 : x 0 * x 3 = 0) :
      eval (R + (eval B 0 + α) • F) x = 0 := by
    have h := (modLow_iff.mp hm) x hx0
    rw [eval_mul', eval_affine hB x, show dotv (lin B) x = α from hx] at h
    rw [eval_add', eval_smul', ← h, mul_comm (eval F x), CharTwo.add_self_eq_zero]
  have extract {C : A6} (hC : C ∈ V4 Q) {α : F₂} (hα : a = 0 → α = 0)
      (hv : ∀ x : Vec, dotv a x = α → eval (R + C) x = 0) :
      ∃ π ∈ Q, ∃ u v : Vec, pi2 R = π + wedge u v := by
    apply restore_correction hC.2
    refine ⟨0, Q.zero_mem, a, ?_⟩
    by_cases ha : a = 0
    · refine ⟨0, ?_⟩
      have hzero : R + C = 0 := by
        apply eval_injective 6
        funext x
        change eval (R + C) x = eval (0 : A6) x
        simpa using hv x (by rw [ha, hα ha]; simp [dotv])
      simp [hzero, wedge_zero_right]
    · obtain ⟨v, hv⟩ := pi2_wedge_of_vanish (hR.add hC.1) ha
          (fun x hx => hv x (f2_eq_of_add_eq_zero hx).symm)
      exact ⟨v, by rw [hv, zero_add]⟩
  have extract_with_flips {e d : Vec} (he : dotv a e = 0) (hd : dotv a d = 0)
      (he0 : e 0 = 1) (hd0 : d 0 = 0) (hd3 : d 3 = 1) :
      ∃ π ∈ Q, ∃ u v : Vec, pi2 R = π + wedge u v := by
    let t := eval B 0 + (0 : F₂)
    have hTF : t • F ∈ V4 Q := (V4 Q).smul_mem t hF
    obtain ⟨c, hc⟩ := low_product_on_plane (hR.add hTF.1)
      he hd he0 hd0 hd3 (product_on_plane 0)
    apply extract ((V4 Q).add_mem hTF ((V4 Q).smul_mem c hp)) (α := 0) (fun _ => rfl)
    intro x hx
    rw [← add_assoc, eval_add', hc x hx, eval_smul', eval_p0, CharTwo.add_self_eq_zero]
  by_cases hex : ∃ j : Fin 6, j ≠ 0 ∧ j ≠ 3 ∧ a j = 1
  · obtain ⟨j, hj0, hj3, hj⟩ := hex
    let e := unitVec 0 + a 0 • unitVec j
    let d := unitVec 3 + a 3 • unitVec j
    have he (i : Fin 6) : dotv a (unitVec i + a i • unitVec j) = 0 := by
      rw [dotv_add_right, dotv_smul_right, dotv_unitVec, dotv_unitVec, hj, mul_one,
        CharTwo.add_self_eq_zero]
    exact extract_with_flips (e := e) (d := d) (he 0) (he 3)
      (by simp [e, unitVec, Ne.symm hj0])
      (by simp [d, unitVec, Ne.symm hj0]) (by simp [d, unitVec, Ne.symm hj3])
  by_cases ha : a = 0
  · exact extract_with_flips (e := unitVec 0) (d := unitVec 3)
      (by simp [ha, dotv]) (by simp [ha, dotv])
      (by simp [unitVec]) (by simp [unitVec]) (by simp [unitVec])
  let α := a 0 + a 3 + 1
  have hz (j : Fin 6) (hj0 : j ≠ 0) (hj3 : j ≠ 3) : a j = 0 :=
    (f2_eq_zero_or_one (a j)).resolve_right (fun h => hex ⟨j, hj0, hj3, h⟩)
  have hplane (x : Vec) (hx : dotv a x = α) : x 0 * x 3 = 0 := by
    rcases f2_eq_zero_or_one (x 0 * x 3) with h0 | h1
    · exact h0
    have hx0 : x 0 = 1 := (f2_eq_zero_or_one (x 0)).resolve_left
      (fun h => by simp [h] at h1)
    have hx3 : x 3 = 1 := (f2_eq_zero_or_one (x 3)).resolve_left
      (fun h => by simp [h] at h1)
    have hdot : dotv a x = a 0 + a 3 := by
      simp [dotv, Fin.sum_univ_succ, hx0, hx3, hz 1 (by norm_num) (by norm_num),
        hz 2 (by norm_num) (by norm_num), hz 4 (by norm_num) (by norm_num),
        hz 5 (by norm_num) (by norm_num)]
    have h : a 0 + a 3 + 0 = a 0 + a 3 + 1 := (add_zero _).trans (hdot.symm.trans hx)
    exact (zero_ne_one ((add_right_inj _).mp h)).elim
  exact extract ((V4 Q).smul_mem (eval B 0 + α) hF) (fun h => (ha h).elim)
    (fun x hx => product_on_plane α x hx (hplane x hx))

/-- The paper's quadratic extraction lemma, including redundant generators. -/
theorem idealExtract : IdealExtract := by
  intro l r f h R hf hh hR hm
  let Q := Qlr l r
  let p := linANF l * linANF r
  have hP : P0form ∈ Q := by
    change P0form ∈ Qlr l r
    rw [qlr_eq]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have split_factor {g : A6} (hg : g ∈ V4 Q) :
      ∃ A ∈ affine 6, ∃ t : F₂, ∀ x : Vec, x 0 * x 3 = 0 →
        eval g x = eval A x + t * eval p x := by
    have hspace : V4 Q = (affine 6 ⊔ singleton P0) ⊔ singleton p := by
      change V4 (Qlr l r) = _
      rw [← (quadratic_space_eq l r).1, Base, v4_q0, extGate_zero]
    rw [hspace] at hg
    obtain ⟨D, hD, t, rfl⟩ := mem_extend.mp hg
    obtain ⟨A, hA, s, rfl⟩ := mem_extend.mp hD
    exact ⟨A, hA, t, fun x hx => by
      simp only [eval_add', eval_smul', eval_p0, hx, mul_zero, add_zero]⟩
  obtain ⟨B, hB, t, ht⟩ := split_factor hh
  rcases f2_eq_zero_or_one t with rfl | rfl
  · apply extract_affine_right hP hf hB hR
    apply modLow_iff.mpr
    intro x hx
    simpa only [eval_mul', ht x hx, zero_mul, add_zero] using modLow_iff.mp hm x hx
  obtain ⟨A, hA, s, hs⟩ := split_factor hf
  rcases f2_eq_zero_or_one s with rfl | rfl
  · apply extract_affine_right hP hh hA hR
    apply modLow_iff.mpr
    intro x hx
    rw [mul_comm h A]
    simpa only [eval_mul', hs x hx, zero_mul, add_zero] using modLow_iff.mp hm x hx
  apply restore_correction hf.2
  apply extract_affine_right hP hf ((affine 6).add_mem hA hB) (hR.add hf.1)
  apply modLow_iff.mpr
  intro x hx
  have hsum : eval (A + B) x = eval (f + h) x := by
    simp only [eval_add', ht x hx, hs x hx, one_mul]
    rw [show (eval A x + eval p x) + (eval B x + eval p x) =
        (eval A x + eval B x) + (eval p x + eval p x) by ac_rfl,
      CharTwo.add_self_eq_zero, add_zero]
  calc
    eval (f * (A + B)) x = eval (f * (f + h)) x := by rw [eval_mul', hsum, ← eval_mul']
    _ = eval (R + f) x := by
      rw [mul_add, anf_mul_self, eval_add', eval_add', modLow_iff.mp hm x hx, add_comm]

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
