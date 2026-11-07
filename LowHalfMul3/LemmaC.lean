import LowHalfMul3.LemmaA

/-!
# Lemma C for spaces without a good direction; `BadClaim` and `LambdaCase 3`

Let `Q` have a `U`-direction (`UDir`): `e = (0, e₁, e₂, 0, e₄, e₅)` with
`(e₁, e₄) ≠ 0`, `ι_e(Q) ⊆ ⟨ℓ⟩`, and `ℓ = 0` or `ℓ` has a nonzero `a₂`/`b₂`
coordinate. Suppose `f, h ∈ V(Q)` and `g = f h + z₂ + ε z₁ ∈ V(Q)`.

* By the bridge, `D_e f = c_f + γ_f ℓ` and `D_e h = c_h + γ_h ℓ`. On the
  hyperplane `ker ℓ` both are constant, so there
  `D_e z₂ = c_f h + c_h f + c_f c_h + ε D_e z₁ + D_e g` has degree `≤ 2`.
* `D_e z₂` contains the cubic `a₀ b₀ (e₁ b₁ + e₄ a₁)` (the derivative of the
  carry), which does not involve `a₂, b₂`. Take the cube spanned by
  `u_t = e_t + ℓ_t w` (`t ∈ {0, 3, 4}` if `e₁ = 1`, `t ∈ {0, 1, 3}` if `e₄ = 1`),
  with `w ∈ {a₂, b₂, 0}` chosen so that `⟨ℓ, u_t⟩ = 0`. The third difference
  `T3` over this cube is `0` on functions of degree `≤ 2` (`T3_quad`) and on affine
  functions (`T3_affine`), but equals `e₁` (resp. `e₄`), i.e. `1`, on `D_e z₂`
  (`T3_Dz2_a`, `T3_Dz2_b`). Contradiction (`noPlace_z2_of_uDir`).

Every `Q₃` without a good direction has a `U`-direction (`uDir_of_bad`), so this
gives the `z₂` and `z₂ + z₁` conjuncts of `BadClaim`. Together with Lemma A
(`noPlace_z1_bad`), `badClaim : BadClaim`, hence `lambdaCase_three : LambdaCase 3`.

This replaces Lemma C, Lemma D1 and the 4-form computations of
`lambda3_proof.tex` for these spaces; see LEAN_LOG.md, phase 6.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-! ## Third differences -/

/-- The third finite difference of `F` over the cube spanned by `a, b, c`. -/
def T3 (F : (Fin 6 → F₂) → F₂) (a b c : Fin 6 → F₂) : F₂ :=
  F 0 + F a + F b + F c + F (a + b) + F (a + c) + F (b + c) + F (a + b + c)

theorem deriv_apply (e : Fin 6 → F₂) (F : (Fin 6 → F₂) → F₂) (x : Fin 6 → F₂) :
    deriv e F x = F (x + e) + F x := rfl

/-- The third difference of a function of degree `≤ 2` vanishes. -/
theorem T3_quad {p : ANF 6} (hp : DegreeLE 2 p) (a b c : Fin 6 → F₂) :
    T3 (eval p) a b c = 0 := by
  have hB := bridge_all a p hp
  have e2 := hB b
  have e3 := hB c
  have e4 := hB (b + c)
  have hD : deriv a (eval p) 0 = eval p a + eval p 0 := by rw [deriv_apply, zero_add]
  rw [deriv_apply a (eval p) b, show b + a = a + b by abel] at e2
  rw [deriv_apply a (eval p) c, show c + a = a + c by abel] at e3
  rw [deriv_apply a (eval p) (b + c), show b + c + a = a + b + c by abel, dotv_add_right] at e4
  simp only [T3]
  linear_combination (-1 : F₂) * hD + e2 + e3 + e4 +
    (2 * deriv a (eval p) 0 + dotv (iota a (pi2 p)) b + dotv (iota a (pi2 p)) c) * two_f2

/-- The third difference of an affine function vanishes. -/
theorem T3_affine (d : F₂) (lv a b c : Fin 6 → F₂) :
    T3 (fun x => d + dotv lv x) a b c = 0 := by
  simp only [T3, dotv_add_right, dotv_zero_right]
  linear_combination (4 * d + 2 * dotv lv a + 2 * dotv lv b + 2 * dotv lv c) * two_f2

theorem T3_congr {F G : (Fin 6 → F₂) → F₂} {ℓ a b c : Fin 6 → F₂} (ha : dotv ℓ a = 0)
    (hb : dotv ℓ b = 0) (hc : dotv ℓ c = 0) (h : ∀ x, dotv ℓ x = 0 → F x = G x) :
    T3 F a b c = T3 G a b c := by
  have h0 : dotv ℓ 0 = 0 := dotv_zero_right ℓ
  have hab : dotv ℓ (a + b) = 0 := by rw [dotv_add_right, ha, hb, add_zero]
  have hac : dotv ℓ (a + c) = 0 := by rw [dotv_add_right, ha, hc, add_zero]
  have hbc : dotv ℓ (b + c) = 0 := by rw [dotv_add_right, hb, hc, add_zero]
  have habc : dotv ℓ (a + b + c) = 0 := by rw [dotv_add_right, hab, hc, add_zero]
  simp only [T3]
  rw [h 0 h0, h a ha, h b hb, h c hc, h _ hab, h _ hac, h _ hbc, h _ habc]

set_option maxRecDepth 100000 in
/-- The cube for `e₁ = 1` sees the carry monomial `a₀ b₀ b₁`. -/
theorem T3_Dz2_a (e1 e2 e4 e5 l0 l3 l4 w2 w5 : F₂) :
    T3 (fun x => deriv (mkDir e1 e2 e4 e5) (eval (lowMul3 2)) x)
      ![1, 0, l0 * w2, 0, 0, l0 * w5] ![0, 0, l3 * w2, 1, 0, l3 * w5]
      ![0, 0, l4 * w2, 0, 1, l4 * w5] = e1 := by
  simp only [T3, deriv_apply, eval_lowMul3_two, mkDir]
  simp
  revert e1 e2 e4 e5 l0 l3 l4 w2 w5
  decide

set_option maxRecDepth 100000 in
/-- The cube for `e₄ = 1` sees the carry monomial `a₀ a₁ b₀`. -/
theorem T3_Dz2_b (e1 e2 e4 e5 l0 l1 l3 w2 w5 : F₂) :
    T3 (fun x => deriv (mkDir e1 e2 e4 e5) (eval (lowMul3 2)) x)
      ![1, 0, l0 * w2, 0, 0, l0 * w5] ![0, 1, l1 * w2, 0, 0, l1 * w5]
      ![0, 0, l3 * w2, 1, 0, l3 * w5] = e4 := by
  simp only [T3, deriv_apply, eval_lowMul3_two, mkDir]
  simp
  revert e1 e2 e4 e5 l0 l1 l3 w2 w5
  decide

/-! ## Lemma C along a `U`-direction -/

set_option maxRecDepth 100000 in
theorem fin_pt : ∀ F H Z Z' Y Y' ε cf ch : F₂,
    Z' + Z = cf * H + F * ch + cf * ch + ε * (Y' + Y) +
      (((F + cf) * (H + ch) + (Z' + ε * Y')) + (F * H + (Z + ε * Y))) := by
  decide

theorem f2_cube : ∀ lt l2 l5 w2 w5 : F₂, lt * (1 + l2 * w2 + l5 * w5) = 0 →
    lt + l2 * (lt * w2) + l5 * (lt * w5) = 0 := by decide

theorem dotv_cube (ℓ : Fin 6 → F₂) (c0 c1 c3 c4 lt w2 w5 : F₂) :
    dotv ℓ ![c0, c1, lt * w2, c3, c4, lt * w5] =
      ℓ 0 * c0 + ℓ 1 * c1 + ℓ 2 * (lt * w2) + ℓ 3 * c3 + ℓ 4 * c4 + ℓ 5 * (lt * w5) := by
  simp [dotv, Fin.sum_univ_succ]
  ring

theorem f2_one_ne_zero : (1 : F₂) ≠ 0 := by decide

/-- **Lemma C along a `U`-direction.** -/
theorem noPlace_z2_of_uDir {Q : Submodule F₂ TwoForm6} (hU : UDir Q) (ε : F₂) :
    NoPlace Q (lowMul3 2 + ε • lowMul3 1) := by
  intro f h hf hh hg
  obtain ⟨e, ℓ, h0, h3, he14, hQℓ, hℓ⟩ := hU
  obtain ⟨γf, hf'⟩ := bridge_line hQℓ hf
  obtain ⟨γh, hh'⟩ := bridge_line hQℓ hh
  -- The correction `w` with `⟨ℓ, e_t + ℓ_t w⟩ = 0`.
  obtain ⟨w2, w5, hw⟩ : ∃ w2 w5 : F₂, ∀ t, ℓ t * (1 + ℓ 2 * w2 + ℓ 5 * w5) = 0 := by
    rcases f2_eq_zero_or_one (ℓ 2) with a | a
    · rcases f2_eq_zero_or_one (ℓ 5) with b | b
      · have hz := hℓ a b
        exact ⟨0, 0, fun t => by rw [hz]; exact zero_mul _⟩
      · have k : (1 : F₂) + 0 * 0 + 1 * 1 = 0 := by decide
        exact ⟨0, 1, fun t => by rw [a, b, k, mul_zero]⟩
    · have k : (1 : F₂) + 1 * 1 + ℓ 5 * 0 = 0 := by
        rw [mul_zero, add_zero]; decide
      exact ⟨1, 0, fun t => by rw [a, k, mul_zero]⟩
  have hd0 : dotv ℓ ![1, 0, ℓ 0 * w2, 0, 0, ℓ 0 * w5] = 0 := by
    rw [dotv_cube]; linear_combination f2_cube _ _ _ _ _ (hw 0)
  have hd1 : dotv ℓ ![0, 1, ℓ 1 * w2, 0, 0, ℓ 1 * w5] = 0 := by
    rw [dotv_cube]; linear_combination f2_cube _ _ _ _ _ (hw 1)
  have hd3 : dotv ℓ ![0, 0, ℓ 3 * w2, 1, 0, ℓ 3 * w5] = 0 := by
    rw [dotv_cube]; linear_combination f2_cube _ _ _ _ _ (hw 3)
  have hd4 : dotv ℓ ![0, 0, ℓ 4 * w2, 0, 1, ℓ 4 * w5] = 0 := by
    rw [dotv_cube]; linear_combination f2_cube _ _ _ _ _ (hw 4)
  -- `e` in coordinates.
  have he : e = mkDir (e 1) (e 2) (e 4) (e 5) := by
    funext i; fin_cases i <;> simp [mkDir, h0, h3]
  -- The pointwise identity on `ker ℓ`.
  set G := f * h + (lowMul3 2 + ε • lowMul3 1) with hGdef
  have hGdeg : DegreeLE 2 G := hg.1
  set cf := deriv e (eval f) 0
  set ch := deriv e (eval h) 0
  have hpt : ∀ x, dotv ℓ x = 0 →
      deriv e (eval (lowMul3 2)) x = cf * eval h x + eval f x * ch + cf * ch +
        ε * deriv e (eval (lowMul3 1)) x + deriv e (eval G) x := by
    intro x hx
    have hfx : eval f (x + e) = eval f x + cf := by
      have := hf' x; rw [hx, mul_zero, add_zero, deriv_apply] at this
      rw [← this]; exact f2_shift_aux _ _
    have hhx : eval h (x + e) = eval h x + ch := by
      have := hh' x; rw [hx, mul_zero, add_zero, deriv_apply] at this
      rw [← this]; exact f2_shift_aux _ _
    simp only [deriv_apply, hGdef, eval_add', eval_mul', eval_smul', hfx, hhx]
    exact fin_pt _ _ _ _ _ _ _ _ _
  -- The third difference of the right side vanishes.
  have hRHS : ∀ a b c : Fin 6 → F₂, T3 (fun x => cf * eval h x + eval f x * ch + cf * ch +
      ε * deriv e (eval (lowMul3 1)) x + deriv e (eval G) x) a b c = 0 := by
    intro a b c
    have th := T3_quad hh.1 a b c
    have tf := T3_quad hf.1 a b c
    have tz : T3 (fun x => deriv e (eval (lowMul3 1)) x) a b c = 0 := by
      have hfun : (fun x => deriv e (eval (lowMul3 1)) x) = fun x =>
          deriv e (eval (lowMul3 1)) 0 + dotv (iota e (pi2 (lowMul3 1))) x :=
        funext (bridge_all e _ degreeLE_two_lowMul3_one)
      rw [hfun]; exact T3_affine _ _ a b c
    have tg : T3 (fun x => deriv e (eval G) x) a b c = 0 := by
      have hfun : (fun x => deriv e (eval G) x) = fun x =>
          deriv e (eval G) 0 + dotv (iota e (pi2 G)) x := funext (bridge_all e G hGdeg)
      rw [hfun]; exact T3_affine _ _ a b c
    simp only [T3] at th tf tz tg ⊢
    linear_combination cf * th + ch * tf + ε * tz + tg + (4 * cf * ch) * two_f2
  -- The third difference of the left side is `1`.
  rcases he14 with h1 | h4
  · have key := T3_congr hd0 hd3 hd4 hpt
    rw [hRHS, he, T3_Dz2_a, h1] at key
    exact f2_one_ne_zero key
  · have key := T3_congr hd0 hd1 hd3 hpt
    rw [hRHS, he, T3_Dz2_b, h4] at key
    exact f2_one_ne_zero key

/-! ## `BadClaim` and `LambdaCase 3` -/

/-- **`BadClaim`, second conjunct (Lemma C, `T = z₂`).** -/
theorem noPlace_z2_bad (l1 r1 l2 r2 : Fin 6 → F₂) (hbad : ¬ GoodDir (Q3span l1 r1 l2 r2)) :
    NoPlace (Q3span l1 r1 l2 r2) (lowMul3 2) := by
  have := noPlace_z2_of_uDir (uDir_of_bad l1 r1 l2 r2 hbad) 0
  rwa [zero_smul, add_zero] at this

/-- **`BadClaim`, third conjunct (Lemma C, `T = z₂ + z₁`).** -/
theorem noPlace_z21_bad (l1 r1 l2 r2 : Fin 6 → F₂) (hbad : ¬ GoodDir (Q3span l1 r1 l2 r2)) :
    NoPlace (Q3span l1 r1 l2 r2) (lowMul3 2 + lowMul3 1) := by
  have := noPlace_z2_of_uDir (uDir_of_bad l1 r1 l2 r2 hbad) 1
  rwa [one_smul] at this

/-- **`BadClaim` holds.** -/
theorem badClaim : BadClaim := fun l1 r1 l2 r2 hbad =>
  ⟨noPlace_z1_bad l1 r1 l2 r2 hbad, noPlace_z2_bad l1 r1 l2 r2 hbad,
    noPlace_z21_bad l1 r1 l2 r2 hbad⟩

/-- **`LambdaCase 3`** (Theorem of `lambda3_proof.tex`): no five-gate circuit in
normal form with exactly three linear gates computes `lowMul3`. -/
theorem lambdaCase_three : LambdaCase 3 := lambdaCase_three_of_badClaim badClaim

/-- `MC(lowMul3) = 6` from `LambdaCase 1` and `LambdaCase 2`. -/
theorem mc_eq_six_of_lambda_one_two (h1 : LambdaCase 1) (h2 : LambdaCase 2) :
    MC(lowMul3) = 6 :=
  mc_eq_six_of_badClaim h1 h2 badClaim

end

end LowHalfMul3

end UnrestrictedBooleanMul
