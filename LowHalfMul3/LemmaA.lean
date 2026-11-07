module

public import LowHalfMul3.Coset

@[expose] public section

/-!
# Lemma A for spaces without a good direction (the `z₁` part of `BadClaim`)

Toolkit (part 1):

* `bridge_all`: for every direction `e ∈ F₂⁶` and `deg p ≤ 2`,
  `D_e p (x) = D_e p (0) + ⟨ι_e (π₂ p), x⟩` (from the six unit vectors and
  additivity in `e`);
* `iota_wedge`: `ι_e (l ∧ r) = ⟨l, e⟩ r + ⟨r, e⟩ l`;
* `affine_vanish`: an affine function vanishing on a hyperplane
  `{⟨ℓ, x⟩ = c}` has linear part `0` or `ℓ`;
* `pi2_wedge_of_vanish` (**Lemma W**): a function of degree `≤ 2` vanishing on a
  hyperplane `{⟨a, x⟩ = α}` has quadratic part `a ∧ m`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-! ## The bridge for every direction -/

/-- The bridge identity for the direction `e`. -/
def Bridge (e : Fin 6 → F₂) : Prop :=
  ∀ p : ANF 6, DegreeLE 2 p → ∀ x, deriv e (eval p) x = deriv e (eval p) 0 + dotv (iota e (pi2 p)) x

theorem bridge_of_termwise (e : Fin 6 → F₂)
    (hterm : ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL e t x = termR e t x) : Bridge e :=
  fun p hp x => (f2_add_eq_iff _ _ _).mp (deriv_add_deriv_zero_eq_of_termwise e hterm p hp x)

set_option maxRecDepth 100000 in
theorem termwise_unit0 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL (unitVec 0) t x = termR (unitVec 0) t x := by
  unfold termL termR sel unitVec
  decide

set_option maxRecDepth 100000 in
theorem termwise_unit1 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL (unitVec 1) t x = termR (unitVec 1) t x := by
  unfold termL termR sel unitVec
  decide

set_option maxRecDepth 100000 in
theorem termwise_unit2 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL (unitVec 2) t x = termR (unitVec 2) t x := by
  unfold termL termR sel unitVec
  decide

set_option maxRecDepth 100000 in
theorem termwise_unit3 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL (unitVec 3) t x = termR (unitVec 3) t x := by
  unfold termL termR sel unitVec
  decide

set_option maxRecDepth 100000 in
theorem termwise_unit4 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL (unitVec 4) t x = termR (unitVec 4) t x := by
  unfold termL termR sel unitVec
  decide

set_option maxRecDepth 100000 in
theorem termwise_unit5 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL (unitVec 5) t x = termR (unitVec 5) t x := by
  unfold termL termR sel unitVec
  decide

theorem bridge_unit (i : Fin 6) : Bridge (unitVec i) := by
  fin_cases i
  · exact bridge_of_termwise _ termwise_unit0
  · exact bridge_of_termwise _ termwise_unit1
  · exact bridge_of_termwise _ termwise_unit2
  · exact bridge_of_termwise _ termwise_unit3
  · exact bridge_of_termwise _ termwise_unit4
  · exact bridge_of_termwise _ termwise_unit5

theorem shiftBy_eq (e x : Fin 6 → F₂) : shiftBy e x = x + e := rfl

theorem f2_split3 : ∀ a b c : F₂, a + c = (a + b) + (b + c) := by decide

theorem bridge_zero : Bridge 0 := by
  intro p _ x
  have hs : ∀ y : Fin 6 → F₂, shiftBy 0 y = y := fun y => by rw [shiftBy_eq, add_zero]
  have hi : iota 0 (pi2 p) = 0 := by funext j; simp [iota_apply]
  simp only [deriv, hs, CharTwo.add_self_eq_zero, hi, dotv, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero]

theorem bridge_add {e e' : Fin 6 → F₂} (he : Bridge e) (he' : Bridge e') : Bridge (e + e') := by
  intro p hp x
  have hs : ∀ y : Fin 6 → F₂, shiftBy (e + e') y = shiftBy e' (shiftBy e y) := fun y => by
    simp only [shiftBy_eq, add_assoc]
  have key : ∀ y, deriv (e + e') (eval p) y =
      deriv e' (eval p) (shiftBy e y) + deriv e (eval p) y := fun y => by
    simp only [deriv, hs]
    exact f2_split3 _ _ _
  rw [key x, key 0, he' p hp (shiftBy e x), he' p hp (shiftBy e 0), he p hp x, iota_add_dir,
    dotv_add_left, shiftBy_eq, shiftBy_eq, dotv_add_right, zero_add]
  ring

theorem vec_eq_sum_unit (e : Fin 6 → F₂) : e = ∑ i, e i • unitVec i := by
  funext k
  simp [unitVec, Finset.sum_apply]

theorem bridge_smul_unit (c : F₂) (i : Fin 6) : Bridge (c • unitVec i) := by
  rcases f2_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul]; exact bridge_zero
  · rw [one_smul]; exact bridge_unit i

/-- **The bridge for every direction.** -/
theorem bridge_all (e : Fin 6 → F₂) : Bridge e := by
  rw [vec_eq_sum_unit e]
  exact Finset.sum_induction _ Bridge (fun _ _ ha hb => bridge_add ha hb) bridge_zero
    fun i _ => bridge_smul_unit (e i) i

/-! ## Linear algebra on `F₂⁶` -/

theorem dotv_smul_right (c : F₂) (a x : Fin 6 → F₂) : dotv a (c • x) = c * dotv a x := by
  simp [dotv, Finset.mul_sum, mul_left_comm]

theorem iota_wedge (e l r : Fin 6 → F₂) :
    iota e (wedge l r) = dotv l e • r + dotv r e • l := by
  funext j
  simp only [iota_apply, wedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotv, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring

theorem exists_coord_one {v : Fin 6 → F₂} (hv : v ≠ 0) : ∃ i, v i = 1 := by
  by_contra h
  simp only [not_exists] at h
  exact hv (funext fun i => (f2_eq_zero_or_one (v i)).resolve_right (h i))

theorem f2_hx : ∀ c y : F₂, c + (c * 1 + y + y * 1) = 0 := by decide

theorem f2_vanish_aux : ∀ c ai lj li α : F₂, α + c * li = 0 →
    α + (c * li + lj + ai * li) = 0 → lj = ai * li := by decide

/-- An affine function vanishing on the hyperplane `{⟨ℓ, x⟩ = c}` has linear
part `0` or `ℓ`. -/
theorem affine_vanish {ℓ lv : Fin 6 → F₂} {c α : F₂} (hℓ : ℓ ≠ 0)
    (h : ∀ x, c + dotv ℓ x = 0 → α + dotv lv x = 0) : lv = 0 ∨ lv = ℓ := by
  obtain ⟨i, hi⟩ := exists_coord_one hℓ
  have hx0 : c + dotv ℓ (c • unitVec i) = 0 := by
    rw [dotv_smul_right, dotv_unitVec, hi, mul_one, CharTwo.add_self_eq_zero]
  have h0 := h _ hx0
  rw [dotv_smul_right, dotv_unitVec] at h0
  have hcoord : ∀ j, lv j = ℓ j * lv i := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hi, one_mul]
    · have hx : c + dotv ℓ (c • unitVec i + unitVec j + ℓ j • unitVec i) = 0 := by
        rw [dotv_add_right, dotv_add_right, dotv_smul_right, dotv_smul_right, dotv_unitVec,
          dotv_unitVec, hi]
        exact f2_hx c (ℓ j)
      have h1 := h _ hx
      rw [dotv_add_right, dotv_add_right, dotv_smul_right, dotv_smul_right, dotv_unitVec,
        dotv_unitVec] at h1
      exact f2_vanish_aux c (ℓ j) (lv j) (lv i) α h0 h1
  rcases f2_eq_zero_or_one (lv i) with h | h
  · left; funext j; rw [hcoord j, h, mul_zero]; rfl
  · right; funext j; rw [hcoord j, h, mul_one]

theorem iota_unit_comb (j i : Fin 6) (c : F₂) (ω : TwoForm6) (k : Fin 6) :
    iota (unitVec j + c • unitVec i) ω k = ω j k + c * ω i k := by
  simp [iota_apply, unitVec, add_mul, Finset.sum_add_distrib]

theorem f2_row_aux : ∀ wjk wik aj ak wji : F₂, wjk + aj * wik = wji * ak →
    wjk = aj * wik + ak * wji := by decide

theorem f2_dot_aux : ∀ aj : F₂, aj + aj * 1 = 0 := by decide

/-- A 2-form all of whose contractions along `a⊥` are multiples of `a` is
`a ∧ m`. -/
theorem wedge_of_contractions {ω : TwoForm6} {a : Fin 6 → F₂} (hdiag : ∀ i, ω i i = 0)
    (hsymm : ∀ i j, ω i j = ω j i) (ha : a ≠ 0)
    (h : ∀ e, dotv a e = 0 → ∃ c : F₂, iota e ω = c • a) : ∃ m, ω = wedge a m := by
  obtain ⟨i, hi⟩ := exists_coord_one ha
  refine ⟨fun k => ω i k, ?_⟩
  funext j k
  simp only [wedge]
  by_cases hj : j = i
  · subst hj; rw [hi, hdiag, mul_zero, add_zero, one_mul]
  · have he : dotv a (unitVec j + a j • unitVec i) = 0 := by
      rw [dotv_add_right, dotv_smul_right, dotv_unitVec, dotv_unitVec, hi]
      exact f2_dot_aux _
    obtain ⟨c, hc⟩ := h _ he
    have hk := congrFun hc k
    have hii := congrFun hc i
    rw [iota_unit_comb] at hk hii
    rw [hdiag, mul_zero, add_zero, Pi.smul_apply, smul_eq_mul, hi, mul_one] at hii
    rw [Pi.smul_apply, smul_eq_mul, ← hii] at hk
    rw [f2_row_aux _ _ _ _ _ hk, hsymm j i]

theorem pi2_diag (p : ANF 6) (i : Fin 6) : pi2 p i i = 0 := by simp [pi2_apply]

/-- **Lemma W.** A function of degree `≤ 2` vanishing on the hyperplane
`{⟨a, x⟩ = α}` (`a ≠ 0`) has quadratic part `a ∧ m`. -/
theorem pi2_wedge_of_vanish {G : ANF 6} (hG : DegreeLE 2 G) {a : Fin 6 → F₂} {α : F₂}
    (ha : a ≠ 0) (hvan : ∀ x, α + dotv a x = 0 → eval G x = 0) :
    ∃ m, pi2 G = wedge a m := by
  refine wedge_of_contractions (pi2_diag G) (pi2_symm G) ha fun e he => ?_
  have hD : ∀ x, α + dotv a x = 0 →
      deriv e (eval G) 0 + dotv (iota e (pi2 G)) x = 0 := by
    intro x hx
    rw [← bridge_all e G hG x]
    have hx' : α + dotv a (shiftBy e x) = 0 := by
      rw [shiftBy_eq, dotv_add_right, he, add_zero]; exact hx
    simp only [deriv, hvan _ hx', hvan _ hx, add_zero]
  rcases affine_vanish ha hD with h0 | h1
  · exact ⟨0, by rw [h0, zero_smul]⟩
  · exact ⟨1, by rw [h1, one_smul]⟩

/-! ## Directions with a `U`-component (part 2) -/

/-- A direction `e` with `ι_e(Q) ⊆ span{ℓ}` and `ι_e Z₁ ∉ span{ℓ}`. -/
def GenDir (Q : Submodule F₂ TwoForm6) : Prop :=
  ∃ e ℓ : Fin 6 → F₂, (∀ ω ∈ Q, ∃ γ : F₂, iota e ω = γ • ℓ) ∧ ∀ γ : F₂, iota e Z1form ≠ γ • ℓ

theorem bridge_line {Q : Submodule F₂ TwoForm6} {e ℓ : Fin 6 → F₂}
    (hQ : ∀ ω ∈ Q, ∃ γ : F₂, iota e ω = γ • ℓ) {p : ANF 6} (hp : p ∈ V4 Q) :
    ∃ γ : F₂, ∀ x, deriv e (eval p) x = deriv e (eval p) 0 + γ * dotv ℓ x := by
  obtain ⟨γ, hγ⟩ := hQ _ hp.2
  exact ⟨γ, fun x => by rw [bridge_all e p hp.1 x, hγ, dotv_smul_left]⟩

theorem affine_zero {a : Fin 6 → F₂} {α : F₂} (h : ∀ x, α + dotv a x = 0) : a = 0 := by
  funext j
  have h0 := h 0
  have hj := h (unitVec j)
  rw [dotv_zero_right, add_zero] at h0
  rw [dotv_unitVec, h0, zero_add] at hj
  exact hj

theorem f2_c1 : ∀ u w H A : F₂, 1 * w + u * H + 1 * H = A → A = 0 → u * w = 0 := by decide

theorem f2_c0 : ∀ u w H A : F₂, 0 * w + u * H + 0 * H = A → u * H = A := by decide

theorem f2_h1 : ∀ u w A : F₂, u * 1 = A → A = 0 → u * w = 0 := by decide

theorem f2_sumaux : ∀ g g' b c : F₂, g * b + c = g' * b → c = (g + g') * b := by decide

theorem f2_sum_ne {z ℓ : Fin 6 → F₂} {γ γ' : F₂} (hZ : ∀ γ : F₂, z ≠ γ • ℓ)
    (h : γ • ℓ + z = γ' • ℓ) : False := by
  apply hZ (γ + γ')
  funext j
  have hj := congrFun h j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
  exact f2_sumaux _ _ _ _ hj

/-- **Core of Lemma A (derivative form).** Along a direction as in `GenDir`, a
placement `f h ∈ z₁ + V(Q)` produces a function `G` of degree `≤ 2` with
`π₂ G ∈ Z₁ + Q` that vanishes on a hyperplane. -/
theorem z1_place_vanish {Q : Submodule F₂ TwoForm6} (hG : GenDir Q) {f h : ANF 6}
    (hf : f ∈ V4 Q) (hh : h ∈ V4 Q) (hfh : f * h + lowMul3 1 ∈ V4 Q) :
    ∃ G : ANF 6, DegreeLE 2 G ∧ pi2 G + Z1form ∈ Q ∧
      ∃ (a : Fin 6 → F₂) (α : F₂), a ≠ 0 ∧ ∀ x, α + dotv a x = 0 → eval G x = 0 := by
  obtain ⟨e, ℓ, hQℓ, hZ⟩ := hG
  have hz1 : ∀ x, deriv e (eval (lowMul3 1)) x =
      deriv e (eval (lowMul3 1)) 0 + dotv (iota e Z1form) x := fun x => by
    rw [bridge_all e _ degreeLE_two_lowMul3_one x, pi2_lowMul3_one]
  have step : ∀ u w : ANF 6, u ∈ V4 Q → w ∈ V4 Q → u * w + lowMul3 1 ∈ V4 Q →
      (∀ x, deriv e (eval u) x = deriv e (eval u) 0) →
      ∃ G : ANF 6, DegreeLE 2 G ∧ pi2 G + Z1form ∈ Q ∧
        ∃ (a : Fin 6 → F₂) (α : F₂), a ≠ 0 ∧ ∀ x, α + dotv a x = 0 → eval G x = 0 := by
    intro u w hu hw huw hconst
    refine ⟨u * w, ?_, ?_, ?_⟩
    · have hs : u * w = (u * w + lowMul3 1) + lowMul3 1 := by
        rw [add_assoc, anf_add_self, add_zero]
      rw [hs]; exact huw.1.add degreeLE_two_lowMul3_one
    · have := huw.2
      rwa [map_add, pi2_lowMul3_one] at this
    obtain ⟨γw, hw'⟩ := bridge_line hQℓ hw
    obtain ⟨γg, hg'⟩ := bridge_line hQℓ huw
    set a : Fin 6 → F₂ := γg • ℓ + iota e Z1form with ha_def
    set α : F₂ := deriv e (eval (u * w + lowMul3 1)) 0 + deriv e (eval (lowMul3 1)) 0
      with hα_def
    have ha : a ≠ 0 := by
      intro h0
      exact f2_sum_ne (γ' := 0) hZ (by rw [← ha_def, h0, zero_smul])
    -- `D_e(u w) = A` with `A(x) = α + ⟨a, x⟩`.
    have hA : ∀ x, deriv e (eval (u * w)) x = α + dotv a x := fun x => by
      have hs : deriv e (eval (u * w)) x =
          deriv e (eval (u * w + lowMul3 1)) x + deriv e (eval (lowMul3 1)) x := by
        rw [deriv_add, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hs, hg' x, hz1 x, ha_def, hα_def, dotv_add_left, dotv_smul_left]
      ring
    have hprod : ∀ x, deriv e (eval u) 0 * eval w x + eval u x * deriv e (eval w) x +
        deriv e (eval u) 0 * deriv e (eval w) x = α + dotv a x := fun x => by
      rw [← hA x, deriv_mul, hconst x]
    refine ⟨a, α, ha, ?_⟩
    rcases f2_eq_zero_or_one (deriv e (eval u) 0) with hc | hc
    · -- `c = 0`: `u · D_e w = A`.
      have hUH : ∀ x, eval u x * deriv e (eval w) x = α + dotv a x := fun x => by
        have := hprod x; rw [hc] at this; exact f2_c0 _ _ _ _ this
      by_cases hℓ' : γw • ℓ = 0
      · have hHc : ∀ x, deriv e (eval w) x = deriv e (eval w) 0 := fun x => by
          rw [hw' x, ← dotv_smul_left, hℓ', dotv, Finset.sum_eq_zero (fun j _ => by
            rw [Pi.zero_apply, zero_mul]), add_zero]
        rcases f2_eq_zero_or_one (deriv e (eval w) 0) with h0 | h1
        · exfalso
          exact ha (affine_zero fun x => by rw [← hUH x, hHc x, h0, mul_zero])
        · intro x hx
          rw [eval_mul']
          have := hUH x
          rw [hHc x, h1] at this
          exact f2_h1 _ _ _ this hx
      · exfalso
        have hvan : ∀ x, deriv e (eval w) 0 + dotv (γw • ℓ) x = 0 → α + dotv a x = 0 := by
          intro x hx
          rw [← hUH x, hw' x, ← dotv_smul_left, hx, mul_zero]
        rcases affine_vanish hℓ' hvan with h0 | h1
        · exact ha h0
        · exact f2_sum_ne hZ (by rw [← ha_def]; exact h1)
    · -- `c = 1`: `u w = u A`.
      intro x hx
      rw [eval_mul']
      have := hprod x
      rw [hc] at this
      exact f2_c1 _ _ _ _ this hx
  obtain ⟨γf, hf'⟩ := bridge_line hQℓ hf
  obtain ⟨γh, hh'⟩ := bridge_line hQℓ hh
  rcases f2_eq_zero_or_one γf with h0 | h1
  · exact step f h hf hh hfh fun x => by rw [hf' x, h0, zero_mul, add_zero]
  rcases f2_eq_zero_or_one γh with h0' | h1'
  · exact step h f hh hf (by rw [mul_comm]; exact hfh)
      fun x => by rw [hh' x, h0', zero_mul, add_zero]
  refine step (f + h) h ((V4 Q).add_mem hf hh) hh ?_ fun x => ?_
  · have hs : (f + h) * h + lowMul3 1 = (f * h + lowMul3 1) + h := by
      rw [add_mul, anf_mul_self]; ring
    rw [hs]; exact (V4 Q).add_mem hfh hh
  · rw [deriv_add, deriv_add, hf' x, hh' x, h1, h1']
    generalize deriv e (eval f) 0 = A
    generalize deriv e (eval h) 0 = B
    generalize dotv ℓ x = C
    revert A B C; decide

/-! ## From a vanishing product to a good direction -/

theorem goodDir_mono {Q Q' : Submodule F₂ TwoForm6} (h : GoodDir Q') (hle : Q ≤ Q') :
    GoodDir Q := by
  obtain ⟨e, d, ℓ, hp, hℓ, hQ⟩ := h
  exact ⟨e, d, ℓ, hp, hℓ, fun ω hω => hQ ω (hle hω)⟩

/-- **Lemma A for spaces with a `U`-direction.** If `Q₃` has no good direction
but satisfies `GenDir`, the third gate cannot place `z₁`. -/
theorem noPlace_z1_of_genDir (l1 r1 l2 r2 : Fin 6 → F₂)
    (hbad : ¬ GoodDir (Q3span l1 r1 l2 r2)) (hG : GenDir (Q3span l1 r1 l2 r2)) :
    NoPlace (Q3span l1 r1 l2 r2) (lowMul3 1) := by
  intro f h hf hh hfh
  obtain ⟨G, hGdeg, hGQ, a, α, ha, hvan⟩ := z1_place_vanish hG hf hh hfh
  obtain ⟨m, hm⟩ := pi2_wedge_of_vanish hGdeg ha hvan
  apply hbad
  let L : Fin 4 → Fin 6 → F₂ := ![unitVec 0, l1, l2, a]
  let R : Fin 4 → Fin 6 → F₂ := ![unitVec 3, r1, r2, m]
  have hle : Q3span l1 r1 l2 r2 ≤ Submodule.span F₂ (Set.range fun k => wedge (L k) (R k)) := by
    rw [Q3span, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
    · exact Submodule.subset_span ⟨2, rfl⟩
  have hZ : Z1form ∈ Submodule.span F₂ (Set.range fun k => wedge (L k) (R k)) := by
    have hs : Z1form = (pi2 G + Z1form) + wedge (L 3) (R 3) := by
      show Z1form = (pi2 G + Z1form) + wedge a m
      rw [← hm, add_comm (pi2 G), add_assoc, tf_add_self, add_zero]
    rw [hs]
    exact Submodule.add_mem _ (hle hGQ) (Submodule.subset_span ⟨3, rfl⟩)
  exact goodDir_mono (goodDir_main L R rfl hZ) hle

/-! ## Classification by types (part 3) -/

/-- The direction `(0, e₁, e₂, 0, e₄, e₅)`: no `a₀`, `b₀` component. -/
def mkDir (e1 e2 e4 e5 : F₂) : Fin 6 → F₂ := ![0, e1, e2, 0, e4, e5]

theorem dotv_mkDir (v : Fin 6 → F₂) (e1 e2 e4 e5 : F₂) :
    dotv v (mkDir e1 e2 e4 e5) = v 1 * e1 + v 2 * e2 + v 4 * e4 + v 5 * e5 := by
  simp [dotv, mkDir, Fin.sum_univ_succ]
  ring

theorem dotv_unit_left (i : Fin 6) (e : Fin 6 → F₂) : dotv (unitVec i) e = e i := by
  rw [dotv_comm, dotv_unitVec]

theorem iota_P0_gen (e : Fin 6 → F₂) (h0 : e 0 = 0) (h3 : e 3 = 0) : iota e P0form = 0 := by
  rw [P0form, iota_wedge, dotv_unit_left, dotv_unit_left, h0, h3, zero_smul, zero_smul, add_zero]

theorem iota_Z1_apply (e : Fin 6 → F₂) (j : Fin 6) :
    iota e Z1form j = e 4 * unitVec 0 j + e 0 * unitVec 4 j + (e 3 * unitVec 1 j + e 1 * unitVec 3 j) := by
  rw [Z1form, map_add, iota_wedge, iota_wedge]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotv_unit_left]
  ring

/-- A direction with no `a₀, b₀` component and a nonzero `a₁` or `b₁` component,
along which `Q` contracts into one line `⟨ℓ⟩`, with `ℓ = 0` or `ℓ` having a nonzero
`a₂`/`b₂` coordinate. Gives both Lemma A (`genDir_of_uDir`) and Lemma C
(`LemmaC.lean`) for spaces without a good direction. -/
def UDir (Q : Submodule F₂ TwoForm6) : Prop :=
  ∃ e ℓ : Fin 6 → F₂, e 0 = 0 ∧ e 3 = 0 ∧ (e 1 = 1 ∨ e 4 = 1) ∧
    (∀ ω ∈ Q, ∃ γ : F₂, iota e ω = γ • ℓ) ∧ (ℓ 2 = 0 → ℓ 5 = 0 → ℓ = 0)

theorem uDir_of_kill {l1 r1 l2 r2 : Fin 6 → F₂} (e : Fin 6 → F₂) (h0 : e 0 = 0)
    (h3 : e 3 = 0) (hU : e 1 = 1 ∨ e 4 = 1) (hk1 : iota e (wedge l1 r1) = 0)
    (hk2 : iota e (wedge l2 r2) 2 = 0 → iota e (wedge l2 r2) 5 = 0 → iota e (wedge l2 r2) = 0) :
    UDir (Q3span l1 r1 l2 r2) := by
  refine ⟨e, iota e (wedge l2 r2), h0, h3, hU, fun ω hω => ?_, hk2⟩
  have hle : Q3span l1 r1 l2 r2 ≤
      (Submodule.span F₂ {iota e (wedge l2 r2)}).comap (iota e) := by
    rw [Q3span, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · show iota e P0form ∈ Submodule.span F₂ {iota e (wedge l2 r2)}
      rw [iota_P0_gen e h0 h3]; exact Submodule.zero_mem _
    · show iota e (wedge l1 r1) ∈ Submodule.span F₂ {iota e (wedge l2 r2)}
      rw [hk1]; exact Submodule.zero_mem _
    · exact Submodule.mem_span_singleton_self _
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_comap.mp (hle hω))
  exact ⟨γ, hγ.symm⟩

theorem genDir_of_uDir {Q : Submodule F₂ TwoForm6} (h : UDir Q) : GenDir Q := by
  obtain ⟨e, ℓ, h0, h3, hU, hQ, hk2⟩ := h
  have hZ0 : iota e Z1form ≠ 0 := by
    intro h
    have a := congrFun h 0
    have b := congrFun h 3
    simp [iota_Z1_apply, unitVec, h0, h3] at a b
    rcases hU with h1 | h4
    · rw [h1] at b; exact one_ne_zero b
    · rw [h4] at a; exact one_ne_zero a
  refine ⟨e, ℓ, hQ, fun γ hγ => ?_⟩
  rcases f2_eq_zero_or_one γ with rfl | rfl
  · rw [zero_smul] at hγ; exact hZ0 hγ
  · rw [one_smul] at hγ
    have h2 : ℓ 2 = 0 := by rw [← hγ]; simp [iota_Z1_apply, unitVec]
    have h5 : ℓ 5 = 0 := by rw [← hγ]; simp [iota_Z1_apply, unitVec]
    exact hZ0 (hγ.trans (hk2 h2 h5))

theorem hk2_full {l r : Fin 6 → F₂} (hnf : NFfull l r) (e : Fin 6 → F₂) :
    iota e (wedge l r) 2 = 0 → iota e (wedge l r) 5 = 0 → iota e (wedge l r) = 0 := by
  rw [iota_wedge]
  intro h2 h5
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hnf.1, hnf.2.1, hnf.2.2.1, hnf.2.2.2,
    mul_zero, mul_one, add_zero, zero_add] at h2 h5
  rw [h2, h5, zero_smul, zero_smul, add_zero]

theorem f2_tv : ∀ t a b : F₂, t * a = 0 → t * b = 0 → ¬ (a = 0 ∧ b = 0) → t = 0 := by decide

theorem hk2_v {l r : Fin 6 → F₂} (hnf : NFv l r) (e : Fin 6 → F₂) (hl : dotv l e = 0) :
    iota e (wedge l r) 2 = 0 → iota e (wedge l r) 5 = 0 → iota e (wedge l r) = 0 := by
  rw [iota_wedge, hl, zero_smul, zero_add]
  intro h2 h5
  simp only [Pi.smul_apply, smul_eq_mul] at h2 h5
  rw [f2_tv _ _ _ h2 h5 hnf.2.2, zero_smul]

theorem kill_v_fin : ∀ l1 l2 l4 l5 r1 r4 : F₂, ¬ (l2 = 0 ∧ l5 = 0) →
    ∃ e1 e2 e4 e5 : F₂, (e1 = 1 ∨ e4 = 1) ∧ l1 * e1 + l2 * e2 + l4 * e4 + l5 * e5 = 0 ∧
      r1 * e1 + 0 * e2 + r4 * e4 + 0 * e5 = 0 := by
  decide

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem kill_vv_fin : ∀ l1 l2 l4 l5 r1 r4 m1 m2 m4 m5 : F₂, ¬ (l2 = 0 ∧ l5 = 0) →
    ¬ (m2 = 0 ∧ m5 = 0) → ¬ (l2 = m2 ∧ l5 = m5) →
    ∃ e1 e2 e4 e5 : F₂, (e1 = 1 ∨ e4 = 1) ∧ l1 * e1 + l2 * e2 + l4 * e4 + l5 * e5 = 0 ∧
      r1 * e1 + 0 * e2 + r4 * e4 + 0 * e5 = 0 ∧ m1 * e1 + m2 * e2 + m4 * e4 + m5 * e5 = 0 := by
  decide

theorem f2_full_kill : ∀ a c : F₂, a * 1 + 1 * a + c * 0 + 0 * c = 0 ∧
    c * 1 + 0 * a + c * 0 + 1 * c = 0 := by decide

theorem iota_kill {l r e : Fin 6 → F₂} (hl : dotv l e = 0) (hr : dotv r e = 0) :
    iota e (wedge l r) = 0 := by
  rw [iota_wedge, hl, hr, zero_smul, zero_smul, add_zero]

theorem Q3span_comm (l1 r1 l2 r2 : Fin 6 → F₂) : Q3span l1 r1 l2 r2 = Q3span l2 r2 l1 r1 := by
  apply le_antisymm <;> rw [Q3span, Submodule.span_le] <;> rintro _ ⟨k, rfl⟩ <;> fin_cases k
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨2, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨2, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩

theorem Q3span_eq_span4 (l1 r1 l2 r2 : Fin 6 → F₂) :
    Q3span l1 r1 l2 r2 =
      Submodule.span F₂ (Set.range ![P0form, wedge l1 r1, wedge l2 r2, (0 : TwoForm6)]) := by
  unfold Q3span
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨k, rfl⟩ <;> fin_cases k
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · exact Submodule.subset_span ⟨2, rfl⟩
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · exact Submodule.subset_span ⟨2, rfl⟩
  · exact Submodule.zero_mem _

theorem goodDir_zero1 {l1 r1 l2 r2 : Fin 6 → F₂} (h : NFzero l1 r1) :
    GoodDir (Q3span l1 r1 l2 r2) := by
  rw [Q3span_eq_span4]
  refine goodDir_caseA _ l2 r2 fun k => ?_
  fin_cases k
  · exact Or.inl phi_P0
  · exact Or.inl (phi_of_NFzero h)
  · exact Or.inr rfl
  · exact Or.inl (map_zero Phi)

theorem goodDir_zero2 {l1 r1 l2 r2 : Fin 6 → F₂} (h : NFzero l2 r2) :
    GoodDir (Q3span l1 r1 l2 r2) := by
  rw [Q3span_comm]; exact goodDir_zero1 h

theorem goodDir_sameV {l1 r1 l2 r2 : Fin 6 → F₂} (h1 : NFv l1 r1) (h2 : NFv l2 r2)
    (hs2 : l1 2 = l2 2) (hs5 : l1 5 = l2 5) : GoodDir (Q3span l1 r1 l2 r2) := by
  rw [Q3span_eq_span4]
  rcases f2_eq_zero_or_one (l1 5) with h5 | h5
  · have hp : PaperPair dirB2 (unitVec 0) := Or.inr (Or.inl ⟨rfl, rfl⟩)
    refine goodDir_kill _ hp fun k => ?_
    fin_cases k
    · exact iota_P0 hp
    · exact iota_dirB2_v h1 h5
    · exact iota_dirB2_v h2 (hs5 ▸ h5)
    · exact map_zero _
  rcases f2_eq_zero_or_one (l1 2) with h2' | h2'
  · have hp : PaperPair dirA2 (unitVec 3) := Or.inl ⟨rfl, rfl⟩
    refine goodDir_kill _ hp fun k => ?_
    fin_cases k
    · exact iota_P0 hp
    · exact iota_dirA2_v h1 h2'
    · exact iota_dirA2_v h2 (hs2 ▸ h2')
    · exact map_zero _
  · have hp : PaperPair dirA2B2 (unitVec 0 + unitVec 3) := Or.inr (Or.inr ⟨rfl, rfl⟩)
    have hsum : ∀ a b : F₂, a = 1 → b = 1 → a + b = 0 := by decide
    refine goodDir_kill _ hp fun k => ?_
    fin_cases k
    · exact iota_P0 hp
    · exact iota_dirA2B2_v h1 (hsum _ _ h2' h5)
    · exact iota_dirA2B2_v h2 (hsum _ _ (hs2 ▸ h2') (hs5 ▸ h5))
    · exact map_zero _

theorem uDir_v_first {l1 r1 l2 r2 : Fin 6 → F₂} (h1 : NFv l1 r1) (h2 : NFfull l2 r2) :
    UDir (Q3span l1 r1 l2 r2) := by
  obtain ⟨e1, e2, e4, e5, hU, hl, hr⟩ :=
    kill_v_fin (l1 1) (l1 2) (l1 4) (l1 5) (r1 1) (r1 4) h1.2.2
  refine uDir_of_kill (mkDir e1 e2 e4 e5) rfl rfl hU (iota_kill ?_ ?_) (hk2_full h2 _)
  · rw [dotv_mkDir]; exact hl
  · rw [dotv_mkDir, h1.1, h1.2.1]; exact hr

theorem uDir_vv {l1 r1 l2 r2 : Fin 6 → F₂} (h1 : NFv l1 r1) (h2 : NFv l2 r2)
    (hd : ¬ (l1 2 = l2 2 ∧ l1 5 = l2 5)) : UDir (Q3span l1 r1 l2 r2) := by
  obtain ⟨e1, e2, e4, e5, hU, hl, hr, hm⟩ :=
    kill_vv_fin (l1 1) (l1 2) (l1 4) (l1 5) (r1 1) (r1 4) (l2 1) (l2 2) (l2 4) (l2 5)
      h1.2.2 h2.2.2 hd
  refine uDir_of_kill (mkDir e1 e2 e4 e5) rfl rfl hU (iota_kill ?_ ?_)
    (hk2_v h2 _ (by rw [dotv_mkDir]; exact hm))
  · rw [dotv_mkDir]; exact hl
  · rw [dotv_mkDir, h1.1, h1.2.1]; exact hr

theorem uDir_full {l1 r1 l2 r2 : Fin 6 → F₂} (h1 : NFfull l1 r1) (h2 : NFfull l2 r2) :
    UDir (Q3span l1 r1 l2 r2) := by
  refine uDir_of_kill (mkDir 1 (l1 1) 0 (r1 1)) rfl rfl (Or.inl rfl) (iota_kill ?_ ?_)
    (hk2_full h2 _)
  · rw [dotv_mkDir, h1.1, h1.2.1]; exact (f2_full_kill (l1 1) (r1 1)).1
  · rw [dotv_mkDir, h1.2.2.1, h1.2.2.2]; exact (f2_full_kill (l1 1) (r1 1)).2

/-- Every `Q₃` in normal form has a good direction or a `U`-direction. -/
theorem goodDir_or_uDir {l1 r1 l2 r2 : Fin 6 → F₂}
    (h1 : NFzero l1 r1 ∨ NFv l1 r1 ∨ NFfull l1 r1)
    (h2 : NFzero l2 r2 ∨ NFv l2 r2 ∨ NFfull l2 r2) :
    GoodDir (Q3span l1 r1 l2 r2) ∨ UDir (Q3span l1 r1 l2 r2) := by
  rcases h1 with z1 | v1 | f1
  · exact Or.inl (goodDir_zero1 z1)
  rcases h2 with z2 | v2 | f2
  · exact Or.inl (goodDir_zero2 z2)
  · by_cases hs : l1 2 = l2 2 ∧ l1 5 = l2 5
    · exact Or.inl (goodDir_sameV v1 v2 hs.1 hs.2)
    · exact Or.inr (uDir_vv v1 v2 hs)
  · exact Or.inr (uDir_v_first v1 f2)
  rcases h2 with z2 | v2 | f2
  · exact Or.inl (goodDir_zero2 z2)
  · rw [Q3span_comm]; exact Or.inr (uDir_v_first v2 f1)
  · exact Or.inr (uDir_full f1 f2)

/-- Every `Q₃ = span{P₀, l₁∧r₁, l₂∧r₂}` without a good direction has a
`U`-direction. -/
theorem uDir_of_bad (l1 r1 l2 r2 : Fin 6 → F₂) (hbad : ¬ GoodDir (Q3span l1 r1 l2 r2)) :
    UDir (Q3span l1 r1 l2 r2) := by
  obtain ⟨a1, b1, hw1, hn1⟩ := types l1 r1
  obtain ⟨a2, b2, hw2, hn2⟩ := types l2 r2
  have hQ : Q3span l1 r1 l2 r2 = Q3span a1 b1 a2 b2 := by simp only [Q3span, hw1, hw2]
  rw [hQ] at hbad ⊢
  rcases goodDir_or_uDir hn1 hn2 with hg | hg
  · exact (hbad hg).elim
  · exact hg

/-- **`BadClaim`, first conjunct (Lemma A for bad spaces).** -/
theorem noPlace_z1_bad (l1 r1 l2 r2 : Fin 6 → F₂) (hbad : ¬ GoodDir (Q3span l1 r1 l2 r2)) :
    NoPlace (Q3span l1 r1 l2 r2) (lowMul3 1) :=
  noPlace_z1_of_genDir l1 r1 l2 r2 hbad (genDir_of_uDir (uDir_of_bad l1 r1 l2 r2 hbad))

end

end LowHalfMul3

end UnrestrictedBooleanMul
