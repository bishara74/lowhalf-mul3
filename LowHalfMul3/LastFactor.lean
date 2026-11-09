module

public import LowHalfMul3.Shared
public import LowHalfMul3.OneHigh

@[expose] public section

/-!
# Last-factor rigidity modulo the low-bit ideal

A nonzero constant external difference of the last factor would give an
ordinary product placing the target. When the extra generator has a killing
external direction, the remaining derivative forces two low-bit fibers on
which the last factor is one. Their free slopes determine the factor on all
off-ideal fibers. Independent external parts are handled by a mixed difference.
-/

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

private theorem eval_extGate (d : F₂) (l b x : Vec) :
    eval (ExtGate d l b) x = (d * (x 0 * x 3) + dotv l x) * dotv b x := by
  rw [ExtGate, eval_mul', eval_add', eval_smul', eval_p0, eval_linANF, eval_linANF]

private theorem z1_shift (x e : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) :
    eval z1 (x + e) = eval z1 x + (e 1 * x 3 + e 4 * x 0) := by
  simp only [eval_lowMul3_one, Pi.add_apply, he0, he3, add_zero]
  ring

private theorem z2_shift (x e : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) :
    eval z2 (x + e) = eval z2 x + (e 2 * x 3 + e 5 * x 0) +
      (1 + x 0 * x 3) * (e 1 * x 4 + e 4 * x 1 + e 1 * e 4) := by
  simp only [eval_lowMul3_two, Pi.add_apply, he0, he3, add_zero]
  ring

private def gateDelta (d : F₂) (l b e : Vec) : A6 :=
  dotv b e • (d • P0 + linANF l) + dotv l e • linANF b +
    (dotv l e * dotv b e) • (1 : A6)

private theorem gateDelta_mem (d : F₂) (l b e : Vec) :
    gateDelta d l b e ∈ V4 Q0 := by
  have hp : P0 ∈ V4 Q0 := by rw [v4_q0]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have ha (v : Vec) := affine_le_V4 Q0 (linANF_mem_affine v)
  have h1 := affine_le_V4 Q0 (one_mem_affine 6)
  exact (V4 Q0).add_mem ((V4 Q0).add_mem
    ((V4 Q0).smul_mem _ ((V4 Q0).add_mem ((V4 Q0).smul_mem _ hp) (ha l)))
    ((V4 Q0).smul_mem _ (ha b))) ((V4 Q0).smul_mem _ h1)

private theorem gate_shift (d : F₂) (l b x e : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) :
    eval (ExtGate d l b) (x + e) = eval (ExtGate d l b) x + eval (gateDelta d l b e) x := by
  simp only [eval_extGate, gateDelta, eval_add', eval_smul', eval_one', mul_one, eval_p0,
    eval_linANF, dotv_add_right, Pi.add_apply, he0, he3, add_zero]
  ring

private theorem gateDelta_shift (d : F₂) (l b x e v : Vec) (hv0 : v 0 = 0) (hv3 : v 3 = 0) :
    eval (gateDelta d l b e) (x + v) = eval (gateDelta d l b e) x +
      (dotv b e * dotv l v + dotv l e * dotv b v) := by
  simp only [gateDelta, eval_add', eval_smul', eval_one', mul_one, eval_p0,
    eval_linANF, dotv_add_right, Pi.add_apply, hv0, hv3, add_zero]
  ring

private theorem s0_shift {u : A6} (hu : u ∈ V4 S0) :
    ∃ f : LowForm, ∃ ζ : F₂, ∀ x e : Vec, e 0 = 0 → e 3 = 0 →
      eval u (x + e) = eval u x + (dotv f.slope e + ζ * (e 1 * x 3 + e 4 * x 0)) := by
  rw [v4_s0] at hu
  obtain ⟨v, hv, ζ, rfl⟩ := mem_extend.mp hu
  obtain ⟨f, hf⟩ := lowForm_of_mem hv
  refine ⟨f, ζ, fun x e he0 he3 => ?_⟩
  simp only [eval_add', eval_smul', hf, LowForm.value, z1_shift x e he0 he3,
    Pi.add_apply, he0, he3, add_zero, dotv_add_right]
  ring

private theorem v4q0_le_s0 : V4 Q0 ≤ V4 S0 := by
  rw [v4_s0]
  exact le_sup_left

private theorem s0_le_plus (c : A6) : V4 S0 ≤ PlusZ1 c := le_sup_left

private theorem plus_zero (d : F₂) {l b : Vec} {k R D : A6}
    (h : k * D = R) (hbase : R + z2 ∈ PlusZ1 (ExtGate d l b))
    (hk : k ∈ PlusZ1 (ExtGate d l b))
    (hD : D ∈ PlusZ1 (ExtGate d l b)) (hb : OffLowSpan b) : False := by
  have hprod : k * D + z2 ∈ PlusZ1 (ExtGate d l b) := h ▸ hbase
  rcases f2_eq_zero_or_one d with rfl | rfl
  · rw [(quadratic_space_eq l b).2] at hprod hk hD
    exact formA_zero hk hD hprod
  · let W := PlusZ1 (ExtGate 1 l b)
    have hF : ∀ i : Fin 4, (![k, D, 0, 0] : Fin 4 → A6) i ∈ W := by
      intro i
      fin_cases i
      · exact hk
      · exact hD
      · exact W.zero_mem
      · exact W.zero_mem
    exact ordinary_pair_noPlace hb hF (by simpa using hprod)

private theorem fixed_scalar {k k' r r' : F₂} (h : k * r = r) (h' : k' * r' = r')
    (hd : k' = k + 1) : r = k * (r' + r) := by
  rcases f2_eq_zero_or_one k with rfl | rfl
  · simpa using h.symm
  · have h0 : k' = 0 := by simpa only [CharTwo.add_self_eq_zero] using hd
    rw [h0, zero_mul] at h'
    rw [← h', zero_add, one_mul]

private theorem fixed_constant_shift {k r r' : F₂} (h : k * r = r)
    (h' : k * r' = r') : (1 + k) * (r' + r) = 0 := by
  rw [mul_add, add_mul, one_mul, h', add_mul, one_mul, h]
  simp [CharTwo.add_self_eq_zero]

private def extDelta (d : F₂) (l b e : Vec) (σ a : F₂) : A6 :=
  a • (1 : A6) + e 2 • X 3 + e 5 • X 0 + σ • gateDelta d l b e

private theorem extDelta_mem (d : F₂) (l b e : Vec) (σ a : F₂) :
    extDelta d l b e σ a ∈ V4 Q0 := by
  have ha : a • (1 : A6) + e 2 • X 3 + e 5 • X 0 ∈ affine 6 :=
    (affine 6).add_mem ((affine 6).add_mem ((affine 6).smul_mem _ (one_mem_affine 6))
      ((affine 6).smul_mem _ (X_mem_affine _))) ((affine 6).smul_mem _ (X_mem_affine _))
  exact (V4 Q0).add_mem (affine_le_V4 _ ha) ((V4 Q0).smul_mem _ (gateDelta_mem d l b e))

private theorem extDelta_eval (d : F₂) (l b e x : Vec) (σ a : F₂) :
    eval (extDelta d l b e σ a) x =
      a + e 2 * x 3 + e 5 * x 0 + σ * eval (gateDelta d l b e) x := by
  simp only [extDelta, eval_add', eval_smul', eval_one', eval_X, mul_one]

private theorem target_ext_shift (d : F₂) (l b : Vec) {v : A6} (hv : v ∈ V4 S0) (σ : F₂) :
    ∃ a : Vec, ∀ x s t, eval (z2 + (v + σ • ExtGate d l b)) (x + extDir s t) =
      eval (z2 + (v + σ • ExtGate d l b)) x +
        eval (extDelta d l b (extDir s t) σ (dotv a (extDir s t))) x := by
  obtain ⟨f, ζ, hf⟩ := s0_shift hv
  refine ⟨f.slope, fun x s t => ?_⟩
  let e := extDir s t
  have h0 : e 0 = 0 := rfl
  have h3 : e 3 = 0 := rfl
  have h1 : e 1 = 0 := rfl
  have h4 : e 4 = 0 := rfl
  change eval (z2 + (v + σ • ExtGate d l b)) (x + e) = _
  simp only [eval_add', eval_smul', z2_shift x e h0 h3, hf x e h0 h3,
    gate_shift d l b x e h0 h3, extDelta_eval, h1, h4, zero_mul, add_zero, mul_zero]
  ring

private theorem fixed_shift_zero {d : F₂} {l b : Vec} {k R D : A6} (hb : OffLowSpan b)
    (hk : k ∈ PlusZ1 (ExtGate d l b)) (hR : R + z2 ∈ PlusZ1 (ExtGate d l b))
    (hfix : k * R = R) (hD : D ∈ V4 Q0) {e : Vec} {γ : F₂}
    (hk' : ∀ x : Vec, eval k (x + e) = eval k x + γ)
    (hR' : ∀ x : Vec, eval R (x + e) = eval R x + eval D x) : γ = 0 := by
  rcases f2_eq_zero_or_one γ with h | h
  · exact h
  exfalso
  have hfix' (x : Vec) : eval k x * eval R x = eval R x := by
    rw [← eval_mul', hfix]
  have hprod : k * D = R := anf_ext_eval fun x => by
    rw [eval_mul']
    have he := fixed_scalar (hfix' x) (hfix' (x + e)) (by rw [hk', h])
    rw [hR', add_comm (eval R x), add_assoc, CharTwo.add_self_eq_zero, add_zero] at he
    exact he.symm
  exact plus_zero d hprod hR hk (s0_le_plus _ (v4q0_le_s0 hD)) hb

private theorem target_second_diff (d σ : F₂) (l b : Vec) {v : A6} (hv : v ∈ V4 S0)
    (x e f : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) (hf0 : f 0 = 0) (hf3 : f 3 = 0) :
    let R := z2 + (v + σ • ExtGate d l b)
    eval R (x + f + e) + eval R (x + f) + (eval R (x + e) + eval R x) =
      (1 + x 0 * x 3) * (e 1 * f 4 + e 4 * f 1) +
        σ * (dotv b e * dotv l f + dotv l e * dotv b f) := by
  obtain ⟨a, ζ, ha⟩ := s0_shift hv
  have hgate := gateDelta_shift d l b x e f hf0 hf3
  dsimp only
  simp only [eval_add', eval_smul', z2_shift (x + f) e he0 he3, z2_shift x e he0 he3,
    ha (x + f) e he0 he3, ha x e he0 he3, gate_shift d l b (x + f) e he0 he3,
    gate_shift d l b x e he0 he3, hgate, Pi.add_apply, hf0, hf3, add_zero]
  ring_nf
  simp [two_f2]

private theorem kernel_two_rows {a b c d u v : F₂}
    (h : a*d+b*c = 1) (h₁ : a*v+b*u = 0) (h₂ : c*v+d*u = 0) :
    u = 0 ∧ v = 0 := by
  constructor
  · linear_combination (norm := (ring_nf; simp [two_f2])) a*h₂ + c*h₁ - u*h
  · linear_combination (norm := (ring_nf; simp [two_f2])) d*h₁ + b*h₂ - v*h

private theorem target_nonzero_fiber {d σ : F₂} {l b : Vec} {v : A6} (hv : v ∈ V4 S0)
    (hn : ¬ CoreHi (ExtGate d l b)) (x : Vec) (hx : x 0 * x 3 = 0) :
    ∃ y : Vec, y 0 = x 0 ∧ y 3 = x 3 ∧ eval (z2 + (v + σ • ExtGate d l b)) y = 1 := by
  by_contra! h
  let R := z2 + (v + σ • ExtGate d l b)
  have hz (y : Vec) (h0 : y 0 = x 0) (h3 : y 3 = x 3) : eval R y = 0 :=
    (f2_eq_zero_or_one _).resolve_right (h y h0 h3)
  have hc (i j : Fin 6) (hi0 : i ≠ 0) (hi3 : i ≠ 3) (hj0 : j ≠ 0) (hj3 : j ≠ 3) :
      (unitVec i 1 * unitVec j 4 + unitVec i 4 * unitVec j 1) =
        σ * (l i * b j + l j * b i) := by
    have i0 : unitVec i 0 = 0 := by simp [unitVec, Ne.symm hi0]
    have i3 : unitVec i 3 = 0 := by simp [unitVec, Ne.symm hi3]
    have j0 : unitVec j 0 = 0 := by simp [unitVec, Ne.symm hj0]
    have j3 : unitVec j 3 = 0 := by simp [unitVec, Ne.symm hj3]
    have e := target_second_diff d σ l b hv x (unitVec i) (unitVec j) i0 i3 j0 j3
    change eval R (x + unitVec j + unitVec i) + eval R (x + unitVec j) +
      (eval R (x + unitVec i) + eval R x) = _ at e
    simp only [hz (x + unitVec j + unitVec i) (by simp [Pi.add_apply, i0, j0])
        (by simp [Pi.add_apply, i3, j3]),
      hz (x + unitVec j) (by simp [Pi.add_apply, j0]) (by simp [Pi.add_apply, j3]),
      hz (x + unitVec i) (by simp [Pi.add_apply, i0]) (by simp [Pi.add_apply, i3]),
      hz x rfl rfl, hx, add_zero, one_mul, dotv_unitVec, mul_comm (b i)] at e
    exact f2_eq_of_add_eq_zero (by simpa only [add_comm (l j * b i)] using e.symm)
  have h14 := hc 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hσ : σ = 1 := (f2_eq_zero_or_one σ).resolve_left (by
    intro hs
    simp [unitVec, hs] at h14)
  have hdet : l 1 * b 4 + b 1 * l 4 = 1 := by
    simpa [unitVec, hσ, mul_comm (b 1)] using h14.symm
  have hex (j : Fin 6) (hj : j = 2 ∨ j = 5) : l j = 0 ∧ b j = 0 := by
    have h1 (j : Fin 6) (hj0 : j ≠ 0) (hj3 : j ≠ 3) (hj1 : j ≠ 1) (hj4 : j ≠ 4) :
        l j = 0 ∧ b j = 0 := by
      have h1 := hc 1 j (by norm_num) (by norm_num) hj0 hj3
      have h4 := hc 4 j (by norm_num) (by norm_num) hj0 hj3
      exact kernel_two_rows hdet
        (by simpa [unitVec, Ne.symm hj1, Ne.symm hj4, hσ, mul_comm (b 1)] using h1.symm)
        (by simpa [unitVec, Ne.symm hj1, Ne.symm hj4, hσ, mul_comm (b 4)] using h4.symm)
    rcases hj with rfl | rfl <;> exact h1 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hn (coreHi_extGate_of_core_any d (hex 2 (Or.inl rfl)).1 (hex 5 (Or.inr rfl)).1
    (hex 2 (Or.inl rfl)).2 (hex 5 (Or.inr rfl)).2)

private def SameLow (x y : Vec) : Prop := x 0 = y 0 ∧ x 3 = y 3

private theorem sameLow_add (x e : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) :
    SameLow (x + e) x := ⟨by simp [Pi.add_apply, he0], by simp [Pi.add_apply, he3]⟩

private theorem sameLow_refl (x : Vec) : SameLow x x := ⟨rfl, rfl⟩

private theorem sameLow_trans {x y z : Vec} (h : SameLow x y) (h' : SameLow y z) :
    SameLow x z := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

private theorem fiber_constant {k : A6} (x : Vec)
    (hshift : ∀ e : Vec, e 0 = 0 → e 3 = 0 → eval k (x + e) = eval k x) :
    ∀ y : Vec, SameLow y x → eval k y = eval k x := by
  intro y h
  have he := hshift (x + y) (by simp [Pi.add_apply, h.1, CharTwo.add_self_eq_zero])
    (by simp [Pi.add_apply, h.2, CharTwo.add_self_eq_zero])
  rwa [← add_assoc, vec_add_self, zero_add] at he

private theorem source_shift (d : F₂) (l b : Vec) {u : A6} (hu : u ∈ V4 S0) (τ : F₂) :
    ∃ a : Vec, ∃ ζ : F₂, ∀ x e : Vec, e 0 = 0 → e 3 = 0 →
      eval (u + τ • ExtGate d l b) (x + e) =
      eval (u + τ • ExtGate d l b) x +
        (dotv a e + ζ * (e 1 * x 3 + e 4 * x 0) + τ * eval (gateDelta d l b e) x) := by
  obtain ⟨f, ζ, hf⟩ := s0_shift hu
  refine ⟨f.slope, ζ, fun x e he0 he3 => ?_⟩
  simp only [eval_add', eval_smul', hf x e he0 he3, gate_shift d l b x e he0 he3]
  ring

private theorem cancel_shift {r s : F₂} (h : r = r + s) : s = 0 := by
  exact add_left_cancel (by simpa only [add_zero] using h.symm : r + s = r + 0)

private theorem add_cancel_f2 (x y : F₂) : x + y + x = y := by
  rw [add_comm x y, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem k_fibers_of_slopes {k R : A6} (a b : Vec) (ζ : F₂) (C : Vec → F₂)
    (hk : ∀ x e : Vec, e 0 = 0 → e 3 = 0 → eval k (x + e) =
      eval k x + (dotv a e + ζ * (e 1 * x 3 + e 4 * x 0) + C x * dotv b e))
    (hC : ∀ x y, SameLow y x → C y = C x)
    (hfix : ∀ x : Vec, eval k x * eval R x = eval R x)
    (hR : ∀ x : Vec, x 0 * x 3 = 0 → ∃ y : Vec, SameLow y x ∧ eval R y = 1)
    {p q : Vec} (hneq : ¬ SameLow p q)
    (hp : ∀ x, SameLow x p → eval k x = 1) (hq : ∀ x, SameLow x q → eval k x = 1)
    (hcase : (∀ x, C x = 0) ∨ ∃ j : Fin 6, (j = 2 ∨ j = 5) ∧ b j = 1 ∧
      ∀ x : Vec, x 0 * x 3 = 0 →
        ¬ (∀ y : Vec, SameLow y x → eval k (y + unitVec j) = eval k y + 1)) :
    ∀ x : Vec, x 0 * x 3 = 0 → eval k x = 1 := by
  have hzero (x : Vec) (h : ∀ y, SameLow y x → eval k y = 1)
      (e : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) :
      dotv a e + ζ * (e 1 * x 3 + e 4 * x 0) + C x * dotv b e = 0 :=
    cancel_shift (by rw [← hk x e he0 he3, h x (sameLow_refl x), h _ (sameLow_add x e he0 he3)])
  have hrow (x : Vec) (h : ∀ y, SameLow y x → eval k y = 1)
      (j : Fin 6) (hj0 : j ≠ 0) (hj3 : j ≠ 3) :
      a j + ζ * (unitVec j 1 * x 3 + unitVec j 4 * x 0) + C x * b j = 0 := by
    simpa only [dotv_unitVec] using hzero x h (unitVec j)
      (by simp [unitVec, Ne.symm hj0]) (by simp [unitVec, Ne.symm hj3])
  have heq : C p = C q := by
    rcases hcase with hc | ⟨j, hj, hb, _⟩
    · rw [hc, hc]
    have hz (x : Vec) (h : ∀ y, SameLow y x → eval k y = 1) : C x = a j := by
      rcases hj with rfl | rfl
      · have hz := hrow x h 2 (by norm_num) (by norm_num)
        exact (f2_eq_of_add_eq_zero (by simpa [unitVec, hb] using hz)).symm
      · have hz := hrow x h 5 (by norm_num) (by norm_num)
        exact (f2_eq_of_add_eq_zero (by simpa [unitVec, hb] using hz)).symm
    rw [hz p hp, hz q hq]
  have hζ : ζ = 0 := by
    rcases f2_eq_zero_or_one ζ with h | h
    · exact h
    exfalso
    apply hneq
    have hcoord {u v x y : F₂} (h₁ : u + x + v = 0) (h₂ : u + y + v = 0) : x = y := by
      have h' : u + x + v = u + y + v := h₁.trans h₂.symm
      exact add_left_cancel (add_right_cancel h')
    constructor
    · apply hcoord (u := a 4) (v := C q * b 4)
      · simpa [unitVec, h, heq] using hrow p hp 4 (by norm_num) (by norm_num)
      · simpa [unitVec, h] using hrow q hq 4 (by norm_num) (by norm_num)
    · apply hcoord (u := a 1) (v := C q * b 1)
      · simpa [unitVec, h, heq] using hrow p hp 1 (by norm_num) (by norm_num)
      · simpa [unitVec, h] using hrow q hq 1 (by norm_num) (by norm_num)
  have ha (e : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) :
      dotv a e = C p * dotv b e :=
    f2_eq_of_add_eq_zero (by simpa [hζ] using hzero p hp e he0 he3)
  have hCx (x : Vec) (hx : x 0 * x 3 = 0) : C x = C p := by
    rcases hcase with hc | ⟨j, hj, hb, hn⟩
    · rw [hc, hc]
    by_contra h
    have hsum : C p + C x = 1 := (f2_eq_zero_or_one _).resolve_left
      (fun hz => h (f2_eq_of_add_eq_zero hz).symm)
    have he0 : unitVec j 0 = 0 := by rcases hj with rfl | rfl <;> rfl
    have he3 : unitVec j 3 = 0 := by rcases hj with rfl | rfl <;> rfl
    apply hn x hx
    intro y hy
    simpa [hζ, hC x y hy, ha _ he0 he3, dotv_unitVec, hb, hsum] using hk y _ he0 he3
  intro x hx
  have hconst := fiber_constant x (k := k) fun e he0 he3 => by
    simpa [hζ, ha e he0 he3, hCx x hx, CharTwo.add_self_eq_zero] using hk x e he0 he3
  obtain ⟨y, hy, hRy⟩ := hR x hx
  have hyk := hfix y
  rw [hRy, mul_one] at hyk
  exact (hconst y hy).symm.trans hyk

private theorem zero_fiber_slope_relation {d : F₂} {l b p : Vec} {k : A6} {a : Vec} {ζ : F₂}
    (hkp : ∀ x, SameLow x p → eval k x = 1)
    (hk : ∀ x e : Vec, e 0 = 0 → e 3 = 0 → eval k (x + e) =
      eval k x + (dotv a e + ζ * (e 1 * x 3 + e 4 * x 0) + eval (gateDelta d l b e) x))
    (e f : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) (hf0 : f 0 = 0) (hf3 : f 3 = 0) :
    dotv b e * dotv l f + dotv l e * dotv b f = 0 := by
  let A := dotv a e + ζ * (e 1 * p 3 + e 4 * p 0)
  have h (x : Vec) (hx : SameLow x p) : A + eval (gateDelta d l b e) x = 0 := by
    have hh := hk x e he0 he3
    rw [hkp _ hx, hkp _ (sameLow_trans (sameLow_add x e he0 he3) hx), hx.1, hx.2] at hh
    exact cancel_shift hh
  have hp := h p (sameLow_refl p)
  have hf := h (p + f) (sameLow_add p f hf0 hf3)
  rw [gateDelta_shift d l b p e f hf0 hf3, ← add_assoc, hp, zero_add] at hf
  exact hf

private theorem fiber_finish {d τ σ : F₂} {l b : Vec} {u v : A6}
    (hu : u ∈ V4 S0) (hv : v ∈ V4 S0) (hb : OffLowSpan b)
    (hn : ¬ CoreHi (ExtGate d l b))
    {p q : Vec} (hneq : ¬ SameLow p q)
    (hp : ∀ x, SameLow x p → eval (u + τ • ExtGate d l b) x = 1)
    (hq : ∀ x, SameLow x q → eval (u + τ • ExtGate d l b) x = 1)
    (hfix : (u + τ • ExtGate d l b) * (z2 + (v + σ • ExtGate d l b)) =
      z2 + (v + σ • ExtGate d l b)) :
    ModLow (u + τ • ExtGate d l b) 1 := by
  let c := ExtGate d l b
  let k := u + τ • c
  let R := z2 + (v + σ • c)
  have hF (x : Vec) : eval k x * eval R x = eval R x := by
    rw [← eval_mul']
    exact congrArg (fun v : A6 => eval v x) hfix
  have hR (x : Vec) (hx : x 0 * x 3 = 0) : ∃ y : Vec, SameLow y x ∧ eval R y = 1 := by
    obtain ⟨y, h0, h3, he⟩ := target_nonzero_fiber (σ := σ) hv hn x hx
    exact ⟨y, ⟨h0, h3⟩, he⟩
  obtain ⟨a, ζ, hk⟩ := source_shift d l b hu τ
  change ∀ x e : Vec, e 0 = 0 → e 3 = 0 → eval k (x + e) = eval k x +
      (dotv a e + ζ * (e 1 * x 3 + e 4 * x 0) + τ * eval (gateDelta d l b e) x) at hk
  have done (h : ∀ x : Vec, x 0 * x 3 = 0 → eval k x = 1) : ModLow k 1 :=
    modLow_iff.mpr fun x hx => by rw [eval_one']; exact h x hx
  rcases f2_eq_zero_or_one τ with ht | ht
  · apply done
    apply k_fibers_of_slopes a b ζ (fun _ => 0) _ (fun _ _ _ => rfl) hF hR hneq hp hq
      (Or.inl fun _ => rfl)
    intro x e he0 he3
    simpa [ht] using hk x e he0 he3
  have hks (x e : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) :
      eval k (x + e) = eval k x +
        (dotv a e + ζ * (e 1 * x 3 + e 4 * x 0) + eval (gateDelta d l b e) x) := by
    simpa [ht] using hk x e he0 he3
  have hrel := zero_fiber_slope_relation hp hks
  obtain ⟨j, hj0, hj3, hj⟩ := hb
  let η := l j
  have hdep (i : Fin 6) (hi0 : i ≠ 0) (hi3 : i ≠ 3) : l i = η * b i := by
    have he := hrel (unitVec j) (unitVec i)
      (by simp [unitVec, Ne.symm hj0]) (by simp [unitVec, Ne.symm hj3])
      (by simp [unitVec, Ne.symm hi0]) (by simp [unitVec, Ne.symm hi3])
    rw [dotv_unitVec, dotv_unitVec, dotv_unitVec, dotv_unitVec, hj, one_mul] at he
    exact f2_eq_of_add_eq_zero he
  have hbext : ∃ i : Fin 6, (i = 2 ∨ i = 5) ∧ b i = 1 := by
    rcases f2_eq_zero_or_one (b 2) with h2 | h2
    · rcases f2_eq_zero_or_one (b 5) with h5 | h5
      · exact (hn (coreHi_extGate_of_core_any d
          (by rw [hdep 2 (by norm_num) (by norm_num), h2, mul_zero])
          (by rw [hdep 5 (by norm_num) (by norm_num), h5, mul_zero]) h2 h5)).elim
      · exact ⟨5, Or.inr rfl, h5⟩
    · exact ⟨2, Or.inl rfl, h2⟩
  obtain ⟨i, hi, hbi⟩ := hbext
  let L0 := l 0 + η * b 0
  let L3 := l 3 + η * b 3
  let C (x : Vec) := d * (x 0 * x 3) + L0 * x 0 + L3 * x 3 + η
  have hl : l = η • b + L0 • unitVec 0 + L3 • unitVec 3 := by
    funext i
    by_cases h0 : i = 0
    · subst i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec]
      norm_num
      simp [L0, add_comm (η * b 0), add_assoc, CharTwo.add_self_eq_zero]
    by_cases h3 : i = 3
    · subst i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec, ite_eq_right h0]
      simp [L3, add_comm (η * b 3), add_assoc, CharTwo.add_self_eq_zero]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec, h0, h3, hdep i h0 h3]
  have hC (x y : Vec) (hy : SameLow y x) : C y = C x := by simp [C, hy.1, hy.2]
  have hc (x : Vec) : eval c x = C x * dotv b x := by
    rw [eval_extGate]
    have hx : dotv l x = η * dotv b x + L0 * x 0 + L3 * x 3 := by
      rw [hl, dotv_add_left, dotv_add_left, dotv_smul_left, dotv_smul_left, dotv_smul_left,
        dotv_unit_left, dotv_unit_left]
    rw [hx]
    rcases f2_eq_zero_or_one (dotv b x) with h | h
    · simp [h]
    · simp [h, C]
      ring
  obtain ⟨fa, ζ', huf⟩ := s0_shift hu
  have hkC (x e : Vec) (he0 : e 0 = 0) (he3 : e 3 = 0) :
      eval k (x + e) = eval k x +
        (dotv fa.slope e + ζ' * (e 1 * x 3 + e 4 * x 0) + C x * dotv b e) := by
    simp only [k, eval_add', eval_smul', ht, one_mul, huf x e he0 he3, hc, dotv_add_right,
      hC x (x + e) (sameLow_add x e he0 he3)]
    ring
  apply done
  apply k_fibers_of_slopes fa.slope b ζ' C hkC hC hF hR hneq hp hq
  right
  refine ⟨i, hi, hbi, fun x hx hki => ?_⟩
  let e := unitVec i
  have he0 : e 0 = 0 := by rcases hi with rfl | rfl <;> rfl
  have he3 : e 3 = 0 := by rcases hi with rfl | rfl <;> rfl
  have he1 : e 1 = 0 := by rcases hi with rfl | rfl <;> rfl
  have he4 : e 4 = 0 := by rcases hi with rfl | rfl <;> rfl
  obtain ⟨fr, ζr, hvr⟩ := s0_shift hv
  let D := e 2 * x 3 + e 5 * x 0 + dotv fr.slope e + σ * (C x * dotv b e)
  have hRshift (y : Vec) (hy : SameLow y x) : eval R (y + e) = eval R y + D := by
    simp only [R, eval_add', eval_smul', z2_shift y e he0 he3, hvr y e he0 he3,
      hc, dotv_add_right, hC y (y + e) (sameLow_add y e he0 he3), hC x y hy,
      he1, he4, hy.1, hy.2, zero_mul, add_zero, mul_zero, D]
    ring
  have hprod (y : Vec) (hy : SameLow y x) : eval R y = eval k y * D := by
    have h := fixed_scalar (hF y) (hF (y + e)) (hki y hy)
    rw [hRshift y hy, add_cancel_f2] at h
    exact h
  let e1 := unitVec 1
  let e4 := unitVec 4
  have h1 : SameLow (x + e1) x := sameLow_add _ _ rfl rfl
  have h4 : SameLow (x + e4) x := sameLow_add _ _ rfl rfl
  have h41 : SameLow (x + e4 + e1) x := sameLow_trans (sameLow_add _ _ rfl rfl) h4
  have hdiff := target_second_diff d σ l b hv x e1 e4 rfl rfl rfl rfl
  change eval R (x + e4 + e1) + eval R (x + e4) +
      (eval R (x + e1) + eval R x) = _ at hdiff
  rw [hprod _ h41, hprod _ h4, hprod _ h1, hprod _ (sameLow_refl x),
    ← add_mul, ← add_mul, ← add_mul, hkC (x + e4) e1 rfl rfl, hkC x e1 rfl rfl,
    h4.1, h4.2, hC x _ h4, hrel e1 e4 rfl rfl rfl rfl] at hdiff
  simp only [hx, add_zero, one_mul, mul_zero] at hdiff
  have hkdiff : (eval k (x + e4) +
        (dotv fa.slope e1 + ζ' * (e1 1 * x 3 + e1 4 * x 0) + C x * dotv b e1)) +
      eval k (x + e4) +
      (eval k x + (dotv fa.slope e1 + ζ' * (e1 1 * x 3 + e1 4 * x 0) + C x * dotv b e1) +
        eval k x) = 0 := by
    rw [add_cancel_f2, add_cancel_f2, CharTwo.add_self_eq_zero]
  rw [hkdiff, zero_mul] at hdiff
  exact zero_ne_one hdiff

private theorem plus_mem {c u : A6} (hu : u ∈ V4 S0) (t : F₂) :
    u + t • c ∈ PlusZ1 c := mem_extend.mpr ⟨u, hu, t, rfl⟩

private theorem target_coset (c : A6) {v : A6} (hv : v ∈ V4 S0) (σ : F₂) :
    z2 + (v + σ • c) + z2 ∈ PlusZ1 c := by
  rw [add_comm z2, add_cancel_right]
  exact plus_mem hv σ

private theorem gateDelta_kill (d : F₂) (l b e : Vec) (hl : dotv l e = 0) (hb : dotv b e = 0) :
    gateDelta d l b e = 0 := by simp [gateDelta, hl, hb]

private theorem two_low_fibers (s t a : F₂) (hn : s ≠ 0 ∨ t ≠ 0) :
    ∃ p q : Vec, ¬ SameLow p q ∧
      a + s * p 3 + t * p 0 = 1 ∧ a + s * q 3 + t * q 0 = 1 := by
  rcases f2_eq_zero_or_one s with h0 | h1
  · have ht : t = 1 := (f2_eq_zero_or_one t).resolve_left
      (fun h => hn.elim (fun h' => h' h0) (fun h' => h' h))
    refine ⟨lowPoint (1 + a) 0, lowPoint (1 + a) 1, ?_, ?_, ?_⟩
    · intro h
      exact zero_ne_one h.2
    · simpa [lowPoint, h0, ht, add_assoc] using add_cancel_f2 a 1
    · simpa [lowPoint, h0, ht, add_assoc] using add_cancel_f2 a 1
  · refine ⟨lowPoint 0 (1 + a), lowPoint 1 (1 + a + t), ?_, ?_, ?_⟩
    · intro h
      exact zero_ne_one h.1
    · simpa [lowPoint, h1, add_assoc] using add_cancel_f2 a 1
    · rw [h1]
      change a + 1 * (1 + a + t) + t * 1 = 1
      rw [one_mul, mul_one]
      calc
        _ = (a + 1 + a) + (t + t) := by ac_rfl
        _ = 1 := by rw [add_cancel_f2, CharTwo.add_self_eq_zero, add_zero]

private theorem ext_kill_of_det {l b : Vec} (hd : l 2 * b 5 + l 5 * b 2 = 0) :
    ∃ s t : F₂, (s ≠ 0 ∨ t ≠ 0) ∧ dotv l (extDir s t) = 0 ∧ dotv b (extDir s t) = 0 := by
  rcases f2_eq_zero_or_one (b 2) with h0 | h1
  · rcases f2_eq_zero_or_one (b 5) with h5 | h5
    · rcases f2_eq_zero_or_one (l 2) with hl | hl
      · exact ⟨1, 0, Or.inl one_ne_zero, by simp [dotv_extDir, hl], by simp [dotv_extDir, h0]⟩
      · exact ⟨l 5, 1, Or.inr one_ne_zero,
          by simp [dotv_extDir, hl, CharTwo.add_self_eq_zero], by simp [dotv_extDir, h0, h5]⟩
    · exact ⟨1, 0, Or.inl one_ne_zero, by simpa [dotv_extDir, h0, h5] using hd,
        by simp [dotv_extDir, h0]⟩
  · exact ⟨b 5, 1, Or.inr one_ne_zero, by simpa [dotv_extDir, h1] using hd,
      by simp [dotv_extDir, h1, CharTwo.add_self_eq_zero]⟩

private theorem rigid_of_kill_dir {d τ σ : F₂} {l b : Vec} {u v : A6}
    (hu : u ∈ V4 S0) (hv : v ∈ V4 S0) (hb : OffLowSpan b)
    (hn : ¬ CoreHi (ExtGate d l b))
    (hfix : (u + τ • ExtGate d l b) * (z2 + (v + σ • ExtGate d l b)) =
      z2 + (v + σ • ExtGate d l b)) {s t : F₂}
    (he : s ≠ 0 ∨ t ≠ 0)
    (hk : τ = 0 ∨ dotv l (extDir s t) = 0 ∧ dotv b (extDir s t) = 0)
    (hR : σ = 0 ∨ dotv l (extDir s t) = 0 ∧ dotv b (extDir s t) = 0) :
    ModLow (u + τ • ExtGate d l b) 1 := by
  let e := extDir s t
  let c := ExtGate d l b
  let k := u + τ • c
  let R := z2 + (v + σ • c)
  obtain ⟨a, ζ, ha⟩ := source_shift d l b hu τ
  obtain ⟨v', hv'⟩ := target_ext_shift d l b hv σ
  let D := extDelta d l b e σ (dotv v' e)
  have hK (x : Vec) : eval k (x + e) = eval k x + dotv a e := by
    have h := ha x e rfl rfl
    have hz : τ * eval (gateDelta d l b e) x = 0 := by
      rcases hk with h | ⟨h, h'⟩
      · rw [h, zero_mul]
      · rw [gateDelta_kill d l b e h h']; simp
    have he1 : e 1 = 0 := rfl
    have he4 : e 4 = 0 := rfl
    simpa only [he1, he4, zero_mul, add_zero, mul_zero, hz] using h
  have hR' (x : Vec) : eval R (x + e) = eval R x + eval D x := hv' x s t
  have hγ := fixed_shift_zero hb (plus_mem hu τ) (target_coset c hv σ)
    hfix (extDelta_mem d l b e σ (dotv v' e)) hK hR'
  have hD (x : Vec) : eval D x = dotv v' e + s * x 3 + t * x 0 := by
    rw [extDelta_eval]
    have hz : σ * eval (gateDelta d l b e) x = 0 := by
      rcases hR with h | ⟨h, h'⟩
      · rw [h, zero_mul]
      · rw [gateDelta_kill d l b e h h']; simp
    rw [hz, add_zero]
    rfl
  have hF (x : Vec) : eval k x * eval R x = eval R x := by rw [← eval_mul']; exact congrArg (fun v : A6 => eval v x) hfix
  have hAt (x : Vec) (hx : eval D x = 1) : eval k x = 1 := by
    have h' := hF (x + e)
    rw [hK, hγ, add_zero] at h'
    have h := fixed_constant_shift (hF x) h'
    rw [hR', add_cancel_f2, hx, mul_one] at h
    exact (f2_eq_of_add_eq_zero h).symm
  obtain ⟨p, q, hpq, hp, hq⟩ := two_low_fibers s t (dotv v' e) he
  apply fiber_finish hu hv hb hn hpq _ _ hfix
  · intro x hx
    apply hAt
    rwa [hD, hx.1, hx.2]
  · intro x hx
    apply hAt
    rwa [hD, hx.1, hx.2]

private theorem external_mixed_scalar (k r a b e f : F₂)
    (h00 : (1 + k) * r = 0)
    (h10 : (1 + (k + a)) * (r + e) = 0)
    (h01 : (1 + (k + b)) * (r + f) = 0)
    (h11 : (1 + (k + b + (a + 1))) * (r + f + e) = 0) :
    r = e + f + a * f + b * e := by
  have four_f2 : (4 : F₂) = 0 := rfl
  linear_combination (norm := (ring_nf; simp [four_f2, two_f2])) h00 + h10 + h01 + h11

private theorem independent_generator_factor {d : F₂} {l b : Vec} {u v : A6}
    (hu : u ∈ V4 S0) (hv : v ∈ V4 S0)
    (hd : l 2 * b 5 + l 5 * b 2 = 1)
    (hfix : (u + ExtGate d l b) * (z2 + v) = z2 + v) : False := by
  let e := extDir 1 0
  let f := extDir 0 1
  let k := u + ExtGate d l b
  let R := z2 + v
  obtain ⟨a, ζ, ha⟩ := source_shift d l b hu 1
  obtain ⟨v', hv'⟩ := target_ext_shift d l b hv 0
  let A := dotv a e • (1 : A6) + gateDelta d l b e
  let B := dotv a f • (1 : A6) + gateDelta d l b f
  let E := extDelta d l b e 0 (dotv v' e)
  let F := extDelta d l b f 0 (dotv v' f)
  have hS (g : Vec) : dotv a g • (1 : A6) + gateDelta d l b g ∈ V4 S0 :=
    v4q0_le_s0 ((V4 Q0).add_mem
      (affine_le_V4 _ ((affine 6).smul_mem _ (one_mem_affine 6))) (gateDelta_mem d l b g))
  have hE := v4q0_le_s0 (extDelta_mem d l b e 0 (dotv v' e))
  have hF := v4q0_le_s0 (extDelta_mem d l b f 0 (dotv v' f))
  have hAe (x : Vec) : eval k (x + e) = eval k x + eval A x := by
    simpa only [A, k, eval_add', eval_smul', eval_one', one_smul, one_mul, mul_one,
      show e 1 = 0 from rfl, show e 4 = 0 from rfl, zero_mul, add_zero, mul_zero] using ha x e rfl rfl
  have hBf (x : Vec) : eval k (x + f) = eval k x + eval B x := by
    simpa only [B, k, eval_add', eval_smul', eval_one', one_smul, one_mul, mul_one,
      show f 1 = 0 from rfl, show f 4 = 0 from rfl, zero_mul, add_zero, mul_zero] using ha x f rfl rfl
  have hA' (x : Vec) : eval A (x + f) = eval A x + 1 := by
    simp only [A, eval_add', eval_smul', eval_one',
      gateDelta_shift d l b x e f rfl rfl, add_assoc]
    have h : dotv b e * dotv l f + dotv l e * dotv b f = 1 := by
      simpa [e, f, dotv_extDir, mul_comm (b 2), add_comm] using hd
    rw [h]
  have hRe (x : Vec) : eval R (x + e) = eval R x + eval E x := by
    simpa only [zero_smul, add_zero] using hv' x 1 0
  have hRf (x : Vec) : eval R (x + f) = eval R x + eval F x := by
    simpa only [zero_smul, add_zero] using hv' x 0 1
  have hE' (x : Vec) : eval E (x + f) = eval E x := by
    simp only [E, extDelta_eval, zero_mul, add_zero, Pi.add_apply,
      show f 0 = 0 from rfl, show f 3 = 0 from rfl]
  have hann (x : Vec) : (1 + eval k x) * eval R x = 0 := by
    have hh := congrArg (fun p : A6 => eval p x) hfix
    change eval (k * R) x = _ at hh
    rw [eval_mul'] at hh
    rw [add_mul, one_mul, hh, CharTwo.add_self_eq_zero]
  have hEq : R = E + F + A * F + B * E := anf_ext_eval fun x => by
    have h10 := hann (x + e)
    have h01 := hann (x + f)
    have h11 := hann (x + f + e)
    rw [hAe, hRe] at h10
    rw [hBf, hRf] at h01
    rw [hAe, hBf, hA', hRe, hRf, hE'] at h11
    simp only [eval_add', eval_mul']
    exact external_mixed_scalar _ _ _ _ _ _ (hann x) h10 h01 h11
  have hdeg := ((hE.1.add hF.1).mono (by omega : 2 ≤ 3)).add
    ((degree_s0_mul (hS e) hF).add (degree_s0_mul (hS f) hE))
  have hdeg' : DegreeLE 3 R := by rw [hEq]; simpa only [add_assoc] using hdeg
  have hZ : z2 = R + v := (add_cancel_right z2 v).symm
  have hz : DegreeLE 3 z2 := hZ ▸ hdeg'.add (hv.1.mono (by omega))
  have hf := hz carryMonomial (by rw [carryMonomial_card]; omega)
  rw [coeff_lowMul3_two_carry] at hf
  exact one_ne_zero hf

private theorem independent_base_factor {d : F₂} {l b : Vec} {u v : A6}
    (hu : u ∈ V4 S0) (hv : v ∈ V4 S0) (hb : OffLowSpan b)
    (hd : l 2 * b 5 + l 5 * b 2 = 1)
    (hfix : u * (z2 + (v + ExtGate d l b)) = z2 + (v + ExtGate d l b)) :
    ModLow u 1 := by
  let c := ExtGate d l b
  let R := z2 + (v + c)
  have hk : u ∈ PlusZ1 c := s0_le_plus _ hu
  have hR : R + z2 ∈ PlusZ1 c := by simpa only [one_smul] using target_coset c hv 1
  obtain ⟨a, ζ, ha⟩ := s0_shift hu
  obtain ⟨b', hB⟩ := target_ext_shift d l b hv 1
  have hshift (s t : F₂) (x : Vec) : eval u (x + extDir s t) = eval u x := by
    let e := extDir s t
    let D := extDelta d l b e 1 (dotv b' e)
    have h' (x : Vec) : eval u (x + e) = eval u x + dotv a.slope e := by
      simpa only [show e 1 = 0 from rfl, show e 4 = 0 from rfl,
        zero_mul, add_zero, mul_zero] using ha x e rfl rfl
    have hD (x : Vec) : eval R (x + e) = eval R x + eval D x := by
      simpa only [one_smul] using hB x s t
    have hg := fixed_shift_zero hb hk hR hfix (extDelta_mem d l b e 1 (dotv b' e)) h' hD
    rw [h', hg, add_zero]
  have hann (x : Vec) : (1 + eval u x) * eval R x = 0 := by
    have hf := congrArg (fun p : A6 => eval p x) hfix
    change eval (u * R) x = eval R x at hf
    rw [eval_mul'] at hf
    rw [add_mul, one_mul, hf, CharTwo.add_self_eq_zero]
  apply modLow_iff.mpr
  intro x _
  let e := extDir 1 0
  let f := extDir 0 1
  have hm := target_second_diff d 1 l b hv x e f rfl rfl rfl rfl
  have hd' : dotv b e * dotv l f + dotv l e * dotv b f = 1 := by
    simpa [e, f, dotv_extDir, mul_comm (b 2), add_comm] using hd
  simp only [one_smul, show e 1 = 0 from rfl, show e 4 = 0 from rfl,
    zero_mul, zero_add, mul_zero, hd', one_mul] at hm
  change eval R (x + f + e) + eval R (x + f) + (eval R (x + e) + eval R x) = 1 at hm
  have h1 := hann (x + f + e)
  have h2 := hann (x + f)
  have h3 := hann (x + e)
  rw [hshift 1 0 (x + f), hshift 0 1 x] at h1
  rw [hshift 0 1 x] at h2
  rw [hshift 1 0 x] at h3
  have hz := congrArg (fun t : F₂ => (1 + eval u x) * t) hm
  simp only [mul_add, h1, h2, h3, hann, add_zero, mul_one] at hz
  rw [eval_one']
  exact (f2_eq_of_add_eq_zero hz.symm).symm

/-- Last-factor rigidity for the common quadratic and cubic first-gate spaces. -/
theorem lastFactorLowIdeal : LastFactorLowIdeal := by
  intro d l b hb hn k R hk hR hfix
  obtain ⟨u, hu, τ, rfl⟩ := mem_extend.mp hk
  obtain ⟨v, hv, σ, hRv⟩ := mem_extend.mp hR
  have hRe : R = z2 + (v + σ • ExtGate d l b) := by
    rw [← hRv, add_comm z2, add_cancel_right]
  rw [hRe] at hfix
  rcases f2_eq_zero_or_one (l 2 * b 5 + l 5 * b 2) with hd | hd
  · obtain ⟨s, t, he, hl, hb'⟩ := ext_kill_of_det hd
    exact rigid_of_kill_dir hu hv hb hn hfix he (Or.inr ⟨hl, hb'⟩) (Or.inr ⟨hl, hb'⟩)
  rcases f2_eq_zero_or_one τ with rfl | rfl
  · rcases f2_eq_zero_or_one σ with rfl | rfl
    · exact rigid_of_kill_dir hu hv hb hn hfix (s := 1) (t := 0) (Or.inl one_ne_zero)
        (Or.inl rfl) (Or.inl rfl)
    · simp only [zero_smul, one_smul, add_zero] at hfix ⊢
      exact independent_base_factor hu hv hb hd hfix
  let c := ExtGate d l b
  let k := u + c
  let R' := z2 + (v + σ • c)
  have hfix' : k * R' = R' := by simpa only [one_smul] using hfix
  have hR' : R' + σ • k = z2 + (v + σ • u) := by
    calc
      _ = (z2 + (v + σ • u)) + (σ • c + σ • c) := by
        simp only [R', k, smul_add]
        ac_rfl
      _ = _ := by rw [anf_add_self, add_zero]
  have hnorm : k * (z2 + (v + σ • u)) = z2 + (v + σ • u) := by
    rw [← hR', mul_add, mul_smul_comm, anf_mul_self, hfix']
  exact (independent_generator_factor hu ((V4 S0).add_mem hv ((V4 S0).smul_mem σ hu)) hd hnorm).elim

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
