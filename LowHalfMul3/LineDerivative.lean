module

public import LowHalfMul3.Product

@[expose] public section

/-!
# Lemma 8′: the derivative lemma with a one-dimensional contraction

**Lemma 8′.** Let `e ∈ {a₂, b₂, a₂+b₂}` and `δ_e = ι_e(q₂) ∈ {b₀, a₀, a₀+b₀}`.
If `ι_e(Q) ⊆ span{ℓ}` for one linear form `ℓ ≠ δ_e`, then (★) has no solution.
The case `ℓ = 0` is Lemma 8.

This strengthening is not in `lambda4_proof.tex`; it replaces Proposition 7
(and with it Lemma 5 and the identity `π₄(fh) = f₂ ∧ h₂`) in the proof of
Theorem 12. See LEAN_LOG.md, phase 4.

Proof. For `p ∈ V₄(Q)` the bridge gives `D_e p = c_p + γ_p ℓ`. Replacing
`(f, h)` by `(h, f)` or `(f + h, h)` (which changes `f h + z₂` by `h ∈ V₄(Q)`)
we may assume `γ_f = 0`. The product rule gives, pointwise,
`c_f h + H f + c_f H + δ_e = K` with `H = c_h + γ_h ℓ`, `K = c_g + γ_g ℓ`.
If `c_f = 1`, `h = H (f + 1) + A` with `A` affine, so `f h = f A` has degree
`≤ 3`. If `c_f = 0`, `H f = K + δ_e`; a finite fact (`hfin`) forces `H ≡ 1`,
so `f` is affine and again `deg (f h) ≤ 3`. Both contradict the carry
`a₀a₁b₀b₁` of `z₂`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-! ## Linear forms as ANFs -/

/-- The linear form `x ↦ ⟨ℓ, x⟩` as an ANF. -/
def linANF (ℓ : Fin 6 → F₂) : ANF 6 := ∑ j, ℓ j • X j

theorem eval_linANF (ℓ x : Fin 6 → F₂) : eval (linANF ℓ) x = dotv ℓ x := by
  rw [linANF, eval_eq_evalHom, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ← eval_eq_evalHom, eval_X, smul_eq_mul]

theorem linANF_mem_affine (ℓ : Fin 6 → F₂) : linANF ℓ ∈ affine 6 :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (X_mem_affine j)

theorem dotv_comm (a b : Fin 6 → F₂) : dotv a b = dotv b a := by
  simp [dotv, mul_comm]

/-- An affine function `c + γ ⟨ℓ, x⟩ + ⟨d, x⟩`. -/
def affANF (c γ : F₂) (ℓ d : Fin 6 → F₂) : ANF 6 :=
  c • (1 : ANF 6) + γ • linANF ℓ + linANF d

theorem eval_affANF (c γ : F₂) (ℓ d x : Fin 6 → F₂) :
    eval (affANF c γ ℓ d) x = c + γ * dotv ℓ x + dotv d x := by
  simp [affANF, eval_linANF]

theorem affANF_mem_affine (c γ : F₂) (ℓ d : Fin 6 → F₂) : affANF c γ ℓ d ∈ affine 6 :=
  Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (one_mem_affine 6))
    (Submodule.smul_mem _ _ (linANF_mem_affine ℓ))) (linANF_mem_affine d)

/-! ## Derivative rules and the degree obstruction -/

theorem deriv_add (e : Fin 6 → F₂) (p q : ANF 6) (x : Fin 6 → F₂) :
    deriv e (eval (p + q)) x = deriv e (eval p) x + deriv e (eval q) x := by
  simp only [deriv, eval_add']
  ring

theorem deriv_mul (e : Fin 6 → F₂) (p q : ANF 6) (x : Fin 6 → F₂) :
    deriv e (eval (p * q)) x = deriv e (eval p) x * eval q x + eval p x * deriv e (eval q) x +
      deriv e (eval p) x * deriv e (eval q) x := by
  simp only [deriv, eval_mul']
  generalize eval p (shiftBy e x) = A
  generalize eval p x = B
  generalize eval q (shiftBy e x) = C
  generalize eval q x = D
  revert A B C D
  decide

/-- If `f h + z₂` has degree at most two, `f h` has degree four (the carry). -/
theorem not_degreeLE_three_of_star {f h : ANF 6} (hg : DegreeLE 2 (f * h + lowMul3 2)) :
    ¬ DegreeLE 3 (f * h) := by
  intro hdeg3
  have hsplit : f * h = (f * h + lowMul3 2) + lowMul3 2 := by
    rw [add_assoc, anf_add_self, add_zero]
  have hcoeff : (f * h).coeff carryMonomial = 1 := by
    rw [hsplit]
    have : ((f * h + lowMul3 2) + lowMul3 2).coeff carryMonomial =
        (f * h + lowMul3 2).coeff carryMonomial + (lowMul3 2).coeff carryMonomial := by simp
    rw [this, hg carryMonomial (by rw [carryMonomial_card]; omega),
      coeff_lowMul3_two_carry, zero_add]
  have : (f * h).coeff carryMonomial = 0 :=
    hdeg3 carryMonomial (by rw [carryMonomial_card]; omega)
  rw [hcoeff] at this
  exact one_ne_zero this

theorem f2_add_eq_iff (a b c : F₂) : a + b = c ↔ a = b + c := by
  revert a b c
  decide

/-! ## The core computation -/

/-- The core of Lemma 8′, after the normalisation `γ_f = 0`. -/
theorem line_core (e d ℓ : Fin 6 → F₂)
    (hd : ∀ x, deriv e (eval (lowMul3 2)) x = dotv d x)
    (hfin : ∀ ch γh cg γg : F₂,
      (∀ x, ch + γh * dotv ℓ x = 0 → cg + γg * dotv ℓ x + dotv d x = 0) →
      ∀ x, ch + γh * dotv ℓ x = 1)
    (f h : ANF 6) (hfdeg : DegreeLE 2 f) (hhdeg : DegreeLE 2 h)
    (hgdeg : DegreeLE 2 (f * h + lowMul3 2))
    (cf : F₂) (hcf : ∀ x, deriv e (eval f) x = cf)
    (ch γh : F₂) (hch : ∀ x, deriv e (eval h) x = ch + γh * dotv ℓ x)
    (cg γg : F₂) (hcg : ∀ x, deriv e (eval (f * h + lowMul3 2)) x = cg + γg * dotv ℓ x) :
    False := by
  have key : ∀ x, cg + γg * dotv ℓ x =
      cf * eval h x + eval f x * (ch + γh * dotv ℓ x) + cf * (ch + γh * dotv ℓ x) +
        dotv d x := by
    intro x
    rw [← hcg x, deriv_add, deriv_mul, hcf x, hch x, hd x]
  have hfh3 : DegreeLE 3 (f * affANF cg γg ℓ d) :=
    DegreeLE.mul hfdeg (degreeLE_one_of_mem_affine (affANF_mem_affine cg γg ℓ d))
  rcases f2_eq_zero_or_one cf with hc0 | hc1
  · -- `c_f = 0`: `H f = K + δ`, so `H ≡ 1` and `f` is affine.
    have hz : ∀ x, ch + γh * dotv ℓ x = 0 → cg + γg * dotv ℓ x + dotv d x = 0 := by
      intro x hx
      have hk := key x
      rw [hc0, hx] at hk
      revert hk
      generalize cg + γg * dotv ℓ x = K
      generalize dotv d x = D
      generalize eval h x = B'
      generalize eval f x = B
      revert K D B' B
      decide
    have hH := hfin ch γh cg γg hz
    have hfeq : f = affANF cg γg ℓ d := by
      apply eval_injective 6
      funext x
      show eval f x = eval (affANF cg γg ℓ d) x
      rw [eval_affANF]
      have hk := key x
      rw [hc0, hH x] at hk
      revert hk
      generalize cg + γg * dotv ℓ x = K
      generalize dotv d x = D
      generalize eval h x = B'
      generalize eval f x = B
      revert K D B' B
      decide
    apply not_degreeLE_three_of_star hgdeg
    rw [hfeq]
    have := DegreeLE.mul (degreeLE_one_of_mem_affine (affANF_mem_affine cg γg ℓ d)) hhdeg
    simpa using this
  · -- `c_f = 1`: `h = H (f + 1) + A`, so `f h = f A`.
    have hheq : h = affANF ch γh ℓ 0 * (f + 1) + affANF cg γg ℓ d := by
      apply eval_injective 6
      funext x
      show eval h x = eval (affANF ch γh ℓ 0 * (f + 1) + affANF cg γg ℓ d) x
      rw [eval_add', eval_mul', eval_add', eval_one', eval_affANF, eval_affANF]
      have hk := key x
      rw [hc1] at hk
      have hd0 : dotv (0 : Fin 6 → F₂) x = 0 := by simp [dotv]
      rw [hd0]
      revert hk
      generalize ch + γh * dotv ℓ x = H
      generalize cg + γg * dotv ℓ x = K
      generalize dotv d x = D
      generalize eval h x = B'
      generalize eval f x = B
      intro hk
      rw [add_zero]
      revert hk
      revert H K D B' B
      decide
    apply not_degreeLE_three_of_star hgdeg
    have hfh : f * h = f * affANF cg γg ℓ d := by
      rw [hheq]
      have : f * (affANF ch γh ℓ 0 * (f + 1) + affANF cg γg ℓ d) =
          affANF ch γh ℓ 0 * (f * f + f) + f * affANF cg γg ℓ d := by ring
      rw [this, anf_mul_self, anf_add_self, mul_zero, zero_add]
    rw [hfh]
    exact hfh3

/-! ## Lemma 8′ -/

/-- The three directions together with `δ_e = ι_e(q₂)`. -/
def PaperPair (e d : Fin 6 → F₂) : Prop :=
  (e = dirA2 ∧ d = unitVec 3) ∨ (e = dirB2 ∧ d = unitVec 0) ∨
    (e = dirA2B2 ∧ d = unitVec 0 + unitVec 3)

theorem PaperPair.isPaperDir {e d : Fin 6 → F₂} (h : PaperPair e d) : IsPaperDir e := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem PaperPair.deriv_z2 {e d : Fin 6 → F₂} (h : PaperPair e d) (x : Fin 6 → F₂) :
    deriv e (eval (lowMul3 2)) x = dotv d x := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [deriv_lowMul3_two_dirA2, dotv_comm, dotv_unitVec]
    simp [bVar]
  · rw [deriv_lowMul3_two_dirB2, dotv_comm, dotv_unitVec]
    simp [aVar]
  · rw [deriv_lowMul3_two_dirA2B2, dotv_comm, dotv_add_right, dotv_unitVec, dotv_unitVec]
    simp [aVar, bVar]

/-- A direction along which every contraction of `Q` is a multiple of one
linear form `ℓ ≠ δ_e`. -/
def GoodDir (Q : Submodule F₂ TwoForm6) : Prop :=
  ∃ e d ℓ : Fin 6 → F₂, PaperPair e d ∧ ℓ ≠ d ∧ ∀ ω ∈ Q, ∃ γ : F₂, iota e ω = γ • ℓ

/-! ## The finite fact behind `H ≡ 1` (one `decide` per direction) -/

set_option maxRecDepth 100000 in
theorem line_finite_b0 : ∀ ℓ : Fin 6 → F₂, ℓ ≠ (unitVec 3) → ∀ ch γh cg γg : F₂,
    (∀ x : Fin 6 → F₂, ch + γh * dotv ℓ x = 0 → cg + γg * dotv ℓ x + dotv (unitVec 3) x = 0) →
    ∀ x : Fin 6 → F₂, ch + γh * dotv ℓ x = 1 := by
  unfold dotv unitVec
  decide

set_option maxRecDepth 100000 in
theorem line_finite_a0 : ∀ ℓ : Fin 6 → F₂, ℓ ≠ (unitVec 0) → ∀ ch γh cg γg : F₂,
    (∀ x : Fin 6 → F₂, ch + γh * dotv ℓ x = 0 → cg + γg * dotv ℓ x + dotv (unitVec 0) x = 0) →
    ∀ x : Fin 6 → F₂, ch + γh * dotv ℓ x = 1 := by
  unfold dotv unitVec
  decide

set_option maxRecDepth 100000 in
theorem line_finite_a0b0 : ∀ ℓ : Fin 6 → F₂, ℓ ≠ (unitVec 0 + unitVec 3) → ∀ ch γh cg γg : F₂,
    (∀ x : Fin 6 → F₂, ch + γh * dotv ℓ x = 0 → cg + γg * dotv ℓ x + dotv (unitVec 0 + unitVec 3) x = 0) →
    ∀ x : Fin 6 → F₂, ch + γh * dotv ℓ x = 1 := by
  unfold dotv unitVec
  decide

theorem PaperPair.fin {e d : Fin 6 → F₂} (h : PaperPair e d) (ℓ : Fin 6 → F₂) (hℓ : ℓ ≠ d) :
    ∀ ch γh cg γg : F₂,
      (∀ x, ch + γh * dotv ℓ x = 0 → cg + γg * dotv ℓ x + dotv d x = 0) →
      ∀ x, ch + γh * dotv ℓ x = 1 := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact line_finite_b0 ℓ hℓ
  · exact line_finite_a0 ℓ hℓ
  · exact line_finite_a0b0 ℓ hℓ

/-- For `p ∈ V₄(Q)` and `ι_e(Q) ⊆ span{ℓ}`: `D_e p = D_e p (0) + γ ⟨ℓ, x⟩`. -/
theorem deriv_line_of_mem {e d ℓ : Fin 6 → F₂} (hp : PaperPair e d)
    {Q : Submodule F₂ TwoForm6} (hQ : ∀ ω ∈ Q, ∃ γ : F₂, iota e ω = γ • ℓ)
    {p : ANF 6} (hpQ : p ∈ V4 Q) :
    ∃ γ : F₂, ∀ x, deriv e (eval p) x = deriv e (eval p) 0 + γ * dotv ℓ x := by
  obtain ⟨γ, hγ⟩ := hQ _ hpQ.2
  refine ⟨γ, fun x => ?_⟩
  have hid := deriv_add_deriv_zero_eq hp.isPaperDir p hpQ.1 x
  rw [hγ] at hid
  have hs : ∑ j, (γ • ℓ) j * x j = γ * dotv ℓ x := by
    simp [dotv, Finset.mul_sum, mul_assoc]
  rw [hs] at hid
  exact (f2_add_eq_iff _ _ _).mp hid

/-- **Lemma 8′.** If some paper direction `e` has `ι_e(Q) ⊆ span{ℓ}` with
`ℓ ≠ δ_e`, then (★) has no solution. -/
theorem starFree_of_goodDir {Q : Submodule F₂ TwoForm6} (hQ : GoodDir Q)
    (f h : ANF 6) (hf : f ∈ V4 Q) (hh : h ∈ V4 Q)
    (hg : f * h + lowMul3 2 ∈ V4 Q) : False := by
  obtain ⟨e, d, ℓ, hp, hℓ, hQℓ⟩ := hQ
  have step : ∀ u w : ANF 6, u ∈ V4 Q → w ∈ V4 Q → u * w + lowMul3 2 ∈ V4 Q →
      (∀ x, deriv e (eval u) x = deriv e (eval u) 0) → False := by
    intro u w hu hw huw hconst
    obtain ⟨γw, hγw⟩ := deriv_line_of_mem hp hQℓ hw
    obtain ⟨γg, hγg⟩ := deriv_line_of_mem hp hQℓ huw
    exact line_core e d ℓ hp.deriv_z2 (hp.fin ℓ hℓ) u w hu.1 hw.1 huw.1
      _ hconst _ γw hγw _ γg hγg
  obtain ⟨γf, hγf⟩ := deriv_line_of_mem hp hQℓ hf
  obtain ⟨γh, hγh⟩ := deriv_line_of_mem hp hQℓ hh
  rcases f2_eq_zero_or_one γf with hf0 | hf1
  · exact step f h hf hh hg (fun x => by rw [hγf x, hf0, zero_mul, add_zero])
  · rcases f2_eq_zero_or_one γh with hh0 | hh1
    · refine step h f hh hf ?_ (fun x => by rw [hγh x, hh0, zero_mul, add_zero])
      rw [mul_comm]
      exact hg
    · refine step (f + h) h ((V4 Q).add_mem hf hh) hh ?_ ?_
      · have hrw : (f + h) * h + lowMul3 2 = (f * h + lowMul3 2) + h := by
          rw [add_mul, anf_mul_self]
          ring
        rw [hrw]
        exact (V4 Q).add_mem hg hh
      · intro x
        rw [deriv_add, deriv_add, hγf x, hγh x, hf1, hh1]
        generalize deriv e (eval f) 0 = A
        generalize deriv e (eval h) 0 = B
        generalize dotv ℓ x = T
        revert A B T
        decide

end

end LowHalfMul3

end UnrestrictedBooleanMul
