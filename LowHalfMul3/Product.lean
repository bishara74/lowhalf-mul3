module

public import LowHalfMul3.CrossPart

@[expose] public section

/-!
# The product-coefficient layer: `π₂(L R) = ℓ(L) ∧ ℓ(R)` for affine `L, R`

Everything here is semantic, i.e. phrased through evaluation:

* `pi2_eq_mobius`: for every ANF `p` and `i ≠ j`,
  `π₂ p i j = p(0) + p(eᵢ) + p(eⱼ) + p(eᵢ + eⱼ)` (Möbius inversion on the pair
  `{i, j}`). Reduced to a termwise identity on single monomials, checked by
  `decide` (64 subsets × 36 pairs).
* `lin L j := L(eⱼ) + L(0)` is the linear part, and `eval_affine`:
  `L(x) = L(0) + ⟨lin L, x⟩` for affine `L`.
* `pi2_mul_affine`: `π₂(L * R) = wedge (lin L) (lin R)` for affine `L, R`.

Consequences used later: `π₂(a₀ b₀) = P0form`, `π₂(z₁) = Z1form`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- The `i`-th unit vector of `F₂⁶`. -/
def unitVec (i : Fin 6) : Fin 6 → F₂ := fun k => if k = i then 1 else 0

/-- The dot product on `F₂⁶`. -/
def dotv (a b : Fin 6 → F₂) : F₂ := ∑ j, a j * b j

theorem dotv_unitVec (a : Fin 6 → F₂) (i : Fin 6) : dotv a (unitVec i) = a i := by
  simp [dotv, unitVec]

theorem dotv_add_left (a b x : Fin 6 → F₂) : dotv (a + b) x = dotv a x + dotv b x := by
  simp [dotv, add_mul, Finset.sum_add_distrib]

theorem dotv_add_right (a x y : Fin 6 → F₂) : dotv a (x + y) = dotv a x + dotv a y := by
  simp [dotv, mul_add, Finset.sum_add_distrib]

theorem dotv_smul_left (c : F₂) (a x : Fin 6 → F₂) : dotv (c • a) x = c * dotv a x := by
  simp [dotv, Finset.mul_sum, mul_assoc]

theorem dotv_zero_right (a : Fin 6 → F₂) : dotv a 0 = 0 := by simp [dotv]

/-- The linear part of a function, read off from its values. -/
def lin (p : ANF 6) : Fin 6 → F₂ := fun j => eval p (unitVec j) + eval p 0

theorem lin_add (p q : ANF 6) : lin (p + q) = lin p + lin q := by
  funext j
  simp only [lin, eval_add', Pi.add_apply]
  ring

theorem lin_smul (c : F₂) (p : ANF 6) : lin (c • p) = c • lin p := by
  funext j
  simp only [lin, eval_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- Affine functions are determined by their constant and linear parts. -/
theorem eval_affine {L : ANF 6} (hL : L ∈ affine 6) (x : Fin 6 → F₂) :
    eval L x = eval L 0 + dotv (lin L) x := by
  revert x
  refine Submodule.span_induction
    (p := fun L _ => ∀ x : Fin 6 → F₂, eval L x = eval L 0 + dotv (lin L) x) ?_ ?_ ?_ ?_ hL
  · intro q hq x
    rcases hq with hq | hq
    · have hq1 : q = 1 := by simpa only [Set.mem_singleton_iff] using hq
      subst hq1
      have hlin : lin (1 : ANF 6) = 0 := by
        funext j
        simp [lin, CharTwo.add_self_eq_zero]
      rw [hlin]
      simp [dotv]
    · obtain ⟨i, rfl⟩ := hq
      have hlin : lin (X i : ANF 6) = unitVec i := by
        funext j
        simp only [lin, eval_X, unitVec, Pi.zero_apply, add_zero]
        by_cases h : i = j
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [hlin, eval_X, eval_X]
      simp [dotv, unitVec]
  · intro x
    have hlin : lin (0 : ANF 6) = 0 := by funext j; simp [lin]
    rw [hlin]
    simp [dotv]
  · intro p q _ _ hp hq x
    rw [eval_add', hp x, hq x, eval_add', lin_add, dotv_add_left]
    ring
  · intro c p _ hp x
    rw [eval_smul', hp x, eval_smul', lin_smul, dotv_smul_left]
    ring

/-! ## Möbius inversion on a pair -/

set_option maxRecDepth 100000 in
theorem sel_eq_mobius_termwise : ∀ t : Finset (Fin 6), ∀ i j : Fin 6, i ≠ j →
    sel t i j = (∏ k ∈ t, (0 : Fin 6 → F₂) k) + (∏ k ∈ t, unitVec i k) +
      (∏ k ∈ t, unitVec j k) + ∏ k ∈ t, (unitVec i + unitVec j) k := by
  unfold sel unitVec
  decide

/-- **Möbius inversion on a pair.** For every ANF `p` and `i ≠ j`, the
coefficient of `xᵢ xⱼ` is `p(0) + p(eᵢ) + p(eⱼ) + p(eᵢ + eⱼ)`. -/
theorem pi2_eq_mobius (p : ANF 6) {i j : Fin 6} (hij : i ≠ j) :
    pi2 p i j = eval p 0 + eval p (unitVec i) + eval p (unitVec j) +
      eval p (unitVec i + unitVec j) := by
  rw [pi2_eq_sum, eval_eq_sum_support, eval_eq_sum_support, eval_eq_sum_support,
    eval_eq_sum_support, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sel_eq_mobius_termwise s.vars i j hij]
  ring

/-! ## Quadratic part of a product of affine functions -/

theorem f2_wedge_identity (c c' a b a' b' : F₂) :
    c * c' + (c + a) * (c' + a') + (c + b) * (c' + b') + (c + (a + b)) * (c' + (a' + b')) =
      a * b' + b * a' := by
  revert c c' a b a' b'
  decide

/-- **Product layer.** For affine `L, R`, `π₂(L R) = ℓ(L) ∧ ℓ(R)`. -/
theorem pi2_mul_affine {L R : ANF 6} (hL : L ∈ affine 6) (hR : R ∈ affine 6) :
    pi2 (L * R) = wedge (lin L) (lin R) := by
  funext i j
  by_cases hij : i = j
  · subst hij
    rw [pi2_apply]
    simp only [↓reduceIte, wedge]
    rw [mul_comm (lin L i) (lin R i)]
    exact (CharTwo.add_self_eq_zero _).symm
  · rw [pi2_eq_mobius _ hij]
    simp only [eval_mul']
    rw [eval_affine hL (unitVec i), eval_affine hL (unitVec j),
      eval_affine hL (unitVec i + unitVec j), eval_affine hR (unitVec i),
      eval_affine hR (unitVec j), eval_affine hR (unitVec i + unitVec j),
      dotv_add_right, dotv_add_right, dotv_unitVec, dotv_unitVec, dotv_unitVec,
      dotv_unitVec]
    simp only [wedge]
    exact f2_wedge_identity _ _ _ _ _ _

/-! ## The two quadratic targets -/

theorem lin_X (i : Fin 6) : lin (X i : ANF 6) = unitVec i := by
  funext j
  simp only [lin, eval_X, unitVec, Pi.zero_apply, add_zero]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `P₀ = a₀ ∧ b₀`. -/
def P0form : TwoForm6 := wedge (unitVec 0) (unitVec 3)

/-- `Z₁ = a₀ ∧ b₁ + a₁ ∧ b₀`. -/
def Z1form : TwoForm6 := wedge (unitVec 0) (unitVec 4) + wedge (unitVec 1) (unitVec 3)

theorem pi2_aVar_mul_bVar (i j : Fin 3) :
    pi2 (aVar 3 i * bVar 3 j) =
      wedge (unitVec ⟨i.val, by omega⟩) (unitVec ⟨3 + j.val, by omega⟩) := by
  rw [pi2_mul_affine (aVar_mem_affine 3 i) (bVar_mem_affine 3 j)]
  simp only [aVar, bVar, lin_X]

theorem pi2_a0b0 : pi2 (aVar 3 0 * bVar 3 0) = P0form := by
  rw [pi2_aVar_mul_bVar]
  rfl

theorem pi2_lowMul3_one : pi2 (lowMul3 1) = Z1form := by
  rw [z1_eq]
  show pi2 (aVar 3 0 * bVar 3 1 + aVar 3 1 * bVar 3 0) = Z1form
  rw [map_add, pi2_aVar_mul_bVar, pi2_aVar_mul_bVar]
  rfl

end

end LowHalfMul3

end UnrestrictedBooleanMul
