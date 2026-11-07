module

public import LowHalfMul3.Product

@[expose] public section

/-!
# Wedge algebra, Pfaffians, and the instances of Lemma 3 used in Theorem 12

* Bilinearity and symmetry of `wedge` (characteristic two: `l ∧ l = 0`,
  `l ∧ r = r ∧ l`).
* `pf ω i j k m`, the 4×4 Pfaffian; every `l ∧ r` has all Pfaffians zero.
* **Lemma 3, the two instances needed:** if `l ∧ r + l' ∧ r' = Z` with
  `Z ∈ {Z₁, Z₁ + P₀}`, then `Φ(l ∧ r) = 0`, i.e. `l ∧ r ∈ Λ²(U)`. Finite check
  in Pfaffian form (all 15 Pfaffians of `Z + l ∧ r` vanish ⟹ `Φ(l ∧ r) = 0`),
  one `decide` over the 4096 pairs `(l, r)` per `Z`.
* `Z₁ + c₀ P₀` is never a wedge: its Pfaffian `Pf₀₁₃₄` is `1`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-! ## Wedge algebra -/

theorem wedge_apply (a b : Fin 6 → F₂) (i j : Fin 6) :
    wedge a b i j = a i * b j + a j * b i := rfl

theorem wedge_comm (a b : Fin 6 → F₂) : wedge a b = wedge b a := by
  funext i j
  simp only [wedge]
  ring

theorem wedge_self (a : Fin 6 → F₂) : wedge a a = 0 := by
  funext i j
  simp only [wedge, Pi.zero_apply]
  rw [mul_comm (a j)]
  exact CharTwo.add_self_eq_zero _

theorem wedge_add_left (a b c : Fin 6 → F₂) : wedge (a + b) c = wedge a c + wedge b c := by
  funext i j
  simp only [wedge, Pi.add_apply]
  ring

theorem wedge_add_right (a b c : Fin 6 → F₂) : wedge a (b + c) = wedge a b + wedge a c := by
  funext i j
  simp only [wedge, Pi.add_apply]
  ring

theorem wedge_smul_left (s : F₂) (a b : Fin 6 → F₂) : wedge (s • a) b = s • wedge a b := by
  funext i j
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

theorem wedge_smul_right (s : F₂) (a b : Fin 6 → F₂) : wedge a (s • b) = s • wedge a b := by
  funext i j
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

theorem wedge_zero_right (a : Fin 6 → F₂) : wedge a 0 = 0 := by
  funext i j
  simp [wedge]

theorem wedge_add_self_right (a b : Fin 6 → F₂) : wedge a (a + b) = wedge a b := by
  rw [wedge_add_right, wedge_self, zero_add]

theorem wedge_add_self_left (a b : Fin 6 → F₂) : wedge (a + b) b = wedge a b := by
  rw [wedge_add_left, wedge_self, add_zero]

theorem tf_add_self (ω : TwoForm6) : ω + ω = 0 := by
  funext i j
  exact CharTwo.add_self_eq_zero _

theorem vec_add_self (x : Fin 6 → F₂) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

/-! ## Pfaffians -/

/-- The Pfaffian of the principal 4×4 minor on `i, j, k, m`. -/
def pf (ω : TwoForm6) (i j k m : Fin 6) : F₂ :=
  ω i j * ω k m + ω i k * ω j m + ω i m * ω j k

theorem pf_wedge (a b : Fin 6 → F₂) (i j k m : Fin 6) : pf (wedge a b) i j k m = 0 := by
  simp only [pf, wedge]
  generalize a i = ai
  generalize a j = aj
  generalize a k = ak
  generalize a m = am
  generalize b i = bi
  generalize b j = bj
  generalize b k = bk
  generalize b m = bm
  revert ai aj ak am bi bj bk bm
  decide

/-- All fifteen principal 4×4 Pfaffians vanish (rank at most 2). -/
def AllPfZero (ω : TwoForm6) : Prop :=
      pf ω 0 1 2 3 = 0 ∧
      pf ω 0 1 2 4 = 0 ∧
      pf ω 0 1 2 5 = 0 ∧
      pf ω 0 1 3 4 = 0 ∧
      pf ω 0 1 3 5 = 0 ∧
      pf ω 0 1 4 5 = 0 ∧
      pf ω 0 2 3 4 = 0 ∧
      pf ω 0 2 3 5 = 0 ∧
      pf ω 0 2 4 5 = 0 ∧
      pf ω 0 3 4 5 = 0 ∧
      pf ω 1 2 3 4 = 0 ∧
      pf ω 1 2 3 5 = 0 ∧
      pf ω 1 2 4 5 = 0 ∧
      pf ω 1 3 4 5 = 0 ∧
      pf ω 2 3 4 5 = 0

theorem allPfZero_wedge (a b : Fin 6 → F₂) : AllPfZero (wedge a b) := by
  simp only [AllPfZero, pf_wedge, and_self]

/-! ## The two targets as literal matrices -/

/-- `Z₁` as a literal matrix (for `decide`). -/
def Z1lit : TwoForm6 := ![![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]]

/-- `Z₁ + P₀` as a literal matrix (for `decide`). -/
def Z1P0lit : TwoForm6 := ![![0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]]

theorem Z1form_eq_lit : Z1form = Z1lit := by
  funext i j
  revert i j
  unfold Z1form wedge unitVec Z1lit
  decide

theorem Z1form_add_P0form_eq_lit : Z1form + P0form = Z1P0lit := by
  funext i j
  revert i j
  unfold Z1form P0form wedge unitVec Z1P0lit
  decide

theorem Z_eq_lit_cases (c0 : F₂) :
    Z1form + c0 • P0form = Z1lit ∨ Z1form + c0 • P0form = Z1P0lit := by
  rcases f2_eq_zero_or_one c0 with rfl | rfl
  · left; rw [zero_smul, add_zero, Z1form_eq_lit]
  · right; rw [one_smul, Z1form_add_P0form_eq_lit]

/-! ## `Z₁ + c₀ P₀` is not a wedge -/

theorem wedge_ne_Z (l r : Fin 6 → F₂) (c0 : F₂) : wedge l r ≠ Z1form + c0 • P0form := by
  intro h
  have hpf := pf_wedge l r 0 1 3 4
  rw [h] at hpf
  rcases Z_eq_lit_cases c0 with hZ | hZ <;> rw [hZ] at hpf <;> revert hpf <;>
    unfold pf <;> decide

/-! ## Lemma 3, the two instances -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lemma3_finite_Z1 : ∀ l r : Fin 6 → F₂,
    AllPfZero (Z1lit + wedge l r) →
    ∀ j : Fin 6, wedge l r 2 j = 0 ∧ wedge l r 5 j = 0 := by
  unfold AllPfZero pf Z1lit wedge
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lemma3_finite_Z1P0 : ∀ l r : Fin 6 → F₂,
    AllPfZero (Z1P0lit + wedge l r) →
    ∀ j : Fin 6, wedge l r 2 j = 0 ∧ wedge l r 5 j = 0 := by
  unfold AllPfZero pf Z1P0lit wedge
  decide

/-- **Lemma 3 (instances).** Every splitting of `Z₁` or `Z₁ + P₀` into two
wedges lies in `Λ²(U)`: the cross part of each summand vanishes. -/
theorem lemma3 {l r l' r' : Fin 6 → F₂} {c0 : F₂}
    (h : wedge l r + wedge l' r' = Z1form + c0 • P0form) : Phi (wedge l r) = 0 := by
  have hZ : Z1form + c0 • P0form + wedge l r = wedge l' r' := by
    rw [← h, add_comm (wedge l r), add_assoc, tf_add_self, add_zero]
  have hpf : AllPfZero (Z1form + c0 • P0form + wedge l r) := by
    rw [hZ]; exact allPfZero_wedge l' r'
  have hfin : ∀ j : Fin 6, wedge l r 2 j = 0 ∧ wedge l r 5 j = 0 := by
    rcases Z_eq_lit_cases c0 with hc | hc <;> rw [hc] at hpf
    · exact lemma3_finite_Z1 l r hpf
    · exact lemma3_finite_Z1P0 l r hpf
  ext j
  · simp [Phi, iota_dirA2_apply, (hfin j).1]
  · simp [Phi, iota_dirB2_apply, (hfin j).2]

end

end LowHalfMul3

end UnrestrictedBooleanMul
