import LowHalfMul3.LemmaThree

/-!
# Lemma 11 of `lambda4_proof.tex` (types of rank-2 forms)

For a linear form `x` write `π(x) = (x(e_{a₂}), x(e_{b₂})) = (x 2, x 5)`.
Every `l ∧ r` can be rewritten, without changing the form, as `l' ∧ r'` in one
of three normal forms:

* `NFzero`: `π(l') = π(r') = 0` — the cross part vanishes;
* `NFv` (type `v`): `π(r') = 0`, i.e. `r' ∈ U`, and `π(l') = v ≠ 0`;
* `NFfull`: `π(l') = (1, 0)` and `π(r') = (0, 1)`, i.e.
  `l' ∧ r' = (a₂ + x) ∧ (b₂ + y)` with `x, y ∈ U`.

This is the paper's Lemma 11 with the zero-cross-part case added (the paper
assumes `Φ(R) ≠ 0`). The rewriting is a change of basis of `⟨l, r⟩`:
`(a l + b r) ∧ (c l + d r) = (a d + b c) (l ∧ r)` (`wedge_lincomb`), and a
suitable invertible `(a b; c d)` exists by a finite check on the four bits
`π(l), π(r)` (`types_finite`, `decide`, 16 × 16 cases).

The cross-part formulas of the paper are `rows_v` (`Φ(R) = v ⊗ r`: rows 2 and 5
of `l ∧ r` are `l 2 • r` and `l 5 • r`) and `rows_full` (rows 2 and 5 are `r`
and `l`; the paper's `Φ(R) = (y, x, 1)`).
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-! ## The three normal forms -/

/-- Cross part zero: `π(l) = π(r) = 0`. -/
def NFzero (l r : Fin 6 → F₂) : Prop := l 2 = 0 ∧ l 5 = 0 ∧ r 2 = 0 ∧ r 5 = 0

/-- Type `v`: `r ∈ U` and `π(l) = v ≠ 0`. -/
def NFv (l r : Fin 6 → F₂) : Prop := r 2 = 0 ∧ r 5 = 0 ∧ ¬ (l 2 = 0 ∧ l 5 = 0)

/-- Full type: `π(l) = (1, 0)`, `π(r) = (0, 1)`. -/
def NFfull (l r : Fin 6 → F₂) : Prop := l 2 = 1 ∧ l 5 = 0 ∧ r 2 = 0 ∧ r 5 = 1

/-! ## Change of basis -/

/-- `(a l + b r) ∧ (c l + d r) = (a d + b c) (l ∧ r)` in characteristic two. -/
theorem wedge_lincomb (a b c d : F₂) (l r : Fin 6 → F₂) :
    wedge (a • l + b • r) (c • l + d • r) = (a * d + b * c) • wedge l r := by
  funext i j
  simp only [wedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  generalize l i = x1
  generalize l j = x2
  generalize r i = y1
  generalize r j = y2
  revert a b c d x1 x2 y1 y2
  decide

/-- The finite core of Lemma 11: for any `π(l), π(r)` there is an invertible
change of basis reaching one of the three normal forms. -/
theorem types_finite : ∀ p2 p5 q2 q5 : F₂, ∃ a b c d : F₂, a * d + b * c = 1 ∧
    ((a * p2 + b * q2 = 0 ∧ a * p5 + b * q5 = 0 ∧ c * p2 + d * q2 = 0 ∧ c * p5 + d * q5 = 0) ∨
     (c * p2 + d * q2 = 0 ∧ c * p5 + d * q5 = 0 ∧ ¬ (a * p2 + b * q2 = 0 ∧ a * p5 + b * q5 = 0)) ∨
     (a * p2 + b * q2 = 1 ∧ a * p5 + b * q5 = 0 ∧ c * p2 + d * q2 = 0 ∧ c * p5 + d * q5 = 1)) := by
  decide

/-- **Lemma 11 (types).** Every `l ∧ r` equals some `l' ∧ r'` in normal form. -/
theorem types (l r : Fin 6 → F₂) :
    ∃ l' r' : Fin 6 → F₂, wedge l' r' = wedge l r ∧
      (NFzero l' r' ∨ NFv l' r' ∨ NFfull l' r') := by
  obtain ⟨a, b, c, d, hdet, hnf⟩ := types_finite (l 2) (l 5) (r 2) (r 5)
  refine ⟨a • l + b • r, c • l + d • r, by rw [wedge_lincomb, hdet, one_smul], ?_⟩
  simp only [NFzero, NFv, NFfull, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact hnf

/-! ## Cross parts in normal form -/

theorem phi_fst (ω : TwoForm6) (t : Fin 6) : (Phi ω).1 t = ω 2 t := iota_dirA2_apply ω t

theorem phi_snd (ω : TwoForm6) (t : Fin 6) : (Phi ω).2 t = ω 5 t := iota_dirB2_apply ω t

theorem phi_eq_zero_of_rows {ω : TwoForm6} (h : ∀ t, ω 2 t = 0 ∧ ω 5 t = 0) : Phi ω = 0 :=
  Prod.ext (funext fun t => by rw [phi_fst]; exact (h t).1)
    (funext fun t => by rw [phi_snd]; exact (h t).2)

/-- Type `v`: `Φ(l ∧ r) = v ⊗ r`, i.e. rows 2 and 5 are `l 2 • r` and `l 5 • r`. -/
theorem rows_v {l r : Fin 6 → F₂} (h : NFv l r) (t : Fin 6) :
    wedge l r 2 t = l 2 * r t ∧ wedge l r 5 t = l 5 * r t := by
  constructor <;> simp [wedge, h.1, h.2.1]

/-- Full type: rows 2 and 5 of `l ∧ r` are `r` and `l` (the paper's `(y, x, 1)`). -/
theorem rows_full {l r : Fin 6 → F₂} (h : NFfull l r) (t : Fin 6) :
    wedge l r 2 t = r t ∧ wedge l r 5 t = l t := by
  constructor <;> simp [wedge, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem phi_of_NFzero {l r : Fin 6 → F₂} (h : NFzero l r) : Phi (wedge l r) = 0 :=
  phi_eq_zero_of_rows fun t => by constructor <;> simp [wedge, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- The `a₂ ∧ b₂` coefficient `γ` vanishes for type `v`. -/
theorem gamma_v {l r : Fin 6 → F₂} (h : NFv l r) : wedge l r 2 5 = 0 := by
  simp [wedge, h.1, h.2.1]

/-- The `a₂ ∧ b₂` coefficient `γ` is `1` for the full type. -/
theorem gamma_full {l r : Fin 6 → F₂} (h : NFfull l r) : wedge l r 2 5 = 1 := by
  simp [wedge, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- For type `v`, the contraction along `e` is `l(e) r`: it vanishes exactly
when `e` kills `v`. The three paper directions. -/
theorem iota_dirA2_v {l r : Fin 6 → F₂} (h : NFv l r) (hx : l 2 = 0) :
    iota dirA2 (wedge l r) = 0 :=
  funext fun t => by rw [iota_dirA2_apply, (rows_v h t).1, hx, zero_mul]; rfl

theorem iota_dirB2_v {l r : Fin 6 → F₂} (h : NFv l r) (hy : l 5 = 0) :
    iota dirB2 (wedge l r) = 0 :=
  funext fun t => by rw [iota_dirB2_apply, (rows_v h t).2, hy, zero_mul]; rfl

theorem iota_dirA2B2_v {l r : Fin 6 → F₂} (h : NFv l r) (hxy : l 2 + l 5 = 0) :
    iota dirA2B2 (wedge l r) = 0 := by
  rw [iota_dirA2B2]
  funext t
  simp only [Pi.add_apply]
  rw [iota_dirA2_apply, iota_dirB2_apply, (rows_v h t).1, (rows_v h t).2, ← add_mul, hxy,
    zero_mul]
  rfl

end

end LowHalfMul3

end UnrestrictedBooleanMul
