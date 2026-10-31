import LowHalfMul3.Assembly

/-!
# Cross parts: Lemma 4 (kernel) and Lemma 6 of `lambda4_proof.tex`

Coordinates: `a₀ a₁ a₂ b₀ b₁ b₂ = x₀ … x₅`, so `a₂ = 2`, `b₂ = 5`, and
`U = ⟨a₀, a₁, b₀, b₁⟩ = ⟨x₀, x₁, x₃, x₄⟩`.

* `InLambdaU ω`: `ω ∈ Λ²(U)`, no monomial through `a₂` or `b₂`.
* `Phi ω = (ι_{a₂} ω, ι_{b₂} ω)`. The paper's cross part `(α, β, γ)` is read off
  from these two contractions (`γ = ω(a₂, b₂)` is a coordinate of each), so
  `Phi` has the same kernel and the same fibres on symmetric forms.
* `wedge l r` is `l ∧ r`; every rank-2 form is one.

Proved here: Lemma 4's kernel statement `ker Φ = Λ²(U)` on symmetric forms
(the dimension count `dim Φ(Q) = 4 - d_U` is not formalized), and Lemma 6:
no `l ∧ r` has the cross part of `q₂`. Lemma 6 is a finite check over all
`64 × 64` pairs `(l, r)`, by `decide`, after `π₂(z₂)` is computed explicitly.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- `ω ∈ Λ²(U)`: no monomial through `a₂ = x₂` or `b₂ = x₅`. -/
def InLambdaU (ω : TwoForm6) : Prop :=
  ∀ i j : Fin 6, (i = 2 ∨ i = 5 ∨ j = 2 ∨ j = 5) → ω i j = 0

/-- Symmetric 2-forms (alternating ones, in characteristic two, once the
diagonal vanishes). -/
def IsSymm (ω : TwoForm6) : Prop := ∀ i j, ω i j = ω j i

/-- The cross part, as the pair of contractions `(ι_{a₂} ω, ι_{b₂} ω)`. -/
def Phi : TwoForm6 →ₗ[F₂] (Fin 6 → F₂) × (Fin 6 → F₂) :=
  LinearMap.prod (iota dirA2) (iota dirB2)

theorem iota_dirA2_apply (ω : TwoForm6) (j : Fin 6) : iota dirA2 ω j = ω 2 j := by
  simp [iota_apply, dirA2, Fin.sum_univ_succ]

theorem iota_dirB2_apply (ω : TwoForm6) (j : Fin 6) : iota dirB2 ω j = ω 5 j := by
  simp [iota_apply, dirB2, Fin.sum_univ_succ]

theorem pi2_symm (p : ANF 6) : IsSymm (pi2 p) := by
  intro i j
  rw [pi2_apply, pi2_apply]
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : j ≠ i := fun h => hij h.symm
    simp only [hij, hji, ↓reduceIte, Finset.pair_comm]

/-- **Lemma 4 (kernel).** On symmetric forms, `Φ ω = 0` iff `ω ∈ Λ²(U)`. -/
theorem phi_eq_zero_iff {ω : TwoForm6} (hω : IsSymm ω) : Phi ω = 0 ↔ InLambdaU ω := by
  constructor
  · intro h i j hij
    have hA : ∀ k, ω 2 k = 0 := fun k => by
      have := congrFun (congrArg Prod.fst h) k
      simpa [Phi, iota_dirA2_apply] using this
    have hB : ∀ k, ω 5 k = 0 := fun k => by
      have := congrFun (congrArg Prod.snd h) k
      simpa [Phi, iota_dirB2_apply] using this
    rcases hij with rfl | rfl | rfl | rfl
    · exact hA j
    · exact hB j
    · rw [hω]; exact hA i
    · rw [hω]; exact hB i
  · intro h
    ext k
    · simp [Phi, iota_dirA2_apply, h 2 k (Or.inl rfl)]
    · simp [Phi, iota_dirB2_apply, h 5 k (Or.inr (Or.inl rfl))]

/-- `l ∧ r` as a symmetric zero-diagonal matrix (characteristic two). -/
def wedge (l r : Fin 6 → F₂) : TwoForm6 := fun i j => l i * r j + l j * r i

/-- `π₂(q₂) = π₂(z₂)`, `q₂ = a₀b₂ + a₁b₁ + a₂b₀`, as an explicit matrix. -/
def q2Form : TwoForm6 :=
  ![![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0]]

theorem pi2_lowMul3_two : pi2 (lowMul3 2) = q2Form := by
  funext i j
  rw [pi2_apply]
  fin_cases i <;> fin_cases j <;>
    simp [lowMul3, Mul, mulCoefficient, aVar, bVar, X, Fin.sum_univ_succ,
      monomial_mul, q2Form] <;> decide

/-- The cross part of `q₂`: `ι_{a₂} q₂ = b₀`, `ι_{b₂} q₂ = a₀`, i.e.
`Φ(q₂) = (b₀, a₀, 0)` in the paper's notation. -/
theorem phi_q2 : Phi q2Form = (![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]) := by
  ext k <;> fin_cases k <;> simp [Phi, iota_dirA2_apply, iota_dirB2_apply, q2Form]

set_option maxRecDepth 100000 in
theorem lemma6_finite : ∀ l r : Fin 6 → F₂,
    (fun j => wedge l r 2 j, fun j => wedge l r 5 j) ≠
      ((![0, 0, 0, 1, 0, 0] : Fin 6 → F₂), (![1, 0, 0, 0, 0, 0] : Fin 6 → F₂)) := by
  unfold wedge
  decide

/-- **Lemma 6.** No form `l ∧ r` (in particular no rank-2 form) has the cross
part of `q₂`. -/
theorem lemma6 (l r : Fin 6 → F₂) : Phi (wedge l r) ≠ Phi (pi2 (lowMul3 2)) := by
  rw [pi2_lowMul3_two, phi_q2]
  have h := lemma6_finite l r
  intro heq
  apply h
  rw [← heq]
  ext k
  · simp [Phi, iota_dirA2_apply]
  · simp [Phi, iota_dirB2_apply]

end

end LowHalfMul3

end UnrestrictedBooleanMul
