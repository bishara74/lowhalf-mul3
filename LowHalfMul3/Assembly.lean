import LowHalfMul3.LemmaTwo
import LowHalfMul3.Reduction

/-!
# The case split of the five-gate exclusion, and the `λ = 4` reduction

`LambdaCase lam` is the exclusion of five-gate circuits in the normal form of
Lemma 1 with exactly `lam` linear gates. `LambdaCase 5` is proved
(`LambdaFive.lean`).

`StarFree` is Theorem 11 of `lambda4_proof.tex` in algebraic form: for four
products of affine functions `Lᵢ Rᵢ` with `L₀ R₀ = a₀ b₀` and
`Q = span {π₂(Lᵢ Rᵢ)} ∋ Z₁`, condition (★) has no solution. It deliberately
allows degenerate products (`π₂(Lᵢ Rᵢ)` of rank `< 2`, `dim Q < 4`): the paper's
reduction to rank-2 forms and `dim Q = 4` is part of the proof of Theorem 11,
not of the circuit-to-(★) reduction proved here.

* `lambdaCase_four_of_starFree : StarFree → LambdaCase 4` is the paragraph
  after Lemma 2 ("Hence `z₀, z₁ ∈ V₄` iff `P₀, Z₁ ∈ Q`, and the remaining
  condition on the last gate is (★)").
* `not_hasCircuit_five_of_cases` and `mc_eq_six_of_remaining_cases` assemble
  Lemma 1, the five cases, padding and the upper bound.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- Exclusion of five-gate circuits in normal form with exactly `lam` linear
gates (`g₀ = a₀b₀`, gates `0..lam-1` linear, the others not). -/
def LambdaCase (lam : Nat) : Prop :=
  ∀ D : Circuit 6 5, D.Computes lowMul3 →
    D.gate 0 = aVar 3 0 * bVar 3 0 → D.left 0 = aVar 3 0 → D.right 0 = bVar 3 0 →
    (∀ k : Fin 5, (k.val < lam ↔ IsLinearGate D k)) → False

theorem lambdaCase_five : LambdaCase 5 :=
  fun D hD _ _ _ hlam => not_lambda_five D hD hlam

/-- The quadratic span of four products. -/
def quadSpan (L R : Fin 4 → ANF 6) : Submodule F₂ TwoForm6 :=
  Submodule.span F₂ (Set.range fun i => pi2 (L i * R i))

/-- **Theorem 11 of `lambda4_proof.tex`, algebraic form.** For affine
`L₀..L₃, R₀..R₃` with `L₀ = a₀`, `R₀ = b₀` and `Z₁ ∈ Q := span{π₂(Lᵢ Rᵢ)}`,
there are no `f, h ∈ V₄(Q)` with `f h ∈ z₂ + V₄(Q)`. -/
def StarFree : Prop :=
  ∀ (L R : Fin 4 → ANF 6), (∀ i, L i ∈ affine 6) → (∀ i, R i ∈ affine 6) →
    L 0 = aVar 3 0 → R 0 = bVar 3 0 →
    pi2 (lowMul3 1) ∈ quadSpan L R →
    ∀ f h : ANF 6, f ∈ V4 (quadSpan L R) → h ∈ V4 (quadSpan L R) →
      f * h + lowMul3 2 ∈ V4 (quadSpan L R) → False

/-- The part of Theorem 11 already covered by Lemma 8: every `Q` annihilated
by some `ι_e` (685 of the 783 orbits in the paper's count). -/
theorem starFree_instance_of_iota (L R : Fin 4 → ANF 6)
    {e : Fin 6 → F₂} (he : IsPaperDir e)
    (hQ : Submodule.map (iota e) (quadSpan L R) = ⊥)
    (f h : ANF 6) (hf : f ∈ V4 (quadSpan L R)) (hh : h ∈ V4 (quadSpan L R))
    (hg : f * h + lowMul3 2 ∈ V4 (quadSpan L R)) : False :=
  derivative_lemma_paper he _ hQ f h hf hh hg

theorem degreeLE_two_lowMul3_one : DegreeLE 2 (lowMul3 1) := by
  rw [z1_eq]
  show DegreeLE 2 (aVar 3 0 * bVar 3 1 + aVar 3 1 * bVar 3 0)
  exact (DegreeLE.mul (degreeLE_one_aVar 0) (degreeLE_one_bVar 1)).add
    (DegreeLE.mul (degreeLE_one_aVar 1) (degreeLE_one_bVar 0))

/-- Left factors of the first four gates of a five-gate circuit. -/
def prefixLeft (D : Circuit 6 5) : Fin 4 → ANF 6 := fun k => D.left (Fin.castSucc k)

/-- Right factors of the first four gates of a five-gate circuit. -/
def prefixRight (D : Circuit 6 5) : Fin 4 → ANF 6 := fun k => D.right (Fin.castSucc k)

theorem gateQ_le_quadSpan (D : Circuit 6 5) :
    gateQ D 4 ≤ quadSpan (prefixLeft D) (prefixRight D) := by
  rw [gateQ, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨i.val, hi⟩, ?_⟩
  have hk : Fin.castSucc (⟨i.val, hi⟩ : Fin 4) = i := Fin.ext rfl
  show pi2 (D.left (Fin.castSucc ⟨i.val, hi⟩) * D.right (Fin.castSucc ⟨i.val, hi⟩)) =
    pi2 (D.gate i)
  rw [hk, D.gate_eq i]

theorem finalWire_five_eq (D : Circuit 6 5) :
    D.finalWire = wireSpace D.gate 4 ⊔ Submodule.span F₂ {D.gate 4} := by
  show wireSpace D.gate (4 + 1) = _
  rw [N4.wireSpace_succ D.gate (by norm_num)]
  rfl

/-- **The `λ = 4` reduction.** Theorem 11 (`StarFree`) excludes the case of
four linear gates. -/
theorem lambdaCase_four_of_starFree (hstar : StarFree) : LambdaCase 4 := by
  intro D hD _ hl0 hr0 hlam
  have hlin : ∀ i : Fin 5, i.val < 4 → IsLinearGate D i := fun i hi => (hlam i).mp hi
  have hV : wireSpace D.gate 4 ≤ V4 (quadSpan (prefixLeft D) (prefixRight D)) :=
    (wireSpace_eq_V4 D 4 hlin).le.trans (V4_mono (gateQ_le_quadSpan D))
  have hVdeg : ∀ p ∈ wireSpace D.gate 4, DegreeLE 2 p := fun p hp => (hV hp).1
  -- If the last gate had degree ≤ 2, so would `z₂`.
  have hg4 : ¬ DegreeLE 2 (D.gate 4) := by
    intro h4
    apply not_degreeLE_two_lowMul3_two
    have hle : D.finalWire ≤ degreeLESubmodule 6 2 := by
      rw [finalWire_five_eq]
      apply sup_le
      · exact fun p hp => hVdeg p hp
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact h4
    exact hle (hD 2)
  have hz1mem := hD 1
  rw [finalWire_five_eq] at hz1mem
  obtain ⟨v1, hv1, w1, hw1, hz1⟩ := Submodule.mem_sup.mp hz1mem
  obtain ⟨c1, rfl⟩ := Submodule.mem_span_singleton.mp hw1
  have hz2mem := hD 2
  rw [finalWire_five_eq] at hz2mem
  obtain ⟨v2, hv2, w2, hw2, hz2⟩ := Submodule.mem_sup.mp hz2mem
  obtain ⟨c2, rfl⟩ := Submodule.mem_span_singleton.mp hw2
  -- `Z₁ ∈ Q`: the `z₁`-decomposition cannot use the last gate.
  have hZ1 : pi2 (lowMul3 1) ∈ quadSpan (prefixLeft D) (prefixRight D) := by
    rcases f2_eq_zero_or_one c1 with h | h
    · rw [h, zero_smul, add_zero] at hz1
      rw [← hz1]
      exact (hV hv1).2
    · exfalso
      rw [h, one_smul] at hz1
      apply hg4
      have hgate : D.gate 4 = lowMul3 1 + v1 := by
        rw [← hz1, add_comm v1, add_assoc, anf_add_self, add_zero]
      rw [hgate]
      exact degreeLE_two_lowMul3_one.add (hVdeg v1 hv1)
  -- (★): the `z₂`-decomposition must use the last gate.
  have hstar' : D.left 4 * D.right 4 + lowMul3 2 ∈
      V4 (quadSpan (prefixLeft D) (prefixRight D)) := by
    rcases f2_eq_zero_or_one c2 with h | h
    · exfalso
      rw [h, zero_smul, add_zero] at hz2
      exact not_degreeLE_two_lowMul3_two (hz2 ▸ hVdeg v2 hv2)
    · rw [h, one_smul] at hz2
      rw [← D.gate_eq 4, ← hz2]
      have hcancel : D.gate 4 + (v2 + D.gate 4) = v2 := by
        rw [add_comm v2, ← add_assoc, anf_add_self, zero_add]
      rw [hcancel]
      exact hV hv2
  refine hstar (prefixLeft D) (prefixRight D)
    (fun i => (hlin (Fin.castSucc i) (by show i.val < 4; exact i.isLt)).1)
    (fun i => (hlin (Fin.castSucc i) (by show i.val < 4; exact i.isLt)).2)
    hl0 hr0 hZ1 (D.left 4) (D.right 4) (hV (D.left_mem 4)) (hV (D.right_mem 4)) hstar'

/-- **Assembly.** The five-gate exclusion follows from the four cases
`λ = 1, 2, 3, 4` (the case `λ = 5` is proved). -/
theorem not_hasCircuit_five_of_cases (h1 : LambdaCase 1) (h2 : LambdaCase 2)
    (h3 : LambdaCase 3) (h4 : LambdaCase 4) : ¬ HasCircuit lowMul3 5 := by
  rintro ⟨⟨C, hC⟩⟩
  obtain ⟨D, hD, hg, hl, hr, lam, hlo, hhi, hlam⟩ := normal_form_five C hC
  have hcases : lam = 1 ∨ lam = 2 ∨ lam = 3 ∨ lam = 4 ∨ lam = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact h1 D hD hg hl hr hlam
  · exact h2 D hD hg hl hr hlam
  · exact h3 D hD hg hl hr hlam
  · exact h4 D hD hg hl hr hlam
  · exact lambdaCase_five D hD hg hl hr hlam

/-- **`MC(lowMul3) = 6` from the remaining cases.** What is still missing in
Lean is exactly: `LambdaCase 1`, `LambdaCase 2`, `LambdaCase 3`, and
`StarFree` (Theorem 11). -/
theorem mc_eq_six_of_remaining_cases (h1 : LambdaCase 1) (h2 : LambdaCase 2)
    (h3 : LambdaCase 3) (h4 : StarFree) : MC(lowMul3) = 6 :=
  mc_eq_six_of_no_five
    (not_hasCircuit_five_of_cases h1 h2 h3 (lambdaCase_four_of_starFree h4))

end

end LowHalfMul3

end UnrestrictedBooleanMul
