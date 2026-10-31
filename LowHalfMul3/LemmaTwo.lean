import LowHalfMul3.LambdaFive
import LowHalfMul3.Contraction

/-!
# Lemma 2 of `lambda4_proof.tex`: `V_j = V₄(Q)`

If the first `j` gates of a circuit are linear, the wire space before gate `j`
is exactly

  `V4 Q = {f : deg f ≤ 2, π₂ f ∈ Q}`,   `Q = span {π₂ g_i : i < j}`.

The paper's proof: if `π₂ f = ∑ αᵢ Pᵢ` then `f - ∑ αᵢ gᵢ` has no quadratic part
and therefore lies in `Aff`. The Lean proof needs that last step as a lemma
(`mem_affine_of_degreeLE_two_of_pi2_eq_zero`), proved by rebuilding an ANF
from its coefficients (`anf_eq_sum_monomials`).
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- Every ANF is the sum of its monomials. -/
theorem anf_eq_sum_monomials (p : ANF 6) :
    p = ∑ s ∈ p.coeff.support, p.coeff s • monomial s.vars := by
  apply eval_injective 6
  funext x
  show eval p x = eval (∑ s ∈ p.coeff.support, p.coeff s • monomial s.vars) x
  have hsum : ∀ S : Finset (Monomial 6),
      eval (∑ s ∈ S, p.coeff s • monomial s.vars) x =
        ∑ s ∈ S, p.coeff s * ∏ i ∈ s.vars, x i := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp
    · intro a S ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, eval_add', ih, eval_smul',
        eval_monomial]
  rw [hsum, eval_eq_sum_support]

theorem monomial_empty : (monomial ∅ : ANF 6) = 1 := by
  rw [monomial, MonoidAlgebra.one_def]
  rfl

/-- A function of degree at most two with no quadratic part is affine. -/
theorem mem_affine_of_degreeLE_two_of_pi2_eq_zero (p : ANF 6)
    (hp : DegreeLE 2 p) (h0 : pi2 p = 0) : p ∈ affine 6 := by
  rw [anf_eq_sum_monomials p]
  refine Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ ?_
  have hne : p.coeff s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hcard : s.vars.card ≤ 1 := by
    by_contra hgt
    have h2 : s.vars.card ≤ 2 := by
      by_contra h3
      exact hne (hp s (by omega))
    obtain ⟨i, j, hij, hs2⟩ := Finset.card_eq_two.mp (show s.vars.card = 2 by omega)
    have hcoef := congrFun (congrFun h0 i) j
    rw [pi2_apply] at hcoef
    simp only [hij, ↓reduceIte] at hcoef
    have hs' : s = ⟨{i, j}⟩ := Monomial.ext hs2
    rw [← hs'] at hcoef
    exact hne hcoef
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h | h
  · rw [Finset.card_eq_zero.mp h, monomial_empty]
    exact one_mem_affine 6
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    rw [hi]
    exact X_mem_affine i

/-- Affine functions have no quadratic part. -/
theorem pi2_eq_zero_of_mem_affine {p : ANF 6} (hp : p ∈ affine 6) : pi2 p = 0 := by
  funext i j
  rw [pi2_apply]
  split_ifs with hij
  · rfl
  · exact coefficient_eq_zero_of_mem_affine hp ⟨{i, j}⟩ (Finset.card_pair hij)

theorem V4_mono {Q Q' : Submodule F₂ TwoForm6} (h : Q ≤ Q') : V4 Q ≤ V4 Q' :=
  fun _ hp => ⟨hp.1, h hp.2⟩

theorem affine_le_V4 (Q : Submodule F₂ TwoForm6) : affine 6 ≤ V4 Q := by
  intro p hp
  refine ⟨(degreeLE_one_of_mem_affine hp).mono (by omega), ?_⟩
  rw [pi2_eq_zero_of_mem_affine hp]
  exact Q.zero_mem

/-- The quadratic span `Q_j = span {π₂ g_i : i < j}` of the first `j` gates. -/
def gateQ {r : Nat} (C : Circuit 6 r) (j : Nat) : Submodule F₂ TwoForm6 :=
  Submodule.span F₂ (pi2 '' prefixGates C.gate j)

theorem span_prefix_le_degreeTwo {r j : Nat} (C : Circuit 6 r)
    (hlin : ∀ i : Fin r, i.val < j → IsLinearGate C i) :
    Submodule.span F₂ (prefixGates C.gate j) ≤ degreeLESubmodule 6 2 := by
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  show DegreeLE 2 (C.gate i)
  rw [C.gate_eq i]
  exact DegreeLE.mul (degreeLE_one_of_mem_affine (hlin i hi).1)
    (degreeLE_one_of_mem_affine (hlin i hi).2)

/-- **Lemma 2.** If the first `j` gates are linear, then the wire space before
gate `j` is `V₄(Q_j)`. -/
theorem wireSpace_eq_V4 {r : Nat} (C : Circuit 6 r) (j : Nat)
    (hlin : ∀ i : Fin r, i.val < j → IsLinearGate C i) :
    wireSpace C.gate j = V4 (gateQ C j) := by
  apply le_antisymm
  · apply sup_le (affine_le_V4 _)
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨span_prefix_le_degreeTwo C hlin
      (Submodule.subset_span ⟨i, hi, rfl⟩), ?_⟩
    exact Submodule.subset_span ⟨C.gate i, ⟨i, hi, rfl⟩, rfl⟩
  · rintro p ⟨hdeg, hQ⟩
    rw [gateQ, Submodule.span_image] at hQ
    obtain ⟨q, hq, hpq⟩ := hQ
    have hqdeg : DegreeLE 2 q := span_prefix_le_degreeTwo C hlin hq
    have haff : p + q ∈ affine 6 := by
      apply mem_affine_of_degreeLE_two_of_pi2_eq_zero _ (hdeg.add hqdeg)
      rw [map_add, ← hpq]
      funext i j
      exact CharTwo.add_self_eq_zero (pi2 q i j)
    have hp : p = (p + q) + q := by rw [add_assoc, anf_add_self, add_zero]
    rw [hp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left haff)
      (Submodule.mem_sup_right hq)

end

end LowHalfMul3

end UnrestrictedBooleanMul
