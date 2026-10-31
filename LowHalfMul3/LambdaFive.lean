import LowHalfMul3.NormalForm
import LowHalfMul3.Derivative

/-!
# The case `λ = 5`

If every gate of a circuit is linear (both factors affine), every gate output
has degree at most two, so the whole final wire space does. But `z₂` contains
the carry monomial `a₀a₁b₀b₁` of degree four. Hence no circuit all of whose
gates are linear computes `lowMul3`, whatever the number of gates; in
particular the case `λ = 5` of the normal form is impossible.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- The functions of degree at most `d`, as a subspace. -/
def degreeLESubmodule (m d : Nat) : Submodule F₂ (ANF m) where
  carrier := {p | DegreeLE d p}
  add_mem' := fun hp hq => DegreeLE.add hp hq
  zero_mem' := by
    intro s _
    simp
  smul_mem' := fun c _ hp => DegreeLE.smul hp c

theorem mem_degreeLESubmodule {m d : Nat} {p : ANF m} :
    p ∈ degreeLESubmodule m d ↔ DegreeLE d p := Iff.rfl

/-- A circuit whose gates are all linear has a final wire space of degree at
most two. -/
theorem finalWire_le_degreeTwo {m r : Nat} (C : Circuit m r)
    (hlin : ∀ k, IsLinearGate C k) :
    C.finalWire ≤ degreeLESubmodule m 2 := by
  rw [Circuit.finalWire_eq]
  apply sup_le
  · intro p hp
    exact (degreeLE_one_of_mem_affine hp).mono (by omega)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show DegreeLE 2 (C.gate k)
    rw [C.gate_eq k]
    exact DegreeLE.mul (degreeLE_one_of_mem_affine (hlin k).1)
      (degreeLE_one_of_mem_affine (hlin k).2)

/-- `z₂` has degree four, so it is not of degree at most two. -/
theorem not_degreeLE_two_lowMul3_two : ¬ DegreeLE 2 (lowMul3 2) := by
  intro h
  have h0 := h carryMonomial (by rw [carryMonomial_card]; omega)
  rw [coeff_lowMul3_two_carry] at h0
  exact one_ne_zero h0

/-- No circuit all of whose gates are linear computes `lowMul3`. -/
theorem no_all_linear_circuit {r : Nat} (C : Circuit 6 r) (hC : C.Computes lowMul3)
    (hlin : ∀ k, IsLinearGate C k) : False :=
  not_degreeLE_two_lowMul3_two (finalWire_le_degreeTwo C hlin (hC 2))

/-- **The case `λ = 5`.** In the normal form of Lemma 1, `λ = 5` is impossible. -/
theorem not_lambda_five (D : Circuit 6 5) (hD : D.Computes lowMul3)
    (hlam : ∀ k : Fin 5, (k.val < 5 ↔ IsLinearGate D k)) : False :=
  no_all_linear_circuit D hD (fun k => (hlam k).mp k.isLt)

end

end LowHalfMul3

end UnrestrictedBooleanMul
