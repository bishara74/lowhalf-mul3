import LowHalfMul3.Upper
import UnrestrictedBooleanMul.N4.Rewiring

/-!
# The normal form (Lemma 1 of `lambda4_proof.tex`)

If a `k`-gate circuit computes `lowMul3`, so does a `k`-gate circuit in which

* gate 0 is `a₀ * b₀`, with factors exactly `a₀` and `b₀`, and
* gates `0, …, λ-1` are linear (both factors affine) and gates `λ, …, k-1`
  are not, for some `1 ≤ λ ≤ k`.

Part (a) instantiates the first-entry chain of `N4/Rewiring.lean`
(`exists_first_entry_gate`, `circuit_first_entry_replacement`,
`replaceFirstEntryCircuit`) at `t = a₀b₀`.

Part (b) needs a stronger move lemma than `N4.exists_move_direct_gate_left`,
whose conclusion records only the *gate values* below the target position.
`exists_move_linear_gate_left` repeats the same induction over
`N4.swapAdjacentDirectCircuit`, but also records the *factors*, so that "the
first `i` gates are linear" survives the move. The sorting induction
`exists_linear_prefix` then runs on `r - i`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- Gate `k` is linear: both of its factors are affine in the inputs. -/
def IsLinearGate {m r : Nat} (C : Circuit m r) (k : Fin r) : Prop :=
  C.left k ∈ affine m ∧ C.right k ∈ affine m

/-- Gate `k` of `D` agrees with gate `k` of `C`, factors included. -/
def SameGate {m r : Nat} (D C : Circuit m r) (k : Fin r) : Prop :=
  D.gate k = C.gate k ∧ D.left k = C.left k ∧ D.right k = C.right k

/-! ## The strengthened move lemma -/

/-- Move a linear gate at position `j` down to position `p ≤ j`, preserving the
final wire space and every gate *with its factors* below `p`. -/
theorem exists_move_linear_gate_left {m r : Nat}
    (C : Circuit m r) (p j : Fin r) (hpj : p.val ≤ j.val)
    (hlin : IsLinearGate C j) :
    ∃ D : Circuit m r,
      D.finalWire = C.finalWire ∧
      D.gate p = C.gate j ∧ D.left p = C.left j ∧ D.right p = C.right j ∧
      (∀ k : Fin r, k.val < p.val → SameGate D C k) := by
  generalize hd : j.val - p.val = d
  induction d using Nat.strong_induction_on generalizing C j with
  | h d ih =>
      by_cases hpjeq : p = j
      · subst hpjeq
        exact ⟨C, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
      · have hpjlt : p.val < j.val := by
          have hvals : p.val ≠ j.val := fun h => hpjeq (Fin.ext h)
          omega
        let a : Fin r := ⟨j.val - 1, by omega⟩
        have haj : a.val + 1 = j.val := by dsimp [a]; omega
        have haj' : a ≠ j := by
          intro h
          have := congrArg Fin.val h
          dsimp [a] at this
          omega
        let C' := N4.swapAdjacentDirectCircuit C a j haj hlin.1 hlin.2
        have hC'gate : C'.gate a = C.gate j := by
          dsimp [C', N4.swapAdjacentDirectCircuit]
          simp [N4.swapAdjacentFun]
        have hC'left : C'.left a = C.left j := by
          dsimp [C', N4.swapAdjacentDirectCircuit]
          simp [N4.swapAdjacentFun]
        have hC'right : C'.right a = C.right j := by
          dsimp [C', N4.swapAdjacentDirectCircuit]
          simp [N4.swapAdjacentFun]
        have hlin' : IsLinearGate C' a := by
          refine ⟨?_, ?_⟩
          · rw [hC'left]; exact hlin.1
          · rw [hC'right]; exact hlin.2
        have hpa : p.val ≤ a.val := by dsimp [a]; omega
        have hdist : a.val - p.val < d := by dsimp [a]; omega
        obtain ⟨D, hDf, hDg, hDl, hDr, hDb⟩ := ih (a.val - p.val) hdist C' a hpa hlin' rfl
        refine ⟨D, hDf.trans
            (N4.swapAdjacentDirectCircuit_finalWire C a j haj hlin.1 hlin.2),
          hDg.trans hC'gate, hDl.trans hC'left, hDr.trans hC'right, ?_⟩
        intro k hk
        obtain ⟨h1, h2, h3⟩ := hDb k hk
        have hka : k ≠ a := by
          intro h
          subst k
          omega
        have hkj : k ≠ j := by
          intro h
          subst k
          omega
        refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩
        · dsimp [C', N4.swapAdjacentDirectCircuit]
          simp [N4.swapAdjacentFun, hka, hkj]
        · dsimp [C', N4.swapAdjacentDirectCircuit]
          simp [N4.swapAdjacentFun, hka, hkj]
        · dsimp [C', N4.swapAdjacentDirectCircuit]
          simp [N4.swapAdjacentFun, hka, hkj]

/-! ## (a) `g₀ = a₀b₀` -/

theorem lowMul3_zero_eq_a0b0 : lowMul3 0 = aVar 3 0 * bVar 3 0 := z0_eq

theorem coeff_a0b0 :
    (aVar 3 0 * bVar 3 0 : ANF 6).coeff ⟨{0, 3}⟩ = 1 := by
  simp [aVar, bVar, X, monomial_mul]

theorem a0b0_not_mem_affine : aVar 3 0 * bVar 3 0 ∉ affine 6 := by
  intro h
  have h0 := coefficient_eq_zero_of_mem_affine h ⟨{0, 3}⟩ (by decide)
  rw [coeff_a0b0] at h0
  exact one_ne_zero h0

/-- Lemma 1, first half: the first gate can be taken to be `a₀ * b₀`. -/
theorem exists_g0_normal {r : Nat} (C : Circuit 6 r) (hC : C.Computes lowMul3) :
    ∃ (hr : 0 < r) (D : Circuit 6 r), D.Computes lowMul3 ∧
      D.gate ⟨0, hr⟩ = aVar 3 0 * bVar 3 0 ∧
      D.left ⟨0, hr⟩ = aVar 3 0 ∧ D.right ⟨0, hr⟩ = bVar 3 0 := by
  have htfinal : aVar 3 0 * bVar 3 0 ∈ C.finalWire := by
    rw [← lowMul3_zero_eq_a0b0]
    exact hC 0
  obtain ⟨j, htj, htfirst⟩ :=
    N4.exists_first_entry_gate C _ htfinal a0b0_not_mem_affine
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hstate := N4.circuit_first_entry_replacement C j _ htj htfirst
  let C₁ := N4.replaceFirstEntryCircuit C j (aVar 3 0) (bVar 3 0)
    (aVar 3 0 * bVar 3 0) (aVar_mem_affine 3 0) (bVar_mem_affine 3 0) rfl hstate
  have hC₁final : C₁.finalWire = C.finalWire :=
    N4.replaceFirstEntryCircuit_finalWire C j _ _ _ _ _ rfl hstate
  have hC₁gate : C₁.gate j = aVar 3 0 * bVar 3 0 := by
    simp [C₁, N4.replaceFirstEntryCircuit, N4.updateGate]
  have hC₁left : C₁.left j = aVar 3 0 := by
    simp [C₁, N4.replaceFirstEntryCircuit]
  have hC₁right : C₁.right j = bVar 3 0 := by
    simp [C₁, N4.replaceFirstEntryCircuit]
  have hlin : IsLinearGate C₁ j := by
    refine ⟨?_, ?_⟩
    · rw [hC₁left]; exact aVar_mem_affine 3 0
    · rw [hC₁right]; exact bVar_mem_affine 3 0
  obtain ⟨D, hDf, hDg, hDl, hDr, -⟩ :=
    exists_move_linear_gate_left C₁ ⟨0, hr⟩ j (Nat.zero_le _) hlin
  refine ⟨hr, D, ?_, hDg.trans hC₁gate, hDl.trans hC₁left, hDr.trans hC₁right⟩
  intro i
  rw [hDf, hC₁final]
  exact hC i

/-! ## (b) Linear gates first -/

/-- The sorting induction: if the first `i` gates are linear, the linear gates
can be gathered into an initial segment `0, …, λ-1` with `λ ≥ i`, keeping the
final wire space and the first `i` gates (with their factors). -/
theorem exists_linear_prefix {m r : Nat} (C : Circuit m r) (i : Nat) (hi : i ≤ r)
    (hpre : ∀ k : Fin r, k.val < i → IsLinearGate C k) :
    ∃ D : Circuit m r, D.finalWire = C.finalWire ∧
      (∀ k : Fin r, k.val < i → SameGate D C k) ∧
      ∃ lam, i ≤ lam ∧ lam ≤ r ∧ ∀ k : Fin r, (k.val < lam ↔ IsLinearGate D k) := by
  generalize hd : r - i = d
  induction d using Nat.strong_induction_on generalizing C i with
  | h d ih =>
      by_cases hex : ∃ j : Fin r, i ≤ j.val ∧ IsLinearGate C j
      · obtain ⟨j, hij, hlinj⟩ := hex
        have hir : i < r := lt_of_le_of_lt hij j.isLt
        let p : Fin r := ⟨i, hir⟩
        obtain ⟨D₁, hD₁f, hD₁g, hD₁l, hD₁r, hD₁b⟩ :=
          exists_move_linear_gate_left C p j hij hlinj
        have hpre₁ : ∀ k : Fin r, k.val < i + 1 → IsLinearGate D₁ k := by
          intro k hk
          by_cases hki : k.val < i
          · obtain ⟨-, hl, hr⟩ := hD₁b k hki
            exact ⟨hl ▸ (hpre k hki).1, hr ▸ (hpre k hki).2⟩
          · have hkp : k = p := Fin.ext (by dsimp [p]; omega)
            subst hkp
            exact ⟨hD₁l ▸ hlinj.1, hD₁r ▸ hlinj.2⟩
        obtain ⟨D, hDf, hDb, lam, hlam1, hlam2, hlam⟩ :=
          ih (r - (i + 1)) (by omega) D₁ (i + 1) (by omega) hpre₁ rfl
        refine ⟨D, hDf.trans hD₁f, ?_, lam, by omega, hlam2, hlam⟩
        intro k hk
        obtain ⟨g1, l1, r1⟩ := hDb k (by omega)
        obtain ⟨g2, l2, r2⟩ := hD₁b k hk
        exact ⟨g1.trans g2, l1.trans l2, r1.trans r2⟩
      · refine ⟨C, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, i, le_rfl, hi, ?_⟩
        intro k
        constructor
        · exact hpre k
        · intro hk
          by_contra hki
          exact hex ⟨k, by omega, hk⟩

/-! ## Lemma 1 -/

/-- **Lemma 1 (normal form), any number of gates.** -/
theorem normal_form {r : Nat} (C : Circuit 6 r) (hC : C.Computes lowMul3) :
    ∃ (hr : 0 < r) (D : Circuit 6 r), D.Computes lowMul3 ∧
      D.gate ⟨0, hr⟩ = aVar 3 0 * bVar 3 0 ∧
      D.left ⟨0, hr⟩ = aVar 3 0 ∧ D.right ⟨0, hr⟩ = bVar 3 0 ∧
      ∃ lam, 1 ≤ lam ∧ lam ≤ r ∧ ∀ k : Fin r, (k.val < lam ↔ IsLinearGate D k) := by
  obtain ⟨hr, D₀, hD₀, hg, hl, hrt⟩ := exists_g0_normal C hC
  have hpre : ∀ k : Fin r, k.val < 1 → IsLinearGate D₀ k := by
    intro k hk
    have hk0 : k = ⟨0, hr⟩ := Fin.ext (by show k.val = 0; omega)
    subst hk0
    exact ⟨hl ▸ aVar_mem_affine 3 0, hrt ▸ bVar_mem_affine 3 0⟩
  obtain ⟨D, hDf, hDb, lam, hlam1, hlam2, hlam⟩ := exists_linear_prefix D₀ 1 hr hpre
  obtain ⟨g1, l1, r1⟩ := hDb ⟨0, hr⟩ (by simp)
  refine ⟨hr, D, ?_, g1.trans hg, l1.trans hl, r1.trans hrt, lam, hlam1, hlam2, hlam⟩
  intro i
  rw [hDf]
  exact hD₀ i

/-- **Lemma 1 (normal form) for five gates**, as used in the `k = 5` exclusion:
any 5-gate circuit computing `lowMul3` can be replaced by one with
`g₀ = a₀b₀`, gates `0, …, λ-1` linear and the rest nonlinear, `1 ≤ λ ≤ 5`. -/
theorem normal_form_five (C : Circuit 6 5) (hC : C.Computes lowMul3) :
    ∃ D : Circuit 6 5, D.Computes lowMul3 ∧
      D.gate 0 = aVar 3 0 * bVar 3 0 ∧ D.left 0 = aVar 3 0 ∧ D.right 0 = bVar 3 0 ∧
      ∃ lam, 1 ≤ lam ∧ lam ≤ 5 ∧ ∀ k : Fin 5, (k.val < lam ↔ IsLinearGate D k) := by
  obtain ⟨_, D, hD, hg, hl, hrt, lam, h1, h2, hlam⟩ := normal_form C hC
  exact ⟨D, hD, hg, hl, hrt, lam, h1, h2, hlam⟩

end

end LowHalfMul3

end UnrestrictedBooleanMul
