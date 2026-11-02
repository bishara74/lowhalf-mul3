import LowHalfMul3.MainTheorem

/-!
# The case `λ = 3` (`lambda3_proof.tex`): reduction to two claims

Circuit in normal form with `λ = 3`: `g₀ = a₀b₀`, `g₁, g₂` linear, `g₃ = F₃H₃`
with `F₃, H₃ ∈ V₃ = V(Q₃)`, `Q₃ = span{P₀, P₁, P₂}`, and `g₄ = F₄H₄` with
`F₄, H₄ ∈ V₄ = V₃ + ⟨g₃⟩`.

This file proves `LambdaCase 3` from two claims:

* `BadClaim`: if `Q₃` has no good direction (`¬ GoodDir Q₃`), no product of two
  elements of `V₃` lies in `T + V₃` for `T ∈ {z₁, z₂, z₂ + z₁}` (Lemmas A and C
  of `lambda3_proof.tex` for those `Q₃`);
* `B3Claim`: if `Q₃ ⊆ Λ²(U)`, the last gate cannot place `z₂`
  (Proposition B3).

Everything else is proved here, by a shorter route than the paper's:

* if `Q₃` has a good direction (Lemma 8′), so does `Q' = Q₃ + ⟨Z₁⟩` because
  `ι_e Z₁ = 0`; since `z₁ ∈ V(Q')`, Lemma C for `Q₃` follows from
  `starFree_of_goodDir` for `Q'` (`noPlace_of_goodDir`);
* Lemma C gives `z₁ ∈ V₄` and `g₄ ∈ z₂ + V₄` (`flow`);
* if `z₁ ∈ V₃`, then `Z₁ ∈ Q₃` and Lemma 3 gives `Q₃ ⊆ Λ²(U)`
  (Lemma B3U, `phi_of_Z1_mem`): `B3Claim`;
* otherwise `g₃ ∈ z₁ + V₃`, so `V₄ ⊆ V(Q')`, and the last gate solves (★) for
  `Q'`: excluded by `starFree_of_goodDir` (good `Q₃`) or `BadClaim` (bad `Q₃`).

The paper's step (1) (`dim Q₃ = 3`) is not needed. See LEAN_LOG.md, phase 5.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- `Q₃ = span{P₀, l₁ ∧ r₁, l₂ ∧ r₂}`. -/
def Q3span (l1 r1 l2 r2 : Fin 6 → F₂) : Submodule F₂ TwoForm6 :=
  Submodule.span F₂ (Set.range ![P0form, wedge l1 r1, wedge l2 r2])

/-- No product of two elements of `V(Q)` lies in `T + V(Q)`. -/
def NoPlace (Q : Submodule F₂ TwoForm6) (T : ANF 6) : Prop :=
  ∀ f h : ANF 6, f ∈ V4 Q → h ∈ V4 Q → f * h + T ∈ V4 Q → False

/-- **Bad spaces** (Lemmas A and C of `lambda3_proof.tex` for `Q₃` without a
good direction): the third gate places none of `z₁`, `z₂`, `z₂ + z₁`. -/
def BadClaim : Prop :=
  ∀ l1 r1 l2 r2 : Fin 6 → F₂, ¬ GoodDir (Q3span l1 r1 l2 r2) →
    NoPlace (Q3span l1 r1 l2 r2) (lowMul3 1) ∧ NoPlace (Q3span l1 r1 l2 r2) (lowMul3 2) ∧
      NoPlace (Q3span l1 r1 l2 r2) (lowMul3 2 + lowMul3 1)

/-- **Proposition B3**: if `Q ⊆ Λ²(U)` and `g₃ = f h` with `f, h ∈ V(Q)`, no
`F, H ∈ V(Q) + ⟨g₃⟩` have `F H ∈ z₂ + V(Q) + ⟨g₃⟩`. -/
def B3Claim : Prop :=
  ∀ Q : Submodule F₂ TwoForm6, (∀ ω ∈ Q, Phi ω = 0) →
    ∀ f h F H : ANF 6, f ∈ V4 Q → h ∈ V4 Q →
      F ∈ V4 Q ⊔ Submodule.span F₂ {f * h} → H ∈ V4 Q ⊔ Submodule.span F₂ {f * h} →
      F * H + lowMul3 2 ∈ V4 Q ⊔ Submodule.span F₂ {f * h} → False

/-! ## Good directions survive adding `Z₁` -/

theorem iota_Z1 {e d : Fin 6 → F₂} (hp : PaperPair e d) : iota e Z1form = 0 := by
  rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · funext t; rw [iota_dirA2_apply]; simp [Z1form, wedge, unitVec]
  · funext t; rw [iota_dirB2_apply]; simp [Z1form, wedge, unitVec]
  · rw [iota_dirA2B2]; funext t
    simp only [Pi.add_apply]
    rw [iota_dirA2_apply, iota_dirB2_apply]; simp [Z1form, wedge, unitVec]

theorem goodDir_sup_Z1 {Q : Submodule F₂ TwoForm6} (hQ : GoodDir Q) :
    GoodDir (Q ⊔ Submodule.span F₂ {Z1form}) := by
  obtain ⟨e, d, ℓ, hp, hℓ, hQℓ⟩ := hQ
  refine ⟨e, d, ℓ, hp, hℓ, fun ω hω => ?_⟩
  obtain ⟨q, hq, z, hz, rfl⟩ := Submodule.mem_sup.mp hω
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  obtain ⟨γ, hγ⟩ := hQℓ q hq
  exact ⟨γ, by rw [map_add, map_smul, iota_Z1 hp, smul_zero, add_zero, hγ]⟩

theorem z1_mem_V4_sup (Q : Submodule F₂ TwoForm6) :
    lowMul3 1 ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) :=
  ⟨degreeLE_two_lowMul3_one, by
    rw [pi2_lowMul3_one]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩

/-- **Lemma C for spaces with a good direction.** -/
theorem noPlace_of_goodDir {Q : Submodule F₂ TwoForm6} (hQ : GoodDir Q) :
    NoPlace Q (lowMul3 2) ∧ NoPlace Q (lowMul3 2 + lowMul3 1) := by
  refine ⟨fun f h hf hh hg => starFree_of_goodDir hQ f h hf hh hg, fun f h hf hh hg => ?_⟩
  have hle : V4 Q ≤ V4 (Q ⊔ Submodule.span F₂ {Z1form}) := V4_mono le_sup_left
  refine starFree_of_goodDir (goodDir_sup_Z1 hQ) f h (hle hf) (hle hh) ?_
  have hsplit : f * h + lowMul3 2 = (f * h + (lowMul3 2 + lowMul3 1)) + lowMul3 1 := by
    rw [add_assoc (f * h), add_assoc (lowMul3 2), anf_add_self, add_zero]
  rw [hsplit]
  exact Submodule.add_mem _ (hle hg) (z1_mem_V4_sup Q)

/-! ## The linear-algebra flow (proof of Theorem, `lambda3_proof.tex` §7) -/

theorem not_degreeLE_two_z2_add_z1 : ¬ DegreeLE 2 (lowMul3 2 + lowMul3 1) := by
  intro h
  apply not_degreeLE_two_lowMul3_two
  have hs : lowMul3 2 = (lowMul3 2 + lowMul3 1) + lowMul3 1 := by
    rw [add_assoc, anf_add_self, add_zero]
  rw [hs]
  exact h.add degreeLE_two_lowMul3_one

/-- A target of degree `> 2` that the third gate cannot place is not in `V₄`. -/
theorem not_mem_sup_of_noPlace {V : Submodule F₂ (ANF 6)} (hV : ∀ p ∈ V, DegreeLE 2 p)
    {g T : ANF 6} (hT : ¬ DegreeLE 2 T) (hg : g + T ∈ V → False)
    (hmem : T ∈ V ⊔ Submodule.span F₂ {g}) : False := by
  obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rcases f2_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, add_zero] at hvw
    exact hT (hvw ▸ hV v hv)
  · rw [one_smul] at hvw
    apply hg
    rw [← hvw, add_comm v, ← add_assoc, anf_add_self, zero_add]
    exact hv

/-- **Proof of the Theorem, first part.** From Lemma C: `z₁ ∈ V₄` and
`g₄ ∈ z₂ + V₄`. -/
theorem flow {V : Submodule F₂ (ANF 6)} (hV : ∀ p ∈ V, DegreeLE 2 p) {g3 g4 : ANF 6}
    (hC2 : g3 + lowMul3 2 ∈ V → False) (hC21 : g3 + (lowMul3 2 + lowMul3 1) ∈ V → False)
    (hz1 : lowMul3 1 ∈ (V ⊔ Submodule.span F₂ {g3}) ⊔ Submodule.span F₂ {g4})
    (hz2 : lowMul3 2 ∈ (V ⊔ Submodule.span F₂ {g3}) ⊔ Submodule.span F₂ {g4}) :
    lowMul3 1 ∈ V ⊔ Submodule.span F₂ {g3} ∧ g4 + lowMul3 2 ∈ V ⊔ Submodule.span F₂ {g3} := by
  obtain ⟨v2, hv2, w2, hw2, h2⟩ := Submodule.mem_sup.mp hz2
  obtain ⟨c2, rfl⟩ := Submodule.mem_span_singleton.mp hw2
  obtain ⟨v1, hv1, w1, hw1, h1⟩ := Submodule.mem_sup.mp hz1
  obtain ⟨c1, rfl⟩ := Submodule.mem_span_singleton.mp hw1
  rcases f2_eq_zero_or_one c2 with rfl | rfl
  · rw [zero_smul, add_zero] at h2
    exact (not_mem_sup_of_noPlace hV not_degreeLE_two_lowMul3_two hC2 (h2 ▸ hv2)).elim
  rw [one_smul] at h2
  have hg4 : g4 + lowMul3 2 = v2 := by
    rw [← h2, add_comm v2, ← add_assoc, anf_add_self, zero_add]
  rcases f2_eq_zero_or_one c1 with rfl | rfl
  · rw [zero_smul, add_zero] at h1
    exact ⟨h1 ▸ hv1, hg4 ▸ hv2⟩
  · exfalso
    rw [one_smul] at h1
    have hs : lowMul3 2 + lowMul3 1 = v2 + v1 := by
      rw [← h2, ← h1, add_add_add_comm, anf_add_self, add_zero]
    exact not_mem_sup_of_noPlace hV not_degreeLE_two_z2_add_z1 hC21
      (hs ▸ Submodule.add_mem _ hv2 hv1)

/-! ## Lemma B3U: `Z₁ ∈ Q₃` forces `Q₃ ⊆ Λ²(U)` -/

theorem f2_swap3 : ∀ x y z : F₂, y + z = x + y + z + x := by decide

theorem phi_of_Z1_mem {l1 r1 l2 r2 : Fin 6 → F₂} (h : Z1form ∈ Q3span l1 r1 l2 r2) :
    ∀ ω ∈ Q3span l1 r1 l2 r2, Phi ω = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F₂).mp h
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hc
  have hgen : Phi (wedge l1 r1) = 0 ∧ Phi (wedge l2 r2) = 0 := by
    rcases f2_eq_zero_or_one (c 1) with h1 | h1 <;>
      rcases f2_eq_zero_or_one (c 2) with h2 | h2 <;> rw [h1, h2] at hc
    · simp only [zero_smul, add_zero] at hc; exact (none_false hc).elim
    · simp only [zero_smul, one_smul, add_zero] at hc; exact (single_false hc).elim
    · simp only [zero_smul, one_smul, add_zero] at hc; exact (single_false hc).elim
    · simp only [one_smul] at hc
      have h12 : wedge l1 r1 + wedge l2 r2 = Z1form + c 0 • P0form := by
        rw [← hc]; funext i j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact f2_swap3 _ _ _
      have h21 : wedge l2 r2 + wedge l1 r1 = Z1form + c 0 • P0form := by
        rw [add_comm]; exact h12
      exact ⟨lemma3 h12, lemma3 h21⟩
  have hle : Q3span l1 r1 l2 r2 ≤ LinearMap.ker Phi := by
    rw [Q3span, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact phi_P0
    · exact hgen.1
    · exact hgen.2
  intro ω hω
  exact hle hω

/-! ## The third quadratic span of a `λ = 3` circuit -/

theorem gateQ_three (D : Circuit 6 5) (hg0 : D.gate 0 = aVar 3 0 * bVar 3 0)
    (hlin : ∀ i : Fin 5, i.val < 3 → IsLinearGate D i) :
    gateQ D 3 = Q3span (lin (D.left 1)) (lin (D.right 1)) (lin (D.left 2)) (lin (D.right 2)) := by
  have hp : ∀ i : Fin 5, i.val < 3 → i ≠ 0 → pi2 (D.gate i) = wedge (lin (D.left i)) (lin (D.right i)) :=
    fun i hi _ => by rw [D.gate_eq i]; exact pi2_mul_affine (hlin i hi).1 (hlin i hi).2
  have hset : pi2 '' prefixGates D.gate 3 =
      Set.range ![P0form, wedge (lin (D.left 1)) (lin (D.right 1)),
        wedge (lin (D.left 2)) (lin (D.right 2))] := by
    ext ω
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      rcases i with ⟨_ | _ | _ | n, hn⟩
      · exact ⟨0, by show P0form = pi2 (D.gate 0); rw [hg0, pi2_a0b0]⟩
      · exact ⟨1, by show wedge _ _ = pi2 (D.gate 1); rw [hp 1 (by decide) (by decide)]⟩
      · exact ⟨2, by show wedge _ _ = pi2 (D.gate 2); rw [hp 2 (by decide) (by decide)]⟩
      · exact absurd hi (by simp)
    · rintro ⟨k, rfl⟩
      fin_cases k
      · exact ⟨D.gate 0, ⟨0, by decide, rfl⟩, by show pi2 (D.gate 0) = P0form; rw [hg0, pi2_a0b0]⟩
      · exact ⟨D.gate 1, ⟨1, by decide, rfl⟩, hp 1 (by decide) (by decide)⟩
      · exact ⟨D.gate 2, ⟨2, by decide, rfl⟩, hp 2 (by decide) (by decide)⟩
  rw [gateQ, hset, Q3span]

/-! ## `λ = 3` from the two claims -/

theorem wireSpace_four_eq (D : Circuit 6 5) :
    wireSpace D.gate 4 = wireSpace D.gate 3 ⊔ Submodule.span F₂ {D.gate 3} := by
  show wireSpace D.gate (3 + 1) = _
  rw [N4.wireSpace_succ D.gate (by norm_num)]
  rfl

/-- **Theorem (`λ = 3`) of `lambda3_proof.tex`, from `BadClaim` and `B3Claim`.** -/
theorem lambdaCase_three_of (hbad : BadClaim) (hB3 : B3Claim) : LambdaCase 3 := by
  intro D hD hg0 _ _ hlam
  have hlin : ∀ i : Fin 5, i.val < 3 → IsLinearGate D i := fun i hi => (hlam i).mp hi
  set Q := Q3span (lin (D.left 1)) (lin (D.right 1)) (lin (D.left 2)) (lin (D.right 2))
    with hQdef
  have hV3 : wireSpace D.gate 3 = V4 Q := by rw [wireSpace_eq_V4 D 3 hlin, gateQ_three D hg0 hlin]
  have hW4 : wireSpace D.gate 4 = V4 Q ⊔ Submodule.span F₂ {D.gate 3} := by
    rw [wireSpace_four_eq, hV3]
  have hVdeg : ∀ p ∈ V4 Q, DegreeLE 2 p := fun p hp => hp.1
  have hL3 : D.left 3 ∈ V4 Q := by rw [← hV3]; exact D.left_mem 3
  have hR3 : D.right 3 ∈ V4 Q := by rw [← hV3]; exact D.right_mem 3
  have hL4 : D.left 4 ∈ V4 Q ⊔ Submodule.span F₂ {D.gate 3} := by rw [← hW4]; exact D.left_mem 4
  have hR4 : D.right 4 ∈ V4 Q ⊔ Submodule.span F₂ {D.gate 3} := by
    rw [← hW4]; exact D.right_mem 4
  have hfin : D.finalWire = (V4 Q ⊔ Submodule.span F₂ {D.gate 3}) ⊔
      Submodule.span F₂ {D.gate 4} := by rw [finalWire_five_eq, hW4]
  have hz1 := hD 1
  have hz2 := hD 2
  rw [hfin] at hz1 hz2
  -- Lemma C.
  have hC : NoPlace Q (lowMul3 2) ∧ NoPlace Q (lowMul3 2 + lowMul3 1) := by
    by_cases hgood : GoodDir Q
    · exact noPlace_of_goodDir hgood
    · exact (hbad _ _ _ _ hgood).2
  obtain ⟨hz1V4, hg4⟩ := flow hVdeg
    (fun h => hC.1 (D.left 3) (D.right 3) hL3 hR3 (by rw [← D.gate_eq 3]; exact h))
    (fun h => hC.2 (D.left 3) (D.right 3) hL3 hR3 (by rw [← D.gate_eq 3]; exact h)) hz1 hz2
  obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hz1V4
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rcases f2_eq_zero_or_one c with rfl | rfl
  · -- `z₁ ∈ V₃`: `Z₁ ∈ Q₃`, so `Q₃ ⊆ Λ²(U)` (case B3).
    rw [zero_smul, add_zero] at hvw
    have hZ : Z1form ∈ Q := by rw [← pi2_lowMul3_one, ← hvw]; exact hv.2
    rw [D.gate_eq 3] at hL4 hR4 hg4
    exact hB3 Q (phi_of_Z1_mem hZ) (D.left 3) (D.right 3) (D.left 4) (D.right 4) hL3 hR3
      hL4 hR4 (by rw [← D.gate_eq 4]; exact hg4)
  · -- `g₃ ∈ z₁ + V₃`.
    rw [one_smul] at hvw
    have hg3 : D.gate 3 + lowMul3 1 ∈ V4 Q := by
      rw [← hvw, add_comm v, ← add_assoc, anf_add_self, zero_add]; exact hv
    by_cases hgood : GoodDir Q
    · have hle : V4 Q ⊔ Submodule.span F₂ {D.gate 3} ≤
          V4 (Q ⊔ Submodule.span F₂ {Z1form}) := by
        apply sup_le (V4_mono le_sup_left)
        rw [Submodule.span_le, Set.singleton_subset_iff]
        have hs : D.gate 3 = (D.gate 3 + lowMul3 1) + lowMul3 1 := by
          rw [add_assoc, anf_add_self, add_zero]
        show D.gate 3 ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form})
        rw [hs]
        exact Submodule.add_mem _ (V4_mono le_sup_left hg3) (z1_mem_V4_sup Q)
      exact starFree_of_goodDir (goodDir_sup_Z1 hgood) (D.left 4) (D.right 4) (hle hL4) (hle hR4)
        (by rw [← D.gate_eq 4]; exact hle hg4)
    · exact (hbad _ _ _ _ hgood).1 (D.left 3) (D.right 3) hL3 hR3
        (by rw [← D.gate_eq 3]; exact hg3)

/-- `MC(lowMul3) = 6` from `LambdaCase 1`, `LambdaCase 2` and the two `λ = 3`
claims. -/
theorem mc_eq_six_of_claims (h1 : LambdaCase 1) (h2 : LambdaCase 2) (hbad : BadClaim)
    (hB3 : B3Claim) : MC(lowMul3) = 6 :=
  mc_eq_six_of_lambda_cases h1 h2 (lambdaCase_three_of hbad hB3)

end

end LowHalfMul3

end UnrestrictedBooleanMul
