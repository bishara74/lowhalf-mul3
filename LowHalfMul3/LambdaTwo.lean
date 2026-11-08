module

public import LowHalfMul3.LemmaC

@[expose] public section

/-!
# The two-linear-gate case (`λ = 2`): reduction to one claim

Notation as in `lambda2_proof.tex`: the linear prefix is `g₀ = a₀b₀` and
`g₁ = L₁R₁`, so `Q = span{P₀, P}` with `P = l ∧ r` (written `Q3span l r 0 0`),
`S = Q + ⟨Z₁⟩`, and `V₃ = V(Q) + ⟨g₂⟩` with `g₂ = f h`, `f, h ∈ V(Q)`.

The Lean route differs from the paper. Neither the split on `deg g₂` nor the
replacement lemma (and hence Lemma P) is used. Instead:

* **`z₁ ∈ V₃`.** Then `g₂ ∈ z₁ + V(Q)`. Outside `Λ²(U)` this is impossible
  (`noPlace_z1_two`: the λ = 3 derivative argument of Lemma A, Lemma W and
  Lemma 3). Inside `Λ²(U)`, `V₃ ⊆ V(S)` with `S ⊆ Λ²(U)`, and the two remaining
  gates are excluded by the coset lemma (`b3Claim`).
* **`z₁ ∉ V₃`.** As in the proof of the theorem in the paper, `g₃` places `z₁`,
  so the space before the last gate lies in `V(S) + ⟨g₂⟩`, and everything
  follows from Proposition `onehigh` (`OneHigh`). Inside `Λ²(U)` this is again
  the coset lemma (`oneHigh_of_phi`).

The one remaining statement is `TwoClaim`: Proposition `onehigh` for
`P ∉ Λ²(U)`. `lambdaCase_two_of : TwoClaim → LambdaCase 2`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- **Proposition `onehigh` of `lambda2_proof.tex`.** For `g = f h` with
`f, h ∈ V(Q)` and `S = Q + ⟨Z₁⟩`: `z₂ ∉ V(S) + ⟨g⟩`, and no product of two
elements of `V(S) + ⟨g⟩` lies in `z₂ + V(S) + ⟨g⟩`. -/
def OneHigh (Q : Submodule F₂ TwoForm6) : Prop :=
  ∀ f h : ANF 6, f ∈ V4 Q → h ∈ V4 Q →
    (lowMul3 2 ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) ⊔ Submodule.span F₂ {f * h} → False) ∧
    ∀ F H : ANF 6,
      F ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) ⊔ Submodule.span F₂ {f * h} →
      H ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) ⊔ Submodule.span F₂ {f * h} →
      F * H + lowMul3 2 ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) ⊔ Submodule.span F₂ {f * h} →
      False

/-- **The open statement of the `λ = 2` case**: Proposition `onehigh` for
`Q = span{P₀, l ∧ r}` with `l ∧ r ∉ Λ²(U)`. -/
def TwoClaim : Prop :=
  ∀ l r : Fin 6 → F₂, Phi (wedge l r) ≠ 0 → OneHigh (Q3span l r 0 0)

/-! ## The quadratic span of a `λ = 2` circuit -/

theorem gateQ_two (D : Circuit 6 5) (hg0 : D.gate 0 = aVar 3 0 * bVar 3 0)
    (hlin : ∀ i : Fin 5, i.val < 2 → IsLinearGate D i) :
    gateQ D 2 = Q3span (lin (D.left 1)) (lin (D.right 1)) 0 0 := by
  have hp1 : pi2 (D.gate 1) = wedge (lin (D.left 1)) (lin (D.right 1)) := by
    rw [D.gate_eq 1]; exact pi2_mul_affine (hlin 1 (by decide)).1 (hlin 1 (by decide)).2
  have hp0 : pi2 (D.gate 0) = P0form := by rw [hg0, pi2_a0b0]
  apply le_antisymm
  · rw [gateQ, Submodule.span_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    rcases i with ⟨_ | _ | n, hn⟩
    · exact Submodule.subset_span ⟨0, by show P0form = pi2 (D.gate 0); rw [hp0]⟩
    · exact Submodule.subset_span ⟨1, by show wedge _ _ = pi2 (D.gate 1); rw [hp1]⟩
    · exact absurd hi (by simp)
  · rw [Q3span, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨D.gate 0, ⟨0, by decide, rfl⟩, hp0⟩
    · exact Submodule.subset_span ⟨D.gate 1, ⟨1, by decide, rfl⟩, hp1⟩
    · show wedge 0 0 ∈ gateQ D 2
      rw [wedge_self]; exact Submodule.zero_mem _

theorem wireSpace_three_eq (D : Circuit 6 5) :
    wireSpace D.gate 3 = wireSpace D.gate 2 ⊔ Submodule.span F₂ {D.gate 2} := by
  show wireSpace D.gate (2 + 1) = _
  rw [N4.wireSpace_succ D.gate (by norm_num)]
  rfl

/-- `Z₁ ∉ span{P₀, l ∧ r}` (Lemma 3: `Z₁`, `Z₁ + P₀` are not rank two). -/
theorem Z1_not_mem_two (l r : Fin 6 → F₂) : Z1form ∉ Q3span l r 0 0 := by
  intro h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F₂).mp h
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, wedge_self, smul_zero, add_zero] at hc
  rcases f2_eq_zero_or_one (c 1) with h1 | h1 <;> rw [h1] at hc
  · simp only [zero_smul, add_zero] at hc; exact none_false hc
  · simp only [one_smul] at hc; exact single_false hc

theorem z1_not_mem_V4_two (l r : Fin 6 → F₂) : lowMul3 1 ∉ V4 (Q3span l r 0 0) :=
  fun h => Z1_not_mem_two l r (by rw [← pi2_lowMul3_one]; exact h.2)

/-- Inside `Λ²(U)`, all of `S = span{P₀, l ∧ r, Z₁}` lies in `Λ²(U)`. -/
theorem phi_S_two {l r : Fin 6 → F₂} (hP : Phi (wedge l r) = 0) :
    ∀ ω ∈ Q3span l r 0 0 ⊔ Submodule.span F₂ {Z1form}, Phi ω = 0 := by
  have hle : Q3span l r 0 0 ⊔ Submodule.span F₂ {Z1form} ≤ LinearMap.ker Phi := by
    apply sup_le
    · rw [Q3span, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      fin_cases k
      · exact phi_P0
      · exact hP
      · show Phi (wedge 0 0) = 0
        rw [wedge_self, map_zero]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      show Phi Z1form = 0
      have := phi_Z 0
      rwa [zero_smul, add_zero] at this
  intro ω hω
  exact hle hω

/-- **Proposition `onehigh` inside `Λ²(U)`**: the coset lemma (B3a/B3b) for the
base `V(S)`. -/
theorem oneHigh_of_phi {Q : Submodule F₂ TwoForm6}
    (hS : ∀ ω ∈ Q ⊔ Submodule.span F₂ {Z1form}, Phi ω = 0) : OneHigh Q := by
  intro f h hf hh
  have hle : V4 Q ≤ V4 (Q ⊔ Submodule.span F₂ {Z1form}) := V4_mono le_sup_left
  exact ⟨fun hz => coset_z2_not_mem (cosetBase_V4 hS) (hle hf) (hle hh) hz,
    fun F H hF hH hFH => b3Claim _ hS f h F H (hle hf) (hle hh) hF hH hFH⟩

/-! ## `g₂` cannot place `z₁` outside `Λ²(U)` -/

/-- A `U`-direction killing two linear forms that are not both internal. -/
theorem kill_two_fin : ∀ l1 l2 l4 l5 r1 r2 r4 r5 : F₂,
    ¬ (l2 = 0 ∧ l5 = 0 ∧ r2 = 0 ∧ r5 = 0) →
    ∃ e1 e2 e4 e5 : F₂, (e1 = 1 ∨ e4 = 1) ∧ l1 * e1 + l2 * e2 + l4 * e4 + l5 * e5 = 0 ∧
      r1 * e1 + r2 * e2 + r4 * e4 + r5 * e5 = 0 := by
  decide

theorem genDir_two {l r : Fin 6 → F₂} (hP : Phi (wedge l r) ≠ 0) :
    GenDir (Q3span l r 0 0) := by
  have hext : ¬ (l 2 = 0 ∧ l 5 = 0 ∧ r 2 = 0 ∧ r 5 = 0) := by
    rintro ⟨h2, h5, h2', h5'⟩
    apply hP
    apply phi_eq_zero_of_rows
    intro t
    simp [wedge_apply, h2, h5, h2', h5']
  obtain ⟨e1, e2, e4, e5, hU, hl, hr⟩ :=
    kill_two_fin (l 1) (l 2) (l 4) (l 5) (r 1) (r 2) (r 4) (r 5) hext
  refine genDir_of_uDir (uDir_of_kill (mkDir e1 e2 e4 e5) rfl rfl hU ?_ ?_)
  · exact iota_kill (by rw [dotv_mkDir]; exact hl) (by rw [dotv_mkDir]; exact hr)
  · intro _ _
    rw [wedge_self, map_zero]

theorem f2_rearr_c0 : ∀ p w z : F₂, p = w + z → w = z + p := by decide

theorem f2_rearr_c1 : ∀ p q w z : F₂, p + q = w + z → q + w = z + p := by decide

/-- **`g₂` does not place `z₁` when `P ∉ Λ²(U)`.** Lemma A's derivative argument
(`z1_place_vanish`), Lemma W and Lemma 3. -/
theorem noPlace_z1_two {l r : Fin 6 → F₂} (hP : Phi (wedge l r) ≠ 0) :
    NoPlace (Q3span l r 0 0) (lowMul3 1) := by
  intro f h hf hh hfh
  obtain ⟨G, hGdeg, hGQ, a, α, ha, hvan⟩ := z1_place_vanish (genDir_two hP) hf hh hfh
  obtain ⟨m, hm⟩ := pi2_wedge_of_vanish hGdeg ha hvan
  rw [hm] at hGQ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F₂).mp hGQ
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, wedge_self, smul_zero, add_zero] at hc
  rcases f2_eq_zero_or_one (c 1) with h1 | h1 <;> rw [h1] at hc
  · simp only [zero_smul, add_zero] at hc
    apply wedge_ne_Z a m (c 0)
    funext i j
    have := congrFun (congrFun hc i) j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    exact f2_rearr_c0 _ _ _ this
  · simp only [one_smul] at hc
    apply hP
    refine lemma3 (l' := a) (r' := m) (c0 := c 0) ?_
    funext i j
    have := congrFun (congrFun hc i) j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    exact f2_rearr_c1 _ _ _ _ this

/-! ## The reduction -/

/-- Membership in `W ⊔ ⟨p⟩` in characteristic two. -/
theorem mem_sup_span_cases {W : Submodule F₂ (ANF 6)} {p x : ANF 6}
    (hx : x ∈ W ⊔ Submodule.span F₂ {p}) : x ∈ W ∨ p + x ∈ W := by
  obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rcases f2_eq_zero_or_one c with rfl | rfl
  · left
    rw [zero_smul, add_zero] at hvw
    rw [← hvw]; exact hv
  · right
    rw [one_smul] at hvw
    rw [← hvw, add_comm v p, ← add_assoc, anf_add_self, zero_add]; exact hv

/-- One product beyond `W` cannot reach `T` if `W` and its products do not. -/
theorem not_mem_after_product {W : Submodule F₂ (ANF 6)} {T : ANF 6}
    (hi : T ∈ W → False) (hii : ∀ F H : ANF 6, F ∈ W → H ∈ W → F * H + T ∈ W → False)
    {F H : ANF 6} (hF : F ∈ W) (hH : H ∈ W) (hT : T ∈ W ⊔ Submodule.span F₂ {F * H}) :
    False := by
  rcases mem_sup_span_cases hT with h | h
  · exact hi h
  · exact hii F H hF hH h

/-- **Theorem (`λ = 2`) of `lambda2_proof.tex`, from `TwoClaim`.** -/
theorem lambdaCase_two_of (hclaim : TwoClaim) : LambdaCase 2 := by
  intro D hD hg0 _ _ hlam
  have hlin : ∀ i : Fin 5, i.val < 2 → IsLinearGate D i := fun i hi => (hlam i).mp hi
  set Q := Q3span (lin (D.left 1)) (lin (D.right 1)) 0 0 with hQdef
  set S := Q ⊔ Submodule.span F₂ {Z1form} with hSdef
  have hV2 : wireSpace D.gate 2 = V4 Q := by
    rw [wireSpace_eq_V4 D 2 hlin, gateQ_two D hg0 hlin]
  have hV3 : wireSpace D.gate 3 = V4 Q ⊔ Submodule.span F₂ {D.left 2 * D.right 2} := by
    rw [wireSpace_three_eq, hV2, D.gate_eq 2]
  have hW4 : wireSpace D.gate 4 = (V4 Q ⊔ Submodule.span F₂ {D.left 2 * D.right 2}) ⊔
      Submodule.span F₂ {D.left 3 * D.right 3} := by
    rw [wireSpace_four_eq, hV3, D.gate_eq 3]
  have hfin : D.finalWire = ((V4 Q ⊔ Submodule.span F₂ {D.left 2 * D.right 2}) ⊔
      Submodule.span F₂ {D.left 3 * D.right 3}) ⊔ Submodule.span F₂ {D.left 4 * D.right 4} := by
    rw [finalWire_five_eq, hW4, D.gate_eq 4]
  have hf : D.left 2 ∈ V4 Q := by rw [← hV2]; exact D.left_mem 2
  have hh : D.right 2 ∈ V4 Q := by rw [← hV2]; exact D.right_mem 2
  have hL3 : D.left 3 ∈ V4 Q ⊔ Submodule.span F₂ {D.left 2 * D.right 2} := by
    rw [← hV3]; exact D.left_mem 3
  have hR3 : D.right 3 ∈ V4 Q ⊔ Submodule.span F₂ {D.left 2 * D.right 2} := by
    rw [← hV3]; exact D.right_mem 3
  have hL4 : D.left 4 ∈ (V4 Q ⊔ Submodule.span F₂ {D.left 2 * D.right 2}) ⊔
      Submodule.span F₂ {D.left 3 * D.right 3} := by
    rw [← hW4]; exact D.left_mem 4
  have hR4 : D.right 4 ∈ (V4 Q ⊔ Submodule.span F₂ {D.left 2 * D.right 2}) ⊔
      Submodule.span F₂ {D.left 3 * D.right 3} := by
    rw [← hW4]; exact D.right_mem 4
  have hz1 := hD 1
  have hz2 := hD 2
  rw [hfin] at hz1 hz2
  set V3 := V4 Q ⊔ Submodule.span F₂ {D.left 2 * D.right 2} with hV3def
  set V4' := V3 ⊔ Submodule.span F₂ {D.left 3 * D.right 3} with hV4def
  have hz1S : lowMul3 1 ∈ V4 S := z1_mem_V4_sup Q
  have hQS : V4 Q ≤ V4 S := V4_mono le_sup_left
  by_cases hz1V3 : lowMul3 1 ∈ V3
  · -- `g₂` places `z₁`: `g₂ ∈ z₁ + V(Q)`.
    rcases mem_sup_span_cases hz1V3 with h0 | h1
    · exact z1_not_mem_V4_two _ _ h0
    by_cases hP : Phi (wedge (lin (D.left 1)) (lin (D.right 1))) = 0
    · -- Inside `Λ²(U)`: `V₃ ⊆ V(S)`, then the coset lemma.
      have hS := phi_S_two hP
      have hle : V3 ≤ V4 S := by
        apply sup_le hQS
        rw [Submodule.span_le, Set.singleton_subset_iff]
        show D.left 2 * D.right 2 ∈ V4 S
        have hs : D.left 2 * D.right 2 =
            (D.left 2 * D.right 2 + lowMul3 1) + lowMul3 1 := by
          rw [add_assoc, anf_add_self, add_zero]
        rw [hs]
        exact (V4 S).add_mem (hQS h1) hz1S
      have hle4 : V4' ≤ V4 S ⊔ Submodule.span F₂ {D.left 3 * D.right 3} :=
        sup_le_sup_right hle _
      rcases mem_sup_span_cases hz2 with h2 | h2
      · exact coset_z2_not_mem (cosetBase_V4 hS) (hle hL3) (hle hR3) (hle4 h2)
      · exact b3Claim S hS (D.left 3) (D.right 3) (D.left 4) (D.right 4) (hle hL3) (hle hR3)
          (hle4 hL4) (hle4 hR4) (hle4 h2)
    · exact noPlace_z1_two hP (D.left 2) (D.right 2) hf hh h1
  · -- `z₁ ∉ V₃`: Proposition `onehigh` for `V(S) + ⟨g₂⟩`.
    have hOH : OneHigh Q := by
      by_cases hP : Phi (wedge (lin (D.left 1)) (lin (D.right 1))) = 0
      · exact oneHigh_of_phi (phi_S_two hP)
      · exact hclaim _ _ hP
    obtain ⟨hi, hii⟩ := hOH (D.left 2) (D.right 2) hf hh
    set W := V4 S ⊔ Submodule.span F₂ {D.left 2 * D.right 2} with hWdef
    have hz1W : lowMul3 1 ∈ W := Submodule.mem_sup_left hz1S
    have hV3W : V3 ≤ W := sup_le_sup_right hQS _
    have hi' : lowMul3 2 + lowMul3 1 ∈ W → False := fun h => hi (by
      have hs : lowMul3 2 = (lowMul3 2 + lowMul3 1) + lowMul3 1 := by
        rw [add_assoc, anf_add_self, add_zero]
      rw [hs]; exact W.add_mem h hz1W)
    have hii' : ∀ F H : ANF 6, F ∈ W → H ∈ W → F * H + (lowMul3 2 + lowMul3 1) ∈ W → False :=
      fun F H hF hH h => hii F H hF hH (by
        have hs : F * H + lowMul3 2 = (F * H + (lowMul3 2 + lowMul3 1)) + lowMul3 1 := by
          rw [add_assoc, add_assoc, anf_add_self, add_zero]
        rw [hs]; exact W.add_mem h hz1W)
    -- Neither `z₂` nor `z₂ + z₁` lies in `V₄`.
    have hV4W : V4' ≤ W ⊔ Submodule.span F₂ {D.left 3 * D.right 3} := sup_le_sup_right hV3W _
    have hno2 : lowMul3 2 ∈ V4' → False := fun h =>
      not_mem_after_product hi hii (hV3W hL3) (hV3W hR3) (hV4W h)
    have hno21 : lowMul3 2 + lowMul3 1 ∈ V4' → False := fun h =>
      not_mem_after_product hi' hii' (hV3W hL3) (hV3W hR3) (hV4W h)
    -- So `z₁ ∈ V₄`.
    have hz1V4 : lowMul3 1 ∈ V4' := by
      rcases mem_sup_span_cases hz1 with h | h
      · exact h
      exfalso
      rcases mem_sup_span_cases hz2 with h2 | h2
      · exact hno2 h2
      apply hno21
      have hs : lowMul3 2 + lowMul3 1 = (D.left 4 * D.right 4 + lowMul3 2) +
          (D.left 4 * D.right 4 + lowMul3 1) := by
        rw [add_add_add_comm, anf_add_self, zero_add]
      rw [hs]
      exact V4'.add_mem h2 h
    -- `g₃` places `z₁`, so `V₄ ⊆ V(S) + ⟨g₂⟩`.
    have hV4'W : V4' ≤ W := by
      apply sup_le hV3W
      rw [Submodule.span_le, Set.singleton_subset_iff]
      show D.left 3 * D.right 3 ∈ W
      rcases mem_sup_span_cases hz1V4 with h | h
      · exact absurd h hz1V3
      have hs : D.left 3 * D.right 3 = (D.left 3 * D.right 3 + lowMul3 1) + lowMul3 1 := by
        rw [add_assoc, anf_add_self, add_zero]
      rw [hs]
      exact W.add_mem (hV3W h) hz1W
    -- The last gate.
    rcases mem_sup_span_cases hz2 with h | h
    · exact hi (hV4'W h)
    · exact hii (D.left 4) (D.right 4) (hV4'W hL4) (hV4'W hR4) (hV4'W h)

/-- `MC(lowMul3) = 6` from `LambdaCase 1` and `TwoClaim`. -/
theorem mc_eq_six_of_twoClaim (h1 : LambdaCase 1) (h2 : TwoClaim) : MC(lowMul3) = 6 :=
  mc_eq_six_of_lambda_one_two h1 (lambdaCase_two_of h2)

end

end LowHalfMul3

end UnrestrictedBooleanMul
