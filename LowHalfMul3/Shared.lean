module

public import LowHalfMul3.IdealExtract
public import LowHalfMul3.LambdaOneOrdinary
public import LowHalfMul3.LemmaA

@[expose] public section

/-!
# Shared statements for `λ = 2` and `λ = 1`

Proofs of the shared statements of `LowHalfMul3.LambdaOneBase`, exactly as stated
there.

* `feedbackNormal : FeedbackNormal`. A product `F H` with `F, H ∈ A + ⟨g⟩` either has
  both factors in `A`, or normalizes to `k (g + a)` with `k, a ∈ A`. Write
  `F = F' + s g` and `H = H' + t g`. Then `(F' + g) H' = H' (g + F')`, and
  `(F' + g)(H' + g) = (F' + H' + 1)(g + F')` because `g g = g`. A `σ g` output
  correction is absorbed by replacing `k` with `k + σ`.
* `q2NotTwoWedges : Q2NotTwoWedges`, the rank part of Lemma `rankext` of
  `lambda2_proof.tex`. A sum of two rank-two forms has a nonzero radical vector:
  four linear forms on `F₂⁶` have a common nonzero zero (`exists_orth4`, by
  rank–nullity). But `q₂ + ε Z₁ + α P₀` has zero radical: `ι_e` of it is nonzero for
  every `e ≠ 0` (`q2_iota_ne_zero`, 256 cases).
* `feedbackNoPlaceModLow : FeedbackNoPlaceModLow` combines quadratic ideal
  extraction with the rank obstruction.
-/

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

local notation "⟪" p "⟫" => singleton p

theorem anf_ext_eval {p q : A6} (h : ∀ x : Vec, eval p x = eval q x) : p = q :=
  eval_injective 6 (funext h)

/-! ## `FeedbackNormal` -/

theorem f2_norm01 : ∀ f h g t a σ : F₂,
    f * (h + g) + t = a + σ * g → (f + σ) * (g + h) + t = a + σ * h := by decide

theorem f2_norm10 : ∀ f h g t a σ : F₂,
    (f + g) * h + t = a + σ * g → (h + σ) * (g + f) + t = a + σ * f := by decide

theorem f2_norm11 : ∀ f h g t a σ : F₂,
    (f + g) * (h + g) + t = a + σ * g → (f + h + (1 + σ)) * (g + f) + t = a + σ * f := by
  decide

theorem feedbackNormal : FeedbackNormal := by
  intro A h1 g F H T hF hH hFH
  obtain ⟨F', hF', s, rfl⟩ := mem_extend.mp hF
  obtain ⟨H', hH', t, rfl⟩ := mem_extend.mp hH
  obtain ⟨a, ha, σ, hσ⟩ := mem_extend.mp hFH
  have hσx : ∀ x : Vec, eval ((F' + s • g) * (H' + t • g) + T) x = eval (a + σ • g) x :=
    fun x => by rw [hσ]
  rcases f2_eq_zero_or_one s with rfl | rfl <;> rcases f2_eq_zero_or_one t with rfl | rfl
  · left
    refine ⟨F', H', hF', hH', ?_⟩
    simpa only [zero_smul, add_zero] using hFH
  · right
    refine ⟨F' + σ • (1 : A6), H', A.add_mem hF' (A.smul_mem σ h1), hH', ?_⟩
    have he : (F' + σ • (1 : A6)) * (g + H') + T = a + σ • H' := anf_ext_eval fun x => by
      have hx := hσx x
      simp only [zero_smul, add_zero, one_smul, eval_add', eval_mul', eval_smul', eval_one',
        mul_one] at hx ⊢
      exact f2_norm01 _ _ _ _ _ _ hx
    rw [he]
    exact A.add_mem ha (A.smul_mem σ hH')
  · right
    refine ⟨H' + σ • (1 : A6), F', A.add_mem hH' (A.smul_mem σ h1), hF', ?_⟩
    have he : (H' + σ • (1 : A6)) * (g + F') + T = a + σ • F' := anf_ext_eval fun x => by
      have hx := hσx x
      simp only [zero_smul, add_zero, one_smul, eval_add', eval_mul', eval_smul', eval_one',
        mul_one] at hx ⊢
      exact f2_norm10 _ _ _ _ _ _ hx
    rw [he]
    exact A.add_mem ha (A.smul_mem σ hF')
  · right
    refine ⟨F' + H' + (1 + σ) • (1 : A6), F',
      A.add_mem (A.add_mem hF' hH') (A.smul_mem _ h1), hF', ?_⟩
    have he : (F' + H' + (1 + σ) • (1 : A6)) * (g + F') + T = a + σ • F' :=
      anf_ext_eval fun x => by
        have hx := hσx x
        simp only [one_smul, eval_add', eval_mul', eval_smul', eval_one',
          mul_one] at hx ⊢
        exact f2_norm11 _ _ _ _ _ _ hx
    rw [he]
    exact A.add_mem ha (A.smul_mem σ hF')

/-! ## `Q2NotTwoWedges` -/

set_option maxRecDepth 100000 in
/-- `q₂ + ε Z₁ + α P₀` has zero radical. -/
theorem q2_iota_ne_zero : ∀ e : Vec, e ≠ 0 → ∀ ε α : F₂,
    iota e (q2Form + ε • Z1form + α • P0form) ≠ 0 := by
  decide

/-- Four linear forms on `F₂⁶` have a common nonzero zero. -/
theorem exists_orth4 (l r a b : Vec) :
    ∃ e : Vec, e ≠ 0 ∧ dotv l e = 0 ∧ dotv r e = 0 ∧ dotv a e = 0 ∧ dotv b e = 0 := by
  let M : Matrix (Fin 4) (Fin 6) F₂ := ![l, r, a, b]
  have hk : LinearMap.ker (Matrix.mulVecLin M) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨e, he, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have h : Matrix.mulVec M e = 0 := LinearMap.mem_ker.mp he
  have hrow : ∀ i : Fin 4, dotv (M i) e = 0 := fun i => by
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct, dotv] using this
  exact ⟨e, hne, hrow 0, hrow 1, hrow 2, hrow 3⟩

/-- **Lemma `rankext`, rank part**: `q₂ + ε Z₁ + α P₀ + l ∧ r` is never a wedge. -/
theorem q2NotTwoWedges : Q2NotTwoWedges := by
  intro ε α l r a b h
  obtain ⟨e, hne, hl, hr, ha, hb⟩ := exists_orth4 l r a b
  apply q2_iota_ne_zero e hne ε α
  have := congrArg (iota e) h
  rw [map_add, iota_kill hl hr, iota_kill ha hb, add_zero] at this
  exact this

/-! ## Feedback placement modulo the low-bit ideal -/

private theorem pi2_q2 : pi2 q2 = q2Form := by
  have hcarry : pi2 (monomial carryMonomial.vars : A6) = 0 := by
    funext i j
    rw [pi2_apply]
    split_ifs with hij
    · rfl
    · have hne : carryMonomial.vars ≠ {i, j} := by
        intro he
        have hc := Finset.card_insert_le i ({j} : Finset (Fin 6))
        rw [← he, carryMonomial_card, Finset.card_singleton] at hc
        omega
      simp [hne]
  have h := pi2_lowMul3_two
  rw [show lowMul3 2 = q2 + monomial carryMonomial.vars from z2_eq_q2_add_carry,
    map_add, hcarry, add_zero] at h
  exact h

/-- A product from the quadratic base cannot place the target modulo the low-bit ideal. -/
theorem feedbackNoPlaceModLow : FeedbackNoPlaceModLow := by
  intro l r f h F v hf hh hF hv hm
  have hFv := (V4 (Slr l r)).add_mem hF hv
  obtain ⟨π, hπ, a, b, he⟩ := idealExtract hf hh (q2_degree.add hFv.1)
    (show ModLow (f * h) (q2 + (F + v)) by simpa only [add_assoc] using hm)
  have hS : pi2 (F + v) + π ∈ Slr l r :=
    (Slr l r).add_mem hFv.2 (Submodule.mem_sup_left hπ)
  have hwedge : q2Form + (pi2 (F + v) + π) = wedge a b := by
    rw [map_add, pi2_q2] at he
    rw [← add_assoc, he, add_comm π (wedge a b), add_assoc, tf_add_self, add_zero]
  obtain ⟨q, hq, z, hz, hsum⟩ := Submodule.mem_sup.mp hS
  obtain ⟨ε, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [qlr_eq] at hq
  obtain ⟨p, hp, w, hw, hqsum⟩ := Submodule.mem_sup.mp hq
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hp
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have heq : q2Form + ε • Z1form + α • P0form + β • wedge l r = wedge a b := by
    calc
      _ = q2Form + ((α • P0form + β • wedge l r) + ε • Z1form) := by ac_rfl
      _ = _ := by rw [hqsum, hsum, hwedge]
  rcases f2_eq_zero_or_one β with rfl | rfl
  · apply q2NotTwoWedges ε α l 0 a b
    simpa only [wedge_zero_right, zero_smul, add_zero] using heq
  · exact q2NotTwoWedges ε α l r a b (by simpa only [one_smul] using heq)

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
