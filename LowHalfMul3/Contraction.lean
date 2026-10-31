import LowHalfMul3.Derivative

/-!
# Quadratic parts, contractions, and Lemma 8 as stated in the paper

* `pi2 p` is the quadratic part of `p` as an alternating `6 × 6` matrix over
  `F₂`: `pi2 p i j = coeff_{x_i x_j} p` for `i ≠ j`, and `0` on the diagonal.
  This is the identification `x_i x_j ↔ x_i ∧ x_j` of `lambda4_proof.tex`.
* `iota e ω` is the contraction of a 2-form with a direction `e ∈ F₂⁶`:
  `(iota e ω) j = ∑ i, e i * ω i j`. For `e = a₂` this is `ι_{a₂}`, the
  coefficient vector of the monomials through `a₂`.
* `V4 Q = {p | deg p ≤ 2 ∧ pi2 p ∈ Q}`, the space `V₄(Q)` of the paper.

The bridge (`deriv_add_deriv_zero_eq`) is the statement used in the first
line of the proof of Lemma 8: for `deg p ≤ 2`,

  `D_e p (x) = D_e p (0) + ∑ j, (ι_e (π₂ p)) j * x j`,

i.e. `D_e p` is affine with linear part `ι_e (π₂ p)`. Hence
`D_e p` is constant iff `ι_e (π₂ p) = 0` (`constDeriv_iff_iota_pi2_eq_zero`).

The bridge is proved for the three directions `a₂`, `b₂`, `a₂ + b₂` from a
termwise identity on single monomials of degree at most two, which is a
finite statement (64 subsets × 64 points) checked by `decide`. The expansion
of both sides over the coefficient support is generic.

`derivative_lemma_paper` is then Lemma 8 verbatim: hypothesis `ι_e(Q) = 0`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- Alternating `6 × 6` matrices over `F₂` model 2-forms on `F₂⁶`. -/
abbrev TwoForm6 := Fin 6 → Fin 6 → F₂

/-- The quadratic part of an ANF, as a 2-form. -/
def pi2 : ANF 6 →ₗ[F₂] TwoForm6 where
  toFun p := fun i j => if i = j then 0 else p.coeff ⟨{i, j}⟩
  map_add' p q := by
    funext i j
    by_cases h : i = j <;> simp [h]
  map_smul' c p := by
    funext i j
    by_cases h : i = j <;> simp [h]

theorem pi2_apply (p : ANF 6) (i j : Fin 6) :
    pi2 p i j = if i = j then 0 else p.coeff ⟨{i, j}⟩ := rfl

/-- Contraction of a 2-form with a direction `e`. -/
def iota (e : Fin 6 → F₂) : TwoForm6 →ₗ[F₂] (Fin 6 → F₂) where
  toFun ω := fun j => ∑ i, e i * ω i j
  map_add' ω ω' := by
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c ω := by
    funext j
    simp [Finset.mul_sum, mul_left_comm]

theorem iota_apply (e : Fin 6 → F₂) (ω : TwoForm6) (j : Fin 6) :
    iota e ω j = ∑ i, e i * ω i j := rfl

/-- Contraction is additive in the direction; in particular
`ι_{a₂+b₂} = ι_{a₂} + ι_{b₂}`, as in the paper. -/
theorem iota_add_dir (e e' : Fin 6 → F₂) (ω : TwoForm6) :
    iota (e + e') ω = iota e ω + iota e' ω := by
  funext j
  simp [iota_apply, add_mul, Finset.sum_add_distrib]

theorem dirA2B2_eq : dirA2B2 = dirA2 + dirB2 := by
  funext i
  fin_cases i <;> rfl

theorem iota_dirA2B2 (ω : TwoForm6) : iota dirA2B2 ω = iota dirA2 ω + iota dirB2 ω := by
  rw [dirA2B2_eq, iota_add_dir]

/-- `V₄(Q)`: functions of degree at most two whose quadratic part lies in `Q`. -/
def V4 (Q : Submodule F₂ TwoForm6) : Submodule F₂ (ANF 6) where
  carrier := {p | DegreeLE 2 p ∧ pi2 p ∈ Q}
  add_mem' := by
    rintro p q ⟨hp1, hp2⟩ ⟨hq1, hq2⟩
    exact ⟨hp1.add hq1, by rw [map_add]; exact Q.add_mem hp2 hq2⟩
  zero_mem' := ⟨fun s _ => by simp, by simp⟩
  smul_mem' := by
    rintro c p ⟨hp1, hp2⟩
    exact ⟨hp1.smul c, by rw [map_smul]; exact Q.smul_mem c hp2⟩

theorem mem_V4 {Q : Submodule F₂ TwoForm6} {p : ANF 6} :
    p ∈ V4 Q ↔ DegreeLE 2 p ∧ pi2 p ∈ Q := Iff.rfl

/-! ## Expansion over the coefficient support -/

/-- The left side of the bridge for a single monomial `t`. -/
def termL (e : Fin 6 → F₂) (t : Finset (Fin 6)) (x : Fin 6 → F₂) : F₂ :=
  (∏ i ∈ t, (x i + e i)) + (∏ i ∈ t, x i) + ((∏ i ∈ t, (0 + e i)) + ∏ _i ∈ t, (0 : F₂))

/-- The selector `[i ≠ j][t = {i, j}]`: the quadratic part of the monomial `t`. -/
def sel (t : Finset (Fin 6)) (i j : Fin 6) : F₂ :=
  if i = j then 0 else if t = {i, j} then 1 else 0

/-- The right side of the bridge for a single monomial `t`. -/
def termR (e : Fin 6 → F₂) (t : Finset (Fin 6)) (x : Fin 6 → F₂) : F₂ :=
  ∑ j, (∑ i, e i * sel t i j) * x j

theorem eval_eq_sum_support (p : ANF 6) (y : Fin 6 → F₂) :
    eval p y = ∑ s ∈ p.coeff.support, p.coeff s * ∏ i ∈ s.vars, y i := rfl

theorem lhs_expand (e : Fin 6 → F₂) (p : ANF 6) (x : Fin 6 → F₂) :
    deriv e (eval p) x + deriv e (eval p) 0 =
      ∑ s ∈ p.coeff.support, p.coeff s * termL e s.vars x := by
  simp only [deriv, shiftBy, eval_eq_sum_support, termL, mul_add,
    Finset.sum_add_distrib]
  rfl

theorem pi2_eq_sum (p : ANF 6) (i j : Fin 6) :
    pi2 p i j = ∑ s ∈ p.coeff.support, p.coeff s * sel s.vars i j := by
  rw [pi2_apply]
  by_cases hij : i = j
  · simp [hij, sel]
  · simp only [hij, ↓reduceIte, sel, mul_ite, mul_one, mul_zero]
    have hiff : ∀ s : Monomial 6, (s.vars = {i, j}) ↔ (s = ⟨{i, j}⟩) := by
      intro s
      constructor
      · intro h; exact Monomial.ext h
      · intro h; rw [h]
    simp only [hiff]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · exact Finsupp.notMem_support_iff.mp hmem

theorem rhs_expand (e : Fin 6 → F₂) (p : ANF 6) (x : Fin 6 → F₂) :
    ∑ j, iota e (pi2 p) j * x j =
      ∑ s ∈ p.coeff.support, p.coeff s * termR e s.vars x := by
  simp only [iota_apply, pi2_eq_sum, termR, Finset.mul_sum, Finset.sum_mul]
  calc
    ∑ j, ∑ i, ∑ s ∈ p.coeff.support, e i * (p.coeff s * sel s.vars i j) * x j
        = ∑ j, ∑ s ∈ p.coeff.support, ∑ i, e i * (p.coeff s * sel s.vars i j) * x j :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ s ∈ p.coeff.support, ∑ j, ∑ i, e i * (p.coeff s * sel s.vars i j) * x j :=
          Finset.sum_comm
    _ = ∑ s ∈ p.coeff.support, ∑ j, ∑ i, p.coeff s * (e i * sel s.vars i j * x j) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun i _ => ?_
          ring

/-- The bridge, reduced to the termwise identity on monomials of degree ≤ 2. -/
theorem deriv_add_deriv_zero_eq_of_termwise (e : Fin 6 → F₂)
    (hterm : ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL e t x = termR e t x)
    (p : ANF 6) (hp : DegreeLE 2 p) (x : Fin 6 → F₂) :
    deriv e (eval p) x + deriv e (eval p) 0 = ∑ j, iota e (pi2 p) j * x j := by
  rw [lhs_expand, rhs_expand]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hcard : s.vars.card ≤ 2 := by
    by_contra hgt
    exact (Finsupp.mem_support_iff.mp hs) (hp s (by omega))
  rw [hterm s.vars hcard x]

/-! ## The termwise identity for the three directions (finite checks) -/

set_option maxRecDepth 100000 in
theorem termwise_dirA2 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL dirA2 t x = termR dirA2 t x := by
  unfold termL termR sel
  decide

set_option maxRecDepth 100000 in
theorem termwise_dirB2 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL dirB2 t x = termR dirB2 t x := by
  unfold termL termR sel
  decide

set_option maxRecDepth 100000 in
theorem termwise_dirA2B2 :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL dirA2B2 t x = termR dirA2B2 t x := by
  unfold termL termR sel
  decide

/-- The three directions of the paper. -/
def IsPaperDir (e : Fin 6 → F₂) : Prop := e = dirA2 ∨ e = dirB2 ∨ e = dirA2B2

theorem termwise_of_paperDir {e : Fin 6 → F₂} (he : IsPaperDir e) :
    ∀ t : Finset (Fin 6), t.card ≤ 2 → ∀ x, termL e t x = termR e t x := by
  rcases he with rfl | rfl | rfl
  · exact termwise_dirA2
  · exact termwise_dirB2
  · exact termwise_dirA2B2

/-! ## The bridge lemma -/

/-- For `deg p ≤ 2` and `e ∈ {a₂, b₂, a₂+b₂}`, `D_e p` is affine with linear
part `ι_e (π₂ p)`. -/
theorem deriv_add_deriv_zero_eq {e : Fin 6 → F₂} (he : IsPaperDir e)
    (p : ANF 6) (hp : DegreeLE 2 p) (x : Fin 6 → F₂) :
    deriv e (eval p) x + deriv e (eval p) 0 = ∑ j, iota e (pi2 p) j * x j :=
  deriv_add_deriv_zero_eq_of_termwise e (termwise_of_paperDir he) p hp x

theorem f2_eq_of_add_eq_zero {a b : F₂} (h : a + b = 0) : a = b := by
  have h2 := congrArg (· + b) h
  simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at h2
  exact h2

/-- **Bridge lemma.** For `deg p ≤ 2` and `e ∈ {a₂, b₂, a₂+b₂}`: the derivative
`D_e p` is constant iff `ι_e (π₂ p) = 0`. -/
theorem constDeriv_iff_iota_pi2_eq_zero {e : Fin 6 → F₂} (he : IsPaperDir e)
    (p : ANF 6) (hp : DegreeLE 2 p) :
    ConstDeriv e p ↔ iota e (pi2 p) = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    funext j
    have hid := deriv_add_deriv_zero_eq he p hp (Pi.single j 1)
    rw [hc, hc, CharTwo.add_self_eq_zero] at hid
    have hsum : ∑ k, iota e (pi2 p) k * (Pi.single j (1 : F₂) : Fin 6 → F₂) k =
        iota e (pi2 p) j := by
      simp [Pi.single_apply]
    rw [hsum] at hid
    exact hid.symm
  · intro hz
    refine ⟨deriv e (eval p) 0, fun x => ?_⟩
    have hid := deriv_add_deriv_zero_eq he p hp x
    rw [hz] at hid
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hid
    exact f2_eq_of_add_eq_zero hid

/-! ## Lemma 8, as stated in `lambda4_proof.tex` -/

/-- **Lemma 8 (derivative lemma), paper form.** Let `Q` be any subspace of
2-forms with `ι_e(Q) = 0` for some `e ∈ {a₂, b₂, a₂+b₂}`. Then (★) has no
solution: there are no `f, h ∈ V₄(Q)` with `f h ∈ z₂ + V₄(Q)`. -/
theorem derivative_lemma_paper {e : Fin 6 → F₂} (he : IsPaperDir e)
    (Q : Submodule F₂ TwoForm6) (hQ : Submodule.map (iota e) Q = ⊥)
    (f h : ANF 6) (hf : f ∈ V4 Q) (hh : h ∈ V4 Q)
    (hg : f * h + lowMul3 2 ∈ V4 Q) : False := by
  have hQ' : ∀ ω ∈ Q, iota e ω = 0 := by
    intro ω hω
    have hmem : iota e ω ∈ Submodule.map (iota e) Q := ⟨ω, hω, rfl⟩
    rw [hQ] at hmem
    exact (Submodule.mem_bot F₂).mp hmem
  have hVder : ∀ p ∈ V4 Q, ConstDeriv e p := fun p hp =>
    (constDeriv_iff_iota_pi2_eq_zero he p hp.1).mpr (hQ' _ hp.2)
  rcases he with rfl | rfl | rfl
  · exact derivative_lemma_dirA2 (V4 Q) (fun p hp => hp.1) hVder f h hf hh hg
  · exact derivative_lemma_dirB2 (V4 Q) (fun p hp => hp.1) hVder f h hf hh hg
  · exact derivative_lemma_dirA2B2 (V4 Q) (fun p hp => hp.1) hVder f h hf hh hg

end

end LowHalfMul3

end UnrestrictedBooleanMul
