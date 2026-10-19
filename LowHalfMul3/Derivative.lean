import LowHalfMul3.Target
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# The derivative lemma (Lemma 8 of `lambda4_proof.tex`)

Lemma 8 says: if `Q` is a space of 2-forms annihilated by the contraction
`ι_e` for some `e ∈ {a₂, b₂, a₂+b₂}`, then the last-gate condition

```
  f, h ∈ V₄(Q),    f * h ∈ z₂ + V₄(Q)                                   (★)
```

has no solution.

The version proved here replaces `V₄(Q)` by an abstract subspace `V` and the
contraction hypothesis `ι_e(Q) = 0` by its two consequences that the proof
actually uses:

* every element of `V` has degree at most 2, and
* every element of `V` has a *constant* derivative along `e`.

For `V = V₄(Q)` both hold exactly when `ι_e(Q) = 0`: for a function of degree
at most 2 the derivative `D_e` is affine with linear part `ι_e` of its
quadratic part, so `D_e` is constant iff `ι_e` kills that quadratic part.
Phrasing the hypothesis through `D_e` avoids building an exterior-algebra
layer for six variables; no 2-form machinery is needed anywhere below.

The direction `e` enters through the single datum `δ`, an ANF of degree at
most 1 computing `D_e z₂`, which must be nonconstant. `δ = b₀, a₀, a₀ + b₀`
for `e = a₂, b₂, a₂ + b₂`; these three instances are discharged at the end.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-! ## Degree measured on coefficients

Same predicate as `UnrestrictedBooleanMul.N4.DegreeLE`, restated locally so
that this file depends only on `LowHalfMul3.Target`. The proof of
`DegreeLE.mul` follows the one in `N4/Degree.lean`.
-/

/-- `p` has no monomial of cardinality above `d`. -/
def DegreeLE {m : Nat} (d : Nat) (p : ANF m) : Prop :=
  ∀ s : Monomial m, d < s.vars.card → p.coeff s = 0

theorem DegreeLE.mono {m d e : Nat} {p : ANF m}
    (hp : DegreeLE d p) (hde : d ≤ e) : DegreeLE e p :=
  fun s hes => hp s (lt_of_le_of_lt hde hes)

theorem DegreeLE.add {m d : Nat} {p q : ANF m}
    (hp : DegreeLE d p) (hq : DegreeLE d q) : DegreeLE d (p + q) := by
  intro s hs
  have : (p + q).coeff s = p.coeff s + q.coeff s := by simp
  rw [this, hp s hs, hq s hs, add_zero]

theorem DegreeLE.smul {m d : Nat} {p : ANF m} (hp : DegreeLE d p) (c : F₂) :
    DegreeLE d (c • p) := by
  intro s hs
  have : (c • p).coeff s = c * p.coeff s := by simp
  rw [this, hp s hs, mul_zero]

/-- Boolean ANF degree is subadditive under multiplication. -/
theorem DegreeLE.mul {m d e : Nat} {p q : ANF m}
    (hp : DegreeLE d p) (hq : DegreeLE e q) :
    DegreeLE (d + e) (p * q) := by
  let D : Monomial m → Nat := fun s => s.vars.card
  have hpSup : p.coeff.support.sup D ≤ d := by
    apply Finset.sup_le
    intro s hs
    apply le_of_not_gt
    intro hsd
    exact (Finsupp.mem_support_iff.mp hs) (hp s hsd)
  have hqSup : q.coeff.support.sup D ≤ e := by
    apply Finset.sup_le
    intro s hs
    apply le_of_not_gt
    intro hse
    exact (Finsupp.mem_support_iff.mp hs) (hq s hse)
  have hmul :
      (p * q).coeff.support.sup D ≤
        p.coeff.support.sup D + q.coeff.support.sup D := by
    apply Finset.sup_le
    intro s hs
    have hs' := MonoidAlgebra.support_coeff_mul_subset p q hs
    rw [Finset.mem_mul] at hs'
    rcases hs' with ⟨u, hu, v, hv, rfl⟩
    calc
      D (u * v) ≤ D u + D v := Finset.card_union_le u.vars v.vars
      _ ≤ p.coeff.support.sup D + q.coeff.support.sup D :=
        Nat.add_le_add (Finset.le_sup hu) (Finset.le_sup hv)
  intro s hs
  by_contra hne
  have hmem : s ∈ (p * q).coeff.support := Finsupp.mem_support_iff.mpr hne
  have hdegree : D s ≤ d + e :=
    (Finset.le_sup hmem).trans (hmul.trans (Nat.add_le_add hpSup hqSup))
  exact (Nat.not_le_of_lt hs) hdegree

/-- Affine functions have degree at most one. -/
theorem degreeLE_one_of_mem_affine {m : Nat} {p : ANF m} (hp : p ∈ affine m) :
    DegreeLE 1 p := by
  intro s hs
  refine Submodule.span_induction (p := fun p _ => p.coeff s = 0) ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with hq | hq
    · have hqone : q = 1 := by simpa only [Set.mem_singleton_iff] using hq
      subst q
      have hne : (1 : Monomial m) ≠ s := by
        intro h
        have hc := congrArg (fun t : Monomial m => t.vars.card) h
        simp at hc
        omega
      rw [MonoidAlgebra.one_def]
      simp [hne]
    · rcases hq with ⟨i, rfl⟩
      have hne : (⟨{i}⟩ : Monomial m) ≠ s := by
        intro h
        have hc := congrArg (fun t : Monomial m => t.vars.card) h
        simp at hc
        omega
      simp [X, monomial, hne]
  · simp
  · intro p q _ _ hpq hqq
    simp [hpq, hqq]
  · intro c p _ hpq
    simp [hpq]

/-- In the Boolean ANF quotient every element is idempotent. -/
theorem anf_mul_self {m : Nat} (p : ANF m) : p * p = p := by
  apply eval_injective m
  funext x
  show eval (p * p) x = eval p x
  rw [eval_mul']
  rcases f2_eq_zero_or_one (eval p x) with h | h <;> rw [h] <;> simp

/-! ## Discrete derivatives -/

/-- Translate an input assignment by a direction. -/
def shiftBy (e x : Fin 6 → F₂) : Fin 6 → F₂ := fun i => x i + e i

/-- The discrete derivative of a Boolean function along `e`. -/
def deriv (e : Fin 6 → F₂) (F : (Fin 6 → F₂) → F₂) : (Fin 6 → F₂) → F₂ :=
  fun x => F (shiftBy e x) + F x

/-- `p` has a constant derivative along `e`. -/
def ConstDeriv (e : Fin 6 → F₂) (p : ANF 6) : Prop :=
  ∃ c : F₂, ∀ x, deriv e (eval p) x = c

theorem nonconstant_of_two_points (p : ANF 6) (x y : Fin 6 → F₂)
    (h : eval p x ≠ eval p y) : ¬ ∃ c : F₂, ∀ z, eval p z = c := by
  rintro ⟨c, hc⟩
  exact h ((hc x).trans (hc y).symm)

/-! ## The quartic coefficient of `z₂` -/

/-- The carry monomial `a₀a₁b₀b₁`. -/
def carryMonomial : Monomial 6 := ⟨{0, 1, 3, 4}⟩

theorem carryMonomial_card : carryMonomial.vars.card = 4 := by decide

theorem coeff_lowMul3_two_carry : (lowMul3 2).coeff carryMonomial = 1 := by
  simp [lowMul3, Mul, mulCoefficient, aVar, bVar, X, Fin.sum_univ_succ,
    carryMonomial, monomial_mul]
  decide

/-! ## The derivative lemma -/

/-- **Lemma 8.** With `V` standing for `V₄(Q)` and `δ` for `ι_e(q₂) = D_e z₂`:
if every element of `V` has degree at most two and constant derivative along
`e`, and `D_e z₂` is a nonconstant function of degree at most one, then the
last-gate condition (★) has no solution. -/
theorem derivative_lemma
    (e : Fin 6 → F₂) (δ : ANF 6)
    (hδdeg : DegreeLE 1 δ)
    (hδeval : ∀ x, deriv e (eval (lowMul3 2)) x = eval δ x)
    (hδnc : ¬ ∃ c : F₂, ∀ x, eval δ x = c)
    (V : Submodule F₂ (ANF 6))
    (hVdeg : ∀ p ∈ V, DegreeLE 2 p)
    (hVder : ∀ p ∈ V, ConstDeriv e p)
    (f h : ANF 6) (hf : f ∈ V) (hh : h ∈ V)
    (hg : f * h + lowMul3 2 ∈ V) : False := by
  obtain ⟨c, hc⟩ := hVder f hf
  obtain ⟨d, hd⟩ := hVder h hh
  obtain ⟨k, hk⟩ := hVder _ hg
  -- Expanding `D_e (f h) = D_e f · h + f · D_e h + D_e f · D_e h`.
  have key : ∀ x, c * eval h x + d * eval f x + c * d + eval δ x = k := by
    intro x
    have hfx : eval f (shiftBy e x) + eval f x = c := hc x
    have hhx : eval h (shiftBy e x) + eval h x = d := hd x
    have hgx : eval (f * h + lowMul3 2) (shiftBy e x)
        + eval (f * h + lowMul3 2) x = k := hk x
    have hzx : eval (lowMul3 2) (shiftBy e x) + eval (lowMul3 2) x
        = eval δ x := hδeval x
    rw [eval_add', eval_add', eval_mul', eval_mul'] at hgx
    clear hc hd hk hVdeg hVder hδeval hδnc hf hh hg
    revert hfx hhx hgx hzx
    generalize eval f (shiftBy e x) = A
    generalize eval f x = B
    generalize eval h (shiftBy e x) = A'
    generalize eval h x = B'
    generalize eval (lowMul3 2) (shiftBy e x) = Z
    generalize eval (lowMul3 2) x = Z'
    generalize eval δ x = E
    revert A B A' B' Z Z' E c d k
    decide
  clear hc hd hk
  -- The degree-4 coefficient of `f * h` is the carry, so `f * h` has degree 4.
  have contra : DegreeLE 3 (f * h) → False := by
    intro hdeg3
    have hsplit : f * h = (f * h + lowMul3 2) + lowMul3 2 := by
      rw [add_assoc, anf_add_self, add_zero]
    have hcoeff : (f * h).coeff carryMonomial = 1 := by
      rw [hsplit]
      have : ((f * h + lowMul3 2) + lowMul3 2).coeff carryMonomial =
          (f * h + lowMul3 2).coeff carryMonomial
            + (lowMul3 2).coeff carryMonomial := by simp
      rw [this, hVdeg _ hg carryMonomial (by rw [carryMonomial_card]; omega),
        coeff_lowMul3_two_carry, zero_add]
    have : (f * h).coeff carryMonomial = 0 :=
      hdeg3 carryMonomial (by rw [carryMonomial_card]; omega)
    rw [hcoeff] at this
    exact one_ne_zero this
  rcases f2_eq_zero_or_one c with hc0 | hc1
  · rcases f2_eq_zero_or_one d with hd0 | hd1
    · -- `c = d = 0`: the derivative of `z₂` would be constant.
      refine hδnc ⟨k, fun x => ?_⟩
      have := key x
      rw [hc0, hd0] at this
      simpa using this
    · -- `c = 0`, `d = 1`: `f` is affine, so `f * h` has degree at most 3.
      refine contra ?_
      -- `eval f x = k + eval δ x`, hence `f = k • 1 + δ`.
      have hfeq : f = k • (1 : ANF 6) + δ := by
        apply eval_injective 6
        funext x
        show eval f x = eval (k • (1 : ANF 6) + δ) x
        have hx := key x
        clear key
        rw [hc0, hd1] at hx
        rw [eval_add', eval_smul', eval_one']
        revert hx
        generalize eval f x = B
        generalize eval h x = B'
        generalize eval δ x = E
        revert B B' E k
        decide
      have hfdeg1 : DegreeLE 1 f := by
        rw [hfeq]
        exact (degreeLE_one_of_mem_affine
          (Submodule.smul_mem _ k (one_mem_affine 6))).add hδdeg
      have := DegreeLE.mul hfdeg1 (hVdeg h hh)
      simpa using this
  · -- `c = 1`: `h = (k + d) • 1 + d • f + δ`, so `f * h` has degree at most 3.
    refine contra ?_
    have hheq : h = (k + d) • (1 : ANF 6) + d • f + δ := by
      apply eval_injective 6
      funext x
      show eval h x = eval ((k + d) • (1 : ANF 6) + d • f + δ) x
      have hx := key x
      clear key
      rw [hc1] at hx
      rw [eval_add', eval_add', eval_smul', eval_smul', eval_one']
      revert hx
      generalize eval f x = B
      generalize eval h x = B'
      generalize eval δ x = E
      revert B B' E k d
      decide
    have hfh : f * h = (k + d) • f + d • f + f * δ := by
      rw [hheq, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_one,
        anf_mul_self]
    rw [hfh]
    have h1 : DegreeLE 3 ((k + d) • f) := ((hVdeg f hf).smul _).mono (by omega)
    have h2 : DegreeLE 3 (d • f) := ((hVdeg f hf).smul _).mono (by omega)
    have h3 : DegreeLE 3 (f * δ) := by
      have := DegreeLE.mul (hVdeg f hf) hδdeg
      simpa using this
    exact (h1.add h2).add h3

/-! ## The three directions `a₂`, `b₂`, `a₂ + b₂` -/

/-- The direction `a₂`. -/
def dirA2 : Fin 6 → F₂ := ![0, 0, 1, 0, 0, 0]

/-- The direction `b₂`. -/
def dirB2 : Fin 6 → F₂ := ![0, 0, 0, 0, 0, 1]

/-- The direction `a₂ + b₂`. -/
def dirA2B2 : Fin 6 → F₂ := ![0, 0, 1, 0, 0, 1]

theorem deriv_lowMul3_two_dirA2 (x : Fin 6 → F₂) :
    deriv dirA2 (eval (lowMul3 2)) x = eval (bVar 3 0) x := by
  simp only [deriv, shiftBy, dirA2, eval_lowMul3_two, bVar, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  revert x
  decide

theorem deriv_lowMul3_two_dirB2 (x : Fin 6 → F₂) :
    deriv dirB2 (eval (lowMul3 2)) x = eval (aVar 3 0) x := by
  simp only [deriv, shiftBy, dirB2, eval_lowMul3_two, aVar, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  revert x
  decide

theorem deriv_lowMul3_two_dirA2B2 (x : Fin 6 → F₂) :
    deriv dirA2B2 (eval (lowMul3 2)) x = eval (aVar 3 0 + bVar 3 0) x := by
  simp only [deriv, shiftBy, dirA2B2, eval_lowMul3_two, aVar, bVar, eval_add',
    eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  revert x
  decide

theorem degreeLE_one_aVar (i : Fin 3) : DegreeLE 1 (aVar 3 i) :=
  degreeLE_one_of_mem_affine (aVar_mem_affine 3 i)

theorem degreeLE_one_bVar (j : Fin 3) : DegreeLE 1 (bVar 3 j) :=
  degreeLE_one_of_mem_affine (bVar_mem_affine 3 j)

theorem nonconstant_bVar_zero : ¬ ∃ c : F₂, ∀ x, eval (bVar 3 0) x = c := by
  refine nonconstant_of_two_points _ (fun _ => 0) ![0, 0, 0, 1, 0, 0] ?_
  simp [bVar]

theorem nonconstant_aVar_zero : ¬ ∃ c : F₂, ∀ x, eval (aVar 3 0) x = c := by
  refine nonconstant_of_two_points _ (fun _ => 0) ![1, 0, 0, 0, 0, 0] ?_
  simp [aVar]

theorem nonconstant_aVar_add_bVar :
    ¬ ∃ c : F₂, ∀ x, eval (aVar 3 0 + bVar 3 0) x = c := by
  refine nonconstant_of_two_points _ (fun _ => 0) ![1, 0, 0, 0, 0, 0] ?_
  simp [aVar, bVar]

/-- Lemma 8 along `e = a₂`. -/
theorem derivative_lemma_dirA2
    (V : Submodule F₂ (ANF 6))
    (hVdeg : ∀ p ∈ V, DegreeLE 2 p)
    (hVder : ∀ p ∈ V, ConstDeriv dirA2 p)
    (f h : ANF 6) (hf : f ∈ V) (hh : h ∈ V)
    (hg : f * h + lowMul3 2 ∈ V) : False :=
  derivative_lemma dirA2 (bVar 3 0) (degreeLE_one_bVar 0)
    deriv_lowMul3_two_dirA2 nonconstant_bVar_zero V hVdeg hVder f h hf hh hg

/-- Lemma 8 along `e = b₂`. -/
theorem derivative_lemma_dirB2
    (V : Submodule F₂ (ANF 6))
    (hVdeg : ∀ p ∈ V, DegreeLE 2 p)
    (hVder : ∀ p ∈ V, ConstDeriv dirB2 p)
    (f h : ANF 6) (hf : f ∈ V) (hh : h ∈ V)
    (hg : f * h + lowMul3 2 ∈ V) : False :=
  derivative_lemma dirB2 (aVar 3 0) (degreeLE_one_aVar 0)
    deriv_lowMul3_two_dirB2 nonconstant_aVar_zero V hVdeg hVder f h hf hh hg

/-- Lemma 8 along `e = a₂ + b₂`. -/
theorem derivative_lemma_dirA2B2
    (V : Submodule F₂ (ANF 6))
    (hVdeg : ∀ p ∈ V, DegreeLE 2 p)
    (hVder : ∀ p ∈ V, ConstDeriv dirA2B2 p)
    (f h : ANF 6) (hf : f ∈ V) (hh : h ∈ V)
    (hg : f * h + lowMul3 2 ∈ V) : False :=
  derivative_lemma dirA2B2 (aVar 3 0 + bVar 3 0)
    ((degreeLE_one_aVar 0).add (degreeLE_one_bVar 0))
    deriv_lowMul3_two_dirA2B2 nonconstant_aVar_add_bVar V hVdeg hVder f h hf hh hg

end

end LowHalfMul3

end UnrestrictedBooleanMul
