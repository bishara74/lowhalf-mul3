module

public import LowHalfMul3.Target
public import LowHalfMul3.Upper
public import LowHalfMul3.Derivative
public import LowHalfMul3.Reduction
public import LowHalfMul3.NormalForm
public import LowHalfMul3.LambdaFive
public import LowHalfMul3.Contraction
public import LowHalfMul3.LemmaTwo
public import LowHalfMul3.Assembly
public import LowHalfMul3.CrossPart
public import LowHalfMul3.Product
public import LowHalfMul3.LineDerivative
public import LowHalfMul3.LemmaThree
public import LowHalfMul3.Types
public import LowHalfMul3.MainTheorem
public import LowHalfMul3.LambdaThree
public import LowHalfMul3.Coset
public import LowHalfMul3.LemmaA
public import LowHalfMul3.LemmaC
public import LowHalfMul3.LambdaTwo
public import LowHalfMul3.OneHigh
public import LowHalfMul3.LambdaOne
public import LowHalfMul3.Shared
public import LowHalfMul3.IdealExtract
public import LowHalfMul3.LastFactor

@[expose] public section

/-!
# The 3 x 3 low-half multiplier

Entry point for the low-half (mod 8) three-bit multiplier target in the
unrestricted XOR--AND model of `unrestricted_boolean_mul`.

* `LowHalfMul3.Target` defines `lowMul3` and checks all 64 inputs against
  integer multiplication modulo 8.
* `LowHalfMul3.Upper` proves `HasCircuit lowMul3 6` with an explicit
  six-gate circuit whose last gate reuses two earlier nonlinear wires.
* `LowHalfMul3.Reduction` proves `mc_eq_six_of_no_five`: the exact value
  `MC(lowMul3) = 6` follows from `¬ HasCircuit lowMul3 5` alone.
* `LowHalfMul3.NormalForm` proves Lemma 1 (normal form): `g₀ = a₀b₀` and
  the linear gates form an initial segment `0, …, λ-1`, `1 ≤ λ`.
* `LowHalfMul3.LambdaFive` excludes `λ = 5`: no circuit whose gates are all
  linear computes `lowMul3`.
* `LowHalfMul3.Derivative` proves the derivative lemma (Lemma 8 of
  `lambda4_proof.tex`) for the three directions `a₂`, `b₂`, `a₂ + b₂`.
* `LowHalfMul3.Contraction` adds the quadratic part `pi2`, the contraction
  `iota e`, the space `V4 Q`, the bridge `D_e p` constant iff `ι_e(π₂ p) = 0`,
  and Lemma 8 in the paper's form (`derivative_lemma_paper`, hypothesis
  `ι_e(Q) = 0`).
* `LowHalfMul3.LemmaTwo` proves Lemma 2: if the first `j` gates are linear,
  the wire space before gate `j` is `V₄(Q_j)`.
* `LowHalfMul3.Assembly` defines the open cases `LambdaCase 1/2/3` and
  `StarFree` (Theorem 12), proves `StarFree → LambdaCase 4`, and proves
  `mc_eq_six_of_remaining_cases`: those four statements imply `MC = 6`.

* `LowHalfMul3.CrossPart` proves Lemma 4's kernel statement
  (`ker Φ = Λ²(U)` on symmetric forms) and Lemma 6 (no `l ∧ r` has the cross
  part of `q₂`).

* `LowHalfMul3.Product` is the product-coefficient layer:
  `π₂(L R) = ℓ(L) ∧ ℓ(R)` for affine `L, R`, via Möbius inversion on pairs.

* `LowHalfMul3.LineDerivative` proves Lemma 8′ (`starFree_of_goodDir`): if
  `ι_e(Q) ⊆ span{ℓ}` with `ℓ ≠ δ_e` for a paper direction `e`, (★) fails.
* `LowHalfMul3.LemmaThree` has the wedge algebra, Pfaffians, the two Lemma 3
  instances (`lemma3`) and `wedge_ne_Z` (`Z₁ + c₀ P₀` is not a wedge).

* `LowHalfMul3.Types` proves Lemma 11 (types) as a normal form: every
  `l ∧ r` equals some `l' ∧ r'` with cross part zero, of type `v`, or full.

* `LowHalfMul3.MainTheorem` proves Theorem 12 (`starFree`, the case `λ = 4`),
  hence `lambdaCase_four`, and `mc_eq_six_of_lambda_cases`.

* `LowHalfMul3.LambdaThree` reduces `LambdaCase 3` to two claims
  (`lambdaCase_three_of : BadClaim → B3Claim → LambdaCase 3`): `BadClaim`
  (Lemmas A and C of `lambda3_proof.tex` for `Q₃` without a good direction) and
  `B3Claim` (Proposition B3, `Q₃ ⊆ Λ²(U)`). Lemma C for spaces with a good
  direction, the flow `z₁ ∈ V₄`, Lemma B3U and the last-gate argument via
  `Q₃ + ⟨Z₁⟩` are proved there.

* `LowHalfMul3.Coset` proves the general coset lemma (B3a + B3b, Proposition
  B3) for any coset base (`CosetBase`: contains `Aff`, constant `a₂`/`b₂`
  derivatives, `1, a₀, b₀` in the radical of the carry pairing), hence
  `b3Claim : B3Claim` and `lambdaCase_three_of_badClaim : BadClaim → LambdaCase 3`.

* `LowHalfMul3.LemmaA` proves Lemma A for spaces without a good direction
  (`noPlace_z1_bad`, the `z₁` conjunct of `BadClaim`): the derivative bridge for
  every direction, Lemma W (a quadratic function vanishing on a hyperplane
  `{a = α}` has quadratic part `a ∧ m`), and a direction with a `U`-component
  (`UDir`, hence `GenDir`) for every `Q₃` in normal form without a good direction.

* `LowHalfMul3.LemmaC` proves Lemma C for those spaces by a third-difference
  argument along the same `U`-direction (`noPlace_z2_of_uDir`), hence
  `badClaim : BadClaim` and **`lambdaCase_three : LambdaCase 3`**, and
  `mc_eq_six_of_lambda_one_two : LambdaCase 1 → LambdaCase 2 → MC(lowMul3) = 6`.
* `LowHalfMul3.LambdaTwo` reduces `λ = 2` to one statement, `TwoClaim`
  (Proposition `onehigh` of `lambda2_proof.tex` for `P ∉ Λ²(U)`):
  `lambdaCase_two_of : TwoClaim → LambdaCase 2`. Inside `Λ²(U)` it uses the coset
  lemma; the placement of `z₁` by `g₂` outside `Λ²(U)` is excluded by Lemma A's
  derivative argument (`noPlace_z1_two`).
* `LowHalfMul3.OneHigh` proves parts 1 and 2 of `TwoClaim`: `z₂ ∉ V(S) + ⟨f h⟩`
  (`z2_not_mem_S_sup`), and the last-gate form `F H + σ f h + z₂ ∈ V(S)` is impossible
  (`formA_zero`, `formA_one_of_phi`, by a 16-point cube sum in `ker l`). Form (b),
  `k (f h + F) + z₂ ∈ V(S)`, remains.

* `LowHalfMul3.LambdaOne` (with `LambdaOneBase`, `LambdaOneTail`, `LambdaOneCore`,
  `LambdaOneEarly`, `LambdaOneParity`, `LambdaOneOrdinary`, `LambdaOneAssembly`) proves
  `lambdaCase_one_of : TwoClaim → LastFactorLowIdeal → IdealExtract → Q2NotTwoWedges →
  FeedbackNoPlaceModLow → FeedbackNormal → LambdaCase 1`.

* `LowHalfMul3.Shared` proves two of the five shared statements:
  `feedbackNormal : FeedbackNormal` and `q2NotTwoWedges : Q2NotTwoWedges`.

The lower bound is therefore reduced, in Lean, to `TwoClaim` and the remaining shared
statements in `LowHalfMul3.LambdaOneBase` (`LastFactorLowIdeal`, `IdealExtract`,
`FeedbackNoPlaceModLow`)
(`mc_eq_six_of_twoClaim : LambdaCase 1 → TwoClaim → MC(lowMul3) = 6`).
-/
