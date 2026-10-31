import LowHalfMul3.Target
import LowHalfMul3.Upper
import LowHalfMul3.Derivative
import LowHalfMul3.Reduction
import LowHalfMul3.NormalForm
import LowHalfMul3.LambdaFive
import LowHalfMul3.Contraction
import LowHalfMul3.LemmaTwo
import LowHalfMul3.Assembly
import LowHalfMul3.CrossPart

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
  `StarFree` (Theorem 11), proves `StarFree → LambdaCase 4`, and proves
  `mc_eq_six_of_remaining_cases`: those four statements imply `MC = 6`.

* `LowHalfMul3.CrossPart` proves Lemma 4's kernel statement
  (`ker Φ = Λ²(U)` on symmetric forms) and Lemma 6 (no `l ∧ r` has the cross
  part of `q₂`).

The lower bound is therefore reduced, in Lean, to exactly four statements:
`LambdaCase 1`, `LambdaCase 2`, `LambdaCase 3` and `StarFree`.

The unconditional claim `MC(lowMul3) = 6` is stated, as a deliberate hole,
in `Challenge.lean`.
-/
