import LowHalfMul3.Target
import LowHalfMul3.Upper
import LowHalfMul3.Derivative

/-!
# The 3 x 3 low-half multiplier

Entry point for the low-half (mod 8) three-bit multiplier target in the
unrestricted XOR--AND model of `unrestricted_boolean_mul`.

* `LowHalfMul3.Target` defines `lowMul3` and checks all 64 inputs against
  integer multiplication modulo 8.
* `LowHalfMul3.Upper` proves `HasCircuit lowMul3 6` with an explicit
  six-gate circuit whose last gate reuses two earlier nonlinear wires.
* `LowHalfMul3.Derivative` proves the derivative lemma (Lemma 8 of
  `lambda4_proof.tex`) for the three directions `a₂`, `b₂`, `a₂ + b₂`.

The lower bound `¬ HasCircuit lowMul3 5` is not formalized here; the claim
`MC(lowMul3) = 6` is stated, as a deliberate hole, in `Challenge.lean`.
-/
