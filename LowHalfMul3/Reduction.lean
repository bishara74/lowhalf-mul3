import LowHalfMul3.Upper
import UnrestrictedBooleanMul.CircuitPadding

/-!
# Reducing `MC(lowMul3) = 6` to the single statement `¬ HasCircuit lowMul3 5`

`HasCircuit.pad` turns a circuit with `s ≤ 5` gates into one with exactly five
(by appending zero products), so excluding five gates excludes every smaller
size. Together with the six-gate circuit `upper`, the value follows from
`mc_eq_of_lower_upper`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

/-- The exact value reduces to the exclusion of five-gate circuits. -/
theorem mc_eq_six_of_no_five (h5 : ¬ HasCircuit lowMul3 5) : MC(lowMul3) = 6 := by
  refine mc_eq_of_lower_upper upper ?_
  intro s hs
  by_contra hlt
  exact h5 (hs.pad (by omega))

end LowHalfMul3

end UnrestrictedBooleanMul
