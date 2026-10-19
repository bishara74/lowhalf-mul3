import UnrestrictedBooleanMul.Mul

/-!
# The 3 x 3 low-half multiplier as a target

`lowMul3` is the triple of low bits of the product of two 3-bit integers.
The first two coordinates agree with the polynomial product coefficients
`Mul 3 0` and `Mul 3 1`; the third carries the extra quartic term
`a₀a₁b₀b₁`, which is the carry out of bit 1.

`lowMul3_eval` checks all 64 inputs against integer multiplication modulo 8.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- The three low bits of the product of two 3-bit integers, least significant
bit first, in the ANF model of `UnrestrictedBooleanMul`. -/
def lowMul3 : Fin 3 → ANF 6 :=
  ![Mul 3 0,
    Mul 3 1,
    Mul 3 2 + aVar 3 0 * aVar 3 1 * bVar 3 0 * bVar 3 1]

/-- Bit `i` of a natural number. -/
def bitF (n i : Nat) : F₂ := if n / 2 ^ i % 2 = 1 then 1 else 0

/-- The six inputs read off two 3-bit integers: `a₀a₁a₂b₀b₁b₂`, LSB first. -/
def inputs (a b : Nat) : Fin 6 → F₂ :=
  fun i => if i.val < 3 then bitF a i.val else bitF b (i.val - 3)

/-- The algebraic normal forms of the three coordinates, written out. -/
theorem eval_lowMul3_zero (x : Fin 6 → F₂) :
    eval (lowMul3 0) x = x 0 * x 3 := by
  simp [lowMul3, Mul, mulCoefficient, aVar, bVar, Fin.sum_univ_succ]

theorem eval_lowMul3_one (x : Fin 6 → F₂) :
    eval (lowMul3 1) x = x 0 * x 4 + x 1 * x 3 := by
  simp [lowMul3, Mul, mulCoefficient, aVar, bVar, Fin.sum_univ_succ]

theorem eval_lowMul3_two (x : Fin 6 → F₂) :
    eval (lowMul3 2) x =
      x 0 * x 5 + x 1 * x 4 + x 2 * x 3 + x 0 * x 1 * x 3 * x 4 := by
  simp [lowMul3, Mul, mulCoefficient, aVar, bVar, Fin.sum_univ_succ]
  ring

/-- All 64 inputs: the three coordinates of `lowMul3` are the three low bits
of the integer product. -/
theorem lowMul3_eval (a b : Fin 8) (s : Fin 3) :
    eval (lowMul3 s) (inputs a.val b.val) = bitF (a.val * b.val % 8) s.val := by
  fin_cases s
  · show eval (lowMul3 0) (inputs a.val b.val) = bitF (a.val * b.val % 8) 0
    rw [eval_lowMul3_zero]; revert a b; decide
  · show eval (lowMul3 1) (inputs a.val b.val) = bitF (a.val * b.val % 8) 1
    rw [eval_lowMul3_one]; revert a b; decide
  · show eval (lowMul3 2) (inputs a.val b.val) = bitF (a.val * b.val % 8) 2
    rw [eval_lowMul3_two]; revert a b; decide

end

end LowHalfMul3

end UnrestrictedBooleanMul
