import LowHalfMul3.Target

/-!
# A six-gate circuit for the 3 x 3 low-half multiplier

The circuit is

```
g0 = a0 b0          g3 = a0 b2
g1 = a0 b1          g4 = a2 b0
g2 = a1 b0          g5 = (g1 + a1) (g2 + b1)
z0 = g0             z1 = g1 + g2
z2 = g5 + g1 + g2 + g3 + g4
```

Gate `g5` reuses the earlier nonlinear wires `g1` and `g2`, so the circuit is
built as a `Circuit` structure with explicit `wireSpace` membership rather
than through `Circuit.ofAffineProducts`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- The six AND-gate outputs. -/
def gate : Fin 6 → ANF 6 :=
  ![aVar 3 0 * bVar 3 0,
    aVar 3 0 * bVar 3 1,
    aVar 3 1 * bVar 3 0,
    aVar 3 0 * bVar 3 2,
    aVar 3 2 * bVar 3 0,
    (aVar 3 0 * bVar 3 1 + aVar 3 1) * (aVar 3 1 * bVar 3 0 + bVar 3 1)]

/-- Left factors of the six gates. -/
def leftFactor : Fin 6 → ANF 6 :=
  ![aVar 3 0, aVar 3 0, aVar 3 1, aVar 3 0, aVar 3 2,
    aVar 3 0 * bVar 3 1 + aVar 3 1]

/-- Right factors of the six gates. -/
def rightFactor : Fin 6 → ANF 6 :=
  ![bVar 3 0, bVar 3 1, bVar 3 0, bVar 3 2, bVar 3 0,
    aVar 3 1 * bVar 3 0 + bVar 3 1]

theorem leftFactor_five : leftFactor 5 = gate 1 + aVar 3 1 := rfl

theorem rightFactor_five : rightFactor 5 = gate 2 + bVar 3 1 := rfl

/-- The six-gate circuit. -/
def circuit : Circuit 6 6 where
  gate := gate
  left := leftFactor
  right := rightFactor
  left_mem := by
    intro j
    fin_cases j
    · exact affine_le_wireSpace _ (aVar_mem_affine 3 0)
    · exact affine_le_wireSpace _ (aVar_mem_affine 3 0)
    · exact affine_le_wireSpace _ (aVar_mem_affine 3 1)
    · exact affine_le_wireSpace _ (aVar_mem_affine 3 0)
    · exact affine_le_wireSpace _ (aVar_mem_affine 3 2)
    · show leftFactor 5 ∈ wireSpace gate 5
      rw [leftFactor_five]
      exact Submodule.add_mem _ (gate_mem_wireSpace gate 1 (by omega))
        (affine_le_wireSpace _ (aVar_mem_affine 3 1))
  right_mem := by
    intro j
    fin_cases j
    · exact affine_le_wireSpace _ (bVar_mem_affine 3 0)
    · exact affine_le_wireSpace _ (bVar_mem_affine 3 1)
    · exact affine_le_wireSpace _ (bVar_mem_affine 3 0)
    · exact affine_le_wireSpace _ (bVar_mem_affine 3 2)
    · exact affine_le_wireSpace _ (bVar_mem_affine 3 0)
    · show rightFactor 5 ∈ wireSpace gate 5
      rw [rightFactor_five]
      exact Submodule.add_mem _ (gate_mem_wireSpace gate 2 (by omega))
        (affine_le_wireSpace _ (bVar_mem_affine 3 1))
  gate_eq := by
    intro j
    fin_cases j <;> rfl

@[simp] theorem circuit_gate (j : Fin 6) : circuit.gate j = gate j := rfl

/-! ## The three output recombinations -/

theorem z0_eq : lowMul3 0 = gate 0 := by
  apply eval_injective 6
  funext x
  show eval (lowMul3 0) x = eval (gate 0) x
  rw [eval_lowMul3_zero]
  simp [gate, aVar, bVar]

theorem z1_eq : lowMul3 1 = gate 1 + gate 2 := by
  apply eval_injective 6
  funext x
  show eval (lowMul3 1) x = eval (gate 1 + gate 2) x
  rw [eval_lowMul3_one]
  simp [gate, aVar, bVar]

theorem z2_eq : lowMul3 2 = gate 5 + gate 1 + gate 2 + gate 3 + gate 4 := by
  apply eval_injective 6
  funext x
  show eval (lowMul3 2) x = eval (gate 5 + gate 1 + gate 2 + gate 3 + gate 4) x
  rw [eval_lowMul3_two]
  simp only [gate, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, eval_add', eval_mul', aVar, bVar, eval_X]
  revert x
  decide

/-- The circuit computes the low-half product. -/
theorem circuit_computes : circuit.Computes lowMul3 := by
  intro s
  fin_cases s
  · show lowMul3 0 ∈ circuit.finalWire
    rw [z0_eq]
    exact gate_mem_finalWire circuit 0
  · show lowMul3 1 ∈ circuit.finalWire
    rw [z1_eq]
    exact Submodule.add_mem _ (gate_mem_finalWire circuit 1) (gate_mem_finalWire circuit 2)
  · show lowMul3 2 ∈ circuit.finalWire
    rw [z2_eq]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.add_mem _ (gate_mem_finalWire circuit 5) (gate_mem_finalWire circuit 1))
          (gate_mem_finalWire circuit 2))
        (gate_mem_finalWire circuit 3))
      (gate_mem_finalWire circuit 4)

/-- Six AND gates suffice for the 3 x 3 low-half product. -/
theorem upper : HasCircuit lowMul3 6 :=
  ⟨⟨circuit, circuit_computes⟩⟩

end

end LowHalfMul3

end UnrestrictedBooleanMul
