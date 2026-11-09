module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
# Unrestricted Boolean multiplicative complexity of the 3 x 3 low-half product

Statement of record for the claim `MC(lowMul3) = 6`, where `lowMul3` is the
triple of low bits of the product of two 3-bit integers, i.e. the product
modulo 8.

Coefficients are in F₂. Squarefree monomials multiply by union, imposing
Boolean idempotence. XOR and constants are free; either input of each paid
AND gate may use arbitrary previously computed nonlinear wires. This is
not a restriction to bilinear, quadratic, homogeneous or formula circuits.
The model is that of arXiv:2608.30238v1, Definition 2.1. The declarations
below are copied from the pinned UnrestrictedBooleanMul revision
`c014e498e51a98529877cc256b9bcdaf5faa2e4f` to keep this file self-contained.

The target differs from `Mul 3` (the four-term polynomial product) in two
ways: only the three low coefficients are required, and coefficient 2 carries
the integer carry `a₀a₁b₀b₁` out of bit 1.

The theorem below is the Challenge statement. Its proof is
`mc_lowMul3` in `LowHalfMul3Solution`.
-/

namespace UnrestrictedBooleanMul
noncomputable section

abbrev F₂ := ZMod 2

/-- A squarefree monomial in `m` Boolean variables. -/
@[ext]
structure Monomial (m : Nat) where
  vars : Finset (Fin m)
deriving DecidableEq

instance {m : Nat} : CommMonoid (Monomial m) where
  one := ⟨∅⟩
  mul s t := ⟨s.vars ∪ t.vars⟩
  one_mul s := congrArg Monomial.mk (Finset.empty_union s.vars)
  mul_one s := congrArg Monomial.mk (Finset.union_empty s.vars)
  mul_assoc r s t := congrArg Monomial.mk (Finset.union_assoc r.vars s.vars t.vars)
  mul_comm s t := congrArg Monomial.mk (Finset.union_comm s.vars t.vars)

/-- Canonical Boolean algebraic normal forms in `m` variables. -/
abbrev ANF (m : Nat) := MonoidAlgebra F₂ (Monomial m)

/-- The ANF consisting of one squarefree monomial. -/
def monomial {m : Nat} (s : Finset (Fin m)) : ANF m :=
  MonoidAlgebra.single ⟨s⟩ 1

/-- The `i`th input variable. -/
def X {m : Nat} (i : Fin m) : ANF m := monomial {i}

/-- The subspace of constants and input-linear functions. -/
noncomputable def affine (m : Nat) : Submodule F₂ (ANF m) :=
  Submodule.span F₂ ({1} ∪ Set.range X)

/-- Outputs of gates whose index is strictly before `j`. -/
def prefixGates {m r : Nat} (g : Fin r → ANF m) (j : Nat) : Set (ANF m) :=
  {p | ∃ i : Fin r, i.val < j ∧ g i = p}

/-- The functions available for free immediately before gate `j`. -/
def wireSpace {m r : Nat} (g : Fin r → ANF m) (j : Nat) : Submodule F₂ (ANF m) :=
  affine m ⊔ Submodule.span F₂ (prefixGates g j)

/-- An unrestricted XOR--AND circuit with exactly `r` AND gates. -/
structure Circuit (m r : Nat) where
  gate : Fin r → ANF m
  left : Fin r → ANF m
  right : Fin r → ANF m
  left_mem : ∀ j, left j ∈ wireSpace gate j.val
  right_mem : ∀ j, right j ∈ wireSpace gate j.val
  gate_eq : ∀ j, gate j = left j * right j

/-- The final free-XOR wire space of a circuit. -/
def Circuit.finalWire {m r : Nat} (C : Circuit m r) : Submodule F₂ (ANF m) :=
  wireSpace C.gate r

/-- A circuit computes a vector-valued target when every coordinate is in its final span. -/
def Circuit.Computes {m r o : Nat} (C : Circuit m r) (target : Fin o → ANF m) : Prop :=
  ∀ i, target i ∈ C.finalWire

/-- There is an unrestricted circuit with `r` AND gates computing `target`. -/
def HasCircuit {m o : Nat} (target : Fin o → ANF m) (r : Nat) : Prop :=
  Nonempty {C : Circuit m r // C.Computes target}

/-- Unrestricted Boolean multiplicative complexity (zero for an uncomputable target). -/
def multiplicativeComplexity {m o : Nat} (target : Fin o → ANF m) : Nat :=
  by
    classical
    exact if h : ∃ r, HasCircuit target r then Nat.find h else 0

notation "MC(" target ")" => multiplicativeComplexity target

/-- The variable `a_i` among the `2n` multiplication inputs. -/
def aVar (n : Nat) (i : Fin n) : ANF (2 * n) :=
  X ⟨i.val, Eq.mpr (congrArg (fun k : Nat => i.val < k) (Nat.two_mul n))
    (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n n))⟩

/-- The variable `b_j` among the `2n` multiplication inputs. -/
def bVar (n : Nat) (j : Fin n) : ANF (2 * n) :=
  X ⟨n + j.val, Eq.mpr (congrArg (fun k : Nat => n + j.val < k) (Nat.two_mul n))
    (Nat.add_lt_add_left j.isLt n)⟩

/-- Coefficient `s` of the product of two `n`-term binary polynomials. -/
def mulCoefficient (n : Nat) (s : Nat) : ANF (2 * n) :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i.val + j.val = s then aVar n i * bVar n j else 0

/-- Binary `n`-term polynomial multiplication in Boolean ANF. -/
def Mul (n : Nat) : Fin (2 * n - 1) → ANF (2 * n) :=
  fun s => mulCoefficient n s.val

namespace LowHalfMul3

/-- The three low bits of the product of two 3-bit integers, least significant
bit first. Coefficient 2 carries the integer carry out of bit 1. -/
def lowMul3 : Fin 3 → ANF 6 :=
  ![Mul 3 0,
    Mul 3 1,
    Mul 3 2 + aVar 3 0 * aVar 3 1 * bVar 3 0 * bVar 3 1]

/-- Six products are necessary and sufficient for the 3 x 3 low-half product. -/
theorem mc_lowMul3 : MC(lowMul3) = 6 := by sorry

end LowHalfMul3
end
end UnrestrictedBooleanMul
