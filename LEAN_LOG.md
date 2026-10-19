# LEAN_LOG

Project: `lowhalf-mul3`. Lean 4.33.1, Mathlib `v4.33.1`, dependency
`unrestricted_boolean_mul` at rev `79a8017` (pinned in `lake-manifest.json`).
No network use: no `lake update`, no `cache get`. `lakefile.toml` and `.lake/`
were not modified.

Build command used throughout (grants: project folder rw, `~/.elan` ro):

```
$env:ELAN_HOME = "C:\Users\HP\.elan"
C:\Users\HP\.elan\bin\lake.exe build            # default target LowHalfMul3
C:\Users\HP\.elan\bin\lake.exe env lean AxiomAudit.lean
C:\Users\HP\.elan\bin\lake.exe env lean Challenge.lean
```

---

## 2026-10-19 — phase 1

### Step 1. `LowHalfMul3/Target.lean` — `lake build` clean, no `sorry`

```
def lowMul3 : Fin 3 → ANF 6 :=
  ![Mul 3 0, Mul 3 1, Mul 3 2 + aVar 3 0 * aVar 3 1 * bVar 3 0 * bVar 3 1]
```

`ANF 6` and `ANF (2 * 3)` are definitionally equal, so the imported
`Mul 3 : Fin 5 → ANF (2 * 3)` is accepted without any coercion.

Decisions:

* Imported `UnrestrictedBooleanMul.Mul`, not `.SmallCases`. The dependency's
  default library target is `globs = ["UnrestrictedBooleanMul"]`, so only the
  root module's import closure is prebuilt — `SmallCases.olean` does not exist
  in `.lake/packages/.../build` and `Mul.lean` had to be compiled on demand
  (183 s, once). Nothing from `SmallCases` is needed: `Circuit.ofAffineProducts`
  cannot express the feedback gate `g5` anyway, and `submodule_add_mem` is just
  `Submodule.add_mem`.
* The 64-input semantics is split into an algebraic step and an arithmetic
  step, so that nothing has to `decide` an `eval`, which is noncomputable:
  * `eval_lowMul3_zero/one/two` give the three coordinates as explicit
    polynomials in `x 0 … x 5` (`simp` with `Mul`, `mulCoefficient`, `aVar`,
    `bVar`, `Fin.sum_univ_succ`; the quartic coordinate needs a closing
    `ring` for re-association only).
  * `lowMul3_eval (a b : Fin 8) (s : Fin 3)` then compares those polynomials,
    evaluated at `inputs a b`, with `bitF (a * b % 8) s` — a statement about
    `Fin 8`, `Nat` and `ZMod 2` only, discharged by `decide` over all 64
    input pairs per coordinate. No `native_decide`, no `ofReduceBool`.
* `fin_cases s` leaves goals of the shape `lowMul3 ((fun i => i) ⟨0, _⟩)`,
  which blocks `rw`. Each branch is restated with `show` (defeq) first.

### Step 2. `LowHalfMul3/Upper.lean` — `lake build` clean, no `sorry`

`theorem upper : HasCircuit lowMul3 6`, with

```
g0 = a0 b0   g1 = a0 b1   g2 = a1 b0   g3 = a0 b2   g4 = a2 b0
g5 = (g1 + a1) (g2 + b1)
z0 = g0      z1 = g1 + g2      z2 = g5 + g1 + g2 + g3 + g4
```

Decisions:

* `circuit : Circuit 6 6` is built field by field (not via
  `Circuit.ofAffineProducts`), because `g5` reuses the earlier nonlinear wires
  `g1` and `g2`. The two membership obligations at `j = 5` are
  `leftFactor 5 = gate 1 + aVar 3 1` (`rfl`) followed by
  `Submodule.add_mem _ (gate_mem_wireSpace gate 1 (by omega)) (affine_le_wireSpace _ _)`;
  `gate_eq` is `fin_cases j <;> rfl` on all six gates.
* The recombination identities `z0_eq`, `z1_eq`, `z2_eq` are proved through
  `eval_injective 6` rather than by `ring_nf` in the monoid algebra. Reason:
  expanding `(a0 b1 + a1)(a1 b0 + b1)` inside `ANF` needs Boolean idempotence
  (`X i * X i = X i`), which `ring_nf` turns into powers instead of collapsing.
  After `eval_injective` and `funext x` the goal is an `F₂`-polynomial identity
  in `x : Fin 6 → F₂`, where idempotence is just `x * x = x` in `ZMod 2`, and
  `revert x; decide` settles it over the 64 assignments.
  `apply eval_injective 6` leaves a beta-redex `(fun p => eval p) _ x`; each
  proof restates the goal with `show` before rewriting.

### Step 3. `Challenge.lean`, `formalization.yaml`, `AxiomAudit.lean`

* `Challenge.lean` is self-contained, in the layout of the dependency's own
  `Challenge.lean`: it repeats the model definitions (`F₂`, `Monomial`, `ANF`,
  `X`, `affine`, `wireSpace`, `Circuit`, `HasCircuit`, `MC`, `aVar`, `bVar`,
  `Mul`) and `lowMul3`, then states the single deliberate hole
  `theorem mc_lowMul3 : MC(lowMul3) = 6 := by sorry`.
* **`Challenge.lean` and `AxiomAudit.lean` are root files outside the
  `LowHalfMul3` library**, exactly as in the dependency, so `lake build` (whose
  default target is the library) does not compile them. Adding
  `[[lean_lib]] Challenge` / `Solution` entries — which is how the dependency
  exposes them — would mean editing `lakefile.toml`, which this task forbids.
  They are therefore checked with `lake env lean <file>`, logged below. If the
  lakefile may later be edited, two `[[lean_lib]]` stanzas make them part of
  `lake build` with no change to the files.
* `Challenge.lean` must not be imported by the library: it redefines the whole
  model inside `namespace UnrestrictedBooleanMul`, so importing it alongside
  the dependency would duplicate every name.
* `formalization.yaml` records `sorry_count: 1` (that hole) and states
  explicitly that `MC(lowMul3) = 6` is **not** proved: only the upper bound is.

### Step 4. `LowHalfMul3.lean`

Now imports `LowHalfMul3.Target` and `LowHalfMul3.Upper`. The old
`#check UnrestrictedBooleanMul.Circuit` probe was removed (it printed an `info`
line on every build).

### Verification run (2026-10-19)

| command | result |
| --- | --- |
| `lake build` | `Build completed successfully (1612 jobs)`, exit 0, no errors, no warnings, no `sorry` |
| `lake env lean AxiomAudit.lean` | exit 0, axioms printed for all 12 proved theorems |
| `lake env lean Challenge.lean` | exit 0, single warning `Challenge.lean:126:8: declaration uses 'sorry'` |

`#print axioms` — identical for every proved theorem:

```
[propext, Classical.choice, Quot.sound]
```

for `eval_lowMul3_zero`, `eval_lowMul3_one`, `eval_lowMul3_two`,
`lowMul3_eval`, `leftFactor_five`, `rightFactor_five`, `circuit_gate`,
`z0_eq`, `z1_eq`, `z2_eq`, `circuit_computes`, `upper`.

No `native_decide`, no `ofReduceBool`, no `sorryAx` outside `Challenge.lean`.

### Status after phase 1

* Proved in Lean: the integer semantics of `lowMul3` on all 64 inputs, and
  `HasCircuit lowMul3 6`.
* Not proved in Lean: `¬ HasCircuit lowMul3 5`, hence not `MC(lowMul3) = 6`.

---

## 2026-10-19 — phase 2, part 1: what the dependency already gives

Read: `.lake/packages/unrestricted_boolean_mul/UnrestrictedBooleanMul/N4/Rewiring.lean`
(19.9 KB), `UnrestrictedBooleanMul/CircuitPadding.lean` (3.0 KB), and the
supporting `N4/Flag.lean`, `N4/Normalization.lean`, `N4/Degree.lean`,
`N4/Exterior.lean`, `N4/TwoForm.lean`.

### Normal form, part A: `g₀ = a₀b₀` — available, no mathematical gap

All four steps exist and are **generic in `(m, r)`**; only the n=4 wrapper
`exists_promote_rational_place` is hardwired to `Circuit 8 8` / `Mul 4`.

| step of Lemma 1 | lemma | file |
| --- | --- | --- |
| find the first gate at which `z₀` enters the wire space | `exists_first_entry_gate (C) (t) (hfinal : t ∈ C.finalWire) (hnotAffine : t ∉ affine m) : ∃ j, t ∈ circuitFlag C (j+1) ∧ t ∉ circuitFlag C j` | `N4/Rewiring.lean` |
| that gate's step is exactly `⊔ span {t}` | `circuit_first_entry_replacement` | `N4/Normalization.lean` |
| replace it by the direct product `u * v = t`, `u, v` affine | `replaceFirstEntryCircuit` + `replaceFirstEntryCircuit_finalWire` (`= C.finalWire`) + `replaceFirstEntryCircuit_computes` | `N4/Rewiring.lean` |
| move that direct gate to position `p` | `exists_move_direct_gate_left (C) (p j) (hpj : p ≤ j) (t) (hgate : C.gate j = t) (hleft hright : ∈ affine m) : ∃ D, D.finalWire = C.finalWire ∧ D.gate p = t ∧ D.left p, D.right p ∈ affine m ∧ ∀ k < p, D.gate k = C.gate k` | `N4/Rewiring.lean` |

Instantiating these at `m = 6`, `t = a₀b₀`, `p = 0` needs only two side
conditions, both cheap for `lowMul3`:

* `a₀b₀ ∈ C.finalWire` — immediate from `C.Computes lowMul3`, because
  `lowMul3 0 = Mul 3 0 = aVar 3 0 * bVar 3 0` (this is `z0_eq` composed with
  `Computes`).
* `a₀b₀ ∉ affine 6` — the analogue of his `rationalPlaceANF_not_mem_affine`;
  three lines from `coefficient_eq_zero_of_mem_affine` in `Mul.lean`
  (affine functions have zero coefficient on any card-2 monomial) plus
  `coeff_monomial`.

Note the Lean route is **shorter than the paper proof**: Lemma 1 puts `a₀b₀`
first and *deletes* the old gate, whereas `replaceFirstEntryCircuit` rewrites
the offending gate in place, so no pruning step is needed. (`CircuitPruning.lean`
exists but is not required here.)

### Normal form, part B: linear gates first — two gaps, both statement-level

Available: `swapAdjacentFun`, `swapAdjacentDirectCircuit` (swap an adjacent
pair `a, a+1` when the *later* gate has both factors affine) with
`_finalWire` and `_computes`, and `exists_move_direct_gate_left`, which
iterates those swaps for **one** gate.

Missing:

1. **No sorting lemma.** Nothing produces a circuit in which the set
   `{j | C.left j, C.right j ∈ affine m}` is an initial segment. Needed shape:
   `∃ D, D.Computes target ∧ D.finalWire = C.finalWire ∧ ∃ λ, (∀ k, k < λ → D.left k ∈ affine m ∧ D.right k ∈ affine m) ∧ (∀ k, λ ≤ k → ¬(D.left k ∈ affine m ∧ D.right k ∈ affine m))`.
   The induction is on the number of direct gates (equivalently on inversions),
   each step being one `exists_move_direct_gate_left`.
2. **`exists_move_direct_gate_left` is too weak to iterate.** Its conclusion
   gives `∀ k < p, D.gate k = C.gate k` but says nothing about `D.left k`,
   `D.right k`. To keep "the first `i` gates are direct" alive across the
   induction one needs the factors, not just the gate values. This is a
   restatement, not new mathematics: `swapAdjacentDirectCircuit` sets
   `left := swapAdjacentFun C.left a b` and `right := swapAdjacentFun C.right a b`,
   so both are untouched outside `{a, b}`, and `replaceFirstEntryCircuit` uses
   `Function.update` at `j` only. Strengthening the conclusion to
   `∀ k < p, D.gate k = C.gate k ∧ D.left k = C.left k ∧ D.right k = C.right k`
   requires only carrying the two extra conjuncts through the existing
   `Nat.strong_induction_on`.

`λ ≥ 1` is free once part A is in place (gate 0 is the direct product `a₀b₀`).

### `CircuitPadding.lean`: the `k ≤ 5` glue, not the normal form

`Circuit.pad`, `Circuit.Computes.pad`, and
`HasCircuit.pad : HasCircuit target s → s ≤ r → HasCircuit target r`
(padding by zero gates, `0 = 0 * 0` with `0 ∈ affine`). This is what turns a
single `¬ HasCircuit lowMul3 5` into a bound against every smaller size:
combined with `mc_eq_of_lower_upper` and our `upper`, the claim
`MC(lowMul3) = 6` reduces to exactly that one statement. Nothing here bears on
the normal form. (A four-line `mc_eq_six_of_no_five` would record that
reduction in Lean; it is not in this commit — say the word and it goes in.
Cost: `UnrestrictedBooleanMul.CircuitPadding` has a 9-module import closure of
which 6 are not yet compiled in `.lake/packages`, so expect one ~5 minute
build.)

### Build-cost note

Only `ANF.olean` and `Circuit.olean` are prebuilt in the dependency's
`.lake/build`, because its default target is `globs = ["UnrestrictedBooleanMul"]`
and our project only imported `Circuit`. Anything else is compiled on demand at
roughly 30–60 s per module. Import closures measured:
`CircuitPadding` 9 modules, `N4.Flag` 8, `N4.Degree` 14, `N4.Normalization` 13,
`N4.Rewiring` 24. Using the Rewiring machinery therefore costs a one-off build
of ~20 modules (≈15–25 min); worth scheduling deliberately rather than
discovering mid-proof.

### What is missing for Lemma 8 in the dependency

* **No contraction and no derivative anywhere.** Grep over all 200+ modules
  finds no `ι_e`, no `D_e`, no translation operator (the `translate*` names in
  `N5` are unrelated coefficient reparametrizations).
* `N4/Exterior.lean` is only partly generic: `vectorWedgeN`, `vectorWedgeTwoN`
  are `{n}`-generic, but `TwoForm`, `wedgeTwo` (2∧2 → 4-form), `placeA/B` and
  everything downstream are hardwired to `Fin 8`. There is no `π₂ : ANF m → TwoForm`
  bridge for `m = 6` (`targetTwo` is the 8-variable Hankel-block map).
* `N4/Degree.lean` has what the degree step needs — `DegreeLE`, `DegreeLE.mul`,
  `homogeneousPart`, `quadraticANFSpace` — but behind a 14-module closure.

## 2026-10-19 — phase 2, part 2: `LowHalfMul3/Derivative.lean`

`lake build` clean, no `sorry`, no warnings. Imports only `LowHalfMul3.Target`
and `Mathlib.Algebra.MonoidAlgebra.Support`, so no N4 closure was built.

**What is proved** (`derivative_lemma`): for `e : Fin 6 → F₂`, `δ : ANF 6` and
a submodule `V ≤ ANF 6` with

* `DegreeLE 1 δ`, `∀ x, D_e (eval z₂) x = eval δ x`, and `δ` nonconstant,
* `∀ p ∈ V, DegreeLE 2 p`,
* `∀ p ∈ V, ConstDeriv e p`,

there are no `f, h ∈ V` with `f * h + z₂ ∈ V`. Instantiated as
`derivative_lemma_dirA2`, `_dirB2`, `_dirA2B2` with
`δ = b₀, a₀, a₀ + b₀` for `e = a₂, b₂, a₂ + b₂`.

**Deliberate deviation from the tex, and the remaining gap.** The paper states
the hypothesis as `ι_e(Q) = 0` with `V = V₄(Q)`. Since no `π₂`/`ι_e` layer
exists for six variables (see above), the Lean statement uses instead the two
consequences the paper's proof actually draws from it in its first two
sentences: elements of `V` have degree ≤ 2 and *constant* derivative along `e`.
For `V = V₄(Q)` these are equivalent to `ι_e(Q) = 0`, because for `deg f ≤ 2`,
`D_e f = ι_e(π₂ f) + f₁(e) + f₂(e)`, i.e. `D_e f` is constant iff `ι_e(π₂ f) = 0`.
**That equivalence is not formalized** — it is the one-line reduction that still
separates `derivative_lemma` from Lemma 8 as written, and it is what the
`π₂`/`ι_e` layer for `ANF 6` would supply. Everything after those two sentences
— the whole content of the lemma — is formalized. The Lean hypotheses are
implied by the paper's, so nothing is assumed that the paper does not grant.

Proof structure as in the tex:

* `key : ∀ x, c·h(x) + d·f(x) + cd + δ(x) = k` from expanding
  `D_e(fh) = D_e f · h + f · D_e h + D_e f · D_e h`. Discharged by generalizing
  the seven `eval` values to `F₂` variables and `decide` (2¹⁰ cases).
* `c = d = 0` ⟹ `δ` constant, contradicting `hδnc`.
* `c = 1` ⟹ `h = (k+d)•1 + d•f + δ` (by `eval_injective` and `decide`), so
  `f*h = (k+d)•f + d•f + f*δ` using `anf_mul_self : p * p = p`, of degree ≤ 3.
* `c = 0, d = 1` ⟹ `f = k•1 + δ` of degree ≤ 1, so `f*h` has degree ≤ 3.
* Degree contradiction: `f*h = (f*h + z₂) + z₂`, the first summand has degree
  ≤ 2 by hypothesis, so the coefficient of the carry monomial `{a₀,a₁,b₀,b₁}`
  in `f*h` equals that of `z₂`, which is `1` (`coeff_lowMul3_two_carry`),
  contradicting degree ≤ 3.

Local support lemmas, all proved, none imported from N4:
`DegreeLE` (same predicate as `N4.DegreeLE`), `DegreeLE.mono/.add/.smul/.mul`
(the `.mul` proof follows `N4/Degree.lean` and uses the Mathlib lemma
`MonoidAlgebra.support_coeff_mul_subset`), `degreeLE_one_of_mem_affine`,
`anf_mul_self`, `shiftBy`, `deriv`, `ConstDeriv`, `carryMonomial`,
`coeff_lowMul3_two_carry`.

Sanity: the hypotheses are satisfiable — `V = affine 6` meets both, where the
lemma asserts the true fact that `f*h + z₂` is never affine for affine `f, h`.
So the statement is not vacuous.

### Verification run (2026-10-19, after phase 2)

| command | result |
| --- | --- |
| `lake build` | `Build completed successfully (1614 jobs)`, exit 0, no errors, no warnings, no `sorry` |
| `lake env lean AxiomAudit.lean` | exit 0; all **23** proved theorems report `[propext, Classical.choice, Quot.sound]` |
| `lake env lean Challenge.lean` | exit 0, single `declaration uses 'sorry'` warning |

### Stop point

As instructed, stopping before the main theorem (Theorem 11 of
`lambda4_proof.tex`). The next formalization steps, in dependency order:

1. strengthen `exists_move_direct_gate_left` (factors, not just gates) and add
   the sorting induction — gives Lemma 1;
2. a `π₂`/`ι_e` layer for `ANF 6` — gives Lemma 8 verbatim, plus Lemmas 4, 5,
   6 and Proposition 7, which are all cross-part statements;
3. the rank-2 type classification (Lemma 10), then Theorem 11.
