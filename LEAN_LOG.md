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

---

## 2026-10-25 — migration to Lean 4.35.0-rc3

Toolchain and dependency bump done by the author (`lake update` and
`cache get` already run; no network used in this session, and `lake update`
was not run here):

| | before | after |
| --- | --- | --- |
| `lean-toolchain` | `leanprover/lean4:v4.33.1` | `leanprover/lean4:v4.35.0-rc3` |
| mathlib | `0df444a3` (`v4.33.1`) | `c55e6e78` (`v4.35.0-rc3`) |
| `unrestricted_boolean_mul` | `79a80176` (`inputRev = main`) | `c014e498` (pinned by rev in `lakefile.toml`) |

### Changes to our files: none

`lake build` succeeded on the new toolchain on the first attempt, with no
error in `LowHalfMul3/*`, `Challenge.lean` or `AxiomAudit.lean`. **No source
edit was needed, so no statement changed and nothing was weakened.** The
reason is that the dependency bump keeps the API this development uses —
`ANF`, `Monomial`, `eval`, `eval_injective`, `affine`, `wireSpace`,
`Circuit`, `HasCircuit`, `MC`, `aVar`, `bVar`, `Mul`, `mulCoefficient` — and
the Mathlib lemmas used here (`MonoidAlgebra.support_coeff_mul_subset`,
`Finset.card_union_le`, `Submodule.span_induction`, the `Matrix.cons_val*`
simp set, `Fin.sum_univ_succ`) are all unchanged under 4.35.0-rc3. Our files
contain no `if_neg` and no `dif_pos`, the two names deprecated in this cycle
(checked by grep).

### The build was genuinely redone, not replayed from a stale cache

A toolchain change invalidates traces, but it was worth confirming rather
than assuming:

* The three oleans were rewritten during this session —
  `.lake/build/lib/lean/LowHalfMul3/{Target,Upper,Derivative}.olean` and
  `LowHalfMul3.olean` carry 2026-10-25 timestamps against 2026-10-19 sources.
* Independently of any cache, each file was re-elaborated from source with
  `lake env lean` (which writes no olean and therefore cannot be served from
  the build tree). All four exit 0 with **no warnings of any kind**, so there
  is not even a deprecation notice in our own code.

| file | `lake env lean` | wall |
| --- | --- | --- |
| `LowHalfMul3/Target.lean` | exit 0, no output | 202 s |
| `LowHalfMul3/Upper.lean` | exit 0, no output | 30 s |
| `LowHalfMul3/Derivative.lean` | exit 0, no output | 32 s |
| `LowHalfMul3.lean` | exit 0, no output | 25 s |
| `Challenge.lean` | exit 0, `Challenge.lean:126:8: declaration uses 'sorry'` (the deliberate hole) | 138 s |
| `AxiomAudit.lean` | exit 0, axioms printed for all 23 theorems | — |

`lake build` itself: `Build completed successfully (1691 jobs)`, exit 0
(1691 jobs against 1614 under 4.33.1), 164 s.

### Two deprecation warnings, both in the dependency

```
warning: UnrestrictedBooleanMul/ANF.lean:224:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: UnrestrictedBooleanMul/Circuit.lean:88:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead
```

Both are inside `.lake/packages/unrestricted_boolean_mul`, which is not ours
to edit (and `.lake/` is off limits by instruction). They are warnings only:
the dependency builds and both `ANF.lean` and `Circuit.lean` produce oleans,
so nothing downstream is affected. Worth passing upstream — `ANF.lean:224` is
in `eval_pointIndicator` and `Circuit.lean:88` is in `mc_eq_of_lower_upper`,
the lemma this project's eventual `MC(lowMul3) = 6` will be built on.

### `#print axioms` after migration — unchanged

All **23** proved theorems report exactly

```
[propext, Classical.choice, Quot.sound]
```

`Target`: `eval_lowMul3_zero`, `eval_lowMul3_one`, `eval_lowMul3_two`,
`lowMul3_eval`.
`Upper`: `leftFactor_five`, `rightFactor_five`, `circuit_gate`, `z0_eq`,
`z1_eq`, `z2_eq`, `circuit_computes`, `upper`.
`Derivative`: `DegreeLE.mul`, `degreeLE_one_of_mem_affine`, `anf_mul_self`,
`coeff_lowMul3_two_carry`, `derivative_lemma`, `deriv_lowMul3_two_dirA2`,
`deriv_lowMul3_two_dirB2`, `deriv_lowMul3_two_dirA2B2`,
`derivative_lemma_dirA2`, `derivative_lemma_dirB2`,
`derivative_lemma_dirA2B2`.

No `sorryAx` outside `Challenge.lean`, no `native_decide`, no
`ofReduceBool`, no new axiom. The library still has zero `sorry`, and the
status is as before: the upper bound `HasCircuit lowMul3 6` and the
derivative lemma are proved; `¬ HasCircuit lowMul3 5`, and hence
`MC(lowMul3) = 6`, is not.

---

## 2026-10-31 — phase 3

Same rules: no network, no `lake update`/`cache get`, no `native_decide`/
`ofReduceBool`, `.lake/` and `lakefile.toml` untouched, `lake build` green
after every step. Toolchain `v4.35.0-rc3`, dependency at `c014e498`.

### Dependency build cost (one-off)

At `c014e498` the dependency uses the Lean module system (`module`,
`public import`, `@[expose] public section`), and its import closures grew:
`CircuitPadding` 21 modules, `N4.Rewiring` 36 (it pulls in `N4.SevenGate`,
`N4.LowProductBridge`, `N4.QuadraticLower`, `N4.Homogeneous`, the `N3.Product*`
certificates, …). Only `ANF`, `Circuit`, `Mul` were prebuilt. Built once with
`lake build UnrestrictedBooleanMul.CircuitPadding UnrestrictedBooleanMul.N4.Rewiring`:
**994 s**, 1723 jobs, exit 0 (slowest: `N4.Homogeneous` 245 s, `N3.ProductC30/C31`
and `N3.Coordinates` 175 s each). Warnings only, all inside the dependency.
Subsequent `lake build` of our library: ~26 s.

(Tooling note: in this sandbox `pathlib.Path.rglob` silently returns nothing
under `.lake/packages`; `os.walk` works. The phase-2 closure counts were taken
before the dependency switched to `public import`, which the old regex would
also have missed.)

### Step 1 — `LowHalfMul3/Reduction.lean`: `mc_eq_six_of_no_five` — PROVED

```lean
theorem mc_eq_six_of_no_five (h5 : ¬ HasCircuit lowMul3 5) : MC(lowMul3) = 6
```

`mc_eq_of_lower_upper upper`, and for the lower bound: if `s < 6` then
`s ≤ 5`, so `hs.pad` (`HasCircuit.pad`) gives a 5-gate circuit, contradicting
`h5`. The whole Challenge statement now reduces in Lean to the single
proposition `¬ HasCircuit lowMul3 5`.

### Step 2 — `LowHalfMul3/NormalForm.lean`: Lemma 1 — PROVED

New definitions: `IsLinearGate C k := C.left k ∈ affine m ∧ C.right k ∈ affine m`
and `SameGate D C k := D.gate k = C.gate k ∧ D.left k = C.left k ∧ D.right k = C.right k`.

* **`exists_move_linear_gate_left`** — the strengthened move lemma asked for in
  phase 2. Same `Nat.strong_induction_on` on `j - p` as the supervisor's
  `N4.exists_move_direct_gate_left`, over his `N4.swapAdjacentDirectCircuit`
  and `N4.swapAdjacentDirectCircuit_finalWire`, but the conclusion is now
  `D.finalWire = C.finalWire ∧ D.gate p = C.gate j ∧ D.left p = C.left j ∧
  D.right p = C.right j ∧ ∀ k < p, SameGate D C k`. The extra conjuncts come
  from unfolding `swapAdjacentFun` at `k ∉ {a, a+1}`; no new mathematics.
* **(a) `exists_g0_normal`** — the supervisor's chain verbatim at `m = 6`,
  `t = a₀b₀`: `N4.exists_first_entry_gate` → `N4.circuit_first_entry_replacement`
  → `N4.replaceFirstEntryCircuit` with `u = aVar 3 0`, `v = bVar 3 0` (and
  `_finalWire`) → our move lemma at `p = 0`. Side conditions:
  `a₀b₀ ∈ finalWire` from `hC 0` and `z0_eq` (`lowMul3_zero_eq_a0b0`);
  `a₀b₀ ∉ affine 6` (`a0b0_not_mem_affine`) from
  `coefficient_eq_zero_of_mem_affine` at the card-2 monomial `{0,3}` and
  `coeff_a0b0 = 1`. `0 < r` falls out of the first-entry index, so the
  statement needs no size hypothesis. The conclusion fixes the *factors*
  `D.left 0 = a₀`, `D.right 0 = b₀`, not just the gate value.
* **(b) `exists_linear_prefix`** — the sorting induction, by strong induction
  on `r - i` with invariant "gates `0..i-1` are linear". If some gate at index
  `≥ i` is linear, move it to `i` (gates below `i` keep their factors, so the
  invariant holds for `i+1`); otherwise stop with `λ = i`, and then
  `k < λ ↔ IsLinearGate D k` holds by construction. No permutation
  bookkeeping is needed.
* **`normal_form`** (any `r`) and **`normal_form_five`**:

```lean
theorem normal_form_five (C : Circuit 6 5) (hC : C.Computes lowMul3) :
    ∃ D : Circuit 6 5, D.Computes lowMul3 ∧
      D.gate 0 = aVar 3 0 * bVar 3 0 ∧ D.left 0 = aVar 3 0 ∧ D.right 0 = bVar 3 0 ∧
      ∃ lam, 1 ≤ lam ∧ lam ≤ 5 ∧ ∀ k : Fin 5, (k.val < lam ↔ IsLinearGate D k)
```

Compiled on the second attempt (fixes: `simp` already closes `coeff_a0b0`;
`omega` needs `show k.val = 0` to see through `Fin.mk`).

### Step 4 (done before step 3) — `LowHalfMul3/LambdaFive.lean`: λ = 5 — PROVED

Done first because it is short and closes a whole case.
`degreeLESubmodule m d` packages `DegreeLE d` (from `Derivative.lean`) as a
submodule; `finalWire_le_degreeTwo` shows an all-linear circuit's final wire
space lies in degree ≤ 2 (via `Circuit.finalWire_eq`, `sup_le`,
`Submodule.span_le`, `DegreeLE.mul`); `not_degreeLE_two_lowMul3_two` uses the
carry coefficient. Result, stronger than asked (any number of gates):

```lean
theorem no_all_linear_circuit {r : Nat} (C : Circuit 6 r) (hC : C.Computes lowMul3)
    (hlin : ∀ k, IsLinearGate C k) : False
theorem not_lambda_five (D : Circuit 6 5) (hD : D.Computes lowMul3)
    (hlam : ∀ k : Fin 5, (k.val < 5 ↔ IsLinearGate D k)) : False
```

`lake build` after steps 1, 2, 4: green each time (1710, 1731, 1732 jobs).

### Step 3 — `LowHalfMul3/Contraction.lean`: π₂ / ι_e layer, bridge, Lemma 8 verbatim — PROVED

Closes the phase-2 divergence: Lemma 8 is now stated with the paper's own
hypothesis `ι_e(Q) = 0`.

Definitions:

* `TwoForm6 := Fin 6 → Fin 6 → F₂` (2-forms as symmetric zero-diagonal
  matrices; characteristic two removes the signs).
* `pi2 : ANF 6 →ₗ[F₂] TwoForm6`, `pi2 p i j = if i = j then 0 else coeff_{x_i x_j} p`
  — the identification `x_i x_j ↔ x_i ∧ x_j`.
* `iota e : TwoForm6 →ₗ[F₂] (Fin 6 → F₂)`, `(iota e ω) j = ∑ i, e i * ω i j`.
  `iota_add_dir` / `iota_dirA2B2`: `ι_{a₂+b₂} = ι_{a₂} + ι_{b₂}`, the paper's definition.
* `V4 Q := {p | DegreeLE 2 p ∧ pi2 p ∈ Q}` as a submodule.
* `IsPaperDir e := e = dirA2 ∨ e = dirB2 ∨ e = dirA2B2`.

Bridge (`deriv_add_deriv_zero_eq`): for `deg p ≤ 2` and a paper direction,
`D_e p (x) + D_e p (0) = ∑ j, ι_e(π₂ p) j * x j` — i.e. `D_e p` is affine with
linear part `ι_e(π₂ p)`. Then `constDeriv_iff_iota_pi2_eq_zero`: `D_e p`
constant iff `ι_e(π₂ p) = 0` (`→` by evaluating at `Pi.single j 1`).

Proof structure: `lhs_expand` and `rhs_expand` write both sides as
`∑ s ∈ support, coeff s * term(s)` (generic; `rhs_expand` is a three-step
`Finset.sum_comm` calc), and `deriv_add_deriv_zero_eq_of_termwise` reduces
the identity to a *termwise* identity on single monomials `t` with
`|t| ≤ 2`. That termwise identity is a finite statement (64 subsets × 64
points per direction), discharged by plain `decide` — `termwise_dirA2`,
`termwise_dirB2`, `termwise_dirA2B2` — with `maxRecDepth 100000`. A scratch
timing test first: 25 s including imports for one direction; the whole file
builds in 35 s. Kernel-checked; no `native_decide`, no `+kernel`.

```lean
theorem derivative_lemma_paper {e : Fin 6 → F₂} (he : IsPaperDir e)
    (Q : Submodule F₂ TwoForm6) (hQ : Submodule.map (iota e) Q = ⊥)
    (f h : ANF 6) (hf : f ∈ V4 Q) (hh : h ∈ V4 Q)
    (hg : f * h + lowMul3 2 ∈ V4 Q) : False
```

(`ι_e(Q) = 0` is written literally as `Q.map (iota e) = ⊥`.)

### Step 5 — what was done, in the brief's order

**Numbering.** I use the numbering of the attached `lambda4_proof.tex`:
Lemma 1 normal form, Lemma 2 `V₄ = V₄(Q)`, Lemma 3 support, Lemma 4 cross
part, Lemma 5 (plane in `Λ²(U)`), Lemma 6 (no `q₂` cross part),
Proposition 7, Lemma 8 derivative, Remark 9, **Lemma 10 types**, **Theorem 11
main**. The brief's "Lemma 11 (types) and Theorem 12" are these two under a
later numbering; the statements are identified by content.

#### Lemma 2 — `LowHalfMul3/LemmaTwo.lean` — PROVED (both inclusions)

```lean
def gateQ {r : Nat} (C : Circuit 6 r) (j : Nat) : Submodule F₂ TwoForm6 :=
  Submodule.span F₂ (pi2 '' prefixGates C.gate j)
theorem wireSpace_eq_V4 {r : Nat} (C : Circuit 6 r) (j : Nat)
    (hlin : ∀ i : Fin r, i.val < j → IsLinearGate C i) :
    wireSpace C.gate j = V4 (gateQ C j)
```

More general than the paper (any prefix length `j`, any circuit size). The
paper's last step "no quadratic part ⟹ affine" is
`mem_affine_of_degreeLE_two_of_pi2_eq_zero`, which needed
`anf_eq_sum_monomials : p = ∑ s ∈ support, coeff s • monomial s.vars`
(by `eval_injective` and `Finset.induction_on`) and `monomial_empty : monomial ∅ = 1`.
Fixes during compilation: `Finset.card_eq_two` needs an explicit `show`; the
deprecated `if_neg` (Lean 4.35) replaced by `↓reduceIte`; `CharTwo.add_self_eq_zero`
does not find `CharP` on the matrix type, so the cancellation is done pointwise.

#### The `λ = 4` reduction and the case split — `LowHalfMul3/Assembly.lean` — PROVED

Not a separate item in the brief, but it is the paragraph of the paper right
after Lemma 2 ("Hence `z₀, z₁ ∈ V₄` iff `P₀, Z₁ ∈ Q`, and the remaining condition
on the last gate is (★)"), and it is what makes the remaining gap an exact
Lean statement.

* `StarFree` is Theorem 11 in algebraic form (printed in full below). Its
  `Q` is `span{π₂(Lᵢ Rᵢ)}` for **affine** `Lᵢ, Rᵢ`, `L₀ = a₀`, `R₀ = b₀`. It
  deliberately allows degenerate products (rank `< 2`, `dim Q < 4`): that is
  what a circuit can produce, and the paper's WLOG "every `Pᵢ` of rank 2,
  `dim Q = 4`" then belongs to the *proof* of `StarFree`, not to this
  reduction. Nothing is assumed here that the circuit does not give.
* `lambdaCase_four_of_starFree : StarFree → LambdaCase 4`. Proof: Lemma 2
  gives `wireSpace 4 ≤ V4 Q`; `finalWire = wireSpace 4 ⊔ span{g₄}`
  (`N4.wireSpace_succ`); if `g₄` had degree ≤ 2 the whole final space would,
  contradicting `z₂`; so the `z₁`-decomposition cannot use `g₄` (giving
  `Z₁ ∈ Q`), and the `z₂`-decomposition must (giving `f h + z₂ ∈ V4 Q` with
  `f, h` the factors of `g₄`, which lie in `wireSpace 4`). Only the inclusion
  `wireSpace 4 ≤ V4 Q` of Lemma 2 is needed.
* `starFree_instance_of_iota`: the part of Theorem 11 that Lemma 8 already
  covers — any `Q` with `ι_e(Q) = 0`.
* `not_hasCircuit_five_of_cases` and `mc_eq_six_of_remaining_cases` assemble
  Lemma 1, the five cases (`λ = 5` proved), padding and `upper`.

#### Lemma 4 (kernel half) and Lemma 6 — `LowHalfMul3/CrossPart.lean` — PROVED

* `Phi := (ι_{a₂}, ι_{b₂})` carries the paper's cross part `(α, β, γ)`
  (`γ = ω(a₂, b₂)` is a coordinate of each contraction).
* `phi_eq_zero_iff`: on symmetric forms, `Φ ω = 0 ↔ ω ∈ Λ²(U)` — Lemma 4's
  `ker Φ = Λ²(U)`. **Not done:** Lemma 4's dimension count
  `dim Φ(Q) = 4 − d_U ≤ 2`.
* `pi2_lowMul3_two : pi2 (lowMul3 2) = q2Form` (explicit matrix, 36 entries by
  `simp`), `phi_q2` (`Φ(q₂) = (b₀, a₀, 0)`), and
  `lemma6 : Phi (wedge l r) ≠ Phi (pi2 (lowMul3 2))` for **all** `l, r`
  (rank 0 and 2 alike), from `lemma6_finite`, a `decide` over all 64 × 64
  pairs `(l, r)`.

#### Stopped here

The rest of step 5 — Lemma 3, Lemma 5, Proposition 7, Lemma 10, Theorem 11 —
sits on a layer that does not exist yet (see plan below) and is clearly over
the 2-hour threshold, so per the brief I stop and report the plan.

### Final verification (2026-10-31, end of phase 3)

| command | result |
| --- | --- |
| `lake build` | `Build completed successfully (1736 jobs)`, exit 0; no warning in our files (the build also replays the dependency's own deprecation/lint warnings in `N4/Rewiring.lean`) |
| grep `sorry\|native_decide\|ofReduceBool\|decide +native` in `LowHalfMul3/*.lean` | no hits |
| `lake env lean AxiomAudit.lean` | exit 0; **69** theorems, every one `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `ofReduceBool` |
| `lake env lean Challenge.lean` | exit 0; single warning `Challenge.lean:126:8: declaration uses 'sorry'` (unchanged hole) |

`lake build` was also green after each of steps 1, 2, 4, 3, Lemma 2,
Assembly, CrossPart (1710 → 1731 → 1732 → 1733 → 1735 → 1736 jobs).

### What is still missing for `¬ HasCircuit lowMul3 5` — exact Lean statements

Proved: `not_hasCircuit_five_of_cases (h1 : LambdaCase 1) (h2 : LambdaCase 2)
(h3 : LambdaCase 3) (h4 : LambdaCase 4) : ¬ HasCircuit lowMul3 5` and
`mc_eq_six_of_remaining_cases (h1 h2 h3) (h4 : StarFree) : MC(lowMul3) = 6`.
So exactly four statements remain:

```lean
def LambdaCase (lam : Nat) : Prop :=
  ∀ D : Circuit 6 5, D.Computes lowMul3 →
    D.gate 0 = aVar 3 0 * bVar 3 0 → D.left 0 = aVar 3 0 → D.right 0 = bVar 3 0 →
    (∀ k : Fin 5, (k.val < lam ↔ IsLinearGate D k)) → False

-- missing: LambdaCase 1, LambdaCase 2, LambdaCase 3, and

def StarFree : Prop :=          -- Theorem 11, algebraic form; implies LambdaCase 4
  ∀ (L R : Fin 4 → ANF 6), (∀ i, L i ∈ affine 6) → (∀ i, R i ∈ affine 6) →
    L 0 = aVar 3 0 → R 0 = bVar 3 0 →
    pi2 (lowMul3 1) ∈ quadSpan L R →
    ∀ f h : ANF 6, f ∈ V4 (quadSpan L R) → h ∈ V4 (quadSpan L R) →
      f * h + lowMul3 2 ∈ V4 (quadSpan L R) → False
-- quadSpan L R := Submodule.span F₂ (Set.range fun i => pi2 (L i * R i))
```

(As expected: the `λ = 1, 2, 3` cases, plus Theorem 11 for `λ = 4`.)

### Plan for `StarFree` (Theorem 11), with estimates

Everything left in the `λ = 4` proof sits on one missing layer: coefficients
of *products*. In dependency order:

1. **Product-coefficient layer** (≈ 3–5 h). Linear part `lin : affine 6 → (Fin 6 → F₂)`;
   `pi2 (L * R) = wedge (lin L) (lin R)` for affine `L, R` (this is what turns
   `quadSpan` into a span of `l ∧ r`'s); for `deg f, deg h ≤ 2`, the cubic and
   quartic parts of `f h` — in particular `π₄(f h) = f₂ ∧ h₂` (the Remark after
   Lemma 2). Route: `MonoidAlgebra.coeff_mul` plus the `support`-expansion
   technique already used in `Contraction.lean`; finite termwise identities
   by `decide` where possible.
2. **WLOG `dim Q = 4`, rank-2 basis containing `P₀`** (≈ 1–2 h): `V4_mono`
   (done) and an exchange-lemma argument; or avoid it by stating the case
   analysis for `dim Q ≤ 4` directly.
3. **Lemma 4, dimension half** (≈ 1–2 h): rank–nullity for `Phi` restricted to
   `Q`, with `P₀, Z₁ ∈ Q ∩ Λ²(U)` independent, giving `d_U ∈ {2, 3, 4}`.
4. **Lemma 3 (support), Lemma 5, Proposition 7** (≈ 3–4 h). Lemma 3 only
   needs the two instances `Z₁`, `Z₁ + P₀`, which are finite (pairs `(l, r)`
   with `Z − l ∧ r` decomposable: decide via 4×4 Pfaffians, or by hand).
   Lemma 5 needs step 1 (cubic part of `f h`). Prop 7 combines 4, 5, 6.
5. **Lemma 10 (types)** (≈ 2 h): by hand from `π(⟨l, r⟩) ⊆ F₂²`.
6. **Theorem 11 case analysis** (≈ 4–6 h): `d_U = 4` and `d_U = 3` type-`v`
   via `starFree_instance_of_iota`; `d_U = 3` full via the `(f, h)` →
   `(f, f+h)` normalisation and Prop 7; `d_U = 2` via the three-term structure
   and the rank argument.

Total ≈ 15–20 h of Lean. Alternative worth weighing before step 6: since
`StarFree` quantifies over affine `L, R` (`2⁷` choices each), a direct
`decide` is out of reach (≈ `10¹²` cases), but after steps 1–3 the residual
`d_U = 3` full-type case (98 orbits) might be checkable by `decide` on an
orbit-representative encoding, provided the orbit reduction itself is
proved — that is a separate, probably comparable, cost.

The `λ = 1, 2, 3` cases are not touched in Lean; their human proofs are the
prerequisite (`λ = 3` has a written proof pending review; `λ = 2, 1` open).
