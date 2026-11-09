# lowhalf-mul3

Lean 4 formalization of the **multiplicative complexity of the 3×3 low-half
multiplier**: `lowMul3 : Fin 3 → ANF 6`, the three low bits of `a · b mod 8` for two
3-bit integers `a = a₀a₁a₂`, `b = b₀b₁b₂`. The model is the unrestricted XOR–AND
circuit model of G. Morse, arXiv:2608.30238 (Definition 2.1): XOR and constants are
free, and each paid AND gate may multiply arbitrary affine combinations of the
inputs *and of earlier AND outputs*. The model comes from the dependency
[`unrestricted_boolean_mul`](https://github.com/GregoryMorse/unrestricted-boolean-mul),
pinned to `c014e498`.

The target statement is `MC(lowMul3) = 6`. The value 6 was already known from SAT
certificates (see `verification/certificates/`). This repository gives a structural,
human-readable lower-bound proof. The unconditional Lean theorem is
`UnrestrictedBooleanMul.LowHalfMul3.mc_lowMul3` in `LowHalfMul3Solution.lean`.

## Status

| Statement | Lean name | Status |
|---|---|---|
| `lowMul3` agrees with integer multiplication mod 8 on all 64 inputs | `lowMul3_eval` | proved |
| Upper bound: a 6-gate circuit | `upper : HasCircuit lowMul3 6` | proved |
| `MC = 6` follows from the absence of 5-gate circuits | `mc_eq_six_of_no_five` | proved |
| Normal form (Lemma 1): `g₀ = a₀b₀`, the `λ` linear gates come first | `normal_form_five` | proved |
| `λ = 5` (all gates linear) | `lambdaCase_five` | proved |
| `λ = 4` (Theorem 12, `StarFree`) | `starFree`, `lambdaCase_four` | proved |
| `λ = 3` | `lambdaCase_three` | proved |
| `λ = 2`, reduced to `TwoClaim` (Proposition `onehigh` for `P ∉ Λ²(U)`) | `lambdaCase_two_of : TwoClaim → LambdaCase 2` | proved |
| `TwoClaim`, part 1 (`z₂ ∉ V(S) + ⟨f h⟩`) and part 2 (last-gate form (a)) | `z2_not_mem_S_sup`, `formA_zero`, `formA_one_of_phi` (`LowHalfMul3/OneHigh.lean`) | proved |
| `TwoClaim`, last-gate form (b), and the full claim | `formB`, `twoClaim` (`LowHalfMul3/OneHighFinish.lean`) | proved |
| `λ = 1`, reduced to `TwoClaim` and five shared statements | `lambdaCase_one_of` (`LowHalfMul3/LambdaOne.lean`) | proved |
| `FeedbackNormal`, `Q2NotTwoWedges` | `feedbackNormal`, `q2NotTwoWedges` (`LowHalfMul3/Shared.lean`) | proved |
| `IdealExtract`, `FeedbackNoPlaceModLow` | `idealExtract` (`LowHalfMul3/IdealExtract.lean`), `feedbackNoPlaceModLow` (`LowHalfMul3/Shared.lean`) | proved |
| `LastFactorLowIdeal` | `lastFactorLowIdeal` (`LowHalfMul3/LastFactor.lean`) | proved |
| `MC(lowMul3) = 6` from the two remaining cases | `mc_eq_six_of_lambda_one_two : LambdaCase 1 → LambdaCase 2 → MC(lowMul3) = 6` | proved |
| `λ = 1` and `λ = 2` (unconditional) | `lambdaCase_one`, `lambdaCase_two` | proved |
| `MC(lowMul3) = 6` (unconditional) | `mc_lowMul3` (`LowHalfMul3Solution.lean`) | proved |

Each case is stated as (`LowHalfMul3/Assembly.lean`):

```lean
def LambdaCase (lam : Nat) : Prop :=
  ∀ D : Circuit 6 5, D.Computes lowMul3 →
    D.gate 0 = aVar 3 0 * bVar 3 0 → D.left 0 = aVar 3 0 → D.right 0 = bVar 3 0 →
    (∀ k : Fin 5, (k.val < lam ↔ IsLinearGate D k)) → False
```

and `λ = 2` now needs only (`LowHalfMul3/LambdaTwo.lean`, with `S = Q + ⟨Z₁⟩`):

```lean
def OneHigh (Q : Submodule F₂ TwoForm6) : Prop :=
  ∀ f h : ANF 6, f ∈ V4 Q → h ∈ V4 Q →
    (lowMul3 2 ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) ⊔ Submodule.span F₂ {f * h} → False) ∧
    ∀ F H : ANF 6,
      F ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) ⊔ Submodule.span F₂ {f * h} →
      H ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) ⊔ Submodule.span F₂ {f * h} →
      F * H + lowMul3 2 ∈ V4 (Q ⊔ Submodule.span F₂ {Z1form}) ⊔ Submodule.span F₂ {f * h} →
      False

def TwoClaim : Prop :=
  ∀ l r : Fin 6 → F₂, Phi (wedge l r) ≠ 0 → OneHigh (Q3span l r 0 0)
```

**Trust base.** Every proved theorem depends only on `propext`,
`Classical.choice` and `Quot.sound` (see `AxiomAudit.lean`). The development uses
no `native_decide`, no `ofReduceBool`, no `decide +kernel` and no custom axioms.
Finite facts are checked by plain `decide`, which the kernel replays; each such
check stays at or below about 2¹⁴ cases.

## Building

Toolchain: `leanprover/lean4:v4.35.0-rc3` (`lean-toolchain`), with Mathlib at the
matching tag (pinned in `lake-manifest.json`).

```sh
lake exe cache get        # optional: download the prebuilt Mathlib cache
lake build                # builds LowHalfMul3 and LowHalfMul3Solution
lake env lean AxiomAudit.lean   # prints the axiom closure of every listed theorem
lake env lean LowHalfMul3Challenge.lean    # the separate Challenge (one deliberate sorry)
```

`LowHalfMul3Challenge.lean` is a separate statement file. The library does not import it.

## Layout

| Path | Contents |
|---|---|
| `LowHalfMul3.lean` | Library root; imports all modules and summarizes them |
| `LowHalfMul3/Target.lean`, `Upper.lean` | The target and the six-gate circuit |
| `LowHalfMul3/Reduction.lean`, `NormalForm.lean`, `LambdaFive.lean`, `Assembly.lean` | Reduction to `¬ HasCircuit lowMul3 5`, the normal form, `λ = 5`, the case split `LambdaCase` |
| `LowHalfMul3/Derivative.lean`, `Contraction.lean`, `LemmaTwo.lean`, `CrossPart.lean`, `Product.lean`, `LineDerivative.lean`, `LemmaThree.lean`, `Types.lean`, `MainTheorem.lean` | The `λ = 4` proof (Lemmas 1–11 and Theorem 12 of the `λ = 4` note) |
| `LowHalfMul3/LambdaThree.lean`, `Coset.lean`, `LemmaA.lean`, `LemmaC.lean` | The `λ = 3` proof: reduction, the general coset lemma (B3a/B3b), Lemma A and Lemma C for spaces without a good direction |
| `LowHalfMul3/LambdaTwo.lean` | The `λ = 2` reduction to `TwoClaim`; Proposition `onehigh` inside `Λ²(U)`; `g₂` cannot place `z₁` outside `Λ²(U)` |
| `LowHalfMul3/OneHigh.lean` | Parts 1 and 2 of `TwoClaim`: the good direction of `S`, and the cube sum in `ker l` that excludes form (a) |
| `LowHalfMul3/LambdaOne*.lean` | The `λ = 1` proof (merged from the `lambda1` branch), from `TwoClaim` and the five shared statements of `LambdaOneBase.lean` |
| `LowHalfMul3/OneHighFinish.lean` | Form (b) and the complete `TwoClaim` |
| `LowHalfMul3/Shared.lean`, `IdealExtract.lean`, `LastFactor.lean` | Feedback normalization and modular exclusion, the rank obstruction, ideal extraction, and last-factor rigidity |
| `AxiomAudit.lean` | `#print axioms` for every theorem listed |
| `LowHalfMul3Challenge.lean` | The statement `MC(lowMul3) = 6` (deliberate `sorry`) |
| `LowHalfMul3Solution.lean` | The proofs of `LambdaCase 1`, `LambdaCase 2`, and `mc_lowMul3` |
| `comparator.json` | Palomar Comparator configuration for the Challenge, Solution, headline theorem, and three standard axioms |
| `LICENSE` | MIT licence (the copyright line still carries the placeholder `<AUTHOR>`) |
| `formalization.yaml` | Metadata, the paper-to-Lean correspondence and the recorded divergences |
| `LEAN_LOG.md` | Chronological development log, with human-readable sketches wherever the Lean route differs from the paper |
| `paper/` | Case notes (`paper/notes/lambda{1,2,3,4}_proof.tex`) and a snapshot of the merged manuscript (`paper/main.tex`); the manuscript itself is maintained at https://github.com/bishara74/lowhalf-mul3-paper |
| `verification/` | Computational evidence: exhaustive Python checks of every lemma, SAT certificates, the internal paper audits (`audit-v1/`, `audit-v2/`), and `verification/lean-support/` (a full check of `BadClaim`); see `verification/README.md` |

## Palomar submission

Not submitted. The repository is prepared for Palomar's checks as follows
(`verification/lean-support/palomar_preflight.md` records the first preflight).

* All `.lean` files use the Lean module system.
* The statement module is `LowHalfMul3Challenge` (root file
  `LowHalfMul3Challenge.lean`). It was renamed from `Challenge` because the
  dependency `unrestricted_boolean_mul` has a top-level `Challenge`, which Palomar
  rejects (`challenge.module_root_shadowed`).
* `comparator.json` names `LowHalfMul3Challenge`, a Solution module
  `LowHalfMul3Solution`, the theorem `UnrestrictedBooleanMul.LowHalfMul3.mc_lowMul3`
  and the axioms `propext`, `Classical.choice`, `Quot.sound`.

The Solution has its own Lake library and is included in the default build.
The Challenge is kept in a separate module with one deliberate proof hole.
See the [Palomar preparation record](verification/lean-support/palomar_preflight.md)
for the checks performed on the finished local source and their scope.

## Where the Lean route differs from the paper

The Lean proofs of `λ = 4` and `λ = 3` follow the notes, but use shorter
arguments in several places. Each one is recorded in `formalization.yaml`
(`fidelity.divergences`) and sketched in `LEAN_LOG.md`.

* **Lemma 8′** (`starFree_of_goodDir`) handles every space with a "good
  direction". For `λ = 4` this replaces Lemma 5, Proposition 7 and the
  `dim Q = 4` reduction. For `λ = 3` it gives Lemma C and Proposition B for such
  spaces through `Q₃ + ⟨Z₁⟩`.
* **The coset lemma** (`coset_obstruction`) is stated once for an abstract base
  space: it contains the affine functions, its `a₂`/`b₂` derivatives are
  constant, and `1, a₀, b₀` lie in the radical of the carry pairing. It covers
  Lemmas B3a/B3b for every `Q ⊆ Λ²(U)`, and is meant for reuse in `λ = 2`
  (inside-`U` branch) and in the core branch of `λ = 1`.
* **Spaces without a good direction** (26,928 spans). Both conjuncts of
  `BadClaim` follow from one direction `e` with a nonzero `a₁`/`b₁` component.
  Lemma A uses Lemma W, a quadratic function vanishing on a hyperplane
  `{a = α}` has quadratic part `a ∧ m`. Lemma C uses a third difference that
  detects the derivative of the carry. This replaces the product lemma, the
  radical lemma, the weight bounds, Lemma D1 and the 4-form computations.
* **`λ = 2`.** The Lean reduction does not split on `deg g₂`, and needs neither the
  replacement lemma nor Lemma P. If `g₂` places `z₁`, Lemma A's derivative argument
  with Lemma W and Lemma 3 excludes `P ∉ Λ²(U)`, and the coset lemma handles
  `P ∈ Λ²(U)`. Otherwise `g₃` places `z₁`, and Proposition `onehigh` finishes.
