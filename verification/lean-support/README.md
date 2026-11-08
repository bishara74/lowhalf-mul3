# lean-support: classical checks of open Lean statements

## `check_badclaim.py` — the Lean statement `BadClaim`

`BadClaim` (`LowHalfMul3/LambdaThree.lean`): for every
`Q₃ = span{P₀, l₁∧r₁, l₂∧r₂}` with `¬ GoodDir Q₃`, there are no `f, h ∈ V(Q₃)` with
`f·h + T ∈ V(Q₃)`, for `T ∈ {z₁, z₂, z₂ + z₁}`.

The script follows the Lean definitions (`wedge`, `iota`, `GoodDir`, `V4`) and is
exhaustive: all 652 forms of rank ≤ 2 for each generator, all resulting spans, and
for each span without `GoodDir` an exact GF(2) linear-algebra decision of the
placement question for every `f ∈ V(Q₃)` modulo constants (511 representatives;
for fixed `f`, `∃ h, fh ∈ T + V ⇔ T ∈ fV + V`).

Run: `python check_badclaim.py` (about 6 minutes with the default 7 worker
processes). The output is `check_badclaim_results.json`; `check_badclaim.log` is
the log of the committed run.

| quantity | value |
|---|---|
| forms of rank ≤ 2 | 652 |
| distinct spans `⟨P₀, w₁, w₂⟩` (dim 1 / 2 / 3) | 164596 (1 / 605 / 163990) |
| spans without `GoodDir` | 26928 (all of dimension 3, none contains `Z₁`) |
| bad spans with a placement of `z₁` / `z₂` / `z₂+z₁` | 0 / 0 / 0 |
| positive control `a₀b₁` placeable (bad spans) | 26928 of 26928 |
| control sample: 2000 dim-3 spans with `GoodDir`, placements of `z₁` / `z₂` / `z₂+z₁` / `a₀b₁` | 208 / 0 / 0 / 2000 |

Result: **PASS**. `BadClaim` holds on its full finite domain. The controls show
that the checker detects placements when they exist: `z₁` is placeable in 208 of
the 2000 sampled good spans, as Lemma A allows, and `z₂`, `z₂+z₁` in none, as
Lemma C predicts.

**Counting convention.** 164,596 counts distinct subspaces `⟨P₀, w₁, w₂⟩`,
including the degenerate ones of dimension 1 and 2. This agrees with
`verification/README.md` and `lambda3-checks/t11_*`. An earlier figure of 164,639, quoted in the 2 November review, came from a bug in the reviewer's own script and has been withdrawn; 164,596 is confirmed independently. The count of spans without `GoodDir`, 26,928,
agrees with the review.

## `TwoClaim` (`λ = 2`, Proposition `onehigh` outside `Λ²(U)`)

`check_twoclaim.py` (results `check_twoclaim_results.json`, log `check_twoclaim.log`)
checks `TwoClaim` on its whole domain: all 616 rank-two forms `P ∉ Λ²(U)`
(the 2-planes `⟨l, r⟩` not contained in `U`), and all `g = f h` with `f, h ∈ V(Q)`. The
script also checks the intermediate claims planned for the Lean proof.

**Method.** Functions are 64-bit truth tables, so products are bitwise AND and every
space is an F₂-subspace of F₂⁶⁴. Membership is exact elimination. Write
`A = V(S)` with `S = span{P₀, P, Z₁}`. A last product with factors in `A + ⟨g⟩`
normalizes to one of two forms:
* (a) `F H + σ g + z₂ ∈ A` with `F, H ∈ A`. This is tested against all products
  `F H`, reduced mod `A`.
* (b) `k (g + F) + z₂ ∈ A` with `k, F ∈ A`. For fixed `k` this is linear:
  `k g + z₂ ∈ A + kA`. Only `k` with `(1 + k)(z₂ + v) = 0` for some `v ∈ A` can occur;
  this set `K_P` is computed over all `k, v ∈ A`.

`g` is enumerated over `f, h ∈ V(Q)` modulo constants, and deduplicated by its coset
mod `A`; that is 5,678,152 cosets over all planes.

| Claim (every plane) | Failures |
|---|---|
| `z₂` semantics on 64 inputs | none |
| `dim A = 10` | 0 |
| (i) `z₂ ∉ A + ⟨g⟩` | 0 |
| (a), `σ = 0`: `F H + z₂ ∉ A` | 0 |
| (a), `σ = 1`: `F H + g + z₂ ∉ A` | 0 |
| (b), every `k ∈ K_P` | 0 |
| part 1: `S` has a good direction | 0 |
| part 2: the fourth difference over the cube `K = span{u + l(u) w}` in `ker l` (`u ∈ e₀, e₁, e₃, e₄`, `w ∈ {e₂, e₅}`, `l(w) = 1`) is 0 on every `F H`, `F, H ∈ A`, and 1 on `z₂` | 0 |
| rigidity: `K_P ⊆ {1, 1 + a₀b₀}` | 0 (`K_P = {1, 1 + a₀b₀}` for all 616) |
| (b) with `k = 1 + a₀b₀`: `g + a₀b₀ g + z₂ ∉ A + a₀b₀ A` | 0 |

**Controls.**
* Positive: on 6 planes, `z₂` is replaced by planted targets `g + a`, `F H + a`,
  `F H + g + a` and `k (g + F) + a` (random `F, H, k, a ∈ A`, `g = f h`). Each one is
  found by the test it targets, and the rigidity test reports failure where it should.
* Direct enumeration of all `F, H ∈ A + ⟨g⟩` (2048² products) finds no placement of
  `z₂` on 12 `(P, g)` pairs. It finds each of 3 planted form-(b) targets.

Result: **PASS** (79.3 s).

## Palomar preflight

`palomar_preflight.md` records a local run of Palomar's preparation phase against
commit `33a708d`. It also covers the verification-stage preconditions that can be
checked without the Linux sandbox. `palomar_preflight_report.json` is the verifier's
report, unchanged. Nothing was submitted.
