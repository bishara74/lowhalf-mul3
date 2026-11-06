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
`verification/README.md` and `lambda3-checks/t11_*`. The review quotes 164,639;
its script is not in the repository, so the 43-space difference could not be
traced. Counting `⟨w₁, w₂⟩` without `P₀` gives 192,697, so that is not the
reviewer's convention either. The count of spans without `GoodDir`, 26,928,
agrees with the review.
