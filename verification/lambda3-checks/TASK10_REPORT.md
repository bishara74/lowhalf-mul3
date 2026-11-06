# TASK 10 REPORT — λ = 1 certified by an independent line B (T10-1)

**Result.** The independent line-B check reproduces line A's λ = 1 totals on every one of the 249 g1 orbits: **0 mismatches** in all 12 compared counts per orbit. Over all g1, both lines find 4,644,000 candidate pairs (g2, g3), all closed at the first-derivative level (level i) and 0 open. By the Task 10 rule, λ = 1 is now **CERTIFIED**, and `session_log/LOWER_BOUND_SUMMARY.md` has been updated to match. Every λ = 1 … 5 is now excluded at k = 5 without SAT: λ = 4, 5 by human proof and λ = 1, 2, 3 certified by two independent implementations.

## Method (line B, `t10_l1_lineB.py`)
- **No shared code with line A:** it does not use `t6_common.py`, `t6_B.py`, `t9_l1.py` or `t9_l1s.py`. It imports only the line-B primitives of `t6_B_indep.py` (64-bit truth tables, `multi_echelon`, `elements`, `sub2`, `level_feasible2`) and the line-B group generators and point-map composition of `t9_l2_indep.py`.
- **g1 orbits rebuilt independently.** A g1 is a 2-dim subspace of V1/<1> (basis a0..b2, a0b0) not inside Aff/<1>. There are 2,016 of them, which union-find under the 32-element group sorts into 249 orbits. This matches line A one-to-one, with equal orbit sizes. Each orbit is represented by its **largest** plane; line A uses the smallest, and only 12 representatives coincide (`t10_orbit_map.json`). Per-orbit agreement therefore also checks that every count is orbit-invariant. g1 never places z1, z2 or z1+z2 (0, 0, 0 in both lines).
- **Same model as line A.** g2 and g3 range over all coordinate-nonlinear planes (10,144 and 42,784). z1 is placed by g2 (A-type g2), by g3 (B-admissible), or by g4. The g4 case requires z2 or z1+z2 to already be in V4; it is counted as n_C_g3 and checked exactly, and it never occurs. Candidates are tested at level i (D_e along e_a2, e_b2, e_a2+e_b2, jointly with the a0a1b0b1 coefficient), and the exact last-gate check is applied if level i does not close. The z1-placement screen uses a single echelon reduction per g2, which is 4.7 ms instead of 17.1 ms. It was checked against the plain span test.
- **Independent stabiliser reduction** (new code, not line A's):
  - g2 is reduced under the stabiliser of the g1 plane, acting linearly on V2 coordinates.
  - For z1-placing g2, line B additionally reduces g3 under the stabiliser of both the g1 and g2 planes. Line A does not reduce g3.
  - Counts are weighted by orbit size.
  - Four orbits with a degenerate g1 (g1 ∈ V1: line-B orbits 0, 1, 20, 21) are run unreduced.
  - Justification: Lemma 3'' (HUMAN PROOF). z1 is fixed and z2 is fixed mod V1. The level-i condition (∃ v ∈ V4 with FH+z2+v independent of a2, b2 and with zero a0a1b0b1 coefficient) is preserved by every group element.

## Timing
- **Estimate** (`t10_timing_estimate.json`):
  - Unreduced run: 20.5 CPU-h.
  - Reduced run plus the 10-orbit unreduced validation: 6.27 CPU-h, below the 12 CPU-h limit, so it was run.
- **Estimate revised mid-run.** After chunk 3, the measured cost per orbit was about 1.7–1.8× the model. The B-pair reduction was weaker than assumed, because candidate pairs concentrate on g2 with large stabilisers. The projection rose to about 10.5 CPU-h, still below 12.
- **Actual:**
  - Reduced run: 33,053 CPU s.
  - Validation: 5,377 CPU s.
  - Total: **38,430 CPU s ≈ 10.7 CPU-h**, or 38,488 s counting 36 duplicate unit records from the load-balancing workers. The duplicates were checked to be identical and counted once.

## Validation of the reduction (10 g1 orbits, unreduced vs reduced, line B)
| line-B orbit | line-A rep | Stab | g2 reps | n_pairs unreduced | n_pairs weighted | pairs tested reduced | closed_i unred / weighted | match |
|---|---|---|---|---|---|---|---|---|
| 24 | 94 | 32 | 1231 | 1488 | 1488 | 764 | 1488 / 1488 | yes |
| 6 | 1 | 16 | 2332 | 1488 | 1488 | 1488 | 1488 / 1488 | yes |
| 7 | 5 | 16 | 2332 | 1488 | 1488 | 1488 | 1488 / 1488 | yes |
| 4 | 12 | 8 | 3040 | 400 | 400 | 324 | 400 / 400 | yes |
| 5 | 16 | 8 | 3040 | 400 | 400 | 324 | 400 / 400 | yes |
| 41 | 30 | 4 | 4456 | 248 | 248 | 248 | 248 / 248 | yes |
| 42 | 32 | 4 | 4456 | 248 | 248 | 248 | 248 / 248 | yes |
| 166 | 207 | 2 | 5188 | 72 | 72 | 38 | 72 / 72 | yes |
| 35 | 25 | 16 | 2332 | 55904 | 55904 | 14504 | 55904 / 55904 | yes |
| 62 | 131 | 32 | 1231 | 55904 | 55904 | 7662 | 55904 / 55904 | yes |

All 12 counts agree on every validation orbit. Orbits 35 and 62 each contain a z1-placing g2, so the g3 reduction is validated too (55,904 pairs unreduced, against 14,504 and 7,662 tested reduced). The unreduced runs also match line A directly.

## Totals (line B = line A, field by field)
- **Over orbit representatives:** n_g2_A 38, n_g2_B_admissible 372654, n_pairs 2295688, closed_i 2295688, open_i 0, closed_exact 0, open_exact 0, n_C_g3 0, n_z2_or_z12_via_g2 0.
- **Over all 2,016 g1 (× orbit size):** n_g2_A 72, n_g2_B_admissible 918432, n_pairs 4644000, closed_i 4644000, open 0.
- **Level-i tests actually run by line B:** 672,904.

## Decided unattended
1. A stabiliser reduction was implemented independently rather than running unreduced (20.5 CPU-h > 12).
2. The run continued after the revised projection (~10.5 CPU-h), because it was still under the 12 CPU-h limit.
3. A reverse-order load-balancing option and per-orbit worker queues were added mid-run (ordering only, no change to any test). The resulting duplicate units were de-duplicated after an identity check.
4. The analysis kernel restarted once between chunks 8 and 9. No data was lost (the workspace was intact), and the driver helpers were rewritten to `t10_helpers.py`.

## Files
`t10_l1_lineB.py`, `t10_helpers.py`, `t10_l1_orbits_lineB.json`, `t10_orbit_map.json`, `t10_timing_estimate.json`, `t10_l1_compare.json`, checkpoints `t10_l1_red_p*.jsonl` / `t10_l1_unred_p*.jsonl`, and `TASK10_BRIEF.txt` (all in `session_work/T6/`); `session_log/LOWER_BOUND_SUMMARY.md` (updated; previous version in `session_log/backup/T10-1/`).
