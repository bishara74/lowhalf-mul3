# LOWER BOUND SUMMARY — no 5-gate circuit for the 3×3 low-half product mod 8 (no SAT)

Targets z0 = a0b0, z1 = a0b1 + a1b0, z2 = a0b2 + a1b1 + a2b0 + a0a1b0b1. Gates are AND gates; XOR, NOT and constants are free. Circuit model and normal form as in `lambda4_proof.tex`: g0 = a0b0, the λ linear gates come first, and λ ≥ 1.
A circuit with fewer than 5 gates can be padded to 5 gates, so excluding k = 5 gives MC ≥ 6. Together with the verified 6-gate circuit, MC = 6.
Every λ = 1, …, 5 is excluded without a SAT solver.

| λ | method | label | evidence |
|---|---|---|---|
| 5 | all gates linear ⇒ every function in V5 has degree ≤ 2, but deg z2 = 4 | HUMAN PROOF | `lambda4_proof.tex` (normal-form section) |
| 4 | derivative lemma (Lemma 8) and rank-2 case analysis (Theorem C), with N1, N2, independence WLOG, product formula, Lemmas 1, 4–7, 9, 10, Theorem B | HUMAN PROOF | `lambda4_proof.tex`; `session_log/proofs/` (theoremC_lambda4.md, lemma9_derivative.md, lemma10_types.md, N1_N2_normalisations.md, lemma1_V4.md, product_formula.md, independence_wlog.md); RESULTS row T4c-AMEND |
| 3 | z1-placement, then a first-derivative test on the last gate (D_e and the a0a1b0b1 coefficient); 8,545 classes, 344,368 surviving pairs, all closed | CERTIFIED (exhaustive, two independent implementations, 0 mismatches) | `TASK6_REPORT.md`, `TASK8_REPORT.md`, `t8_part1_compare.json`, `t6_class_table.csv` |
| 2 | z1-placement; first-derivative test on the last gate; exact last-gate check for the rest; 83 classes, 400,820 candidate pairs (g2, g3): 398,756 closed at level i, 2,064 by the exact check, 0 open | CERTIFIED (exhaustive, two independent implementations, 0 mismatches) | `TASK8_REPORT.md`, `TASK9_REPORT.md`, `t8_l2_summary.json`, `t9_l2_compare.json` |
| 1 | same pipeline with g1 nonlinear: 249 g1 orbits; 4,644,000 candidate pairs (g2, g3) over all g1 (2,295,688 over the orbit representatives), all closed at level i, 0 open | CERTIFIED (exhaustive, two independent implementations, 0 mismatches on all 249 g1 orbits; Task 10) | `TASK9_REPORT.md`, `t9_l1_summary.json` (line A); `TASK10_REPORT.md`, `t10_l1_lineB.py`, `t10_l1_compare.json` (line B) |

**Shared assumptions:**

- Normal-form lemma (`lambda4_proof.tex`).
- Symmetry reduction by Lemma 3'' (HUMAN PROOF, `session_log/proofs/lemma3pp_symmetry_any_lambda.md`).
- V_i characterisations (Lemma 1 and its analogues).
- For λ = 1, line A's stabiliser reduction of g2 was checked against an unreduced run on 3 g1 orbits. Line B used its own reduction (g2 under the stabiliser of the g1 plane; for z1-placing g2 also g3 under the stabiliser of the g1 and g2 planes), checked against an unreduced line-B run on 10 g1 orbits (identical counts, including 2 orbits with a z1-placing g2). Line B rebuilt the 249 g1 orbits itself and used the largest plane of each orbit as representative (line A: the smallest), so per-orbit agreement also checks the orbit invariance of the counts.

**Upper bound:** the 6-gate circuit was found and verified on all 64 inputs by two simulators (`t5_run_a_iii_k6.json`). The SAT certificates (supervisor package and earlier drat-trim proofs) are no longer needed for the lower bound; they remain as an independent cross-check.

**Note (Task 11, T11-1):** for λ = 3 there is now also a written proof without enumeration, `session_log/lambda3_proof.tex`. It is AI-written and pending human review, every lemma passed an exhaustive computer check, and it rests on the HUMAN PROOF results of `lambda4_proof.tex`. The λ = 3 label above (CERTIFIED) is unchanged.
