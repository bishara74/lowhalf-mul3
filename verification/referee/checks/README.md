# Independent referee checks

These scripts were written afresh for the attached `main (1).tex` snapshot in `../source.tex`. They do not import, read, invoke, or reuse the pre-existing workspace checks, proofs, reports, or certificates. Standard Python 3 only; no SAT solver or third-party package.

Run everything from the `referee` folder:

```sh
python3 checks/run_all.py
```

Collect already-completed per-check JSON without rerunning:

```sh
python3 checks/run_all.py --collect-only
```

`results.json` identifies the source by SHA-256, gives all 36 classifications, records actual executed counts and coverage limits, and hashes every script. Each executable script has a planted mutation or relaxed positive instance that exercises its detection predicate. Assertions must remain enabled (do not use `python -O`).

| Script | Checked domain |
|---|---|
| `algebra.py` | Six-variable 64-bit ANF algebra; 10,000 random comparisons of transform multiplication against separate monomial-OR multiplication. |
| `structure.py` | All rank/exterior application forms; all D1 generator pairs; all B3U spaces; all 210 rank-two Plücker matrices and 1,260 kernel bases; all 2,016 first planes; degenerate first gate; upper-bound equality and all 64 inputs. |
| `quadratic_products.py` | All 606 rank-two-generated spaces containing P0; every factor plane modulo constants; exact extraction/replacement/top-degree checks. Also 1,000,000 unrestricted random quadratic pairs, plus deliberate edge cases. |
| `weights_and_product4.py` | All quadratic functions on 4 and 6 bits for weights; every four-variable factor plane for the product lemma, including dependent/constant variants through exact identities. |
| `multipliers.py` | All k and exact existence of R in the three multiplier lemmas, on every original-coordinate application space; no orbit reduction. |
| `ordinary_products.py` | The 32 input maps and all their compositions; all cubic first-space orbits; every ordinary factor plane and exact pair-sum test. |
| `feedback_and_early.py` | All original-coordinate arbitrary-g two-feedback systems (2^64 functions per system by elimination), and every next-gate plane for every cubic first-output coset. |
| `conditioned_products.py` | 1,000,000 independently sampled admissible four-coordinate pairs embedded into six variables; every sampled pair satisfies the product lemma's antecedent. Includes all three proof branches and deliberate rank-0/rank-2 edges. This does not exhaust six-variable pairs. |
| `source_audit.py` | Source identity, all labels/references, result inventory, cycle test on the proof-use graph supplied by the reading audit. Reference semantics and graph completeness are checked by reading, not inferred by this script. |
| `run_all.py` | Runner, status/control validation, source hash validation, and results aggregation. |

Each Boolean function is a 64-bit ANF mask, with bit `s` denoting the squarefree monomial whose variable set is the 6-bit integer `s`. Variable order is `a0,a1,a2,b0,b1,b2`. Temporary 64-bit truth tables accelerate multiplication and linear elimination; the two-feedback script stacks two equations into 128 bits, without enlarging the function domain.

Factor planes are enumerated as `i < j < i XOR j` modulo constants. Constant changes and basis changes add only available functions; dependent factors give an available function or zero. Thus those cases are covered by identities rather than omitted from the domain. The product and extraction checks include P in Lambda^2(U), redundant P, and rank-zero quadratic factors.

Numerical differences from the paper's verification tables are not proof counterexamples: most checks here enumerate all original-coordinate spaces rather than symmetry representatives. The ordinary-products count includes zero product cosets explicitly in its internal sumsets; its reported nonzero-coset total excludes one zero per orbit.
