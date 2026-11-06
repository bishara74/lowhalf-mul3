# Exhaustive checks for the lambda = 2 and lambda = 1 drafts

Run from `task12/`:

```bash
python3 checks/run_all.py
python3 finalize_release.py
```

Python 3.10+ standard library only. No SAT solver, external search code, or numpy is used. Each child has a 1,800-second timeout; individual runtimes are recorded in `results.json`. Each full enumeration also writes per-orbit checkpoints. The master run and release audit hash their Python sources. Verification of a mathematical draft does not imply human review.

## Representation and coverage

Public algebra functions use ANF masks: bit `m` is the monomial with variable subset `m`. Variables are `a0,a1,a2,b0,b1,b2`. The Boolean Möbius transform maps this representation bijectively to truth tables, where a product is bitwise AND. `mul_slow` uses the separate monomial-union rule. All 4,096 monomial products and all 32 symmetries are checked, including every point of their input permutations and every group composition.

A factor plane is a 2D subspace modulo constants, written `i < j < (i ^ j)`. The first six coordinates are homogeneous affine inputs. A semantic nonlinear plane has some vector outside their span. Constants and plane basis changes add only available functions to the product, so they preserve the new function space. Dependent factors also add only an available function. Every prefix in use contains `P0` and `a0`; the nonlinear plane `P0,a0` supplies that same redundant space, so omitted dependent-factor descriptions cannot omit a circuit space.

Products are reduced modulo the *actual* available function space. Multiplicities of first factor planes are retained. The 83 quadratic-space representatives cover 606 spaces. The 222 first-output-function-space orbits in lambda = 1 carry all 2,016 first factor planes (197 of these orbits carry all 1,920 cubic planes). They are not the 249 factor-plane orbits of the previous report.

The exact feedback screen uses this algebraic split, valid even if the base contains cubic signals:

- Both factors in the base `B`: enumerate all product cosets directly.
- One factor uses a new signal `g`: after plane operations it is `k*(g+F)`, with `k,F` in `B`.
- Absorb an output `g` coefficient by changing the constant of `k`. If the result is `T+v`, then `(1+k)*(T+v)=0`.
- Enumerate every eligible `k`; enumerate the complete image of `k*B` modulo `B` and test `T+k*g` exactly. Both constants of `k` are considered.
- Already available targets, zero/redundant `g`, and final affine-factor products are explicitly covered.

This yields a complete finite check rather than a necessary derivative test. `check_screen_bruteforce.py` independently compares its results and placing-plane counts against direct enumeration of **all 17,650,560** next nonlinear planes for **all 1,740** cubic first-output cosets of lambda = 1.

## Scripts and corresponding statements

| Script | Exact statement / domain |
|---|---|
| `check_algebra_symmetry.py` | Boolean algebra, 32 maps, all input points and compositions; all quadratic spaces/orbits |
| `check_replacement.py` | L2 Lemma 2 and L1 Lemma 2: every first nonlinear plane in the full application domain, including zero/redundant increments |
| `check_degree.py` | L2 Lemma 4, on all first nonlinear planes |
| `check_annihilator.py` | L2 Lemma 5: every pair `k,R` for all 581 applicable spaces; 68 symmetry representatives |
| `check_final_factor.py` | L2 Lemma 6: every `k,R` for all 580 applicable spaces; 67 representatives |
| `check_two_feedback.py` | L2 Lemma 7: all 268 representative systems, arbitrary Boolean `g`; exact elimination covers all `2^64` choices and every auxiliary correction |
| `check_reordering.py` | L2 Proposition 8: equality of full available spaces, for all qualifying higher-degree output cosets in all 13 applicable orbits |
| `check_ideal_extraction.py` | L2 Lemma 9: all affine/nonlinear factor planes, constants and dependent factors, all quadratic representatives modulo I, plus the support-based construction |
| `check_rank_exterior.py` | L2 Lemma 10: every rank-two form and every exterior multiplier, via exact image elimination |
| `check_one_high_space.py` | L2 Lemma 11 / Proposition 12: all initial products, all final factors, and all 11 inside-U extension spaces |
| `check_lambda1_normal_form.py` | L1 Lemma 3: all 2,016 planes, normalization identity and degree classification |
| `check_core_cubic.py` | L1 Lemma 5 / Proposition 7: all 33 core cubic spaces and all first/final products, with pairing premises checked |
| `check_early_core.py` | L1 Lemma 6: every cubic first-output coset and next z1-placement plane |
| `check_ordinary_pair.py` | L1 Lemma 8: all 197 cubic first spaces, every pair of product cosets and every output correction |
| `check_noncore_multiplier.py` | L1 Lemma 9: every k,R pair in all 164 noncore application spaces |
| `check_noncore_onehigh.py` | L1 Lemma 10: all noncore first spaces, next nonlinear products, and final factors |
| `explore_prefixes.py` | L1 Lemma 4 / first-output census: all first planes and all three target cosets, plus a planted reachable target |
| `check_screen_bruteforce.py` | Independent direct cross-check of every cubic first-output coset against all next nonlinear planes |
| `check_lambda2_exact.py` | Higher-degree lambda = 2 exact search, all possible target placements |
| `check_lambda2_full.py` | Full lambda = 2 search, including quadratic and redundant products, independent of imported L3 |
| `check_lambda1_exact.py` | Full lambda = 1 search, all first degrees, all possible target placements |
| `check_level_survivors.py` | Weaker derivative-plus-Omega diagnostic, recording every difficult coset and its plane multiplicity |
| `check_historical_counts.py` | Fresh counts versus the supplied reports; exact lambda = 2 redundant-coordinate correction |
| `check_quotient_witness.py` | Independent reconstruction and full simulation of the relaxed quotient-only counterexample |

Every executable check has a mutation or relaxed positive control and records its detection count. `core.py`, `placement.py`, and `lambda1_states.py` are shared implementation helpers, not independent check scripts.

## What the counts mean

The higher-degree lambda = 2 branch has 694,540 distinct output cosets from 814,912 factor planes over the 83 representatives. Exactly 37,518 output cosets admit a semantic nonlinear next plane placing `z1`. The weaker derivative-plus-Omega test leaves **1,776 output cosets, weighted as 2,064 `(g2,g3)` factor-plane pairs**. Thus 2,064 is not a count of distinct `(Q2,g2)` function spaces. All fail the exact final-gate test.

The derivative diagnostic uses the killing directions of the quadratic prefix, or all three external directions if none kills it, together with the Omega coefficient. Its counts are reported for the chosen 83 representatives. No invariance of the one-direction-plus-Omega filter under all shifts is assumed or needed for the exact-circuit proof.

The full lambda = 2 enumeration has 398,732 candidate pairs of actual-function planes, versus 400,820 in the supplied historical coordinate enumeration. The exact difference is 2,088. If `g2` is redundant, one coordinate-plane in the next step has four lifts for a genuinely nonlinear function-plane, and an affine function-plane has three lifts that look coordinate nonlinear. The extra count is exactly

```text
sum_Q 3 * (# first nonlinear planes with output in V(Q))
        * (# all factor planes in V(Q) placing z1) = 2,088.
```

Adding it reproduces 400,820. These extra descriptions all concern low-degree gates and do not alter the 2,064 difficult pairs. For lambda = 1 the new weighted total is 4,623,120, versus 4,644,000 historically. The representation also discards redundant first-gate coordinates, so no complete field-by-field reconciliation is claimed. The complete new search and the separate direct screen check establish their own coverage; the historical counts are not premises.

## Status of the mathematical result

Both full exact enumerations pass with no counterexample. Both human-style proof drafts are now complete and labelled **PROVED**, with no OPEN lemma remaining. The key steps are ideal extraction for lambda = 2 and the two-hyperplane parity / modulo-I multiplier arguments for lambda = 1. See `../PROOF_AUDIT.md` for every named result and its check. The multiplier lemmas are checked on every function pair in their explicit application domains, not on unrelated quadratic or quartic functions outside them. The arbitrary-function claim of the two-feedback lemma is covered on all 2^64 intermediate functions by exact linear elimination. Human review is pending.

The exploratory `explore_lambda1_quotient.py` and `explore_noncore_onehigh.py` files record research diagnostics; their descriptive outcomes are not failed validation statuses. The quotient-only shortcut has a relaxed solution, whose explicit witness is independently verified. Earlier OPEN annotations in archived checkpoints describe the earlier state, not the completed primary drafts.
