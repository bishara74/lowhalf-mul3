# Proof and verification audit

The current primary documents are `lambda2_proof.tex` and `lambda1_proof.tex`. Both contain complete written arguments and label their results PROVED under the task's convention: written proof plus passing exhaustive application-domain check. They remain AI-written drafts pending human review. Earlier OPEN notes in `checkpoints/` and the historical research notes describe earlier states.

## Lambda = 2

| Result | Written argument | Exact check |
|---|---|---|
| Lemma 2: quadratic replacement | Imported product lemma; preserve actual tail functions and pad redundant rank-two directions | `check_replacement.py` |
| Lemma 3: symmetry | Explicit 16 shifts and operand exchange, target correction in Aff+P0 | `check_algebra_symmetry.py` |
| Lemma 4: top degree | Exterior square in a two-dimensional quadratic space | `check_degree.py` |
| Lemma 5: four multipliers | Radical, weight, and codimension-two support arguments | `check_annihilator.py` |
| Lemma 6: last-factor rigidity | Rank-two types; external differentiation and fiber restrictions | `check_final_factor.py` |
| Lemma 7: two feedback placements | Common low-bit fiber forces rank-two support back into U | `check_two_feedback.py`, exact elimination over all Boolean intermediate functions |
| Proposition 8: rank-two reordering | Equality of full available spaces | `check_reordering.py` |
| Lemma 9: extraction modulo I | Actual product representatives; intersecting three-form supports; rank-two residual | `check_ideal_extraction.py`, affine/nonlinear planes, constants, dependent factors, and construction cases |
| Lemma 10: rank/exterior obstruction | Explicit radical equations; decomposable factors of Omega lie in U | `check_rank_exterior.py`, all exterior multipliers covered by exact image elimination |
| Lemma 11: inside-U obstruction | Hypothesis audit of the given algebraic B3a/B3b arguments, not an assumption of rank-two generation of S | `check_one_high_space.py`, all 11 application spaces and all first/final products |
| Proposition 12: one-high-space obstruction | Ordinary quartics divisible by P; feedback multiplier and extraction rank contradiction | `check_one_high_space.py`, all 606 Q spaces and all first-product classes |
| Theorem 1 | Exclude early top-bit placements, force z1 before the last gate, invoke Proposition 12 again | `check_lambda2_full.py`, including quadratic and redundant branches |

## Lambda = 1

| Result | Written argument | Exact check |
|---|---|---|
| Lemma 2: quadratic branch | Replace the gate and apply the now-proved L2 theorem | `check_replacement.py` |
| Lemma 3: cubic normal form | Unique affine factor line; 60 x 32 cubic planes | `check_lambda1_normal_form.py` |
| Lemma 4: first placement | Degree plus rank-four versus rank-two increment | `explore_prefixes.py` |
| Lemma 5: core cubic coset extension | Carry-coefficient pairing modulo its radical, then the feedback derivative argument | `check_core_cubic.py`, all 33 core cubic first spaces, all products and final factors |
| Lemma 6: early z1 forces core | Support of a rank-four sum; three-fiber coefficient rank obstruction | `check_early_core.py`; full-domain direct comparison in `check_screen_bruteforce.py` |
| Proposition 7: core branch | Early placement and final-space case split | Same full intermediate-space check |
| Lemma 8: two ordinary products | Force B into U; parity on B=0/1, isotropic kernels, complementary minors | `check_ordinary_pair.py`, all 197 cubic first spaces and all product-coset pairs |
| Lemma 9: noncore multiplier | Separate quadratic/cubic multipliers and external factor rank; force support of 1+k onto fiber 11 | `check_noncore_multiplier.py`, all 171,966,464 k,R pairs |
| Lemma 10: noncore intermediate space | Ordinary-product exclusion; replace c by its quadratic image modulo I; apply L2 extraction | `check_noncore_onehigh.py`, all 164 noncore first spaces, all next nonlinear gates and final factors |
| Theorem 1 | Quadratic/core/noncore cases; early-top-bit exclusion and one-dimensional final extension | `check_lambda1_exact.py`, all 2,016 first-plane weights, including redundant branches |

The imported L3/L4 files are treated as given and remain byte-for-byte unchanged. Checks of universal function claims cover the complete stated application spaces. The arbitrary intermediate function in L2 Lemma 7 is covered on all 2^64 functions by exact linear elimination. No blanket check of every possible Boolean circuit or unrelated quadratic-function pair is claimed.

Every executable mathematical check includes a detected positive control. The complete normalized circuit searches cover every possible placement of the two remaining target directions, semantic nonlinear factor planes, and all final products. Direct enumeration of all 17,650,560 next-gate planes over all 1,740 cubic first-output cosets separately validates the exact screen and its placing-plane counts.

The final release audit additionally checks references, environment/brace balance, explicit statuses, all required result records and controls, source hashes, preservation of the supplied proofs, and availability of a TeX engine. A static TeX audit is not a substitute for compilation; when no engine exists, compilation is reported as unavailable.
