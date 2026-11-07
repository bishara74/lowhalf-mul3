# Palomar preflight of `bishara74/lowhalf-mul3` (local, no submission)

Run on 7 November 2026 against the pushed commit
`33a708d1323ca5b7ed267c374e68e7268294e072`. Nothing was submitted.

## Procedure

Palomar's checks live in `PalomarRegistry/PalomarSubmission` (used at commit
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, 28 October 2026). Its README describes
two phases. Preparation is non-executing: root files, `formalization.yaml`, licence,
Lean source rules, toolchain and the Comparator configuration. Verification builds
the Challenge and Solution in a Linux bubblewrap sandbox and runs `lake comparator`
with the Lean kernel, NanoDa and con-ron.

* **Preparation** was run unchanged:
  `python -m scripts.verify_submission prepare --event event.json ...`, with
  `mode: preflight`, `comparator_config_path: comparator.json`, and the relationship
  "I am a responsible author or maintainer". The verifier cloned the commit from GitHub
  itself. Its report is `palomar_preflight_report.json` (status `fail`, 24 errors).
* **Verification** needs Linux and bubblewrap, so it cannot run on this Windows machine.
  Its static preconditions were checked with the verifier's own rules (below).

## Failures

| # | Check (code) | Finding |
|---|---|---|
| 1 | `source.module_required` (22 errors) | No `.lean` file starts with `module`. This covers all 19 `LowHalfMul3/*.lean`, `LowHalfMul3.lean`, `Challenge.lean` and `AxiomAudit.lean`. Every `.lean` file in the repository must use the module system. |
| 2 | `license.mismatch` | There is no licence file at the root. `project.license` is `MIT`, so a root `LICENSE` with the MIT text is needed. |
| 3 | `submission.invalid` (comparator-config) | There is no `comparator.json`. It needs `challenge_module`, `solution_module`, `theorem_names` and `permitted_axioms` (a subset of `propext`, `Classical.choice`, `Quot.sound`). |
| 4 | `challenge.module_root_shadowed` (verification stage, predicted) | The dependency `unrestricted_boolean_mul` has `Challenge.lean` and `Challenge/` at its top level. A Challenge module named `Challenge` would be rejected. It needs a project-specific name, for example `LowHalfMul3Challenge`. |
| 5 | Solution / Comparator (verification stage, predicted) | There is no Solution module. The only Challenge theorem, `mc_lowMul3`, is a `sorry`. It cannot be proved yet, because `LambdaCase 1` and `LambdaCase 2` are open. |

## Checks that pass

* **Toolchain.** `leanprover/lean4:v4.35.0-rc3` is accepted. `toolchains.json` sets the
  minimum to `v4.35.0-rc2`, and release candidates are allowed. The verifier's
  `supported_toolchain` returns `v4.35.0-rc3`, and `toolchain_commit` resolves it to Lean
  `470d5ce1400764999581fd26d5d72b00d990b0f4`.
* **`formalization.yaml`.** `load_formalization_metadata` and `normalized_provenance` pass:
  version v0.4, origin source-based, arXiv `cs.CC`, MSC2020 `68Q06, 68Q17, 94D10`, no ORCIDs.
* **Line limits.** All 22 files are under 10,000 lines. `Challenge.lean` has 130 lines
  (5,290 bytes), under 1,000 lines and 100 KiB.
* **Challenge imports.** `Challenge.lean` imports only Mathlib, which is an allowlisted
  statement root.
* **Mathlib pin.** `c55e6e78…` (tag `v4.35.0-rc3`) is an ancestor of `mathlib4` `master`.
  This was checked with the verifier's fetch and `merge-base` sequence. Mathlib's
  toolchain equals the project's.
* **Dependencies.** All are public GitHub repositories at 40-character SHAs, with no
  submodules or LFS. All 326 `.lean` files of `unrestricted_boolean_mul` and the five
  Mathlib modules we import already use the module system, so porting is possible.
* **Build artifacts.** `.lake/` is git-ignored; none are committed.
