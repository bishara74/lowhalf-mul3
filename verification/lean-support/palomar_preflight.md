# Palomar preflight of `bishara74/lowhalf-mul3` (local, no submission)

Status: the Solution is complete. See the final section for the completed
local preparation and its license-detector limitation. The earlier sections
record the original preflight and the run on the published commit `28514d5`.

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

## Rerun after the fixes

The same preparation phase (`verify_submission.py prepare`, preflight mode) was rerun on
the working state that became the next commit. Result: status `pending`, stage
`prepared`, no errors, no warnings. The three earlier preparation failures are gone:

| Earlier failure | Now |
|---|---|
| `source.module_required` (22 files) | 22 files checked, no issues |
| `license.mismatch` | `LICENSE` present; declared `MIT`, detected `MIT` |
| `submission.invalid` (no `comparator.json`) | accepted; Challenge `LowHalfMul3Challenge`, Solution `LowHalfMul3Solution`, theorem `UnrestrictedBooleanMul.LowHalfMul3.mc_lowMul3`, three standard axioms |

Failure 4 (`challenge.module_root_shadowed`, predicted) no longer applies: no dependency
has a top-level `LowHalfMul3Challenge` or `LowHalfMul3Solution`.

**Two substitutions, because the commit was not yet on GitHub.** (1) The verifier
normally clones the commit from GitHub. Here it was given a throwaway local git copy of
the working tree, and that copy's commit id appears in the report; it is not a commit of
this repository. (2) Licence detection normally runs Palomar's Ruby `licensee` script,
which is not installed here. A Python stand-in compared the licence body, without the
copyright line, with the MIT body of the dependency's `LICENSE`. The real detector is
stricter about the text. The preparation phase should be rerun unchanged on the pushed
commit.

**Still open (verification phase, not runnable on Windows):** `LowHalfMul3Solution.lean`
does not exist, so `lake build LowHalfMul3Solution` and the Comparator step cannot pass
yet. `<AUTHOR>` in `LICENSE` is a placeholder.

## Real run on the pushed commit `28514d5`

`verify_submission.py prepare` was run unchanged (preflight mode) on
`28514d5d79842a7bd70ce16f6fd2be32aea1c4e2`, cloned by the verifier from GitHub. The report is
`palomar_preflight_report_28514d5.json`; one local path in it is replaced by `<local path>`.

* **Submitter checks: all pass.** No diagnostic is owned by the submitter. The source
  requirements (22 files, module system), `formalization.yaml`, toolchain and
  `comparator.json` raise no issue.
* **One Palomar-owned error:** `palomar.license_detector_failed` (owner `palomar`,
  retryable, "Do not change the repository"). Palomar's detector runs
  `bundle exec ruby scripts/detect_license.rb` with the `licensee` 10.0.0 gem. It
  cannot run on this machine: rubygems.org is blocked here, and `licensee` depends on
  `nokogiri`, which has no prebuilt build for this Ruby (`x64-mswin64`).
* **Independent licence evidence.** GitHub classifies repository licences with the
  same `licensee` library. Its API reports `spdx_id: MIT` for `LICENSE` at `28514d5`
  (blob `0006f8578a015d6e877451823bea0b96be7bae07`, equal to `git rev-parse
  28514d5:LICENSE`). This matches `project.license: MIT`. GitHub's `licensee` version is
  not known, so this is strong evidence, not Palomar's own result.

The full verification phase (Linux sandbox, Comparator) still needs the Solution module.

## Completed Solution, local preparation on 9 November 2026

The Solution now proves `UnrestrictedBooleanMul.LowHalfMul3.mc_lowMul3`, and
`lake build` includes its Lake library. The Challenge file is byte-identical
to the previous Challenge. Its deliberate proof hole is confined to that file.

Palomar's `scripts.verify_submission prepare` logic at revision
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7` checked the completed Lean sources
and the final `formalization.yaml`. The preflight ran on a temporary local
snapshot based on `3e67bf7` with the final source and metadata edits applied.
The snapshot commit in the report identifies that local copy. The Lean files
and metadata checked by preparation were verified against the working files.
The local source adapter substituted only the initial clone, since the
completed commits are unpublished.

| Run | Result |
| --- | --- |
| Palomar license detector | `error / preflight`. The sole diagnostic was `palomar.license_detector_failed` because trusted Bundler was unavailable. |
| Local MIT text comparison | `pending / prepared`. All 37 Lean files, metadata, toolchain, and Comparator configuration passed with zero errors and zero warnings. |

For the second run, the root MIT text matched Palomar's bundled MIT text
after normalizing whitespace and removing the copyright line. The root
`LICENSE` has the same Git blob as in the earlier run on `28514d5`.
The report records both runs. No Palomar submission or remote verification
was performed. The full Comparator phase requires the Linux sandbox.
[Machine-readable preparation report](palomar_preflight_report_complete.json)
