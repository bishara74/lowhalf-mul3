# Local Palomar statement alignment

Checked on 9 November 2026 with Lean 4.35.0-rc3. The Challenge and Solution
exports now have identical theorem types and identical records throughout
the statement's transitive declaration closure.

| Result | Declarations |
| --- | ---: |
| Challenge statement closure | 7,624 |
| Solution statement closure | 7,624 |
| Shared names with matching records | 7,624 |
| Shared names with differing records | 0 |
| Challenge-only closure names | 0 |
| Solution-only closure names | 0 |

## Challenge imports and source alignment

The pinned Palomar pipeline compiles the Challenge separately against its
verified allowlist. The root repositories are Mathlib, Tau Ceti and CSLib,
with their eligible pinned dependency closures. The project's
`unrestricted_boolean_mul` dependency is outside the Challenge's allowlist.
The proof build may still use it. [Pinned Palomar rules](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/README.md) · [Pinned allowlist](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/allowed-challenge-repositories.json)

The self-contained Challenge copies the model declaration blocks from
`ANF.lean`, `Circuit.lean` and `Mul.lean` at the Lake manifest's pinned
revision `c014e498e51a98529877cc256b9bcdaf5faa2e4f`, with the repository's
line endings. This aligns the monoid law proofs and the index bound proofs
in `aVar` and `bVar`, including their generated declarations. The
`lowMul3` definition has the same body as `LowHalfMul3.Target`. The
Challenge's `lowMul3` and `mc_lowMul3` source block, including the deliberate
`sorry`, is byte-for-byte unchanged from the previous revision.

## Verification

The Challenge was compiled as a separate module under an output alias,
using only the Lean toolchain and the pinned Mathlib closure on its import
path. Its direct imports resolved to Init and Mathlib. Lean reported the
expected warning for the Challenge's deliberate proof hole.

The bundled `leanexport` exported both versions of
`UnrestrictedBooleanMul.LowHalfMul3.mc_lowMul3`. The audit started at the
constants in each theorem type and walked types, bodies, constructors and
recursor rules with `Lake.Check.runForUsedConsts`. It compared the name sets
and the same-name `ConstantInfo` records. The headline theorem's proof was
outside that statement-only walk.

`Lake.Check.compareAt` passed with the configured theorem, allowed axioms
and the bundled Comparator's primitive targets. `Lake.Check.checkAxioms`
also accepted the Solution export. The fresh Solution export is
byte-identical to the one previously replayed successfully by the bundled
`leanchecker --silent --from-export`. The normal `lake build` passed with
1,761 jobs.

The previous audit at `425ecad` found nine differing shared records and
twelve one-sided names. The pinned GitHub Actions workflow can run the full
hosted sandbox stage once the new commit is published. That stage has yet
to run for this revision.
