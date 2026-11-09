# Local Palomar statement alignment

Checked on 9 November 2026 with Lean 4.35.0-rc3. The Challenge was compiled
separately from the Solution. The bundled `leanexport` exported both versions
of `UnrestrictedBooleanMul.LowHalfMul3.mc_lowMul3` into separate environments.

The exported theorem types are identical. The strict dependency comparison
fails. Lean's bundled `Lake.Check.compareAt`, the comparison used by
`lake comparator`, reports

```text
Const does not match between challenge and target 'UnrestrictedBooleanMul.bVar'
```

## Dependency differences

The walk starts from the constants in each theorem type. It follows the
types, values, inductive constructors and recursor rules using
`Lake.Check.runForUsedConsts`, then compares same-name `ConstantInfo` records.
It excludes the headline theorem's proof from the walk.

| Result | Declarations |
| --- | ---: |
| Challenge statement closure | 7,630 |
| Solution statement closure | 7,624 |
| Shared names with matching records | 7,612 |
| Shared names with differing records | 9 |
| Challenge-only closure names | 9 |
| Solution-only closure names | 3 |

The three shared definitions with identical types and differing bodies are
`aVar`, `bVar` and `instCommMonoidMonomial`, in namespace
`UnrestrictedBooleanMul`. The Challenge uses `omega` to prove the two
index bounds. The library uses explicit bounds with `Nat.two_mul`. In the
monoid instance the Challenge proves the laws through `Monomial.ext`,
and the library uses `congrArg Monomial.mk`. The six same-name generated
`instCommMonoidMonomial._proof_1` through `._proof_6` records differ in type
and body.

The following names occur only in the Challenge statement closure.

- `Lean.Omega.Int.ofNat_mul_nonneg`
- `UnrestrictedBooleanMul.Monomial.casesOn`
- `UnrestrictedBooleanMul.Monomial.ext`
- `UnrestrictedBooleanMul.Monomial.rec`
- `UnrestrictedBooleanMul.aVar._proof_2`
- `UnrestrictedBooleanMul.bVar._proof_2`
- `_private.LowHalfMul3Challenge.0.UnrestrictedBooleanMul.Monomial.ext.match_1`
- `_private.LowHalfMul3Challenge.0.UnrestrictedBooleanMul.aVar._proof_1`
- `_private.LowHalfMul3Challenge.0.UnrestrictedBooleanMul.bVar._proof_1`

The following names occur only in the Solution statement closure.

- `Nat.two_mul`
- `UnrestrictedBooleanMul.aVar._proof_1`
- `UnrestrictedBooleanMul.bVar._proof_1`

## Lean definitional equality

A separate scratch module imported the Solution and copied the three
Challenge bodies under fresh names. Lean accepted `rfl` for each equality
between a copied definition and its library counterpart, including the
whole monoid instance. This checks definitional equality in a shared
environment. The strict comparison also requires the same elaborated
proof records and dependencies across the two exports.
The bundled `leanchecker --silent --from-export` also replayed the full
Solution export successfully.

## Workflow scope

The GitHub Actions job calls the reusable `submission.yml` at PalomarSubmission
commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` in `full` mode. The local
comparison identifies a blocker for the hosted mechanical comparison. The
pinned profile resolver selected `ubuntu-24.04` locally. The hosted sandbox
stage has yet to run.
