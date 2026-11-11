# lowhalf-mul3

This Lean 4 development proves that the three low bits of the product of two
three-bit integers require exactly six AND gates in the unrestricted XOR–AND
model. XOR and constants are free, and AND gates may reuse earlier AND outputs.
The model comes from [Morse, Definition 2.1](https://arxiv.org/abs/2608.30238v1)
and is imported from [unrestricted-boolean-mul](https://github.com/GregoryMorse/unrestricted-boolean-mul).
The written proof is in the [manuscript repository](https://github.com/bishara74/Multiplicative-complexity-of-the-3-bit-low-half-multiplier).

The proof in [LowHalfMul3Solution.lean](LowHalfMul3Solution.lean) gives an
explicit six-gate circuit and rules out five gates by normalizing the circuit
and treating each possible number of linear gates. The theorem
`UnrestrictedBooleanMul.LowHalfMul3.mc_lowMul3` uses only
`propext`, `Classical.choice` and `Quot.sound`. The separate
[challenge module](LowHalfMul3Challenge.lean) contains the problem statement
with a deliberate proof hole. The theorem is registered as
[PALOMAR-2026-11-09-000020](https://palomar-registry.org/entry?id=PALOMAR-2026-11-09-000020).

## Build and check

```sh
lake exe cache get  # optional
lake build
lake env lean AxiomAudit.lean
```

[formalization.yaml](formalization.yaml) records the manuscript correspondence.
[Verification files](verification/README.md) contain computational checks, manuscript
audits, and the [SAT certificate regeneration instructions](verification/certificates/REGENERATE.md).

The repository uses the [MIT license](LICENSE). Copyright 2026 Bshara Alhodali
and Gregory Morse.
