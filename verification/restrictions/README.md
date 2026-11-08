# Five AND gates for all 64 affine restrictions

Write the substitution over `F₂` as

```text
b2 = c + s0*a0 + s1*a1 + s2*a2 + t0*b0 + t1*b1
```

Here is one parameterized circuit. The six coefficients are fixed constants for each restriction.

```text
g0 = a0*b0
g1 = a0*b1
g2 = a1*b0
g3 = a2*(b0 + s2*a0)
g4 = (a1 + g1)*(b1 + g2 + s1*a0)

z0 = g0
z1 = g1 + g2
z2 = g3 + g4 + (1 + s1 + t1)*g1 + g2 + t0*g0 + (s0 + c)*a0
```

Using Boolean idempotence, `g4 = a1*b1 + g1*g2 + g1 + g2 + s1*(a0*a1 + g1)`. The term `g1*g2` is the carry `a0*a1*b0*b1`. Substitution and cancellation give the required `z2`. Every factor is affine in the free inputs and earlier gates.

The JSON contains 64 explicit circuits found by a product search with `g0, g1, g2` fixed. Each factor ANF is an XOR list over inputs, constant `1`, and prior gates. The empty list is zero. The generator reduces products modulo the span of the fixed signals and the affine functions. Only `s1` and `s2` change the target in that quotient. The generator finds two products for each of these four residual targets and recovers the free XOR separately for every restriction.

Run `python3 -B restrictions/verify.py` from `paper-artifacts/` to verify the JSON. The standalone verifier checks distinct and complete restriction coverage, factor legality, the gate budget, and all 32 inputs per restriction against integer multiplication. It also rejects two seeded faults, a flipped output constant and a reference to a future gate. Run `python3 -B restrictions/search.py` to regenerate the JSON. [Circuits](circuits.json) · [Verifier](verify.py) · [Search](search.py)
