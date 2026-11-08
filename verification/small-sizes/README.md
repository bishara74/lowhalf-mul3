# Exact multiplicative complexity at widths one and two

For width one, the circuit consists of `g0 = a0*b0` with output `g0`. A zero-gate output must be affine. The verifier enumerates all eight affine functions of two bits and finds zero copies of the target. As a positive control it finds `a0+b0`.

For width two, the circuit uses `g0 = a0*b0`, `g1 = a0*b1`, and `g2 = a1*b0` and returns `(g0, g1+g2)`. To rule out at most two gates, the verifier uses the following exhaustive search.

1. Enumerate the 528 unordered pairs with repetition of the 32 affine functions of four bits. Their products give 172 distinct truth tables for the first gate.
2. For each first gate `g0`, enumerate all unordered pairs with repetition in `Aff + span(g0)` and multiply the two factors pointwise. This gives 308,096 second-factor pairs in total. Commutativity permits unordered pairs. Equal first-gate truth tables give exactly the same available functions for the second gate.
3. Reduce both gate truth tables and both targets modulo the affine subspace by binary Gaussian elimination. Free output XORs can realize both targets exactly when each target residue lies in the span of the two gate residues. The search gives zero matches for the multiplier and 576 for the positive-control pair `(a0*b0, a0*b1)`.

Appending zero gates embeds circuits with fewer gates in the two-gate search. The verifier also checks both upper-bound circuits directly against integer multiplication on every input. Run `python3 -B small_sizes/verify.py` from `paper-artifacts/`. [Circuits](circuits.json) · [Verifier](verify.py)
