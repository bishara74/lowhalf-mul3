# Decisions for the lambda = 2 and lambda = 1 proof drafts

1. Treat REQUEST.txt as the requested task, the two imported proofs as given results, and the earlier reports as historical evidence, not fresh verification.
2. Preserve the existing REPORT.md verbatim in references/REPORT_before_lambda12.md before writing the requested one-page report. Preserve all pre-existing proof and search files.
3. Use standalone pure Python with integer bitsets; the supplied t11_tools.py imports an unavailable module and numpy is absent from the default interpreter. Do not use SAT or the old SAT artifacts.
4. Put unchanged copies of supplied sources in references/ and record their SHA-256 digests. Do not modify either imported proof.
5. Use PROVED only after a written argument and an exhaustive check on its stated application domain. Record any stronger unverified statement as OPEN.
6. Check the exact gate-replacement identity by direct span containment, including dependent quadratic spans and the zero/redundant rank-two increment. Keep the original tail factor functions to preserve their semantic linear/nonlinear status.
7. No pdflatex, latexmk, xelatex, lualatex, or tectonic was found on PATH during initial inspection. Recheck at delivery; do not claim a PDF exists without compilation.
8. Use exact annihilator identities to screen candidate feedback factors: if R = k(g+F), then (1+k)R = 0. This drastically reduces the search without SAT or numerical heuristics.
9. Collapse first-gate products only modulo the available space, retaining each plane multiplicity; report distinct output cosets and factor-plane counts separately.
10. Count historical reports only as supplied evidence; reproduce counts freshly before treating them as verified here.
11. Use actual function spaces rather than redundant signal-coordinate spaces. This reduces lambda = 1 to 222 output-space orbits (197 cubic), while preserving all 2,016 first factor-plane weights.
12. Include quadratic and redundant first nonlinear gates in both full sanity searches, so neither complete computational exclusion relies on the imported lambda = 3 theorem.
13. Allow any product at the last gate. This enlarges the search and avoids needing a separate final semantic-linearity filter. Enumerate semantic nonlinear planes at earlier gates.
14. Prove and check last-factor rigidity using the imported rank-two type classification, differentiation, and restrictions to fibers of (a0,b0). Prove the two-feedback obstruction for arbitrary Boolean g, and verify its full domain by exact linear elimination.
15. Reproduce the weak derivative-plus-Omega count on the stated 83 representatives. Do not assume the one-direction-plus-Omega filter is invariant under every shift; exact circuit feasibility is the symmetry-invariant property used for complete coverage.
16. Retain plane multiplicities when collapsing equal prefix spaces. Report the 2,064 difficult pairs separately from their 1,776 distinct output cosets.
17. Reconcile the lambda = 2 total by computing the exact redundant-coordinate lift correction (2,088). Do not claim a field-by-field reproduction of the historical lambda = 1 total; document the new count and difference explicitly.
18. Use a direct independent enumeration of all 17,650,560 next-gate planes for every cubic lambda = 1 first-output coset to validate the exact screen, including its placing-plane counts.
19. State both main human-proof theorems as OPEN. The new checked structural lemmas and complete computational exclusions do not fill the missing human arguments for all placement branches.
20. Keep the lambda = 1 quadratic reduction explicitly conditional on a full lambda = 2 human theorem. Its computational exclusion is established separately by the full direct search.
21. Preserve per-orbit checkpoints and add a master runner with a 1,800-second limit per child. Include a detected positive control in every executable verification script.
22. Recheck standard Linux and common Windows TeX locations without downloading an engine. No TeX engine is available, so provide the two sources without claiming compiled PDFs.
23. At the explicit user pause request, save all current artifacts under task12/ without beginning additional proof work or checks. Preserve unexecuted scripts and clearly record pending reruns.
24. Save the latest quotient-ideal extraction idea as OPEN_NOTES.md, explicitly unproved and unchecked. Do not incorporate it as a proved result in either draft.
25. Include all completed result summaries in the pause REPORT.md, with full per-orbit counts in copied JSON artifacts; the pause request takes precedence over the earlier one-page report limit.

26. Resume in task12/ as the authoritative working directory, preserving the pause drafts and results under checkpoints/pause_2026-10-31/. Root-level duplicates remain untouched.
27. First test the ideal-quotient extraction idea on every first-gate factor plane, including affine and dependent descriptions, before using it in a proof. Work with genuine affine-input product representatives of decomposable quadratic forms.
28. Promote ideal extraction after its written proof and complete 887,857-plane check passed. Use the ideal of the actual low-bit function, not an exterior ideal.
29. Apply imported B3a/B3b algebraic arguments to S=Q+<Z1> inside U after auditing their hypotheses; independently check all 11 application spaces, including non-rank-two-generated ones.
30. Check the one-high-signal obstruction on all first products, not only z1-admissible ones: 833,824 planes / 701,574 spaces passed. This closes the full lambda=2 human proof.
31. The quotient-only four-gate relaxation for lambda=1 has a solution; do not use it to claim the original exclusion.
32. Extend the core coset argument to cubic functions by replacing quadratic parts with classes modulo the radical of the carry-coefficient pairing. This proves the 33 core cubic first-output orbits; check all corresponding factor spaces.
33. Prove that early z1 placement forces a core cubic first signal; the feedback mechanism cannot place z1 at that stage. Its complete application domain is separately cross-checked by direct enumeration.
34. Isolate the remaining lambda=1 obligation as a stronger noncore intermediate-space lemma, without a z1-placement screen. Its enumeration passes but its human proof remains OPEN.
35. Reconstruct and independently simulate an explicit four-gate circuit on the quotient-only 48-point domain before rejecting that shortcut. The relaxed witness is not a counterexample to the original problem.
36. Close ordinary final products by splitting a core affine factor B into B=0/1 hyperplanes and using complementary-minor parity identities on both. Check every pair of product cosets for all 197 cubic first spaces.
37. Close noncore feedback by proving k=1 modulo (a0b0), splitting quadratic and cubic multipliers and the rank of the two external factor parts. Exhaustively check all 171,966,464 k,R pairs before using the lemma.
38. Apply the already-checked ideal extraction after replacing the first cubic signal by its quadratic representative modulo (a0b0). This finishes the noncore branch and hence the complete lambda=1 human proof.
39. The resumed environment exposes MiKTeX-pdfTeX, so compile PDFs instead of retaining the earlier no-engine limitation. Install only missing required packages in the existing per-user setup using miktex packages require; do not perform a global update or use administrator mode. Compiler shell execution remains disabled.
40. Preserve the master 22-check run and the two additional full-domain check() runs as separate evidence, then audit all 24 required checks together. Rerun replacement and degree checks after adding explicit dependent/affine coverage.
41. Refresh only the MiKTeX package catalog after unknown-package errors. Use the catalog's latex-tools and amscls package IDs, install only missing required dependencies, and leave compiler shell execution disabled.
42. Compile both primary sources, inspect the first page and both computational tables, fix PDF bookmark strings, and repeat compilation only as required to settle references and outlines. Both PDFs have nine pages and no clipped tables.
43. Complete the release audit against all 24 passing check records, input-preservation hashes, current proof labels and references, and the compiled artifacts. Retain all historical OPEN checkpoints while marking them explicitly historical; no OPEN lemma remains in the current primary drafts.
