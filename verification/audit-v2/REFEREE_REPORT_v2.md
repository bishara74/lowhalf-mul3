# Referee report on `main.tex`, version 2

**Verdict.** The written proof of \(\mathrm{MC}(M_3)=6\) survives the audit. I found nine local issues, chiefly omitted qualifications in the exposition and appendix. The proof needs the affine-factor case made explicit in the first-gate lemma and the rank-two basis made explicit in Proposition B. Both repairs are local.

| OK | MINOR | GAP | FALSE | Total |
|---:|---:|---:|---:|---:|
| 51 | 9 | 0 | 0 | 60 |

These counts refer to the rows below. MINOR means a local repair preserves the stated result and its role in the lower bound. GAP would mean a required inference remains unsupported. FALSE would mean a stated result has a counterexample. Some MINOR entries include counterexamples to stronger readings of individual sentences.

I audited the 1,340-line root manuscript with SHA-256 `a8741348127419f97a7200ad0775e83b797adbdf9ec0d71d89cf45185de42aa1`. During version identification I also computed checksums of two other manuscript copies in workspace subdirectories. The proof review and checks use only the root manuscript. I took the four-linear-gate theorem as given and checked the hypotheses at each use. I reviewed the printed verification methods and references in the appendix and independently recomputed the domains identified below. The reported SAT, Lean, and other historical runs were outside the audit. The scripts are new, use 64-bit ANF masks and Python's standard library, and each check has a positive control. Run them with `python3 checks/referee_v2/run_all.py`. The runner writes `checks/referee_v2/results.json`. I used this subdirectory to keep the existing `checks/run_all.py` and `checks/results.json` separate.

## Result inventory

Line numbers refer to the audited `main.tex`. The argument supporting each priority judgment is expanded below the table.

| # | Result and source lines | Class | Referee finding |
|---:|---|---|---|
| 1 | Target ANFs and six-gate upper bound, 71–79 and 188–199 | OK | Independent integer multiplication agrees on all 64 inputs. |
| 2 | Normal form `l4:lem:normal`, 84–90 | OK | Insert \(z_0\) first, delete its first placing gate, and move semantic affine-input products to the front. Original later factor functions remain available. |
| 3 | Quadratic availability `l4:lem:Qonly`, 92–103 | MINOR | The displayed lemma names only the four-gate case. Several citations need the general prefix identity already stated in the preceding prose. M1. |
| 4 | Support `l4:lem:support`, 131–137 | OK | The two rank-two supports must span the four-dimensional support of their rank-four sum. |
| 5 | Cross part `l4:lem:cross`, 139–145 | OK | The kernel is exactly the core forms. The dimension bound uses \(P_0,Z_1\in Q\). |
| 6 | Core factor plane `l4:lem:planeU`, 147–153 | OK | The external cubic coefficients force the external linear parts of both factors to vanish by independence of their quadratic parts. |
| 7 | Cross part of \(q_2\) `l4:lem:noq2`, 155–161 | OK | Both contractions would lie in the rank-two support and force that support into the low-bit plane. |
| 8 | Four-gate Proposition `l4:prop:B`, 163–169 | OK | In the given use, \(d_U=3\), rank-two generation, the product coset, and the core-plane conditions are all supplied. |
| 9 | Types `l4:lem:types`, 171–185 | OK | External projection rank one or two gives the two forms of the support. Counts follow from 15 core lines and eight lifts per type-line, 256 full graphs, and 35 core planes. |
| 10 | Five linear gates `thm:lambda5`, 213–219 | OK | The output space is quadratic and \(z_2\) is quartic. |
| 11 | Toolkit derivative `l4:lem:deriv`, 223–241 | OK | The product rule either makes \(\delta_e\) constant or makes the quartic product a quadratic times an affine function up to a quadratic term. |
| 12 | Toolkit derivative variant `l3:lem:deriv`, 242–251 | OK | Adding \(\varepsilon z_1\) leaves the external derivative and carry intact. |
| 13 | Toolkit notation scope, 254 | MINOR | The stated degree restriction reaches the later cubic-core subsection if read literally. M2. |
| 14 | Radical `l3:lem:rad`, 256–262 | OK | Vanishing derivative cubic forces \((\iota_x\omega)\wedge\eta=0\). A nonzero linear divisor would make \(\eta\) rank at most two. |
| 15 | Weights `l3:lem:wt`, 264–270 | OK | The full-rank Walsh bias has absolute value \(2^{m/2}\). The minimum-weight bound follows by induction on a binary split. |
| 16 | Product `l3:lem:P`, 272–296 | OK | Dependent factors are absorbed. P1 uses one affine coordinate. P2 compares two quadratic wedges and separates their zero/nonzero cases. P3 uses common support, then the weight bound on two disjoint quadratic functions. |
| 17 | General coset part (a), 302–367 | OK | Rank-two coefficient matrix, radical quotient, complementary minors, and both values of \(\sigma\) checked. |
| 18 | General coset part (b), 369–396 | OK | Both multiplier derivative cases, dependence of the external forms, and the hyperplane argument checked. |
| 19 | General coset final product and applications, 398–407 | OK | The two-feedback operation and the output-correction absorption preserve the correct cosets. Cubic degrees are allowed. |
| 20 | Ideal extraction `l2:lem:ideal`, 410–434 | OK | Full plane sweep on all 606 \(Q\), including the nonzero cubic branch and affine planes. |
| 21 | Rank and exterior `l2:lem:rankext`, 436–443 | OK | All four base matrices have rank six, all 2,604 rank-two additions have rank at least four, and all 616 outside-\(U\) exterior images miss \(\Omega\). |
| 22 | Four-linear-gate theorem `l4:thm:main`, 446–505 | OK | Taken as given. Its applications supply a four-dimensional rank-two span with \(P_0,Z_1\) and the actual single-product coset. |
| 23 | Four-dimensional formulation `l3:thm:L4`, 509–512 | OK | Same single-product conclusion with the same hypotheses. |
| 24 | A `l3:lem:A`, 539–545 | OK | New \(z_1\) placement forces a quadratic product with a nonzero quadratic factor part. The Product lemma supplies a new rank-two direction. |
| 25 | D1 `l3:lem:D1`, 549–665 | OK | All four structural branches checked, including the four full/full coefficient subcases and both mixed cases. |
| 26 | C `l3:lem:C`, 667–679 | OK | \(d_U=3\) kills directly. \(d_U=2\) uses type or the explicitly repeated full-plane argument. \(d_U=1\) satisfies D1's hypotheses. |
| 27 | Absorption `l3:lem:abs`, 683–689 | OK | The placing product can be replaced as a signal by \(z_1\), giving exactly \(V(Q')\). |
| 28 | Proposition B `l3:prop:B`, 691–697 | MINOR | Select a basis before extending when the listed generators are dependent. The actual theorem route already has dimension four. M3. |
| 29 | Core \(Q_3\) `l3:lem:B3U`, 701–707 | OK | Rank forces both other generators in the expression for \(Z_1\). The support lemma then puts them in \(U\). |
| 30 | Proposition B3 `l3:prop:B3`, 709–715 | OK | The core \(Q_3\) satisfies Toolkit hypotheses. Both possible feedback forms reduce as stated. |
| 31 | Three-linear-gate theorem `l3:thm:main`, 528–537 and 717–721 | OK | Redundancy replacement preserves tail factor functions. The last one-dimensional extension forces \(z_1\) earlier, and B or B3 covers it. |
| 32 | Replacing a quadratic nonlinear gate `l2:lem:replace`, 732–740 | OK | A rank-two direction supplies every new quadratic class. Extending with monomials keeps the gate count and semantic tail linearity. |
| 33 | Top degree `l2:lem:degree`, 742–747 | OK | The exterior pairing is alternating and every independent change of basis has determinant one. |
| 34 | Last-factor rigidity, type \(v\), 754–800 | OK | Both \(d=0\) and \(d=1\) checked. All low-coordinate and carry entries recomputed. |
| 35 | Last-factor rigidity, full type, 802–829 | MINOR | The rigidity implication is correct. For a fixed \(R\), the value on the fourth fiber may be forced. M4. |
| 36 | Inside-\(U\) coset `l2:lem:coset`, 831–836 | OK | The general Toolkit application permits the actual dimension and rank generation of \(S\). |
| 37 | One higher-degree signal `l2:prop:onehigh`, 838–857 | OK | Core spaces use the coset lemma. Outside-\(U\) spaces use exterior divisibility or multiplier rigidity followed by ideal extraction. |
| 38 | Two-linear-gate theorem `l2:thm:main`, 727–730 and 859–870 | OK | Quadratic \(g_2\) reduces to \(\lambda=3\). Otherwise neither early top-bit coset is reachable, so the \(z_1\)-placing space is exactly the one tested. |
| 39 | Quadratic first gate `l1:lem:reduce`, 880–886 | OK | The \(m=1\) replacement supplies the needed second linear gate and preserves the three tail products. |
| 40 | Cubic first-gate normal form `l1:lem:cubic`, 888–900 | OK | Plane operations leave one affine factor and one with quadratic part \(P_0\). The 63 possible affine directions give 32 planes each and 60 directions are cubic. |
| 41 | First-gate placement `l1:lem:first`, 902–907 | MINOR | The stated universal domain includes two affine factors, which require the immediate rank-two argument. All 32,896 factor pairs pass. M5. |
| 42 | Four multipliers `l2:lem:four`, 910–931 | OK | Rank and radical arguments remove the larger supports. Weight, the zero flat, and the converse give precisely the five possible multipliers. |
| 43 | Feedback placement normalization for \(z_1\), 933–937 | OK | The normalized product yields \(kR=R\). A cubic previous signal excludes \(k=1\). |
| 44 | Core-cubic coset `l1:lem:corecoset`, 939–947 | OK | Every cubic monomial contains both low bits, so \(1,a_0,b_0\) annihilate the carry pairing as required. |
| 45 | Early \(z_1\) `l1:lem:earlycore`, 949–962 | OK | Ordinary placements yield a core rank-four splitting. Feedback cannot match the two independent changes of fiber coefficients. |
| 46 | Core branch `l1:prop:corebranch`, 964–969 | OK | Both placement times yield a space of the form allowed by the core-cubic lemma. |
| 47 | Ordinary-pair hyperplane parity `l1:lem:ordinarypair`, 971–1047 | OK | The exterior restriction on \(B\), isotropic kernel, and global parity cancellation are valid. |
| 48 | Hyperplane worked example, 1049–1063 | OK | Recomputed both external coefficients, kernel, and the five parity pairs below. |
| 49 | Noncore multiplier `l1:lem:noncoremult`, \(\tau=0\), 1069–1081 | OK | The degree-five constraint removes external multiplier terms. Fiber quadratics force \(1+k\in I\). |
| 50 | Noncore multiplier `l1:lem:noncoremult`, \(\tau=1\), 1083–1117 | OK | The determinant, derivative, coefficient, and single-fiber steps all hold. The exact sweep found 24 admissible (first-gate coset, cubic multiplier) pairs. |
| 51 | Noncore intermediate-space obstruction `l1:lem:noncore`, 1120–1133 | OK | Ordinary factors use parity. Feedback uses full-domain rigidity before passing to the quotient. |
| 52 | One-linear-gate theorem `l1:thm:main`, 875–878 and 1135–1141 | OK | Quadratic, core cubic, and noncore cubic are exhaustive. In the noncore branch the two early top-bit exclusions force the stated last space. |
| 53 | Main theorem `thm:MC`, 52–57 and 1146–1148 | OK | Padding to five gates and the normal form cover every circuit of size at most five. The six-gate construction matches the target. |
| 54 | Cross-reference and proof dependency audit, whole paper | OK | All 189 `\ref` and `\eqref` occurrences resolve. I checked the mathematical uses. The scope exceptions are recorded in M1 and M9. The proof dependency graph has no cycle. |
| 55 | Symmetries `l2:lem:sym`, 1167–1177 | OK | The 32 maps are distinct and closed under the 1,024 compositions. The target cosets and semantic linearity are preserved. |
| 56 | Appendix \(Q_3\) counting convention, 1214 | MINOR | The 43 extra objects in the 164,639 convention are unspecified. The stated domain of distinct spans has 164,596 elements. M6. |
| 57 | Appendix \(\lambda=2\) plane counts, 1266 and 1269 | MINOR | The printed values are right for the 83 representatives. The stated domains should say so. M7. |
| 58 | Appendix feedback screen normalization, 1250 | MINOR | State normalization as an equivalence for placement, with a change in the output correction. M8. |
| 59 | Appendix reduced-space and placement logic, 1248 and 1252–1286 | OK | Constants and basis changes stay in the available space, and the early target tests justify reducing to the stated last-gate cosets. This checks the method and its scope. |
| 60 | Appendix coset check reference, 1237 | MINOR | The row cites an undefined “level-i” statement and labels the number of first factor planes as a count of signals. M9. |

## Priority proof details

### Toolkit cosets and cubic cores

- In part (a), the coefficient equations are in the quotient by constants. A row dependence would imply that a nonzero combination of \(b_0,a_0\) is constant. These two right-hand sides then disappear in the quotient by the radical. The four projected core parts have coefficient vectors in \(\ker M\), so their pairings are given by the minors of a two-row kernel matrix. For \(M=[I_2\mid T]\), the kernel matrix is \([T^T\mid I_2]\) over \(\mathbb F_2\). The complementary minors match in both directions. The \(p_1p_2\) comparison is exactly \(\det_{12}M+\det_{34}M=0\). With \(\sigma=1\) this makes the carry bracket zero. With \(\sigma=0\), columns 3 and 4 vanish and the bracket is again zero. The carry equation would instead require one. The scripts exhaust all 210 rank-two matrices.
- In part (b), if \(D_ek=1\), multiplying the differentiated equation by \(k\) kills \(k(k+1)\) and produces a forbidden ordinary product. With all such derivatives zero, the multiplier is a nonzero core function. The external dependence of \(L_e\) is the single linear form \(c(e)d+d(e)c\). A nonzero core multiplier cannot kill that dependence, so \(c,d\) are dependent. For \(c=d=0\), the two external basis equations would make the multiplier equal to two distinct affine functions. In the nonzero rank-one case, the direction killed by the external line identifies the multiplier with \(\delta_{e_0}\) plus a constant. In a different direction, the affine right-hand side must vanish on the same zero hyperplane. It would then have the same nonzero linear part, which contradicts injectivity of \(e\mapsto\delta_e\).
- For the final product, if both factors contain \(g\), replacing the second factor by their sum adds the first factor to the product. This stays in \(\mathcal W\). With one feedback factor, replacing the other factor \(H'\) by \(H'+\sigma\) absorbs the \(\sigma g\) correction at the cost of the available term \(\sigma F'\). The pointwise identity holds on all 64 assignments of the three value bits and three flags. The cubic-core hypothesis follows because every possible cubic term of the first gate is divisible by \(P_0\). Degree-three terms missing either low bit would pair nontrivially with the missing bit, so the maximal admissible core has precisely the two cubic monomials used in the script.
- The two screens used 1,000,000 random instances and 14,641 edge tuples per part. For (a), each sampled \(f,h,F\) was tested for every \(H\) and every correction in \(\mathcal W\), projected onto the external coefficients and carry. For (b), each \(f,h,k\) was tested for every \(F'\) and every correction in \(\mathcal A\). A forbidden cubic provides a positive control that actually matches the external coefficients and carry for (a). A relaxed target exercises the (b) solver.

### Last-factor rigidity and ideal extraction

- For type \(v\), differentiating in the killing direction makes \(k=1\) on the affine hyperplane \(A=1\), so \(1+k=(1+A)B\) with \(B\) affine. With \(d=0\), the rank-two option is only \(P_0\), so \(k\) is low-bit dependent. A rank-two \(P\) outside \(U\) cannot project to \(a_1\wedge b_1\) after fixing the low bits. Indeed that image has rank two, so the whole two-dimensional projected support would lie in the core, and adding back the two low-bit coordinates keeps it there. With \(d=1\), adding a \(Z_1\) component to \(P\) would split a rank-four core form into two rank-two forms, including the external \(P\). With that component excluded, \(\Phi(P)=\Phi(k_2)\) identifies the same core line \(\langle r\rangle\). On \(r=c,B=1\), the chosen coordinates give the external term \(cq+sp\), with \(p\) affine in the free core variables. The three listed carry-active rows give the cubic \(sa_1b_1\). In the other three rows, the \(a_1b_1\) coefficient survives because all competing quadratics involve \(s\).
- For full type, \(p=a_2+x,q=b_2+y\) changes the core correction by \(b_0x+a_0y\). The additional constant shifts only add low-bit affine terms to the target and affine terms to \(pq\). All these corrections become affine on fixed-low-bit fibers. When \(d=1\) the \(pq\) coefficient of \(kR+R\) is \(A+B+T+\epsilon K\), whose quartic part is one carry monomial. When \(d=0\), the derivative test makes \(k\) core. The \(\epsilon=1\) coefficient forces \(k=1\). For \(\epsilon=0\), the annihilator of the two independent affine coefficients is supported on one low-bit fiber. Multiplying its indicator by a nonconstant function in \(a_1,b_1\) would create degree greater than two. On the other three fibers the remaining \(a_1b_1\) coefficient is still one. The elimination sweep over all 616 original external rank-two forms tested 630,784 multipliers against their entire \(R\)-cosets. It found precisely two possibilities per \(P\), both in \(d=0\). It also checked 1,024 full-coordinate shift choices and 48 assignments in the type-\(v\) table.
- In ideal extraction the only nontrivial plane has factors \(p+A,B\) modulo the ideal, where \(p=lr\). If its cubic term vanishes, \(B\) is in the support of \(P\), so \(pB\) is a multiple of \(p\). Otherwise the common three-form identifies a three-space \(W\) and a common line \(\langle t\rangle\) for the two rank-two supports. The part corrected by a multiple of \(P_0\) is quadratic on \(W\). Since \(B\) is outside \(\operatorname{supp}P\), the image of \(B\wedge W\) surjects onto \(\Lambda^2(W)/(t\wedge W)\). Hence its class combines with \(A_1\wedge B\) into a single decomposable form. Direct ANF quotienting tested 6,533,642 planes. Of 1,910,282 quadratic quotient products, 1,384,800 had a nonzero cubic part before quotienting. Affine-factor constants, basis changes, and alternative quadratic lifts add only allowed directions.

### D1 and the use of the four-gate theorem

- D1(i), distinct type directions, gives separate contraction equations. If \(m_{12}=1\), cross-part comparison gives a common core factor and the nonzero four-form would retain an external factor. If \(m_{12}=0\), each contributing core factor lies in the support of \(P_0\), so restriction gives zero.
- In D1(ii), the two full generators give \(R_1\wedge R_2=(a_2+x_1)\wedge(b_2+y_1)\wedge d_x\wedge d_y\). Both printed contractions follow. With \(m_{12}=0\), the contraction constraints force both differences into the low-bit plane. With \(m_{12}=1\) and equal other coefficients, \(d_x\wedge d_y=0\) and the remaining terms vanish by the core contraction equations. With unequal coefficients, \(d_x\wedge d_y=P_0\) and the respective expansion at generator 1 or 2 repeats one of the wedge factors.
- In D1(iii), normalize the type direction to \(b_2\). The \(a_2\)-contraction either leaves just the type generator with a low-bit core factor, or forces \(m_{01}P_0+R_2=(b_2+y)\wedge r_2\). The second contraction then forces \(m_{02}P_0\wedge r_2=0\). For \(m_{01}=1\), the two surviving core terms cancel using \(P_0=(x_2+y)\wedge r_2\). For \(m_{01}=0\), the final term repeats \(y\) and the other term vanishes by the second contraction. D1(iv) gives a killing direction directly. Of all 189,384 independent generator pairs, precisely 2,304 admit \(\Omega\), and every such pair has the same type direction. The mixed, distinct, and full cases were tested with all seven nonzero coefficient triples per pair.
- In Proposition B the new generator \(Z_1+q\) is outside \(Q_3\) and has rank two. Thus \(Q'=Q_3+\langle Z_1\rangle\) is rank-two generated and contains \(P_0,Z_1\). On the theorem's route \(\dim Q_3=3\), so \(Q'\) already has the required dimension. In the broader proposition, extend a rank-two basis that contains \(P_0\). The exact test covered the 15,219 eligible \(Q_3\), including 22 of dimension two, and verified that \(Q'\) embeds into a four-dimensional space with the required generators. An actual placing product with a dependent generating list appears in M3.

### Hyperplane parity and the noncore multiplier

- In the ordinary-pair proof, \(B(cH)=cH\) forces \(B\wedge\Omega=0\) by degree five, so \(B\) is core. On \(B=j\), both low-bit forms remain independent modulo constants. The restricted quadratic directions of \(P_0,Z_1\) are independent because a form lost upon restriction would be divisible by \(B\), which excludes the rank-four candidates and excludes \(P_0\) by support. The two external coefficient rows have rank two. The \(pq\) coefficient makes them isotropic, which also makes their ordinary kernel isotropic under \(J\). This gives \(w^TJz=t^TJz=0\).
- The restricted pairing is alternating because quadratics have even parity on three bits. In \(T\) the functions \(1,r,s\) are in the radical since multiplying \(P_0\) by a low-bit form cannot raise its degree. A right inverse therefore removes the inhomogeneous external equations without changing the relevant pairings. Complementary minors give the zero sum on the adjusted kernel. Restoring the \(Z_1\) terms gives the pairing with a single affine \(D\) because the potentially quadratic and \(j\)-dependent terms cancel. The sum over the two hyperplanes is the parity of \(Z_1D\), which is zero on four bits. The target has carry parity one. An independent product-coset sweep covered all 12,509,280 planes over the 288 viable noncore first-gate cosets with core \(B\). It found no target pair.
- For the example, the product sum is \(P_0+b_0b_1+a_0p+b_0q\), with \(p=b_2,q=a_2\). Thus the two rows pick out \(a_0,b_0\), and the kernel is \(\langle e_2,e_4\rangle\) in the four factor slots numbered from one. The recomputed parity pairs, ordered by \(j=0,1\), are

  | Function in the pairing or target | Parities |
  |---|---|
  | \(P_0b_1\) | \((1,1)\) |
  | \(a_0P_0=P_0\) | \((0,0)\) |
  | \(b_0b_1\) | \((0,0)\) |
  | Sum of the two products at \(p=q=0\) | \((0,0)\) |
  | Target at \(p=q=0\) | \((0,1)\) |

- For \(\tau=1\), the degree-six coefficient is exactly the exterior determinant from the quadratic external part of \(c\) multiplied by the carry. The cubic part of \(c\) contains \(P_0\) and contributes no degree six. After eliminating the second external direction from \(c\), an external derivative of \(k\) equal to one in that direction would make \(R\) an ordinary product in \(A\). Otherwise, comparing coefficients of \(q,pq\) makes \((r+e)w=0\), including its \(p\)-coefficient \((r+e)(C+u_p)=0\). If \(B\) is core, \(C=B\) makes the latter a nonzero product of affine functions with independent linear parts. If \(B=B_U+p\), then \(pB=B+B_UB\) gives the printed normalization including its constant \(\eta\). The vanishing on the half of the low-bit square forces \(H\) low-bit only. The quadratic coefficient of \(C+u_p\) is one, so it is the indicator of a single fiber \(j\). On the two fibers where \(w=0\), subtracting the free linear coefficient equations forces the \(Z_1\) coefficient of \(u\) to vanish. This leaves free coefficient vector \(b\) on \(j\) and zero on the other fibers. Since \(b\) has \(p\)-coefficient one, the cubic \(p a_1b_1\) would survive in \(wR\) if \(j\ne(1,1)\). Thus \(w\) vanishes on all three fibers outside the ideal. The complete sweep tested 860,160 multipliers in each branch. A genuine \(\tau=1\) positive case is \(c=P_0a_2,\ k=1+c,\ R=z_2+b_2+c\).

## Required local revisions

### M1. Generalize the quadratic-availability lemma's displayed scope

Current LaTeX, line 98

```tex
With the gates $g_1,g_2,g_3$ extended accordingly, $V_4=V_4(Q):=\{f:\deg f\le 2,\ \pi_2(f)\in Q\}$.
```

Suggested replacement

```tex
If the first $j$ gates have affine factors and their quadratic parts span $Q$,
then $V_j=V(Q)$. In particular, for the extended four-gate prefix,
$V_4=V_4(Q)=V(Q)$.
```

This gives the actual result cited at lines 526, 736, and 884. The existing proof applies verbatim with \(j\) gates.

### M2. Limit the quadratic-factor convention to the quadratic-product lemmas

Current LaTeX, opening of line 254

```tex
Throughout this section $f,h$ have degree at most $2$, $\omega=f_2$, $\eta=h_2$.
```

Suggested replacement

```tex
In the Radical and Product lemmas, $f,h$ have degree at most $2$,
and we write $\omega=f_2$ and $\eta=h_2$.
```

The general coset lemma permits degree-three factors. Its proof uses the stated cubic hypotheses correctly.

### M3. Extend a basis in Proposition B

Current LaTeX, line 696

```tex
If necessary extend the rank-two generating set of $Q'$ to four independent rank-two forms; this only enlarges the available space. Theorem~\ref{l4:thm:main} then excludes the displayed last product.
```

A generating set can already be dependent. Take \(P_1=a_0b_1\), \(P_2=a_0(b_0+b_1)\), and \(g_3=(P_0+a_1)b_0=z_1+P_0+P_1\). Then \(P_0+P_1+P_2=0\). The listed set cannot itself be extended to an independent set. A basis of its span extends as needed.

Suggested replacement

```tex
Choose a rank-two basis of $Q'$ containing $P_0$, by taking a maximal
independent subset of the displayed generators starting with $P_0$.
If $\dim Q'<4$, extend this basis to four rank-two
forms with independent quadratic monomials. Let $Q^+$ be their span.
Then $Q'\subseteq Q^+$ and $Z_1\in Q^+$, so the displayed product would
satisfy $FH\in z_2+V(Q^+)$ with $F,H\in V(Q^+)$. This contradicts
Theorem~\ref{l3:thm:L4}.
```

### M4. State the last-factor result as a necessity on the fourth fiber

Current LaTeX, end of line 827

```tex
Its value on $(1,1)$ is free, giving exactly $1$ or $1+P_0$.
```

For a fixed \(R\), it need not be free. Set \(R=z_2\), \(k=1+P_0\), and evaluate at \((a_0,a_1,a_2,b_0,b_1,b_2)=(1,0,1,1,0,0)\). Here \(R=1\) and \(kR=0\). This applies for any full \(P\). The necessary classification in the lemma holds. In the complete test, both classified multipliers have a witness \(R\) for every \(P\), with \(R\) allowed to vary.

Suggested replacement

```tex
Thus $k$ is one on the three fibers other than $(1,1)$, which gives
$k\in\{1,1+P_0\}$.
```

### M5. Handle the affine pair before applying the Product lemma

Current LaTeX, line 906

```tex
Lemma~\ref{l1:lem:cubic} gives $\deg g_1\le3$, excluding $z_2$ and $z_1+z_2$, both of degree four. If $z_1\in V_2$, then $g_1\in z_1+V_1$ is quadratic.
The product lemma gives $(g_1)_2=\pi+\rho$, with $\pi\in\langle P_0\rangle$ and $\rho$ zero or rank two.
```

Suggested replacement

```tex
The quartic part $f_2\wedge h_2$ vanishes because both factors have
quadratic parts in $\langle P_0\rangle$. This excludes $z_2$ and $z_1+z_2$,
both of degree four. If $z_1\in V_2$, then $g_1\in z_1+V_1$ is quadratic.
If both factors are affine, $(g_1)_2=f_1\wedge h_1$ has rank at most two.
Otherwise the Product lemma gives $(g_1)_2=\pi+\rho$, with
$\pi\in\langle P_0\rangle$ and $\rho$ zero or rank two.
In the affine case take $\pi=0$ and $\rho=f_1\wedge h_1$.
```

The distinction matters because the Product lemma assumes \(\langle f_2,h_2\rangle\ne0\) and the placement lemma quantifies over every pair in \(V_1\). The printed rank-four contradiction then handles both cases.

### M6. Specify the counted objects in the three-gate appendix

Current LaTeX, line 1214

```tex
The counting convention for the reported totals is 164\,596 with the additional degenerate spans excluded and 164\,639 with them included; the tables use 164\,596. The smaller enumeration itself allows dependent generators: its dimensions $1,2,3$ occur $1,605,163\,990$ times, respectively. Thus ``degenerate spans'' in the inclusive convention refers to the additional accounting, rather than to every span of dimension below three;
```

I enumerated the distinct spans from the stated rank-two domain and found 1, 605, and 163,990 by dimension. Repeated rank-two generators and zero quadratic parts add no distinct spans to this domain. A reader needs a separate object definition to reproduce 164,639. Suggested replacement, keeping the following definition of planes

```tex
The tables use 164\,596 distinct spans, including those with dependent
generators. The counts in dimensions $1$, $2$, and $3$ are respectively
$1$, $605$, and $163\,990$; 
```

### M7. Name the representative domain for the plane totals

Current LaTeX, lines 1266 and 1269

```tex
Lemma~\ref{l2:lem:degree} & All 887,857 affine and nonlinear planes, plus dependent factors & 237,568 quartic products; zero failures\\
Lemma~\ref{l2:lem:ideal} & All factor planes, affine and nonlinear; all quadratic representatives modulo $I$ & 887,857 planes; 270,385 quadratic quotient products; zero failures\\
```

The unreduced family is one dimension-one \(Q\) and 605 dimension-two \(Q\). Modulo constants these give dimension seven and eight factor spaces, respectively. Thus the direct plane total is \(2{,}667+605\cdot10{,}795=6{,}533{,}642\). The 83 symmetry representatives give the reported 887,857. State the domain directly in both rows.

```tex
Lemma~\ref{l2:lem:degree} & All affine and nonlinear planes over the 83 symmetry representatives, plus dependent factors & 887,857 planes; 237,568 quartic products; zero failures\\
Lemma~\ref{l2:lem:ideal} & All affine and nonlinear planes over the 83 symmetry representatives; all quadratic representatives modulo $I$ & 887,857 planes; 270,385 quadratic quotient products; zero failures\\
```

### M8. State the exact screen normalization modulo the available space

Current LaTeX, opening of line 1250

```tex
For a quadratic space $B$ and a preceding signal $g$, every next gate either has both factors in $B$, or normalizes to $k(g+F)$ with $k,F\in B$.
```

If both factors contain \(g\), replacing one by their sum adds the other factor to the product. That term belongs to the available space. The numerical test is for placement, so this change is permissible. Suggested replacement

```tex
For placement of a target $T$ from $B+\langle g\rangle$, first test products
with both factors in $B$ modulo $B+\langle g\rangle$. Any other placing
product can be reduced by plane operations
and absorption of the output correction to a condition
$k(g+F)\in T+B$ with $k,F\in B$.
```

### M9. Identify the predicates in the coset verification row

Current LaTeX, line 1237

```tex
Lemma~\ref{toolkit:coset} & exact and level-i statements, 11 spaces $\times$ 42\,784 $g_3$, all $F,H\in V_3$ (524\,800 products) & 0 violations in both; positive controls detected \\
```

“Level-i” appears only in this row. Name the predicate by its equations and distinguish factor planes from distinct functions. The count 42,784 is the number of nonlinear factor planes per \(Q_3\) of dimension three, namely \((511\cdot510-63\cdot62)/6\). The count 524,800 is the number of unordered factor pairs with repetition. If the historical predicates cannot be recovered from the run, the following row reports the independent check performed for this review.

```tex
Lemma~\ref{toolkit:coset}(a) & For each of $1\,000\,000$ sampled triples
$(f,h,F)$ and $1\,331$ distinct edge triples in the maximal admissible $\mathcal A$,
test all $H\in\mathcal A$ and all $v\in\mathcal W$ by linear elimination
on the external coefficients and the carry coefficient
& 0 violations; a positive control with a forbidden cubic was detected \\
```

## Coverage and reproducibility

Padding uses redundant affine-input gates. The normal form preserves semantic nonlinearity by keeping later factor functions as functions, and the number of linear gates after normalization lies in \(\{1,2,3,4,5\}\). In the \(\lambda=3,2,1\) arguments a final extension has dimension at most one. Whenever both \(z_2\) and \(z_1+z_2\) have been excluded before that extension, \(z_1\) must be available before it. The earlier exclusions cover the relevant degree and placement branches. The proof dependencies between cases go from \(\lambda=1\) to \(\lambda=2\) to \(\lambda=3\) to \(\lambda=4\). The within-case dependencies also form a directed acyclic graph.

| Check | Independent method | Positive control |
|---|---|---|
| `check_source.py` | Parse labels and references and topologically sort the reviewed proof dependency graph | Inject one undefined reference and a two-theorem cycle |
| `check_exterior.py` | Direct disjoint-monomial wedge, contraction, and basis enumeration | Same-type D1 pair giving \(\Omega\), actual dependent-generator placement, and a core wedge image containing \(\Omega\) |
| `check_ideal.py` | Direct ANF quotient by deleting ideal monomials, exact sweep of planes and actual first-gate pairs, plus symmetry action | A genuinely new affine-product direction and a relaxed first-gate target |
| `check_rigidity.py` | Binary elimination on the zero set of each candidate multiplier, exact over all output corrections | Relaxed target and a genuine cubic noncore \(\tau=1\) witness |
| `check_coset_parity.py` | Projected exact coset screens for sampled factors, exhaustive flag and minor tests, pointwise parity, and an exact product-coset sweep on the viable noncore branch | Forbidden cubic, relaxed feedback target, and the worked example as a relaxed ordinary target |
