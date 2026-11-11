# Independent referee audit of paper-v5

**Result.** I found no false mathematical statement or missing case in the lower bound. Two statements use a placement definition that is corrupted in the submitted TeX. Restoring that definition repairs both. The three-product argument remains valid for every dependent quadratic prefix. The appendix needs corrections to its Lean correspondence and verification claims.

**Scope.** I audited the 894-line `paper-v5/main.tex`, SHA-256 `810f57e3f4b8959841b627aa09979b1fe5a57c636c8cdde6f620260efcdf7835`, against the read-only `paper-v5/repo` clone at `b6c00ef8d94ff578585b428270df1af271a96bd6` (`lowhalf-arxiv-v1`). Line numbers below refer to that TeX file. The verdicts use the written mathematics and independent derivations. The Lean comparison is a source inspection. I did not rerun the kernel, external checkers, or historical SAT certificates.

## Verdicts

| Label | Verdict | Reason |
|---|---|---|
| `thm:MC` | CORRECT | Padding and normalization reduce the lower bound to the five exhaustive cases. |
| `l4:lem:normal` | CORRECT | First-entry replacement and affine-input swaps preserve wire availability and do not decrease the linear-gate count. |
| `l4:lem:Qonly` | CORRECT | Matching the quadratic part leaves an affine difference. |
| `l4:lem:support` | CORRECT | The sum of the two supports contains a four-dimensional support and has dimension at most four. |
| `l4:lem:noq2` | CORRECT | The required contractions would force both factors into the low-bit plane. |
| `l4:lem:types` | CORRECT | Classify the projection of the factor plane by dimension, with zero handled separately. |
| `thm:lambda5` | CORRECT | Five affine-input products cannot supply a quartic coefficient. |
| `toolkit:common` | CORRECT | One basis contraction must differ from the target's. |
| `l4:lem:deriv` | CORRECT | A constant factor difference forces a product of degree at most three. |
| `toolkit:w` | CORRECT | The contractions tangent to the hyperplane force divisibility by its normal in the exterior algebra. |
| `toolkit:feedback` | CORRECT | Boolean idempotence reduces both feedback bits and absorbs the output correction. |
| `toolkit:coset` | CORRECT | Complementary minors exclude ordinary products and external differences exclude feedback. |
| `l2:lem:ideal` | CORRECT | A low-bit square corrects the one exceptional fiber before wedge extraction. |
| `l2:lem:rankext` | CORRECT | The target shift has trivial radical while a sum of two wedges has a nonzero common kernel. |
| `toolkit:modfeedback` | CORRECT | Extraction gives a forbidden wedge in the target coset. |
| `toolkit:gram` | CORRECT | Symmetry and the kernel condition give the two-dimensional alternating factorization. |
| `l1:lem:ordinarypair` | CORRECT | The core base satisfies the coset hypotheses and the two noncore slice parities cancel. |
| `l2:lem:lastfactor` | CORRECT | Both projection ranks and all four feedback-coefficient pairs are covered. |
| `l4:lem:goodspan` | CORRECT | All ways to obtain the rank-four target leave a good direction or give a rank contradiction. |
| `l4:thm:main` | CORRECT | The proof uses the stronger good-span lemma and therefore includes redundant circuit prefixes. |
| `l3:thm:main` | CORRECT | The two quartic target classes force early availability of $z_1$, and both possible locations are excluded. |
| `l3:lem:udir` | CORRECT | The full and unequal type cases allow the required middle-bit direction. |
| `l3:lem:A` | CORRECT | Wedge extraction would extend the span to one with a good direction. |
| `l3:lem:third` | CORRECT | A cube tangent to the derivative hyperplane detects the cubic carry difference. |
| `l3:lem:C` | CORRECT | The good-direction and $U$-direction cases exhaust the possibilities. |
| `l3:prop:B` | GAP (definition only) | “Places” is malformed at lines 141–146. With its intended definition the proof is correct. |
| `l3:lem:B3U` | CORRECT | Both wedges must appear in the rank-four split and are core. |
| `l2:thm:main` | CORRECT | The proof excludes an unrestricted three-product tail from every specified quadratic base. |
| `l2:lem:early` | CORRECT | A noncore wedge has a killing direction with nonzero middle-bit part. |
| `l2:lem:onebase` | CORRECT | A single cross part gives a good direction even for a zero or repeated generator. |
| `l2:lem:cube` | CORRECT | The external tilt kills the extra product and retains the carry parity. |
| `l2:prop:onehigh` | CORRECT | The core coset case and the noncore ordinary and feedback cases exhaust the products. |
| `l1:thm:main` | CORRECT | Enlargement preserves the quadratic tail and the cubic tail uses the verified core and noncore obstructions. |
| `l1:lem:cubic` | CORRECT | At most one factor needs a quadratic coefficient and its cubic part is the stated wedge. |
| `l1:lem:reduce` | CORRECT | In the quadratic case $P_0b$ is a scalar multiple of $P_0$. |
| `l1:lem:first` | CORRECT | Degree excludes the quartic targets and a rank-four form cannot be the remaining single wedge. |
| `l1:lem:earlyfeedback` | CORRECT | Four distinct middle-bit slopes cannot be realized by the proposed multiplier. |
| `l1:lem:earlycore` | CORRECT | The ordinary cubic split forces the normalized factors into $U$. |
| `l1:lem:noncore` | GAP (definition only) | “Places $z_2$ in it” invokes the malformed definition. The stronger explicit product obstruction is proved. |

There are 37 CORRECT, two definition-only GAPs and zero ERRORs among the 39 numbered statements. The proof of `thm:MC` uses the explicit membership obstructions supplied by the affected arguments.

## Findings and suggested replacements

### 1. Restore the placement definition (lines 141–146)

The backslashes in the commands for emphasis, span and nonmembership were lost. In `l1:lem:noncore`, an explicit formula also makes the conclusion unambiguous.

~~~latex
Let $A$ be a space of Boolean functions and let $f,h\in A$.
We say that the product $fh$ \emph{places} $T$ from $A$ if
$T\in A+\langle fh\rangle$ and $T\notin A$.
Over $\F$, if $T\notin A$, this is equivalent to $fh+T\in A$.
~~~

In Proposition B, the hypothesis can be written explicitly as $Z_1\notin Q_3$ and $g_3+z_1\in V_3$.

Replace the last sentence of `l1:lem:noncore` with “Put $W=A+\langle g\rangle$. Then $z_2\notin W$, and $FH+z_2\notin W$ for all $F,H\in W$.”

### 2. Correct the verification attribution (lines 81, 782–786)

The pinned checkout contains the challenge placeholder and the separate completed solution. The [statement-alignment record](../lean-support/palomar_statement_alignment.md) reports a local build, successful statement and axiom comparisons, and replay of the solution export by Lean's checker. The [preflight record](../lean-support/palomar_preflight.md) and its JSON report describe preparation runs. The completed run records `pending / prepared` after a local license-text check. The record explicitly leaves the full hosted sandbox stage outstanding for that revision. These artifacts do not substantiate the asserted successful three-checker run at the release commit.

Replace the paragraph at lines 782–786 with:

> The local verification records report a successful Lean build, agreement of the Challenge and Solution statement exports, and a successful axiom comparison. The accepted axioms were `propext`, `Classical.choice` and `Quot.sound`. The recorded Palomar preparation accepted the source and configuration after a local license-text check. A completed three-checker Palomar run at the release commit is not documented in these records.

At line 81 replace “the whole argument is additionally checked in Lean~4” with “a Lean~4 proof of the same theorem uses the case reductions described in Appendix~\ref{sec:lean}”.

### 3. State the general tail once (lines 654–658 and 738)

The reuse is valid, but the cited theorem is stated about normalized circuits with exactly two linear gates. The relevant result is the stronger assertion proved by its argument. State it explicitly, as Lean does with `twoTail_of_twoClaim`.

Insert before line 654 and use it to introduce the proof there:

~~~latex
\paragraph{Three-product tail.}
Let $P=l\wedge r$ for arbitrary homogeneous linear forms $l,r$,
and let $B=V(\langle P_0,P\rangle)$. Starting with $B$, form
$B_{i+1}=B_i+\langle f_i h_i\rangle$ for $i=0,1,2$, where
$B_0=B$ and $f_i,h_i\in B_i$. Then $z_1,z_2$ cannot both belong
to $B_3$. The proof below establishes this assertion. The normalized
two-linear-gate case is its instance $B_i=V_{2+i}$.
~~~

Replace the final sentence of line 738 with:

~~~latex
Apply the three-product tail assertion to this enlarged base.
It allows arbitrary $l,b$, including $l\wedge b=0$ and
$l\wedge b=P_0$. The three factor pairs and both target memberships
remain valid under the successive inclusions of the old wire spaces
in the enlarged spaces.
~~~

**Degenerate hypotheses.** Over $\mathbb F_2$, dependence with the nonzero $P_0$ means exactly $P=0$ or $P=P_0$. In both cases $Q=\langle P_0\rangle$, $S=\langle P_0,Z_1\rangle$, and $\Phi(P)=0$.

| Section 7 citation | What actually happens for either degenerate generator |
|---|---|
| `early` | Its nonzero-cross hypothesis fails. The early-placement branch uses the core coset result instead. In fact $z_1$ cannot be placed by one product from $V(\langle P_0\rangle)$, by `l1:lem:first`, but the tail does not need this stronger observation. |
| `onebase` | Its statement still holds. Every contraction along an external direction vanishes, so use $\ell=0$ and $\delta_e\ne0$. The degenerate branch of `onehigh` can bypass this lemma. |
| `cube` | Its nonzero-cross hypothesis fails and the paper does not invoke it. The core coset result handles both ordinary and feedback products. If desired, the same parity argument on the untilted core cube gives the ordinary-pair result here. |
| `onehigh` | Its first branch applies with $S\subseteq\Lambda^2(U)$ and $f,h\in V(Q)\subseteq V(S)$. The coset lemma has no independence or dimension hypothesis. |

The general tail first excludes $z_1\in B$ because every nonzero candidate $Z_1+\alpha P_0$ has rank four and $P$ has rank at most two. If the first product introduces $z_1$, `early` forces the core case and the extended space lies in $V(S)$. The next product has both factors in $V(S)$, so the coset lemma excludes $z_2$ both before and after the third product. If the first product does not introduce $z_1$, `onehigh` for $W=V(S)+\langle f_0h_0\rangle$ excludes both $z_2,z_2+z_1$ after the second product because $z_1\in W$. Their exclusion forces $z_1$ to be available by then. The second product differs from $z_1$ by a function in the space before it, so that space extended by the second product lies in $W$. The third product cannot reach $z_2$. No step uses the semantic linearity of the prefix gates or nonlinearity of any tail gate.

### 4. Make the core coset application explicit (lines 428, 740 and 742)

Use “core supported” in the sense of line 487. If $c$ is core supported, the only external terms in its ANF are $\gamma a_2+\eta b_2$. Subtracting them leaves the space $A$ equal to its original value because both terms belong to $\mathrm{Aff}$. For the core representative $c_U$, every cubic monomial includes $a_0b_0$. Multiplication by either low bit preserves each such monomial by idempotence. Multiplying the quadratic and affine terms by a low bit produces degree at most three. Thus the core part and both low-bit multiples have even parity. This verifies the three radical conditions against **every** element of the core base by linearity. The argument depends on the shape of $c$, so core support alone for an arbitrary cubic would not suffice.

Replace line 428 with:

~~~latex
Suppose $c$ is core supported. Set $c_U=c|_{a_2=b_2=0}$.
Then $c+c_U\in\langle a_2,b_2\rangle$ and
$A=\mathcal B\oplus\langle a_2,b_2\rangle$, where
$\mathcal B=\Aff(U)+\langle P_0,Z_1,c_U\rangle$.
Each of $X,a_0X,b_0X$ has degree at most three for $X\in\mathcal B$.
Indeed, all cubic terms of $c_U$ contain both low bits, and
multiplication by either of these bits preserves those terms.
All three functions therefore have even parity on $\F^4$, proving
$1,a_0,b_0\in\rad\beta$. Apply Lemma~\ref{toolkit:coset}
with $g=F_1F_2$. The alleged identity would give
$F_3F_4+z_2\in A+\langle g\rangle$, a contradiction.
~~~

At lines 740 and 742 cite this explicit verification of the base. In the early cubic branch, $V_3\subseteq A$ ensures $g_3$ is a product from $A$. In the late core branch $g_2$ is a product from $B\subseteq A$. These are the signal hypotheses of the coset lemma.

### 5. Expose the last-factor case partition (lines 493–517)

Here $u,v\in A_0$, $k=u+\tau c$ and $R=z_2+v+\sigma c$. All external derivatives of $R$ lie in $A_0$ since $D_e c$ has only a possible $P_0$ term and affine terms. If $D_e k=1$, then $R=kD_e R$ follows on $k=0$ and $k=1$ separately. This is a product of elements of $A$ plus an $A$-correction to $z_2$. For $d=1$ the ordinary-pair lemma excludes it using a zero second product. For $d=0$ the sole possible nonzero cross part is that of $l\wedge b$, so the good-direction and derivative lemmas exclude it. Hence **constant** external derivatives of $k$ vanish.

| External projections | $(\tau,\sigma)$ | Reduction and outcome |
|---|---|---|
| Independent | $(1,0),(1,1)$ | Replace $R$ by $R+\sigma k$. The new $R$ has zero mixed external difference. Summing $(1+k)R$ over the external square gives $R=E+F+(D_e k)F+(D_f k)E$. Each product has degree at most three, contradicting the carry. |
| Independent | $(0,1)$ | $k\in A_0$ has zero external differences and $D_fD_eR=1$. The mixed difference gives $1+k=0$ everywhere. |
| Independent | $(0,0)$ | Choose either external unit direction. Neither derivative has a signal contribution. |
| Dependent | All four pairs | A nonzero external direction in the common kernel of $l,b$ removes both signal contributions, regardless of $d$. |

In the last two rows, $D_e k=0$ and $D_eR$ is a nonconstant affine low-bit function. Thus $k=1$ on the two fibers where $D_eR=1$, even if one is the excluded $(1,1)$ fiber. If $\tau=1$, the free quadratic part of $k$ on either of those fibers is $\bar l\wedge\bar b$, so $\bar l=\eta\bar b$ since $\bar b\ne0$. On the fiber $(s,t)$ this gives $c=(dst+l_{\rm low}(s,t)+\eta b_{\rm low}(s,t)+\eta)b$. Noncore support forces an external coefficient of $b$. Subtraction of the two zero free slopes gives equality of the two scalar $b$-coefficients by looking at that external coordinate, then $\zeta=0$ by looking at the differing middle-bit slope. For $\tau=0$ the scalar coefficients are both zero and the same subtraction gives $\zeta=0$.

On an off-ideal fiber the free quadratic part of $R$ is $a_1\wedge b_1+\sigma\bar l\wedge\bar b$. Vanishing would require the latter wedge to be the nonzero $a_1\wedge b_1$, putting both free factors in the middle-bit plane and making $c$ core. For $\tau=1$ the wedge $\bar l\wedge\bar b$ already vanished, so an external unit direction has constant $D_iR$ on the fiber. If the slope of $k$ were $\bar b$, choose a unit direction at a nonzero external coefficient of $b$. The two evaluations would make $R=kD_iR$ affine there, contradicting its $a_1b_1$ coefficient. Hence $k$ is constant on each off-ideal fiber and equals one because $R$ is nonzero there.

Replace the first two sentences of line 509 with:

> It remains to treat dependent external projections with arbitrary $\tau,\sigma$, and independent projections with $\tau=\sigma=0$. In the dependent case choose a nonzero external $e$ in the common kernel of $l,b$, so $D_ec=0$. In the independent case choose either external unit direction, since neither $k$ nor $R+z_2$ uses $c$. In both cases $D_e k=D_e u$ is constant and therefore zero by the first paragraph.

At line 504 replace “whose pairwise exterior products vanish” with “since $P_0\wedge Z_1=0$ and the exterior square of each generator is zero in characteristic two.”

### 6. Align the paper's proof routes with the Lean source

The correspondence table below separates statement coverage from proof route. The substantive difference in `l1:lem:first` is the exclusion of $z_1$: Lean enlarges the base to a noncore quadratic space and calls `noPlace_z1_two`. The paper uses a direct rank argument. To follow Lean here, replace its proof with:

~~~latex
Set $Q_*=\langle P_0,a_2\wedge b_2\rangle$.
We have $V_1\subseteq V(Q_*)$, and $z_1\notin V_1$
since $Z_1$ has rank four. If $z_1\in V_1+\langle fh\rangle$,
then $fh+z_1\in V_1\subseteq V(Q_*)$.
The extra generator of $Q_*$ has nonzero cross part, so
Lemma~\ref{l2:lem:early} excludes this identity.
If both factors are affine, their product has degree at most two.
Otherwise Lemma~\ref{l1:lem:cubic} gives a representative of degree
at most three modulo $V_1$, so the product itself has degree at most
three. Hence neither $z_2$ nor $z_1+z_2$ lies in the extended space.
~~~

The statement of `l4:thm:main` should match the stronger Lean statement used in the proof. Replace its first sentence with “Let $P_1,P_2,P_3$ be wedges, allowing zero, and let $Q=\langle P_0,P_1,P_2,P_3\rangle$ contain $Z_1$. Then \eqref{l4:eq:star} has no solution.” The reduction in Lean starts with an already normalized circuit. The paper's local normalization is valid and can be moved to the common overview so the case theorems consume the same hypotheses.

For the coset lemma and Gram identity, Lean's ordinary-product argument builds $MG=0$ directly and invokes a finite Gram theorem. The paper works with the radical quotient and a kernel basis. To align the order while retaining a hand proof, move `toolkit:gram` and the complementary-minor calculation before `toolkit:coset`. In the Gram proof, replace its reference to the coset lemma with a reference to the relocated calculation. Replace lines 312–338, after that move, with:

> Put $G_{jk}=\beta(x_j,x_k)$. It is alternating. Pairing the two equations in \eqref{coset:linear} with each $x_k$ gives $MG=0$, because $1,a_0,b_0$ are in the radical. Equation \eqref{coset:quadratic} says the complementary minors of $M$ are equal. Lemma~\ref{toolkit:gram} yields $G_{12}=G_{34}$. If $\sigma=1$, this contradicts \eqref{coset:carry}. If $\sigma=0$, the first two columns of $M$ form an invertible block and its other two columns are zero. Hence $MG=0$ forces the first two rows of $G$ to vanish. Then $G_{12}=0$, again contradicting \eqref{coset:carry}.

The remaining differences are local implementations of the same reductions. Replace “same route” in the appendix with the descriptions in the correspondence table. In particular, for coset feedback the paper uses a uniform affine-hyperplane argument where Lean splits according to which of $e_{a_2},e_{b_2},e_{a_2}+e_{b_2}$ kills both factors. To mirror those cases with a hand argument, replace lines 361–367 with:

> Since $c,d$ are dependent, either $e_{a_2}$ kills both, $e_{b_2}$ kills both, or the two nonzero projections agree and $e_{a_2}+e_{b_2}$ kills both. Choose a killing direction $e_0$ from these three cases. Equation \eqref{coset:feedback} gives $a_{e_0}=1$ and $k=\delta_{e_0}+v_{e_0}$. Choose a basis direction $e_1\ne e_0$. The two low-bit forms $\delta_{e_0},\delta_{e_1}$ are independent, so there is a point where $\delta_{e_0}=v_{e_0}$ and $\delta_{e_1}=1+v_{e_1}$. Equation \eqref{coset:feedback} in direction $e_1$ then has left side zero and right side one.

For final feedback normalization in the coset proof, lines 369–377 may be replaced by “Apply Lemma~\ref{toolkit:feedback} with $T=z_2$. Its ordinary conclusion is excluded by (a) and its feedback conclusion by (b).” This uses the same four scalar cases as Lean's `fin_00`, `fin_01`, `fin_10`, `fin_11`.

## Proof and citation ledger

The following checks cover the remaining steps and the hypotheses at their uses. The three longer branch arguments above provide the details for the quadratic tail, the core cubic and the last factor.

| Lines | Hand derivation and citation check |
|---|---|
| 85–104, 189–200 | Bit 0 has one summand. Bit 1 has two summands, whose product is the only carry into bit 2. Reducing the bit-2 column modulo two gives $q_2+\Omega$. The last upper-bound gate expands to $\Omega+g_1+g_2+a_1b_1$ using $a_1^2=a_1$, $b_1^2=b_1$. Each of its factors is available and the stated correction gives $z_2$. |
| 108–125 | $z_0\notin\mathrm{Aff}$, so first entry into the wire filtration means $z_0=g_j+v$, $v\in V_j$. Replacing $g_j$ preserves the next span. Each adjacent swap is legal because the gate moving left uses only affine factors, and the displaced gate retains its old available factors. Later spaces are unchanged. Semantic linearity keeps the same count except for the one possible increase at replacement. For `Qonly`, every generator has degree at most two and subtraction of the selected combination removes all quadratic coefficients. |
| 129–186 | A contraction is a row of the alternating form. External contractions detect exactly the monomials involving an external variable. A sum of forms is supported on the sum of their supports. The dimension bound in `support` is $4\le\dim(\mathrm{supp}\,P+\mathrm{supp}\,P')\le4$. The displayed decompositions of $Z_1$ and $Z_1+P_0$ have four independent factors, so both have rank four and support $U$. In `noq2`, the independent required contractions force the plane of the wedge to be $\langle a_0,b_0\rangle$, yielding zero external contractions. For `types`, dimension one leaves a nonzero core kernel vector, dimension two lifts the two standard external basis vectors, and all the resulting basis changes have determinant one. The count of nonzero wedges is $63\cdot62/6=651$. The core count is $15\cdot14/6=35$. For each of three types $v$, the core line has 15 choices and the external lift has $16/2=8$ choices modulo that line. Full wedges have $16^2$ choices. |
| 202–258 | `normal` puts every five-gate circuit into a case with $1\le\lambda\le5$. For `lambda5` the quartic coefficient cannot occur in the wire space. Expanding a quadratic monomial under a shift gives the constant-plus-contraction formula and a constant second difference. The product rule follows by multiplying the two shifted values. A hyperplane's difference set is its tangent subspace, giving the stated affine normal rule. In `common`, if both basis contractions matched, the two cross parts would match, contradicting `noq2`. This includes a zero generator. For `deriv`, replacing $f$ by $f+h$ adds $h$ to the product. The slope of $A=D_e g+\delta_e$ is outside the derivative line. If $D_e f=1$, multiply $h=H(f+1)+A$ by $f$ to get $fh=fA$. If $D_e f=0$, $Hf=A$ forces $H=1$ by the hyperplane rule, including the possibility $H=0$ with full zero set. Both products have degree at most three. In `w`, for $e\in\ker a$, $\iota_e\omega=m(e)a$ with $m=\iota_v\omega$, $a(v)=1$. Alternation gives $m(v)=0$, so $\omega=a\wedge m$ by testing on $\ker a$ and $v$. |
| 260–267 | When exactly one factor uses $g$, $f(h+g)+T=v+\sigma g$ gives $(f+\sigma)(g+h)+T=v+\sigma h$. When both use $g$, expanding $(f+h+1)(g+f)$ gives their product because $f^2=f,\ g^2=g$. The same correction works with $C=f$. The constants are allowed by $1\in A$. |
| 270–338 | On four bits the coefficient of the full monomial equals the sum over all points. Hence $\beta(1,X)=0$ excludes quartics and $\beta(X,X)=0$. Two constant external differences give the displayed direct sum by subtracting those slopes. The two linear external coefficients have targets $b_0,a_0$, independent modulo constants, so $M$ has rank two. A repeated external variable contributes only scalar linear terms. The mixed coefficient is $\det_{12}M+\det_{34}M$. In the radical quotient each coordinate vector of $\bar x$ lies in $\ker M$, so the pairing is the corresponding minor of $N$ times $\beta(q_1,q_2)$. The displayed minors of $[I\mid T]$ and $[T^{\mathsf T}\mid I]$ are complementary, even after undoing the column permutation because signs vanish. At external zero the carry coefficient is one, but the minor factor is zero for $\sigma=1$ by the mixed equation and for $\sigma=0$ because columns 3–4 vanish. |
| 340–379 | In coset feedback, $D_eG=a_e+L_e$ and the product rule gives (348). If $\mu_e=1$, multiplying by $k$ kills the term with $k+1$ and produces an ordinary product from $A$. If all $\mu_e=0$, $k$ is a nonzero core function because $z_2\notin A$. Evaluating where it is one forces $\det(c,d)=0$. When both projections vanish, the two equations would make $k$ both $a_0+\mathrm{const}$ and $b_0+\mathrm{const}$. Otherwise a common killing direction gives $k=\delta_{e_0}+\mathrm{const}$; a different direction would give a nonconstant affine right side vanishing on $k=0$, forcing its linear part to be the same $\delta_{e_0}$. The three target slopes are distinct. The concluding factor normalization keeps the product correction in $\mathcal W$ and then absorbs $\sigma g$ into the multiplier. The quadratic-core application has all three radical conditions by degree. |
| 381–411 | $P_0$ is the indicator of the $(1,1)$ fiber, so the ideal and congruence are as stated. In `ideal`, subtract a $P_0$ term to replace the affine-modulo-$I$ factor by an affine representative. If both factors have the $lr$ coefficient, addition cancels it and idempotence changes the correction by $f$. For a nonzero low-bit-only $a$, the selected opposite level misses $(1,1)$. Otherwise, changing the same free coordinate in each required low-bit edge keeps it in $\ker a$. Three corners vanish and the double difference is constant, giving $G=cP_0$ on the level. Subtraction is allowed because $P_0\in Q$. The zero-normal level is all of space, so no invocation of `w` with zero normal is needed. Taking $a=0$ also proves the claim about quadratics in $I$. In `rankext`, the common kernel of four forms has dimension at least two. The external, middle and low coordinates of the target contraction successively force all six coordinates to vanish, for either scalar correction. In `modfeedback`, the target correction is quadratic and lies in $q_2+V(S)$, so extraction puts a wedge in $q_2+S$. When the $l\wedge r$ coefficient is zero use the zero wedge in `rankext`. |
| 414–419 | For a right inverse $K$ of $N$, $N^{\mathsf T}K^{\mathsf T}$ fixes $\ker M$. By symmetry it also gives the corresponding right action on $G$, so $G=N^{\mathsf T}(K^{\mathsf T}GK)N$. The middle matrix is alternating since $x^{\mathsf T}Gx=0$ for every $x$. Its sole off-diagonal coefficient gives both minors, which are equal by the hypothesis on $M$. |
| 430–459 | In `ordinarypair` expansion uses $c^2=c$ and absorbs the scalar output coefficient into $H$. Products of $A_0$ have degree at most three because $P_0\wedge Z_1=0$ and squares vanish in exterior degree four. Thus $cH$ has degree at most four with quartic part exactly $\Omega$. Since $B(cH)=cH$, the degree-five part on the left is $B\wedge\Omega=0$, forcing $B\in U$. Then $l$ has a nonzero external part in the noncore case. The external change of basis is invertible, so $r,s$ are independent low-bit forms. On $B=j$ the quadratic $pq$ coefficient is $\alpha^{\mathsf T}Jd$ and the two linear coefficients are exactly $M(j)x(j)$ modulo constants. A nonzero low-bit slope cannot be constant there because the normal $B$ is off the low-bit plane. The same hyperplane argument with `w` shows independence of restricted quadratic parts: $P_0$ cannot have $B$ in its support and the other two nonzero choices have rank four. |
| 461–481 | The two minors sum to $\alpha^{\mathsf T}Jd=0$. `gram` first applies to $w(j)z^{\mathsf T}+zw(j)^{\mathsf T}$, giving $w^{\mathsf T}Jz=t^{\mathsf T}Jz=0$ by the two slices. Next $y=x+zZ_1$ is in the restriction of $\mathrm{Aff}(U)+\langle P_0\rangle$, on which the slice pairing is alternating by quadratic parity on three bits. Multiplication by $r,s$ preserves degree at most two there by low-bit idempotence, proving the radical condition including $1$. Thus $My$ pairs to zero against every $y_i$, and `gram` applies again. The cross terms are $\beta_j(Z_1,D)$ with a common affine $D$ since the $j$-dependent term and both quadratic coefficients vanish. The $Z_1^2$ contribution has zero slice parity. Summing gives zero on the left, and the correction from $A$ at external zero has degree at most three, leaving parity one on the right. |
| 523–539 | In `goodspan`, rank four requires at least two wedges other than $P_0$. With exactly two, `support` applies and the unused generator is the single possible noncore cross part. With three and one zero cross part, the other two cross parts coincide. With all nonzero cross parts, their full count is even by the mixed coefficient. Two full forms plus a type $v$ have $x_2=x_1+v_2r,\ y_2=y_1+v_1r$. On expanding, their external terms cancel and $r\wedge r=0$, giving the displayed single wedge. For three nonfull forms, equal types share a killing direction, exactly two equal types force the third core factor to vanish, and three distinct types force the three core factors equal. Their sum is again a wedge. This proves the stronger span claim used by `l4:thm:main`. With four initial linear gates `Qonly` gives the quadratic space; $z_2$ and $z_2+z_1$ have carry one so only $z_1$ can already be present when the final extension has dimension at most one. If normalization increased the count, `thm:lambda5` applies. |
| 550–568 | In `udir`, one zero cross part or a shared type gives a good direction, so neither occurs in a bad space. A full factor pair permits independent external equations for any middle component. In the mixed case the single core factor imposes at most one homogeneous equation on a two-dimensional middle plane and the remaining factor can be killed externally. For two different nonfull types, the two external equations are independent. In each surviving case contraction of the second generator is zero or has external part as stated. For the unnumbered hyperplane argument normalize the factors as in `deriv`. The resulting $A=D_e(fh)$ has slope outside the line because the correction is in $V(Q)$. The quadratic product vanishes on the nonempty level $A=0$, so `w` applies. For `A`, the contracted $Z_1$ is nonzero and purely low-bit, so the direction satisfies the hyperplane hypothesis. Adding the extracted wedge gives exactly a wedge span satisfying `goodspan`, even if the wedge is zero or redundant. |
| 570–608 | In `third`, restriction to $\ker\ell$ makes both differences constant. An external unit with $\ell(w)=1$ lifts the selected core edges into that hyperplane, preserving their core projections. Every quadratic has zero third difference, and the chosen three edges detect exactly one middle-bit carry derivative. The good-direction branch of `C` enlarges $Q_3$ by $Z_1$, which is externally killed, and therefore invokes `deriv` with its hypotheses intact. Proposition B uses the contrapositive of `A`, identifies $V_4$ with the enlarged quadratic space and invokes `deriv`. In `B3U` both wedges must occur because the two possible target shifts have rank four, so `support` applies to each. The theorem uses `C` and degree for the two quartic classes, then the one-dimensional quotient to get $z_1\in V_4$. If it is absent in $V_3$, Proposition B applies. If it is present in $V_3$, the $B3U$ conclusion gives exactly the core coset hypothesis. Normalization can increase the count only by one. |
| 618–652 | In `early`, nonzero cross part guarantees some external factor. Under dependent projections the basis change removes the second projection, leaving at most one equation on the middle plane; under independent projections both factor equations solve externally. The constructed direction kills $P_0,P$ and detects $Z_1$. The extracted wedge has coefficient one on $P$ by rank four, and is nonzero because otherwise $P=Z_1+\alpha P_0$. Both it and $P$ have rank two, so `support` contradicts nonzero cross part. In `onebase` both factors and the output correction lie in the enlarged quadratic space with a good direction. In `cube` the map $u\mapsto u+l(u)w$ kills $l$, preserves all core coordinates and is linear. The restrictions of $lr$ vanish and the quadratic-generator products stay of degree at most three, giving the parity contradiction even with an arbitrary output correction from $V(S)$. In `onehigh` noncore `onebase` and `cube` cover the zero and one output-signal coefficients. In feedback $kR=R$, $R+z_2\in V(S)$, and swapping the factors of $lr$ gives $b$ off the low-bit plane. Thus `lastfactor` applies with $d=0$. Modulo $I$, $k=1$ and $z_2=q_2$; the signal's original factors are in $V(Q)$ while $F,v\in V(S)$, exactly the `modfeedback` hypotheses. The dichotomy for $k$ is true but redundant for this inference. |
| 669–706 | In `cubic`, dependence modulo constants means a constant factor or two factors differing by a constant, so the product is in $V_1$. Otherwise normalize the nonzero $P_0$-coefficient pair to $(1,0)$. Removing constants adds only available functions. The only cubic part is $P_0\wedge B$. In `reduce`, absence of cubic terms forces $b$ into the low-bit plane and $P_0b=(b_{a_0}+b_{b_0})P_0$. In `first`, degree excludes the quartic targets, and $z_1\notin V_1$ by rank. If the product adds $z_1$, it is quadratic and `reduce` applies after `cubic` for a nonlinear product, while affine factors directly give a wedge. In `earlyfeedback`, a free slope of $k$ yields $R=kD_iR$ with $D_iR$ scalar on each fiber, producing at most two middle slopes. The required four slopes force $k$ to be constant on each fiber. On a fiber with value one the free wedge of $c$ must vanish. With $\bar b\ne0$, proportionality gives a scalar times $b$ on each fiber, allowing at most two slopes on the one fibers and one on the zero fibers. |
| 709–735 | In `earlycore`, `first` ensures $z_1$ must be introduced by the next product. The feedback lemma applies since $V_1$ contains $1$ and the normalized $c$ has the same extension. `earlyfeedback` applies because the cubic coefficient test gives $B$ off the low-bit plane. For the surviving ordinary product, the correction uses $c$ with coefficient one by `first`, so the ordinary product is cubic too. Its normalized cubic terms cancel iff $B+D=L$ is in the low-bit plane. Expanding $AB+CD=(A+C)B+CL$ and absorbing $P_0L$ gives (715). The left side has rank four, so both wedges are nonzero and `support` applies. Both of their factor planes are core, giving $A,B\in U$. In `noncore`, an ordinary correction in the enlarged space is either a single product or a sum of two, so `ordinarypair` covers it. For feedback, idempotence supplies $kR=R$ and `lastfactor` applies with $d=1$. Reducing each factor modulo $I$ sends $B$ to $V(Q)$ and $A$ to $V(Q+\langle Z_1\rangle)$. This verifies every membership in the final `modfeedback` call. |
| 737–749 | The quadratic branch is the general tail checked above. In the early cubic branch `earlycore` establishes the coset base and the next signal is a product from that base. In the late branch either `coset` or `noncore` excludes both quartic target classes through the second tail product. As in the quadratic case, the last extension forces $z_1$ to be available, and its placement by the second tail product puts that product in $W$. The last product cannot give $z_2$. Finally, append affine-input zero products to reach five gates and apply `normal` and the five exclusions, then use the explicit six-gate upper bound. |

The ancillary one- and two-bit claims at line 769 also follow by hand. A one-bit product is nonaffine and takes one gate. The three direct products $a_0b_0,a_0b_1,a_1b_0$ suffice for the two-bit low-half product. For the lower bound, normalize a hypothetical two-gate circuit to put $a_0b_0$ first by the same first-entry replacement. Then the proof of `l1:lem:first` on the four input variables excludes $z_1$ after one further product. Equivalently, extend such a circuit by two ignored variables and apply that lemma verbatim.

## Lean correspondence

Module names below are under `paper-v5/repo/LowHalfMul3/` unless specified. Names in the `LambdaOne` namespace are shown without their full prefix. “Finite” records an implementation difference at the indicated step. The hand derivations above do not rely on those computations.

| Paper label or step | Lean declaration(s), module | Comparison |
|---|---|---|
| `thm:MC` | `mc_lowMul3` (`LowHalfMul3Solution.lean`), `mc_eq_six_of_lambda_one_two` (LemmaC), `not_hasCircuit_five_of_cases` (Assembly), `mc_eq_six_of_no_five` (Reduction) | Same padding, normalization, five exclusions and upper bound. The theorem of the same name in Challenge is a deliberate placeholder. |
| Target ANFs | `lowMul3_eval` (Target) | Same statement. Lean decides the finite evaluations, whereas the paper derives them by integer column carries. |
| `sec:upper` | `upper`, `circuit_computes`, `z2_eq` (Upper) | Same six gates and output expressions. |
| `l4:lem:normal` | `normal_form`, `normal_form_five`, `exists_g0_normal`, `exists_move_linear_gate_left`, `exists_linear_prefix` (NormalForm) | Same replacements and swaps. Lean also returns the first gate's two specific factor functions. |
| `l4:lem:Qonly` | `wireSpace_eq_V4` (LemmaTwo) | Same subtraction of a representative with the desired quadratic part. |
| `l4:lem:support` | `lemma3`, `lemma3_finite_Z1`, `lemma3_finite_Z1P0` (LemmaThree) | Lean proves only the two target instances, by finite checks of the cross part. The general support theorem and dimension proof are paper-only. |
| `l4:lem:cross` | `phi_eq_zero_iff` (CrossPart) | Same coefficient check. Lean stores a pair of contractions and uses symmetry. |
| `l4:lem:noq2` | `lemma6`, `lemma6_finite` (CrossPart) | Same exclusion, finite in Lean. |
| `l4:lem:types` | `types`, `types_finite`, `rows_v`, `rows_full` (Types) | Same projection classification. Lean changes the given factor pair by an invertible matrix, including degenerate pairs. The paper may choose two zero factors for the zero wedge. |
| `thm:lambda5` | `no_all_linear_circuit`, `not_lambda_five` (LambdaFive), `lambdaCase_five` (Assembly) | Same degree obstruction. The first declaration applies to any gate count. |
| `toolkit:common` | `goodDir_caseA` (MainTheorem) | Same comparison of the two contractions. Lean takes four indexed generators. Unused slots can be padded by zero for the paper's applications. |
| `l4:lem:deriv` | `starFree_of_goodDir`, `line_core` and `line_finite_*` (LineDerivative) | Same factor normalization and derivative identities. Lean decides the affine zero-set subclaim. |
| `toolkit:w` | `pi2_wedge_of_vanish`, `wedge_of_contractions` (LemmaA) | Same tangent contractions and extraction, in coordinates in Lean. |
| `toolkit:feedback` | `feedbackNormal`, `f2_norm01`, `f2_norm10`, `f2_norm11` (Shared) | Same scalar cases and corrections. |
| `toolkit:coset` | `CosetBase`, `coset_B3a`, `coset_B3b`, `coset_obstruction`, `coset_z2_not_mem`, `cosetBase_V4` (Coset) | Same obstruction structure. Lean compares differences and forms a Gram matrix directly. The paper compares coefficients then uses the radical quotient. Lean uses the three killing-direction cases and four scalar normalization cases. |
| `l2:lem:ideal` | `idealExtract`, `extract_affine_right`, `low_product_on_plane`, `quadratic_inLowIdeal` (IdealExtract) | Same normalization, exceptional-fiber square and wedge extraction, with zero normal separately. |
| `l2:lem:rankext` | `q2NotTwoWedges`, `exists_orth4`, `q2_iota_ne_zero` (Shared) | Same common-kernel contradiction. Lean decides triviality of the radical. |
| `toolkit:modfeedback` | `feedbackNoPlaceModLow` (Shared) | Same statement and extraction followed by the two coefficient cases. |
| `toolkit:gram` | `gram_apply` (LambdaOneParity), `gram_finite` (Coset) | Same identity. Lean calls the finite theorem. The kernel-basis proof is paper-only. |
| `l1:lem:ordinarypair` | `ordinary_pair_noPlace`, `ordinary_external_B_zero`, `slice_gram_zero`, `two_slices_cancel` (LambdaOneOrdinary), `cosetBase_plusZ1_core` (LambdaOneCore) | Same core coset and two-slice Gram route. Lean uses `core_noNextZ2` in the core branch. Its slice row equations are pointwise and its Gram substep is finite. |
| `l2:lem:lastfactor` | `lastFactorLowIdeal`, `rigid_of_kill_dir`, `independent_generator_factor`, `independent_base_factor` (LastFactor) | Same partition and rigidity. Lean packages the independent $(0,1)$ result as modular despite the proof giving a global identity. |
| `l4:lem:goodspan` | `goodDir_main`, `decomposition_cases`, `triple_core`, `twoFull`, `zeroFull` (MainTheorem) | Same support and type split. Lean decides the nonfull external type subcase in `zeroFull_finite`. |
| `l4:thm:main` | `starFree`, `lambdaCase_four` (MainTheorem), `lambdaCase_four_of_starFree` (Assembly) | Same exclusion. Lean's algebraic statement allows redundant generators directly. The circuit reduction in Lean starts after normalization. |
| `l3:lem:udir` | `uDir_of_bad`, `goodDir_or_uDir`, `kill_v_fin`, `kill_vv_fin` (LemmaA) | Same projection cases. Lean decides the small direction constraints. |
| Unnumbered argument, line 561 | `z1_place_vanish` (LemmaA), then `pi2_wedge_of_vanish` | Same affine-level argument and wedge extraction. |
| `l3:lem:A` | `noPlace_z1_bad`, `noPlace_z1_of_genDir` (LemmaA) | Same good-direction contradiction after adding an extracted wedge. |
| `l3:lem:third` | `noPlace_z2_of_uDir`, `T3_Dz2_a`, `T3_Dz2_b` (LemmaC) | Same tangent cube. Lean decides the target cube values. |
| `l3:lem:C` | `noPlace_of_goodDir` (LambdaThree), `noPlace_z2_bad`, `noPlace_z21_bad` (LemmaC) | Same two branches. The appendix row omits `noPlace_z21_bad` for the bad $z_2+z_1$ case. |
| `l3:prop:B` | Good-$Q$ branch of `lambdaCase_three_of` (LambdaThree) | Same obstruction embedded in the assembly, with no standalone proposition. Lean only needs the inclusion in the enlarged space, while the paper shows equality. |
| `l3:lem:B3U` | `phi_of_Z1_mem` (LambdaThree) | Same two-wedge split, with the target-specific finite support result in Lean. |
| `l3:thm:main` | `lambdaCase_three` (LemmaC), `lambdaCase_three_of`, `flow` (LambdaThree), `b3Claim` (Coset) | Same last-extension flow. Lean splits the coefficient in a representation of $z_1$ and uses inclusion in the good branch. Its input is already normalized. |
| `l2:lem:early` | `noPlace_z1_two`, `genDir_two`, `kill_two_fin` (LambdaTwo) | Same killing-direction and wedge extraction proof. Lean decides the direction choice. |
| `l2:lem:onebase` | `goodDir_S`, `z2_not_mem_S_sup`, `formA_zero` (OneHigh) | Same good-direction obstruction. The zero-correction call in `twoClaim` is specifically to `formA_zero`. |
| `l2:lem:cube` | `formA_one_of_phi`, `csum_phi_basis`, `csum_phi_mul`, `csum_z2` (OneHigh) | Same tilted cube and parity comparison. Lean decides the basis and target sums. |
| `l2:prop:onehigh` | `oneHigh_of_phi` (LambdaTwo), `twoClaim`, `formB`, `lastFactor_two_mod`, `lastFactor_two` (OneHighFinish) | Same split and modular feedback contradiction. Lean's `formB` uses the modular result directly. The explicit dichotomy is a separate corollary in Lean. |
| `l2:thm:main` | `lambdaCase_two` (Solution), `lambdaCase_two_of` (LambdaTwo), `twoTail_of_twoClaim` (LambdaOneTail) | Same general tail flow. Lean has both a normalized circuit wrapper and an explicit tail assertion for arbitrary $l,r$. |
| `l1:lem:cubic` | `first_normal_form`, `first_cubic_coeff`, `first_cubic_iff` (LambdaOneBase) | Same $P_0$-coefficient and constant eliminations. Lean handles dependent factors within those coefficient cases. |
| `l1:lem:reduce` | `quadratic_first_le`, `low_mul_linear` (LambdaOneBase) | Same inclusion, without a nonzero or independent wedge assumption. |
| `l1:lem:first` | `no_z1_in_first`, `no_z1_q0` (LambdaOneEarly), `first_degree` (LambdaOneBase) | **Different $z_1$ proof.** Lean embeds in the noncore space with extra wedge $a_2\wedge b_2$ and calls `noPlace_z1_two`. The paper uses direct rank. `first_degree` is about the normalized representative and transfers to the original product modulo $V_1$. |
| `l1:lem:earlyfeedback` | `early_z1_feedback`, `fiber_line_contradiction` (LambdaOneEarly) | Same two fiber-slope contradictions. Lean uses finite scalar subclaims. |
| `l1:lem:earlycore` | `early_z1_core`, `early_z1_ordinary`, `wedge_core_factors` (LambdaOneEarly) | Same feedback exclusion and cubic split. Lean extracts factor core support from the cross parts of the nonzero wedges. |
| `l1:lem:noncore` | `noncore_noNextZ2` (LambdaOneAssembly), `substitute_c_modLow` (LambdaOneTail) | Same ordinary-product obstruction and feedback substitution modulo $I$. Lean uses the explicit `NoNextZ2` statement. |
| `l1:thm:main` | `lambdaCase_one` (Solution), `lambdaCase_one_of` (LambdaOne), `lambdaCase_one_of_branches`, `cubic_tail_contradiction` (LambdaOneAssembly), `tail_contradiction`, `twoTail_of_twoClaim` (LambdaOneTail), `core_noNextZ2` (LambdaOneCore) | Same quadratic enlargement and cubic early/late branches. The two tail reductions are named and shared in Lean. |

## Independent finite checks

Run `python3 audit-v3/checks/check_proof_steps.py` from the workspace. The script uses truth-table integers, exterior coefficient masks, and ordinary Python operations. It imports no manuscript or Lean verification code. The run passed.

- All 651 nonzero wedges, both target support splittings, the rank-six and two-wedge tests, and the killing direction of `l2:lem:early`. Controls include an explicit target split, a nonzero cross part, a rank-deficient contraction and a pair of core factors for which the direction condition fails.
- All independent Gram row pairs and all alternating $4\times4$ matrices. The controls include a nonzero equality and an unequal pair when the equal-minors hypothesis is removed.
- 165 distinct core signals checked against all three radical elements, five complete ordinary-product pair spaces, and all possible first products from the dependent quadratic base. An arbitrary core cubic missing a low bit violates the radical condition and allows a two-product placement. The spaces also supply reachable nonzero product classes as controls.
- All single-unit tilts in the quadratic cube argument and the untilted degenerate core cube. Products of restricted basis functions have even parity. The nonzero carry parity is the control.
- 52 complete last-factor generator/branch spaces across selected quadratic and cubic signals, covering every $(\tau,\sigma)$ and external rank case. The scalar square identity is checked on all 64 scalar tuples. With $R=z_2+a_2+b_2$, $k=1+P_0$ is a genuine fixed multiplier that differs from one on the ideal fiber. For $c=P_0a_2$, $k=1+c$ is a second such example, in the dependent $\tau=1$ branch.
- All 64 integer multiplication inputs, the six-gate circuit and the stored 48-point relaxed witness. Controls include $3\cdot3\bmod8=1$ with a nonzero carry and toggling an output mask's constant coefficient to cause disagreement at all 48 witness points.

## Typos and notation

| Location | Suggested text or change |
|---|---|
| 89 | “For any Boolean function $f$, let $\pi_d(f)$ denote its degree-$d$ ANF part. If $\deg f\le2$, write $f=f_0+f_1+f_2$ with $f_d=\pi_d(f)$.” This also covers the cubic and quartic uses. |
| 109 | Append “The normalization preserves the number of linear gates unless the replaced gate is nonlinear, in which case it increases that number by one.” The proof already establishes this and the four- and three-linear cases use it. |
| 141–146 | Restore the TeX definition given in Finding 1. |
| 183 | Replace “choose $r\in\ker\pi$” with “choose the nonzero $r$ in the kernel of $\pi$ restricted to the factor plane.” |
| 284 | Replace “in any dimension” with “for every dimension of $Q$” to distinguish the dimension of the form span from the fixed six-variable domain. |
| 424–428, 487 | Move the definition of “core supported” before its first use, or insert “We call a Boolean function core supported when all its terms of degree at least two use only coordinates in $U$.” before `ordinarypair`. |
| 448 | Replace “quadratic coefficients … in the restricted forms” with “coefficients in the independent degree-two parts of $P_0\vert_{B=j}$ and $Z_1\vert_{B=j}$, as proved below.” |
| 651 | For route alignment replace “In either case the congruence” with “The congruence”. The dichotomy can be a separate sentence introduced by “As a corollary”. |
| 670, 674 | Clarify the lemma's subject with “Every product of two factors in $V_1$, at least one of them nonaffine, has a representative … . The original product has degree three exactly when … .” |
| 710 | “Suppose $g_1$ is cubic and $z_1\in V_2+\langle fh\rangle$ for $f,h\in V_2$. Then $g_1$ is core supported.” The proof allows an arbitrary next product, as in Lean. |
| 739–740 | Insert “For this cubic case write $B$ for the base space.” The letter also denotes a homogeneous factor earlier. In the same line write “$g_2+z_1\in B$, hence $V_3=A$” if $z_1\in V_3$, making the coset signal membership immediate. |
| 75 | Replace “can be machine-checked but not inspected by a human” with “can be checked mechanically, but does not by itself give a short structural proof.” |
| 795–797 | Replace the blanket route wording with “Where Lean checks a finite step, the manuscript gives a hand proof. The table also identifies generalizations and differences in proof structure.” |
