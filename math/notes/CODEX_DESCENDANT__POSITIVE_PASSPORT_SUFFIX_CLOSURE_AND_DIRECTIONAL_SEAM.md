# Positive-passport suffix closure and the directional seam

Identity: `CODEX_DESCENDANT`  
Status: **ordinary mathematics; a source-rebase theorem and a sharp
directional no-go, not a Fin4 consumer**

## 1. Question

The strict output of the four-profile descendant-slice theorem is a closed
limit of actual tuples obtained by prefixing one common finite product-root
word to four literal base profiles.  The limit retains

* zero debt for the observer $j$ in the response coordinate;
* a positive signed terminal-law passport $A$; and
* a distinct positive prescribed-payoff gain passport $G$,

both at fixed positive ratios to the response-coordinate total debt.

The export correctly does not claim a limiting finite ancestry code.  The
question here is whether the two positive passports nevertheless prevent the
literal base from disappearing behind a vanishing-reach prefix, and whether
rebasing at an actually reached cut yields an extension-compatible block.

The first answer is yes, more strongly than expected: every cluster of literal
suffix tuples remains in the same normalized descendant slice.  A finite
suffix tuple need not itself satisfy the limiting zero-debt condition.  The second answer
is no: forward play traverses the word from the slice minimizer to its base,
while the descendant construction creates the minimizer by prefixing outward
from that base.  The endpoint mismatch remains unless an additional
cross-rank successor certificate is supplied.

## 2. Abstract four-profile data

Use the notation of
`formalized/FOUR_PROFILE_DESCENDANT_SLICE_NEUTRALIZATION.md`.  Let

\[
X_n=(J(W_n\star R_n),J(W_n\star Q_n),
     J(W_n\star E_n),J(W_n\star S_n))
\tag{2.1}
\]

be a raw sequence converging to a descendant-slice minimizer $X_{\min}$.
Write

\[
D(X_n^R)\longrightarrow\ell>0,
\qquad d_j(X_n^R)\longrightarrow0,
\tag{2.2}
\]

and suppose

\[
\frac{A(X_n)}{D(X_n^R)}\longrightarrow a\ge\theta>0,
\qquad
\frac{G(X_n)}{D(X_n^R)}\longrightarrow g\ge\psi>0.
\tag{2.3}
\]

Let $M>0$ bound reward coordinates in absolute value and let $K=16$ be the
number of terminal-law labels.  At the unprefixed bases,

\[
|A(J(R_n),J(Q_n),J(E_n),J(S_n))|\le KM,
\qquad |G(J(R_n),J(Q_n),J(E_n),J(S_n))|\le2M.
\tag{2.4}
\]

For a word $W$, write $s(W)$ for its joint all-Continue product.

## 3. The positive passports force positive literal reach

Both decorations scale exactly under the same arbitrary word:

\[
A(X_n)=s(W_n)A_n^{\rm base},
\qquad
G(X_n)=s(W_n)G_n^{\rm base}.
\tag{3.1}
\]

Since $D(X_n^R)\to\ell\ge D_*>0$, equations (2.3)--(2.4) imply, after
discarding finitely many ranks,

\[
\boxed{
s(W_n)\ge
\kappa:=\min\left\{
  \frac{\theta D_*}{2KM},
  \frac{\psi D_*}{4M}
\right\}>0.}
\tag{3.2}
\]

Either passport alone gives a positive bound; the minimum merely records both.
Thus the literal base is reached through the common word with probability at
least $\kappa$.  A retained marked-date reach inside the base is multiplied
by this factor; it is not itself bounded below unless the base packet already
supplies such a marked-date floor.  The strict port nevertheless does not lie
in the vanishing-reach regime at the base-entry cut.

This does not by itself give a limiting finite date.  The lengths $|W_n|$ may
still tend to infinity, and the base can escape to later calendar times while
retaining the fixed survival probability (3.2).

## 4. Every actual rebase has only normalized-slice clusters

Fix an arbitrary cut $0\le t_n\le |W_n|$.  Split

\[
W_n=P_n\mathbin{+\!+}V_n,
\tag{4.1}
\]

where $P_n$ is the word before the cut and $V_n$ is the remaining suffix.
Let

\[
Y_n=(J(V_n\star R_n),J(V_n\star Q_n),
     J(V_n\star E_n),J(V_n\star S_n)).
\tag{4.2}
\]

This is a literal actual successor tuple, not a separately chosen carrier
realizer.  Put $p_n=s(P_n)$.  Since

\[
s(W_n)=p_n s(V_n)\le p_n,
\]

(3.2) gives $p_n\ge\kappa$.

For the response coordinate, the exact arbitrary-word cap-debt recursion is

\[
D(X_n^R)=C_n(P_n;Y_n^R)+p_nD(Y_n^R),
\qquad C_n(P_n;Y_n^R)\ge0.
\tag{4.3}
\]

Coordinatewise it gives

\[
d_j(X_n^R)=C_{n,j}(P_n;Y_n^R)+p_n d_j(Y_n^R),
\qquad C_{n,j}(P_n;Y_n^R)\ge0.
\tag{4.4}
\]

Hence

\[
0\le d_j(Y_n^R)\le\frac{d_j(X_n^R)}{\kappa}\longrightarrow0.
\tag{4.5}
\]

The decorations satisfy

\[
A(X_n)=p_nA(Y_n),
\qquad G(X_n)=p_nG(Y_n).
\tag{4.6}
\]

Combining (4.3) and (4.6), with all debts positive, gives the monotonicity

\[
\boxed{
\frac{A(Y_n)}{D(Y_n^R)}
 \ge\frac{A(X_n)}{D(X_n^R)},
\qquad
\frac{G(Y_n)}{D(Y_n^R)}
 \ge\frac{G(X_n)}{D(X_n^R)}.}
\tag{4.7}
\]

Indeed, for the first ratio,

\[
\frac{A(X_n)}{D(X_n^R)}
=\frac{p_nA(Y_n)}{C_n+p_nD(Y_n^R)}
\le\frac{A(Y_n)}{D(Y_n^R)},
\]

and the gain ratio is identical.

Now compactify the literal suffix tuples $Y_n$.  Every cluster belongs to the
same four-profile orbit closure, has zero observer debt by (4.5), and satisfies
the original normalized passport inequalities by (2.3) and (4.7).  Therefore
every such cluster belongs to the same closed descendant slice.

Since $X_{\min}$ minimizes response-coordinate debt on that slice, this also
has the uniform finite-rank consequence

\[
\boxed{
\min_{0\le t\le |W_n|}
 D\bigl(J(W_n[t:]\star R_n).1\bigr)
 \ge\ell-o(1).}
\tag{4.8}
\]

Otherwise one could choose violating cuts and compactify them to a slice point
of debt strictly below $\ell$.

Thus positive passport mass repairs the ancestry issue as far as literal
rebasing is concerned: every actual cut through the common word has only
clusters in the same normalized source class.  The finite tuple itself need
not lie in the closed slice, since its observer debt in (4.5) need not yet be
zero.

## 5. Exact finite-word ledger and the surviving direction

Let

\[
D(J(R_n))\longrightarrow L\ge\ell,
\qquad s(W_n)\longrightarrow s\in[\kappa,1]
\tag{5.1}
\]

after a subsequence, and let $C_n$ be the complete reached cap-defect ledger
of $W_n$ over $R_n$.  The exact word identity is

\[
D(X_n^R)=C_n+s(W_n)D(J(R_n)).
\tag{5.2}
\]

Consequently

\[
\boxed{C_n\longrightarrow\ell-sL\ge0,}
\qquad
s\le\frac{\ell}{L}.
\tag{5.3}
\]

There are two precise regimes.

### 5.1 Equal endpoint debt

If $L=\ell$, then

\[
C_n-\ell(1-s(W_n))\longrightarrow0.
\tag{5.4}
\]

This is an absolute additive identity, not a relative estimate when
$1-s(W_n)\to0$.  If the absorption has a positive liminf, then the ledger has
a positive liminf and, after selecting a convergent-absorption subsequence,
its ratio to absorption tends to $\ell$.  In particular, a word with
nonvanishing absorption cannot become a vanishing-error Nash--Bellman block.
If instead $C_n\to0$, (5.4) only forces $s(W_n)\to1$; it does not imply a
rate comparison between $C_n$ and $1-s(W_n)$.

### 5.2 Strict endpoint ascent

If $L>\ell$, then

\[
1-s\ge1-\frac{\ell}{L}>0.
\tag{5.5}
\]

The common word has a fixed actual absorption floor.  If its cap-defect ledger
also tends to zero, (5.3) forces the sharp balance

\[
s=\frac{\ell}{L}.
\tag{5.6}
\]

This is an asymptotically exact positive-absorption word, but its literal
successor is the **higher-debt** base $R_n$.  It is not a return to the strict
slice minimizer.

## 6. Why this is not yet a charged return or capacity contradiction

The constructional and chronological directions are opposite:

\[
\text{construction: }R_n\longmapsto W_n\star R_n,
\]

\[
\text{forward play: }W_n\star R_n\longmapsto R_n
\quad\text{on all Continue through }W_n.
\tag{6.1}
\]

Equation (4.8) proves that every intermediate forward successor remains in
the normalized slice at the level of clusters.  It does not provide a word beginning at
the reached base $R_n$ whose successor is the next outer descendant.  A word
selected at rank $n+1$ is prefixed to a different base $R_{n+1}$; compact
convergence of the two bases does not make them literally equal behavioral
profiles.

Therefore neither branch of Section 5 is presently iterable:

* in the equal-debt case, positive absorption carries a linear Nash-defect
  moat;
* in the strict-ascent case, vanishing defect is compatible with fixed
  absorption, but the block ends at a different, higher-debt source and has no
  literal return edge.

The exact missing datum is now narrower than a generic ancestry passport:

> **Cross-rank successor compatibility.**  After the literal word reaches
> $R_n$, one needs the next admissible word to start from that exact profile
> (or an explicitly controlled behavioral replacement of it), with errors
> summable relative to the retained absorption/passport scale.

Without this datum, concatenating the words silently reverses the prefix
operation.  The positive atom/gain passports prevent reach from vanishing and
make every within-word rebase source-valid, but they do not orient one rank's
base into the next rank's outer descendant.

There is a second, independent gap before a periodic cap-cocycle consumer can
be invoked.  The ledger controls probability-weighted root cap defects.  It
does not control the distance between the word's periodic Bellman fixed point
and the actual cap at every phase.  A rarely prescribed worse action can have
an order-one endpoint defect while contributing vanishing weighted ledger.
Thus suffix closure alone supplies neither phasewise Nash control nor the
periodic fixed-point estimate required to repeat the word.

## 7. What is new and what is not claimed

The new result is the suffix-closure theorem (3.2), (4.5), and (4.7)--(4.8):
positive normalized passports turn every actual cut of the approximating
common word into another cluster of the same descendant slice.  This uses
their exact joint-survival scaling to recover an actual base-entry reach.  It
does not convert the time-forgetting signed law coordinate into a uniformly
reached marked date inside the base.

The ledger classification (5.3)--(5.6) then isolates the only way the common
word itself can be asymptotically Nash-compatible with positive absorption:
it must run forward from the strict minimizer to a strictly higher-debt base.

No terminal approximate Nash profile, uniform-equilibrium payoff, renewable
finite rank, or concatenable exact-block family is produced.  In particular,
the theorem does not recover a finite limiting marked date and does not turn
horizontal prefix construction into forward chronology.

## 8. Exact source and Lean handoff

The exact checked inputs are:

* `rawDecoration_markedMass_eq_prefixSurvival_mul` and
  `rawDecoration_actualGain_eq_prefixSurvival_mul` in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
  and its total-debt form in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`;
* `quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add`
  in `Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`; and
* the four-profile orbit, slice, and minimizer of
  `formalized/FOUR_PROFILE_DESCENDANT_SLICE_NEUTRALIZATION.md`.

The Lean-sized new adapters are:

1. derive the uniform word-survival floor from either positive decoration and
   its global bound;
2. show normalized decorations are monotone under deleting a common prefix,
   using the nonnegative cap-defect ledger;
3. show zero observer debt propagates to every positively reached suffix;
4. compactify arbitrary selected suffix cuts and invoke slice minimality; and
5. project the exact word ledger to (5.3)--(5.6).
