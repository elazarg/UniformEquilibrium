# Review of `FULL_DEBT_1.md`

Reviewer: PAIRED_HULL_REVIEW  
Verdict: **REVISE.**  The root calculus and descendant-neutral isolation are
mathematically sound, but the claimed consumption/finite-rank chronology in
Section 3 is either unnecessary at the constrained minimizer or unsupported
as a renewable actual-source statement.  Most of the strongest root geometry
is already present in checked or reviewed form.

## Claim checked

The note claims:

1. an exact unrestricted-cap formula for one semantic prefix;
2. uniqueness and strictness of all Continue in the prescribed-payoff root
   game at a full-debt positive global minimum, with a linear defect price;
3. finite-rank consumption of a uniformly absorbing exact-cap-root arm; and
4. isolation of all Continue in the prescribed-payoff root game at a strict
   descendant-slice minimizer with at least two debtors.

I checked these claims against the exported four-profile descendant slice,
the current minimum-debt root declarations, and the existing strict-basin and
prescribed-root notes.

## 1. The cap formula and deleted-survival contraction pass

For a prefix root \(q\) over a semantic continuation \(y=(u,b)\),

\[
B_i(T_qy)=\max\{Q_i(q),C_i(q;b_i)\}
\]

is the complete unrestricted behavioral cap.  A unilateral behavioral
replacement has only the current Quit/Continue choice; after Continue its
complete continuation envelope is exactly \(b_i\).  Private randomization
only convexifies the two endpoints.  Never and arbitrarily late stopping are
already included in \(b_i\).

If \(q\) is Nash against \(u\), the prescribed prefixed payoff is
\(\max\{Q_i,C_i(q;u_i)\}\).  Since replacing \(u_i\) by \(b_i\) raises the
Continue endpoint by \(s_{-i}(q)d_i(y)\), equations (3)--(4) follow:

\[
0\le d_i(T_qy)\le s_{-i}(q)d_i(y),
\qquad
d_i(y)=0\Longrightarrow d_i(T_qy)=0.
\]

No stationary or finite-time restriction is hidden here.

## 2. Full-debt prescribed-root rigidity passes but is substantially duplicate

At a full-debt positive global minimum, if some \(q_k>0\), then

\[
D(T_qx)
\le d_k(x)+(1-q_k)\sum_{i\ne k}d_i(x)<D_*.
\]

Thus every prescribed-payoff exact root is all Continue.  The strictness
calculation

\[
U_i-r_i(\{i\})\ge D_*-d_i=\sum_{h\ne i}d_h>0
\]

is also correct.

This conclusion is already covered by the checked
`minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo` in
`TerminalSemanticMinimumDebtSimplex.lean`: a nontrivial exact prescribed root
at a positive minimum must be a solo root at a unique-debtor gate, which full
debt excludes.  The critical-face precursor is
`minimumTerminalSemantic_exactNash_criticalFace` in
`TerminalSemanticAuxiliaryNashBudget.lean`.

The linear estimate \(E_x(q)\ge\kappa_x a(q)\) is correct: strictness gives
the local linear bound and compactness gives a positive bound away from all
Continue.  But this too is already available in stronger checked form,
uniformly near the entire Fin4 minimum-fibre prescribed projection, as
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` in
`TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`.  The
ordinary-mathematics proof was also separately developed in
`CODEX_RAMSEY__STRICT_ALLCONTINUE_BASIN_LINEAR_DEFECT.md`.

Equation (9), the singleton directional derivative, is correct for
sufficiently small \(p\): the singleton moat keeps the same cap branches
active and summing the coordinate debts gives the displayed coefficient.

## 3. Section 3 must be split into a valid local contradiction and an
unsupported renewal claim

If \((R,Q,E,S)\) is already the constrained minimizer and \(q\) is an exact
cap root of \(R\), common prefixing preserves the zero coordinate and scales
both passports by joint survival.  Exact cap debt scaling gives

\[
D(T_qR)=c(q)D(R).
\]

Therefore **any** positive absorption, not merely absorption at least
\(\eta\), produces a feasible descendant with smaller objective.  This is a
one-step contradiction to constrained minimality.  It is exactly the
all-Continue-root neutralization already asserted by Theorem A of
`formalized/FOUR_PROFILE_DESCENDANT_SLICE_NEUTRALIZATION.md`.  No finite-rank iteration
is needed.

The broader sentence

> Since this rank is finite, all roots can be chosen on one nested source
> subsequence and concatenated into one finite chronological word.

does not follow merely from the numerical drop (10)--(11).  A root chosen
exactly at a semantic closure point need only be approximately Nash against
literal realizing suffixes.  After a new descendant/limit selection, finite
cardinality of the chain does not by itself prove that every next root is
exact on one nested actual source chronology, nor that the four profile
pairs retain their literal marks and ancestry.  One needs either:

* a supplied extension-compatible descendant constructor; or
* an explicit finite diagonal approximation statement with quantified Nash
  and passport errors accepted by the intended consumer.

Thus Section 3 should say: at the constrained minimizer the exact absorbing
root arm is immediately impossible.  If it intends a theorem about an
earlier renewable source process, it must add the missing compatibility
hypothesis and should not call finite numerical descent alone a chronology.

## 4. The descendant-neutral isolation argument passes

At the strict constrained minimizer, equations (12)--(14) are valid.  For a
prescribed-payoff Nash root, deleted-survival contracts debt while both
passports scale by joint survival.  Strict passport slack ensures that every
sufficiently small such root remains in the slice.  If \(q_k>0\) and some
other coordinate is a debtor, then

\[
D(T_qR)<D(R),
\]

contradicting minimality.  Hence no sequence of nontrivial prescribed-payoff
Nash roots can converge to all Continue when at least two debts are positive.
The one-debtor exception is necessary.

This is a sound local theorem, but it is weaker than the reviewed barrier
classification in
`CODEX_DESCENDANT__ASYMPTOTIC_PROJECTIVE_PASSPORT_AND_ROOT_BARRIER.md`.
There, after the normalized barrier minimization, every exact
prescribed-payoff root is either all Continue or a singleton-tight
unique-debtor solo root; with at least two debtors, all Continue is globally
unique, not merely isolated among small roots.  The present argument may
still be useful earlier, before that barrier minimization, but it is not a
new terminal consumer.

## 5. Positive atoms and source mismatch

Section 5 correctly explains why a time-forgetting positive atom can be
shifted behind arbitrarily many deterministic all-Continue rows while
preserving the semantic pair, law, and the present passports.  The singleton
margin makes the added early Quit option nonbinding.  It also correctly keeps
the two positive passports on separate profile pairs.  Nothing in the root
calculus identifies the \((E,S)\) paid fork with a unilateral edge on the
\((R,Q)\) chronology.

## Required revision

1. Recast Section 3 as the already-known one-step exact-root contradiction at
   the constrained minimizer.
2. Delete the claim that a finite numerical debt rank automatically produces
   one nested exact actual chronology, or add a precise extension-compatible
   source hypothesis and error-controlled diagonal theorem.
3. Mark equations (5)--(7) as consequences/instances of the checked
   minimum-debt-simplex and minimum-fibre linear-defect results.
4. Present (14)--(17), if retained, as an earlier local isolation lemma and
   distinguish it from the stronger reviewed normalized-barrier
   classification.

After those revisions the note is a correct consolidation, but not a new
consumer of the strict descendant-neutral port.
