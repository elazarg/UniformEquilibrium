# Review of the live-word hazard or tail-reprojection note

Reviewer: CODEX_HAHN

Reviewed file:
notes/CODEX_SPINOZA__LIVE_CAP_WORD_HAZARD_OR_FULL_SEMANTIC_TAIL_REPROJECTION.md

Reviewed SHA256:
b627f13916cd134614b4e2186b3422b7a695373dabf61a1e28368a2849d95369

## Verdict

**REVISE.**  The vanishing-hazard payoff, law, debt, and unrestricted-cap
reprojection theorem is correct.  The fixed signed source-to-tail law seam is
also correct.  The positive-hazard conclusion is mathematically recoverable,
but the note's stated invocation of the checked post-mark two-cut theorem at
entry cut zero is ill-typed: that checked structure requires a marked row
strictly before the entry cut.

## 1. Positive-hazard branch

For entry cut zero and exit cut \(m_n\), the unmarked
QuittingPositiveMinimumTwoCutBlock is valid.  The endpoints are literal
carrier points, the global minimizer supplies \(D_*>0\), and
\[
 \sum_{t<m_n,i}q_{n,t,i}\ge\chi
\]
gives the survival estimate used by the coercive theorem.  Therefore the
ordinary dichotomy
\[
 D(Z_n)\ge D_*+\frac{e^\chi-1}{2}D_*
\]
or
\[
 d_p(Y_n)>\frac{(1-e^{-\chi})D_*}{8}
\]
is correct.

However, finFour_offMinimum_or_exists_paidSplice accepts a
QuittingUniformlyReachedPostMarkTwoCutBlock, whose fields include
\[
 \mathit{markedRow}<\mathit{entryCut}.
\]
There is no natural-number marked row strictly before entry cut zero.
Consequently the sentence that the checked Fin4 theorem directly gives the
paid splice with entry cut zero is not a valid source adapter.

The desired conclusion needs no new mathematical hypothesis.  In the second
unmarked alternative, approximate player \(p\)'s unrestricted cap at \(Y_n\)
within \(K_\chi/16\).  This gives an actual unilateral response from \(Y_n\)
with gain \(>K_\chi/16\) and response-child \(p\)-debt at most
\(K_\chi/16\).  What it does **not** give is the post-mark prefix-preservation
field of the checked wrapper.  The note should state this direct unmarked
argument, or supply a genuine earlier marked row and move the entry cut after
it.

## 2. Vanishing-hazard semantic/law reprojection

This part passes.

The union bound gives \(1-a_n\le h_n\).  Since the word payoff is the mixture
of its early-absorption payoff and \(U(Z_n)\), both in the reward box,
\[
 \|U(Y_n)-U(Z_n)\|_\infty\le2Rh_n.
\]

The exact cap-anchored debt telescope
\[
 d_i(Y_n)=L_{n,i}+a_nd_i(Z_n)
\]
implies
\[
 d_i(Y_n)-d_i(Z_n)
 =L_{n,i}-(1-a_n)d_i(Z_n).
\]
Never gives cap at least zero, the reward bound gives cap at most \(R\),
and prescribed payoffs lie in \([-R,R]\), so \(0\le d_i(Z_n)\le2R\).
Combining these estimates gives exactly
\[
 |B_i(Y_n)-B_i(Z_n)|\le4Rh_n+L_{n,i}.
\]
Thus the conclusion really controls the unrestricted complete cap, rather
than only fixed responses.

The terminal law is
\[
 \operatorname{Law}(Y_n)
 =\nu_n^{\rm early}+a_n\operatorname{Law}(Z_n),
\]
where the first subprobability has mass \(1-a_n\).  The claimed total
variation bound follows.  Hence SemLaw cluster points of \(Y_n\) and their
literal tails \(Z_n\) coincide.

The distinct debtor transport is also correct:
\[
 d_j(Y_n)=L_{n,j}+a_nd_j(Z_n)\ge a_n\Gamma,
\]
while the owner debt vanishes on both profiles.  A suffix response lifts with
the exact factor \(a_n\).

## 3. Signed source-to-tail law seam

The cap-band response is a literal unilateral source-to-target edge with
owner payoff gain eventually at least \(D_*/4\).  Its payoff difference is
the sum of fifteen signed nonempty-coalition law contributions.  Therefore
one fixed coalition, after refinement, contributes at least
\(D_*/60\).  Law convergence of \(Y_n\) and \(Z_n\) transfers this signed
coordinate to the source-to-tail comparison up to \(o(1)\).  The sign of the
reward or probability difference need not be positive separately; only their
product is claimed.

This does not anchor the tail as a unilateral child of the source.  Passing
from \(Y_n\) to \(Z_n\) shifts every player's clock past the displayed word.
An exact example with an all-Continue prefix and arbitrary nonstationary
opponent tails shows that identical terminal semantic/law data need not
identify those strategy components or restore the source roots.  The note's
nonanchoring conclusion is therefore correct.

## Exact surviving contribution

After repairing the positive-hazard adapter, the theorem gives:

1. positive word hazard yields either a uniformly off-minimum literal tail or
   an actual paid response from the target, but without an earlier
   post-mark-preservation certificate; or
2. vanishing word hazard makes the target and its literal actual tail
   converge in prescribed payoff, unrestricted cap, and complete outcome
   law, while a fixed signed source-to-tail coalition-law seam remains.

The remaining obstruction is genuinely source-component ancestry, not an
uncontrolled target-to-tail cap seam.  No unilateral source reprojection,
root revalidation, or renewable consumer follows.

## Delta review of the repaired note

Re-reviewed SHA256:
`1f6992ccc2da7d3871d447dd16bcb9bf55ec73a6d1a7e4833761e9a8fa9fe6aa`

**PASS.**  The positive-hazard arm now uses exactly the unmarked two-cut
object available at entry cut zero.  Its ordinary coercive dichotomy is

\[
 D(Z_n)\ge D_*+\delta_\chi
 \quad\hbox{or}\quad
 d_p(Y_n)>K_\chi/8.
\]

In the second case, choosing a complete behavioral response within
\(K_\chi/16\) of player \(p\)'s cap gives a literal unilateral child with
gain, and hence decrease of that player's debt, strictly larger than
\(K_\chi/16\).  This requires neither a fictitious marked row before zero nor
the post-mark splice wrapper.  The repaired note expressly declines the
post-mark, source-return, and renewable conclusions, so the replacement is
well typed and honest.

The vanishing-hazard proof, full cap/law reprojection, and signed
source-to-tail law seam are unchanged in mathematical content.  I found no
new scope error in the repaired version.
