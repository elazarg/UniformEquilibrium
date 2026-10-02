# Audit of signed-externality actual-reach localization

Reviewer: SOCIAL_WEIGHT_REVIEW  
Date: 2026-08-31  
Verdict: **PASS with bounded presentation clarifications**

## Claim checked

The note converts a prescribed-payoff fall caused by changing player \(q\)'s
complete strategy into an actually reached first-disagreement row controlled
by \(q\), but evaluated in another player's original payoff coordinate.  It
then applies this to the signed-law arm of the two-response minimum-fibre
fork and gives a Fin4 regression showing that the resulting two-row port is
not yet a chronological consumer.

## Auxiliary-table transfer

Let \(P,Q\) differ only in player \(q\)'s complete strategy and suppose

\[
U_h(P)-U_h(Q)\ge a>0.
\]

Define an auxiliary table with

\[
\widetilde r_q(S)=r_h(S).
\]

The auxiliary prescribed payoff of \(q\) at \(Q\) is exactly \(U_h(Q)\).
Replacing \(q\)'s strategy in \(Q\) by its strategy from \(P\) gives the
literal profile \(P\), with auxiliary \(q\)-payoff \(U_h(P)\).  Since the
opponents of \(q\) agree in \(P,Q\),

\[
\widetilde B_q(Q)-\widetilde U_q(Q)\ge a.
\]

This is the correct complete-cap/debt inequality; no optimality of the
strategy used in \(P\) is required.

The other auxiliary reward coordinates are irrelevant to this debt
calculation and may all be copied from the same bounded original coordinate.
If \(M\) is the supplied original reward bound, the text should say
explicitly that the resulting auxiliary table has
\(\operatorname{quittingRewardBound}(\widetilde r)\le M\).  Applying
*positiveDebt_exists_actualJointReach_paidFirstDisagreementRow* with
\(0<\Delta\le a\) then yields

\[
\text{auxiliary \(q\)-gain}\ge\Delta/4,
\qquad
\Delta^2\le
32\,\operatorname{quittingRewardBound}(\widetilde r)^2
\Pr_Q(\text{survive to the row}),
\]

and hence the stated lower bound using \(M\).

The selected pure-time replacements alter only \(q\).  Terminal laws and
survival events do not depend on which payoff coordinate is used to evaluate
them.  Therefore the auxiliary \(q\)-gain is literally

\[
U_h(Q[q\leftarrow\tau^{\rm rec}])
-
U_h(Q[q\leftarrow\tau^{\rm src}])
\]

in the original table.  The translation is exact.

If the support-strengthened theorem is used, its source witness is supported
by \(q\)'s actual stopping law in \(Q\), not by the stopping law used in
\(P\).  The note states this provenance correctly.

## Constants in the minimum-fibre application

From the limiting payoff fall \(D_*/18\), the eventual actual floor
\(D_*/20\) is valid.  Taking \(\Delta=D_*/20\) gives

\[
\Delta/4=D_*/80,
\qquad
\Delta^2/(32M^2)=D_*^2/(12800M^2).
\]

The same conservative transfer gives
\(d_h(x^2)\ge D_*/9\), so eventually \(d_h(X_n^2)\ge D_*/10\).
Applying the original-table theorem at the same source \(X_n^2\) with
\(\Delta=D_*/10\) gives

\[
D_*/40,
\qquad
D_*^2/(3200M^2).
\]

All constants and quantifiers are correct.  The two rows are co-realized on
one literal source profile, but may occur at unrelated dates and may destroy
one another's gain after execution.  The note correctly refuses to call
them a Bellman chronology.

## Fin4 regression

The four displayed profiles have the stated prescribed payoffs, caps, and
debt vectors.  Each arrow toggles one of \(q,h\) to its exact better endpoint
with gain one.  Player \(k\) strictly prefers Continue at every opponent
root.  Conditional on \(k\) Continuing, the prescribed rules make \(h\) and
\(\ell\) strictly prefer Continue; conditional on all three Continuing,
\(q\) strictly prefers Continue against cap one.  This sequential argument
does exclude every non-all-Continue exact product root.

For complete reproducibility, the reward-table paragraph should be read as
the following total completion:

- use (4.1) for \(k\) on every coalition;
- use the Continue-dominant rule for \(h,\ell\) whenever \(k\notin S\);
- use (4.2)--(4.3) on their listed \(k\)-coalitions and zero on their
  remaining \(k\)-coalitions;
- use (4.2) for \(q\) on its listed \(k\)-coalitions, zero on the remaining
  \(k\)-coalitions, and zero whenever \(k\notin S\).

With this completion all singleton rewards are zero.  The all-Never profile
has payoff and complete cap zero, so the regression has \(D_*=0\), as
claimed.  It does not falsify any theorem using positive-global-minimum
provenance.

## Novelty and conclusion

The role-swapped auxiliary-table localization is a genuine strengthening of
the earlier signed terminal-label conclusion: it restores an actual source,
a pure-time first disagreement, source-witness support, and a quantitative
joint-reach floor without the factor \(16\) from coalition-label
pigeonholing.

It is not a chamber consumer.  The row is profitable in player \(h\)'s
payoff coordinate while controlled by player \(q\); it need not be a legal
profitable deviation for \(q\) in the original game.  A source-matched curl
consumer or a positive-minimum exclusion of the explicit response-cycle
shape is still required.
