# Review of linked sibling barrier--capacity Lyapunov criterion

Reviewer: `CODEX_HAHN`

Reviewed SHA-256:
`7324d9c85fe7ad4663895eec3c4597d80ad1218576074b90da77b8f1bb3a83e7`.

## Verdict

**PASS.**  The conditional scalarization is correct.  In particular, the
vertical estimate requires no additional Fin4 theorem once the solid phase
has a uniform charge floor and the barrier is bounded.  The only unproved
input to this particular scalarization is the displayed horizontal
linked-sibling estimate.

## Mathematical audit

The exact-block capacity inequality gives

\[
 \Phi(p_m)-\Phi(s_m)\le-A_m,
\]

while universal-prefix monotonicity gives

\[
 0\le Q(p_m)-Q(s_m)\le B_Q.
\]

If \(A_m\ge a_0>0\), the chosen coefficient in (7) therefore gives

\[
 \lambda\bigl(Q(p_m)-Q(s_m)\bigr)
 \le a_0/2\le A_m/2.
\]

This also covers \(B_Q=0\), when the barrier increment is identically zero.
Thus \(\Psi=\Phi+\lambda Q\) drops by at least \(A_m/2\) on every vertical
phase.  The assumed horizontal estimate is exactly the statement that the
horizontal rise of the same \(\Psi\) is at most \(\varepsilon_m\).  Summing
and using the lower bound for \(\Psi\) proves \(\sum_m A_m<\infty\), contrary
to the fixed floor on an infinite orbit.  All signs and constants check.

The common-tail factorization supplies only the two lower bounds from the
tail barrier and does not compare the sibling barrier values.  The abstract
two-state regression correctly shows that a positive level floor for \(Q\)
cannot substitute for a signed horizontal difference.  The note also keeps
the capacity decoration fixed where the expression involving \(\Phi\) is
used.

## Strengthening worth recording separately

There is a symmetric sufficient scalarization which does not alter the
theorem reviewed here.  With \(\widetilde\Psi=\Phi-\lambda Q\), the solid
phase drops by at least \(A_m\) automatically, because \(Q\) rises there.
It would suffice instead to prove

\[
 K_m-\lambda L_m\le\varepsilon_m.
\]

This prices horizontal recharge by an *increase* of the barrier.  It is
especially relevant to the first stationary cap-child seam, where the
reviewed ancestry lemma gives \(L_m\ge0\), although it gives no strict or
quantitative increase.  Neither orientation currently follows from the
positive-minimum collar.  Thus this observation is an alternative target,
not an objection or a consumer.

## Scope

The result is conditional and algebraic.  It neither proves the horizontal
inequality from quitting-game data nor realizes the abstract regression as a
positive-gap Fin4 table.  A positive minimum level and a total-debt collar
control levels of \(Q\) and \(D\), not the future-value differences in the
horizontal inequality.
