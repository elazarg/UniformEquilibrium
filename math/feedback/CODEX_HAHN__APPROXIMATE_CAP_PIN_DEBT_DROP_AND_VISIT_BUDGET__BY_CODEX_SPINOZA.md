# Review of approximate cap-pin debt drop and visit budget

Reviewer: `CODEX_SPINOZA`

Reviewed file:
`notes/CODEX_HAHN__APPROXIMATE_CAP_PIN_DEBT_DROP_AND_VISIT_BUDGET.md`

Reviewed SHA-256:
`5f84a9449b29cd50abc8ee0b39d4163210f340377a330613e6701324f208d941`

## Verdict

**PASS.**  The arbitrary-root prefix identity, the two approximate-Nash
endpoint inequalities, the cap-pin case split, and the finite-visit telescope
are correct.  The result applies to a limit-born fixed product root at nearby
actual sources without stationarity.  It gives a finite visit bound only
along one literal vertical approximate-prefix chain with summable total local
Nash error, exactly as qualified.

## Exact identity reconstructed

Fix player `b`.  Write `p=q_b`, let `s` be the probability that all
opponents Continue, let `d=B_b-u_b≥0`, and put

\[
 Q=Q_b(q_{-b}),\qquad C=C_b(q_{-b};u_b),\qquad e=Q-C.
\]

The prescribed successor coordinate is

\[
 u'_b=pQ+(1-p)C=C+pe.
\]

In the semantic cap, a deviation that Continues at the new root and then uses
the complete old-tail cap replaces `u_b` by `B_b=u_b+d`, changing the
Continue endpoint by exactly `sd`.  Therefore

\[
 B'_b=\max\{Q,C+sd\}=C+\max\{e,sd\}
\]

and hence

\[
 d'_b=\max\{e,sd\}-pe.
\]

This uses no Nash condition and faithfully retains the old tail's complete
behavioral envelope, including Never, arbitrarily late stopping, and
randomized behavioral deviations.

## Approximate Nash and cap-pin expenditure

If the row is `ε`-Nash against `u`, its gains from switching the
mixed `b`-coordinate to pure Quit or pure Continue give

\[
 e\ge0\Rightarrow(1-p)e\le\varepsilon,
 \qquad
 e\le0\Rightarrow p(-e)\le\varepsilon.
\]

Splitting the exact identity into `e≥sd`, `0≤e<sd`, and `e<0`
correctly yields

\[
 d'_b\le sd+\varepsilon,
 \qquad d'_b-d\le\varepsilon.
\]

Under `d≥γ` and
`|B_b-r_b({b})|≤γ/4`, the same opponents-law estimate
as in the exact companion gives

\[
 |e-(r_b(\{b\})-u_b)|\le4M(1-s),
 \qquad r_b(\{b\})-u_b\ge3\gamma/4.
\]

If `1-s≥γ/(16M)`, the drop is at least `γ²/(16M)-ε`.  Otherwise
`e>γ/2`.  When `e≥sd`, the new debt is at most `ε`; when `e<sd`, the
identity and `(1-p)e≤ε` give a drop strictly above `γ/2-ε`.  Thus the
advertised common bound

\[
 d-d'_b\ge
 \min\{\gamma/2,\gamma^2/(16M)\}-\varepsilon
\]

has the correct sign and constants.  No exact complementarity or sure-Quit
claim is smuggled into the approximate case.

## Visit telescope

At a chamber visit, the named debt falls by at least `δ_b-ε_k`; at every
other prefix it can rise by at most `ε_k`.  Hence along a literal chain
`X_{k+1}=Prefix(q_k,X_k)`,

\[
 d_b(X_N)\le d_b(X_0)-|V\cap[0,N)|\delta_b
                  +\sum_{k<N}\varepsilon_k.
\]

Actual semantic debt is nonnegative and the common reward bound gives
`d_b(X_0)≤2M`, proving both the exact and finite-total-error visit counts.
Temporary departures from the cap-pin chamber do not invalidate the count,
because every intervening vertical increase is charged to the same error
sum.

## Limit-born roots and scope

If a fixed root is exact at a limiting prescribed payoff, continuity makes it
`ε_n`-Nash with `ε_n→0` at nearby actual sources.
The theorem therefore does handle each such literal prefix and gives an
order-one debt drop whenever the same cap-pin chamber holds.  For repeated
use it correctly requires `Σ_n ε_n<∞`, not merely `ε_n→0`.

No hidden stationary-tail assumption appears: only the current root is an
independent product law, while the tail is represented by its actual
prescribed payoff and complete behavioral cap.  Conversely, the result does
not cover horizontal response/reset edges, correlated private signals, or
renewal of the cap pin.  Those limitations are stated accurately.

The named source declarations checked for correspondence were
`quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticDebt_prefix_eq_blockAct` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`,
`quittingRootSuccessorPayoff_eq_endpointMix` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`, and
`isεQuittingRootNash_iff_coordinateNashDefect_le` in
`UniformEquilibrium/Quitting/Root/NashDefect.lean`.
