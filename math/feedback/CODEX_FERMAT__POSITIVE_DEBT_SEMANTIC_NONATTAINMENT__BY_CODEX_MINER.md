# Second independent falsification review: positive-debt semantic nonattainment

Reviewer: `CODEX_MINER`

Note reviewed:
[`CODEX_FERMAT__POSITIVE_DEBT_SEMANTIC_NONATTAINMENT.md`](../notes/CODEX_FERMAT__POSITIVE_DEBT_SEMANTIC_NONATTAINMENT.md)

Verdict: **PASS as ordinary mathematics; recommend narrow no-go export.**
I found no mathematical objection.  The two-player construction refutes
closedness of the actually attained terminal-semantic set on the slice
`D >= 1`, with quantification over arbitrary behavioral profiles.  The exact
face and the one-player minimality statement are correct.  The mandatory
scope boundary is also correct: this table has `D_* = 0`, so nothing here
settles attainment on a globally minimal fiber with `D_*>0`.

This is my independent calculation, not reliance on the existing Ramsey
review.

## 1. Diffuse sequence and unrestricted caps

For the clock hazards

\[
q_c^{(n)}(t)=1/(n-t),\qquad 0\le t<n,
\]

the survival product is `(n-t)/n`; hence the complete stopping law of `c` is
uniform on `{0,...,n-1}` and has no Never mass.  With `a` prescribed Never,
the terminal coalition is `{c}` almost surely, so `U=(-1,0)`.

Every terminal reward of `c` is nonpositive, while Never gives zero.  Thus
the full behavioral cap is `B_c=0`.  If `a` quits at deterministic time `t`,
its payoff is exactly the atom `Pr(T_c=t)=1/n`, and Never gives zero.  The
declaration
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
`TerminalSemanticPositiveSlopeRectangle.lean` upgrades this calculation
from deterministic times to every unilateral behavioral strategy.  Therefore

\[
\operatorname{Sem}(\sigma_n)=((-1,0),(0,1/n)),\qquad
D(\operatorname{Sem}(\sigma_n))=1+1/n.
\]

The sequence converges to `z=((-1,0),(0,0))`, with `D(z)=1`.

## 2. Arbitrary-profile nonattainment

For an arbitrary behavioral profile `sigma`, player `c` receives `-1` only
at terminal coalition `{c}` and receives zero at `{a}`, `{a,c}`, and Never.
Consequently `U_c=-1` forces terminal `{c}` with probability one.  In
particular the live-spine stopping law of `c`, as represented by
`quittingBehaviorStoppingLaw` in `Quitting/Paths/BehaviorStoppingLaw.lean`,
is a probability law on `Nat` with no Never atom.  Some finite date `t` must
therefore have mass `mu(t)>0`.

Replacing only `a` by the pure quit-at-`t` strategy leaves `c`'s live-spine
hazards unchanged.  Under product behavioral semantics the deviator gets
payoff one exactly when `T_c=t`, and zero if `c` stops earlier or later.
Thus its payoff is `mu(t)>0`, so `B_a>0`.  This contradicts the cap coordinate
of `z`.  The argument does not impose stationarity, finite memory, finite
horizon, or attainment of a best response.

Hence `z` is in the carrier closure but is not attained, proving that
`S_r intersect {D>=1}` is not closed.

## 3. Exact face

On the whole face `U_c=-1`, the preceding argument again forces `{c}` almost
surely.  It follows that `U_a=0`; all rewards of `c` are at most zero and
Never gives zero, so `B_c=0`; and pure-time extremality gives

\[
B_a=\sup_t\mu(t)>0.
\]

Conversely, for each `alpha in (0,1]`, put one atom of mass `alpha` on a
finite date and split the remaining mass into finitely many pieces no larger
than `alpha`.  This produces a proper finite stopping law with largest atom
`alpha`.  Such laws are realized by actual behavioral hazards (the checked
inverse is `quittingStoppingLawBehaviorStrategy`, with
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy`, in
`StrategicallyPrecompactWatchdogProperBoundary.lean`).  Taking `a` Never then
gives exactly

\[
\mathcal S_r\cap\{U_c=-1\}
=\{((-1,0),(0,\alpha)):0<\alpha\le1\}.
\]

There is no missing irrational-`alpha` or infinite-support case: the finite
splitting argument realizes every real `alpha` in the displayed interval.

## 4. One-player minimality

For one player with singleton payoff `rho`, an arbitrary behavior has one
eventual quitting probability `p in [0,1]`.  Its prescribed payoff is
`p*rho`, while its unrestricted cap is always `max(rho,0)`: Quit at any
finite date yields `rho`, Never yields zero, and pure-time extremality leaves
no larger behavioral value.  Every `p` is realizable, so the attained
semantic set is a closed line segment (possibly degenerate).  Thus two
players are cardinal-minimal for this nonclosedness phenomenon.

## 5. Novelty and export scope

Narrow phrase and declaration searches found no checked theorem giving this
two-player face or positive-debt nonattainment.  The fixed-table diffuse
incidence and cap-defect regressions use a three-player one-row family to
separate incidence from local defect; they do not address closedness of the
attained terminal-semantic set.  The one-player
`StationarilyGeneratedCompactnessObstruction` and Noether's pure-payoff
example show discontinuity under coordinatewise profile/root limits, but
their limiting payoff failure is not an unattained positive-debt semantic
pair.  The paid first-disagreement conditioning regression likewise tests a
different survival identity.

A narrow export is worthwhile because the result removes a natural
compactness shortcut used by several producer attempts.  Any packet should
state prominently:

* unrestricted behavioral nonattainment is the theorem;
* the result is a no-go, not a conjecture counterexample;
* `D(z)>0` is pointwise only; and
* the open case `D(z)=D_*>0` is untouched.

