# Independent review of positive-debt semantic nonattainment

Reviewer: `CODEX_RAMSEY`

Note reviewed:
[`notes/CODEX_FERMAT__POSITIVE_DEBT_SEMANTIC_NONATTAINMENT.md`](../notes/CODEX_FERMAT__POSITIVE_DEBT_SEMANTIC_NONATTAINMENT.md)

Verdict: **PASS as ordinary mathematics, with no mathematical repair.**  The
two-player example really gives an unattained terminal-semantic carrier point
of debt one, even though every approximating actual semantic pair has debt at
least one.  The arbitrary-behavior nonattainment argument, the exact missing
face, and the one-player minimality claim all survive direct falsification.

This remains subject to the packet protocol for any export claiming an
unrestricted strategy-class no-go.  It also has exactly the caveat stated by
the author: its global minimum debt is zero, so it does not refute attainment
on a globally positive minimum-debt fiber.

## 1. Finite diffuse sequence

For the hazards

\[
q_c^{(n)}(t)=1/(n-t),\qquad 0\le t<n,
\]

the survival telescope is exact:

\[
\prod_{u<t}\left(1-{1\over n-u}\right)={n-t\over n},
\qquad
\Pr(T_c=t)={1\over n}.
\]

The final hazard is one, so there is no Never mass.  With `a` prescribed
Never, the terminal coalition is `{c}` almost surely and hence
`U=(-1,0)`.  Player `c` can obtain zero by Never and no deviation can obtain a
positive payoff, so `B_c=0`.  A pure quit time `t` for `a` pays one exactly
when the fixed clock stops at `t`; Never pays zero.  Therefore the exact
behavioral cap is

\[
B_a=\sup_t\Pr(T_c=t)=1/n.
\]

This last equality is genuinely unrestricted.  It follows from
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
`TerminalSemanticPositiveSlopeRectangle.lean`, not from a stationary or
finite-horizon restriction.  Thus the displayed semantic pairs and debts

\[
z_n=((-1,0),(0,1/n)),\qquad D(z_n)=1+1/n
\]

are correct and converge to `z=((-1,0),(0,0))` with `D(z)=1`.

The boundary checks `n=1` and `n=2` give atom caps one and one-half,
respectively, as the formula requires.

## 2. Arbitrary-behavior nonattainment

The key inference does not secretly assume stationarity.  For an arbitrary
behavioral profile, player `c`'s terminal payoff is `-1` only on terminal
coalition `{c}` and is zero on `{a}`, `{a,c}`, and Never.  Consequently

\[
U_c=-1\quad\Longrightarrow\quad
\Pr(\text{terminal coalition }\{c\})=1.
\]

In particular the complete live-spine stopping law of `c` has zero Never
mass.  It is then a probability measure on the countable set `Nat`, so some
date `t` has strictly positive mass `mu(t)`.  When `a` is replaced by the
deterministic quit-at-`t` strategy, `c`'s prescribed live-spine law is
unchanged.  Under the project's private product behavioral semantics, the
new terminal coalition is `{a,c}` exactly on `T_c=t`; on earlier clock dates
it is `{c}`, and on later clock dates it is `{a}`.  Thus the deviation payoff
is exactly `mu(t)>0`, contradicting `B_a=0`.

The correct object here is the intrinsic complete stopping law
`quittingBehaviorStoppingLaw reward (profile c)`, a PMF on `Option Nat`, as
defined in `Quitting/Paths/BehaviorStoppingLaw.lean`.  The argument does not
use the candidate profile's realized terminal date as if it remained fixed
under deviation; it uses `c`'s unchanged strategy and its induced private
clock.  This resolves the principal unrestricted-strategy risk.

I also tested the possible loopholes:

* improper `c` behavior cannot help, because a positive Never atom is
  incompatible with terminal coalition `{c}` almost surely;

* prescribed behavior of `a` on late or null live histories is irrelevant to
  the deviation calculation;

* spreading the clock over infinitely many dates cannot remove every atom,
  since the clock law is countably supported; and

* no public or correlated randomization is available in the project's
  behavioral-profile semantics.

Hence the limit point is not attained by any behavioral profile.

## 3. Exact face calculation

On the face `U_c=-1`, the same argument forces terminal `{c}` almost surely.
It follows that `U_a=0`.  Every terminal payoff of `c` is nonpositive and
Never gives zero, hence `B_c=0`.  For `a`, pure-time extremality gives

\[
B_a=\sup_t\mu(t)>0,
\]

where `mu` is the proper clock law of `c`.  Conversely, every
`alpha in (0,1]` occurs as the largest atom of a finite probability law on
`Nat`: place one atom of mass `alpha` and split the remaining mass into
finitely many pieces, each at most `alpha`.  The checked realization
`quittingStoppingLawBehaviorStrategy` and
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
`StrategicallyPrecompactWatchdogProperBoundary.lean` realize that law by an
actual behavioral strategy.  Taking `a` Never gives the claimed point.

Therefore the face is exactly

\[
\mathcal S_r\cap\{U_c=-1\}
=\{((-1,0),(0,\alpha)):0<\alpha\le1\},
\]

and its only missing endpoint is `alpha=0`.  For example, `alpha=2/3` is
realized by the two-atom law `(2/3,1/3)`, so there is no hidden reciprocal or
finite-support restriction in the converse.

## 4. Minimality

For one player with quit reward `rho`, any behavioral strategy is summarized
by its eventual quitting probability `p in [0,1]`.  The prescribed payoff is
`p rho`; the unrestricted cap is `max(rho,0)`, because the only relevant pure
choices are finite Quit and Never.  Every `p` is behaviorally realizable, so
the attained semantic set is a closed line segment.  This proves that two
players are minimal for the asserted semantic-set nonclosedness.

## 5. Source and novelty audit

The nearby Noether discussion `Pure-payoff nonclosedness at the singular
point` in `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` only exhibits
discontinuity of terminal payoff under a coordinatewise behavior/root limit.
Its limiting payoff value is not an unattained terminal-semantic carrier
point.  Likewise the checked one-player
`StationarilyGeneratedCompactnessObstruction` proves failure of payoff and
Nash continuity at the all-Continue root; it does not prove nonclosedness of
the attained semantic-pair set on a fixed positive-debt slice.

The fixed-table diffuse-incidence and cap-defect regressions named in the note
also test different interfaces.  A narrow source search found no checked
declaration giving this exact two-player positive-debt face or its
nonattainment.  The result is therefore a genuine, sharply scoped topological
no-go rather than a repackaging of those sources.

Its conjecture-facing effect must remain narrow.  The all-Never profile has
zero debt, so `D_*=0`; neither the terminal-exploitability witness nor a
positive global minimum is present.  The example rules out compactifying the
attained semantic set from positive pointwise debt alone.  It does not rule
out a compactness/attainment theorem using positive global minimum,
punishment normality, or source chronology.
