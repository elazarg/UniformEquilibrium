# Zero-tail timing Nash grafts transport the retained cap, not only its payoff

Author: `CODEX_PASCAL`

Status: **complete ordinary-mathematics exact characterization; not checked in
Lean; internal no-go/consumer boundary.**  The exact full-behavior cap formula
below is new relative to the retained-tail theorem: here the finite timing law
is Nash only for the hard zero tail and is then grafted in front of a different
actual tail.  The result gives a semantic-minimum consumer and a sharp
cap-dominated regression.  It does not consume the Fin4 hard residual.

## 1. Question and finite data

Let `I` be a nonempty finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow \mathbb R^I
\]

be a finite quitting reward table.  Fix a positive integer `N`.  In the hard
zero-tail timing game, each player chooses

\[
 T_N=\{0,\ldots,N-1\}\sqcup\{\infty\}.
\]

The earliest finite time determines the quitting coalition, while the
all-`infinity` outcome pays zero.  Let

\[
 P=(P_i)_{i\in I}
\]

be an independent mixed Nash equilibrium of this finite game.  Write

\[
 S_i=P_i(\infty),\qquad
 H_i=\prod_{j\ne i}S_j,\qquad
 M=\prod_jS_j=S_iH_i.                                      \tag{1.1}
\]

The timing samples are independent private mixed actions and are realized by
the usual conditional hazards; no player observes another sampled time.
There is one public live history.  A unilateral deviation below replaces the
player's complete behavioral strategy on that history, including its whole
tail behavior.

Let `tau` be an arbitrary actual behavioral tail in the same quitting game.
For player `i`, write

\[
 u_i=U_i(\tau),\qquad B_i=B_i(\tau),\qquad d_i=B_i-u_i.     \tag{1.2}
\]

Here `B_i` is the supremum over all complete unilateral behavioral
strategies, not a finite-time or attained best response.  Let `sigma=P*tau`
be the literal behavioral realization of the timing law followed, on joint
passage through the word, by `tau`.

For the zero-tail timing game define:

* `A_i`, the prescribed mixed-equilibrium payoff;
* `F_(i,t)`, the payoff of the old pure timing action `t<N`;
* `C_i`, the payoff of the timing action `infinity`.

Put

\[
 \alpha_i=\max_{t<N}(F_{i,t}-A_i),\qquad
 \beta_i=C_i-A_i.                                         \tag{1.3}
\]

Finite-game Nash optimality says

\[
 \alpha_i\le0,\qquad \beta_i\le0.                        \tag{1.4}
\]

Moreover, if `P_i(t)>0` then `F_(i,t)=A_i`, and if `S_i>0`
then `C_i=A_i`.

## 2. Exact category ledger

For a relative deterministic tail time

\[
 a\in\mathbb N\sqcup\{\infty\},
\]

let `v_i(a)` be its payoff against `tau_(-i)`.  Relative time zero is the
boundary date immediately after the timing word, positive relative times are
late actions, and `infinity` is literal Never.  Pure-time extremality gives

\[
 B_i=\sup_a v_i(a).                                      \tag{2.1}
\]

### Theorem 2.1 (exact zero-tail-to-retained-tail ledger)

The prescribed graft payoff is

\[
 \boxed{U_i(\sigma)=A_i+Mu_i.}                           \tag{2.2}
\]

Every deviation category has the following exact payoff and gain.

| category | deviation payoff | gain over `U_i(sigma)` |
|---|---:|---:|
| old finite `t<N` | `F_(i,t)` | `F_(i,t)-A_i-Mu_i` |
| boundary `a=0` | `C_i+H_i v_i(0)` | `beta_i+H_i(v_i(0)-S_i u_i)` |
| late finite `a>0` | `C_i+H_i v_i(a)` | `beta_i+H_i(v_i(a)-S_i u_i)` |
| Never `a=infinity` | `C_i+H_i v_i(infinity)` | `beta_i+H_i(v_i(infinity)-S_i u_i)` |
| pass prefix, then prescribed `tau_i` | `C_i+H_i u_i` | `beta_i+H_i(1-S_i)u_i` |
| arbitrary tail behavior | cap `C_i+H_iB_i` | cap gain `beta_i+H_i(B_i-S_i u_i)` |

Consequently the unrestricted behavioral cap and debt are exactly

\[
 \boxed{
 B_i(\sigma)=\max\left\{\max_{t<N}F_{i,t},\ C_i+H_iB_i\right\},}
                                                                  \tag{2.3}
\]

\[
 \boxed{
 D_i(\sigma)
 =\max\{\alpha_i-Mu_i,\ \beta_i+H_iB_i-Mu_i\}}
                                                                  \tag{2.4}
\]

and, using `M=S_iH_i`,

\[
 \boxed{
 D_i(\sigma)
 =\max\{\alpha_i-H_iS_iu_i,
          \ \beta_i+H_i[d_i+(1-S_i)u_i]\}.}            \tag{2.5}
\]

Thus the full tail arm is the pass-through gain plus `H_i d_i`.  Dropping
the retained-tail cap debt is invalid.

### Proof

On the joint timing-pass event, of probability `M`, prescribed play resumes
`tau`; on its complement the zero-tail timing outcome has already absorbed.
This proves (2.2).

An old finite action makes `i` quit before the tail, so its payoff is exactly
`F_(i,t)`.  If `i` forces Continue through the word, all payoff contributions
from opponent absorption during the word sum to `C_i`; the event on which
all opponents pass has probability `H_i`, and on that event the selected
tail strategy has payoff `v_i(a)`.  This proves every row of the table.

The exact quitting-game pure-time extremality theorem identifies the
behavioral cap with the supremum of the boundary, late, and Never values
together with the finitely many old values.  Since `H_i>=0`, the suffix
supremum is `C_i+H_iB_i`, proving (2.3).  Subtracting (2.2) gives
(2.4)--(2.5).  No best response is assumed attained.  `QED`

The checked retained-tail certificate appears as the exact seam-closed
subcase.  The fixed zero-tail law `P` is also a retained-tail timing Nash law
precisely when

\[
 \alpha_i-Mu_i\le0,
 \qquad
 \beta_i+H_i(1-S_i)u_i\le0                            \tag{2.6}
\]

for every player.  Under (2.6), (2.5) gives `D_i(sigma)<=H_i d_i`, exactly
the player-deleted survival bound in
`IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`.
Thus the new terms are not a competing estimate; they are the two certificate
defects created by changing the tail without re-solving the timing game.

## 3. Optimal Nash-only bound and sign split

From (1.4) and (2.4),

\[
\begin{aligned}
 D_i(\sigma)
 &\le H_i\max\{-S_i u_i,\ B_i-S_i u_i\}\\
 &=\boxed{H_i\bigl(B_i^+-S_i u_i\bigr)}.              \tag{3.1}
\end{aligned}
\]

Here `B_i^+=max(B_i,0)`.
The expression is nonnegative because `B_i>=u_i`.  This is the optimal bound
from only `(S_i,H_i,u_i,B_i)` and zero-tail Nash optimality.  If
`0<S_i<1`, some old finite action and `infinity` are both in the support, so
`alpha_i=beta_i=0`; hence (3.1) is an equality:

\[
 \boxed{D_i(\sigma)=H_i(B_i^+-S_i u_i)
 \quad(0<S_i<1).}                                     \tag{3.2}
\]

The correct sign boundary is the sign of the cap `B_i`, not merely the sign
of the payoff `u_i`.

* If `u_i>=0`, then `B_i>=0`, old finite gains fall by exactly `Mu_i`, and
  \[
  D_i(\sigma)\le H_i[d_i+(1-S_i)u_i].                 \tag{3.3}
  \]
* If `u_i<0` but `B_i<=0`, the old finite arm controls the optimal envelope:
  \[
  D_i(\sigma)\le M(-u_i).                             \tag{3.4}
  \]
* If `u_i<0<B_i`, the tail cap reverses that conclusion:
  \[
  D_i(\sigma)\le H_i\bigl(B_i+S_i(-u_i)\bigr),       \tag{3.5}
  \]
  with equality under interior mixing.  The missing `H_iB_i` term can be
  much larger than the finite-action increase `M(-u_i)`.

Two useful endpoint identities are also exact.  If `S_i=1` and `B_i>=0`,
then `beta_i=0` and (2.4) gives

\[
 D_i(\sigma)=H_i d_i.                                 \tag{3.6}
\]

If `S_i=0` and `B_i<=0`, then an old finite support action remains neutral
and every suffix action is nonprofitable, so

\[
 D_i(\sigma)=0.                                       \tag{3.7}
\]

## 4. Exact cap-dominated regression

The following two-player example shows why (3.4) cannot be inferred from
`u_i<0` alone.  Give both players payoff `1` at either singleton coalition
and payoff `-1` at the pair:

\[
 r(\{1\})=(1,1),\qquad r(\{2\})=(1,1),\qquad
 r(\{1,2\})=(-1,-1).                                  \tag{4.1}
\]

In the one-date zero-tail game, the symmetric profile which Quits with
probability `1/3` and chooses `infinity` with probability `2/3` is mixed
Nash.  Indeed, against opponent Quit probability `q`, Quit pays `1-2q` and
Continue pays `q`, so they are equal at `q=1/3`.

Let `tau` make both players Quit surely at its first date.  For either player,

\[
 u=-1,\qquad B=1,\qquad d=2,
 \qquad S=H=\frac23,\qquad M=\frac49.                 \tag{4.2}
\]

The zero-tail equilibrium payoff is `A=C=1/3`.  After grafting,

\[
 U(\sigma)=\frac13-\frac49=-\frac19.                 \tag{4.3}
\]

An old finite action gains only

\[
 M(-u)=\frac49,                                       \tag{4.4}
\]

while passing to a best tail deviation has payoff `1/3+(2/3)1=1` and
therefore gains

\[
 1-\left(-\frac19\right)=\frac{10}{9}.               \tag{4.5}
\]

This equals the sharp formula

\[
 H(B-Su)=\frac23\left(1+\frac23\right)=\frac{10}{9}.
\]

The example has a uniform-equilibrium payoff and is not a positive-minimum
or Fin4 hard-residual example.  Its exact role is narrower: it decisively
refutes every cap-blind graft bound based only on the sign of `u` and the
term `M(-u)`.

## 5. Terminal-gap localization

Assume a fixed terminal exploitability gap `gamma>0` applies to every actual
behavioral profile.  Applying it to `sigma` and using (3.1) gives the finite
screen

\[
 \boxed{
 \exists i,\qquad
 \gamma\le H_i\bigl(B_i^+-S_i u_i\bigr).}             \tag{5.1}
\]

The exact ledger gives a more strategic trichotomy.  For some player `i`, at
least one of the following holds:

1. an old finite action has gain at least `gamma` at `sigma`;
2. the pass-prefix-then-`tau_i` action has gain at least `gamma/2` at
   `sigma`; or
3. `H_i d_i>=gamma/2`.

Indeed, if the old arm of (2.4) is at least `gamma`, use its maximizing old
date.  Otherwise the tail arm is at least `gamma`; it is exactly

\[
 \bigl[\beta_i+H_i(1-S_i)u_i\bigr]+H_id_i,            \tag{5.2}
\]

so the last two alternatives are exhaustive.  In the third arm, for every
positive `epsilon` there is a literal tail behavioral deviation whose gain
over the pass-through profile exceeds `H_i d_i-epsilon`.  This is an actual
post-prefix paid suffix edge, but it is inherited from `tau`; it supplies no
new timing participation.

Thus a gap does give an actual paid response, as it already must.  The new
information is the exact localization into an old timing edge, a pass edge,
or inherited suffix debt.  It does **not** force the first two arms.

## 6. Positive-minimum semantic consumer

The positive minimum need not be attained by one behavioral profile.  Let

\[
 x=(u,B)
\]

be a terminal semantic carrier point minimizing total debt, and let

\[
 D_*=\sum_i(B_i-u_i)>0.                               \tag{6.1}
\]

Choose actual tails `tau_k` whose payoff/cap pairs converge to `x`.  For one
fixed zero-tail timing Nash law `P`, graft `P` in front of every `tau_k`.
Equations (2.2)--(2.4) pass to the limit.  Since the terminal semantic carrier
is closed, the limiting pair is again in the carrier.  Minimum total debt
therefore gives the exact necessary inequality

\[
\boxed{
 D_*\le
 \sum_i\max\{\alpha_i-Mu_i,\ \beta_i+H_iB_i-Mu_i\}
 \le\sum_iH_i(B_i^+-S_i u_i).}                       \tag{6.2}
\]

If the hard residual supplies a terminal gap `gamma`, the same approximation
and finite-player compactness sharpen (6.2) coordinatewise to (5.1).

Conversely, if a sequence of zero-tail timing Nash laws `P^k` satisfied

\[
 \max_i H_i^k\bigl(B_i^+ - S_i^k u_i\bigr)\longrightarrow0, \tag{6.3}
\]

then diagonal actual grafts would have every unrestricted behavioral debt
tending to zero.  Terminal-payoff compact selection would yield a
uniform-equilibrium payoff.  Hence (6.3) is a complete positive consumer,
but a hypothetical hard residual enforces the opposite fixed lower bound
(5.1).

## 7. What the hard residual does and does not force

For the maintained Fin4 hard residual, punishment normality and positive
minimum imply a uniform strict separation of every minimum-fiber payoff above
its own singleton reward.  Thus pure all-`infinity` is strict in the abstract
finite timing game whose all-pass payoff is the minimum payoff `u`; if the
minimum is behaviorally attained, this is the literal retained-tail timing
game.  For a general carrier point the statement applies along sufficiently
close actual tail approximants.  It does not change (2.4) for a Nash law
selected in the different, zero-tail game.

The present route therefore has the following exact disposition.

### No homogeneous/projective participation vector

The hard branch does force the weak fact that `P` is not pure
all-`infinity`: otherwise every singleton reward would have to be
nonpositive, and literal all-Continue would already be an exact terminal
Nash profile.  Hence the finite-participation vector `1-S` is nonzero and can
be normalized projectively.  But (5.1) is only a scalar survival/cap
inequality.  It gives neither vanishing absorption nor singleton-only
first-order Nash equations.  The hard residual's `no_homogeneous` field
concerns the normalized singleton matrix; no entry of that matrix occurs in
(5.1) or (6.2).  Consequently the normalized participation vector is not
shown to be a homogeneous or projective LCP witness.

### Paid edge but no new response square consumer

Alternatives 1 and 2 in Section 5 are genuine prescribed-source paid timing
edges.  Alternative 3 is a paid edge already present in the tail and merely
transported by `H_i`.  Comparing a supported old action with pass across the
zero-tail/tail switch gives the exact cross-change `H_i u_i`, but that switch
changes the complete continuation profile, generally in several player
coordinates.  It is not the one-coordinate common-response square produced
by the adjacent-deadline argument, and hybridizing it does not preserve the
minimum fiber.

### No terminal approximants in the hard branch

Condition (6.3) would produce terminal approximants, but the terminal gap
forces (5.1) at every timing Nash law.  The inherited term `H_i d_i` is not an
error: positive minimum means some tail debt is genuinely positive, and the
retained-tail return-floor machinery pushes survival upward rather than
removing that debt.

The decisive no-go is therefore limited but exact:

\[
\boxed{
 \text{zero-tail timing Nash}+\text{positive-minimum tail}
 \not\Rightarrow
 \text{cap-small retained-tail graft}.}
\]

Any continuation must add a mechanism which eliminates the inherited-debt
arm, closes the block payoff/cap seam, or compares two source-coherent timing
laws.  The payoff `u` and finite-versus-Never participation alone cannot do
so.

## 8. Source audit and nonclaims

Checked declarations inspected directly:

* `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
* `quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt`,
  `quittingPureTimeDeviationPayoff_absolute_sub_pass_eq`,
  `quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul`, and
  `IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
  in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`;
* `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`;
* `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
* `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
* `HasPositiveMinimumTerminalSemanticDebt` in
  `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`;
* `QuittingPositiveMinimumDebtTangentFamily` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
* `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
* `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

The adjacent-deadline paid edge/response-square alternative and its scalar
joint-pass seam were checked in
`CODEX_KOLMOGOROV__FINITE_DEADLINE_PROJECTIVE_BOUNDARY.md`; they are not
reclaimed here.  The retained-tail uniqueness regression in that note and
the nonidentity two-sided-charge lemma in
`CODEX_ROOT__NONIDENTITY_RETAINED_TAIL_TIMING_NASH_TWO_SIDED_CHARGE.md` concern
equilibria of the retained-tail timing game.  The present theorem instead
prices what happens when an equilibrium of the zero-tail game is kept fixed
while its tail is changed.

This note does not prove that a positive minimum is behaviorally attained,
that any selected timing law has interior marginals, that the participation
vector solves an LCP, that a paid edge returns to the same minimum source, or
that a counterexample exists.  It is a supplied-law exact characterization,
a complete envelope-to-terminal-approximation consumer, and a no-go for the
cap-blind graft inference.

## 9. Next exact question

Can one choose a **retained-tail** timing equilibrium, or a pair of
source-coherent zero-tail equilibria, for which the inherited term `H_i d_i`
is charged to a strict decrease of total semantic debt?  Without such a
charge, (6.2) is compatible with the positive minimum and cannot meet the
hard residual's homogeneous or paid-return consumers.
