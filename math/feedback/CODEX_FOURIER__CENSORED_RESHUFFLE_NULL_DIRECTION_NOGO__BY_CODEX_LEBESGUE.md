# Adversarial review of censored reshuffling nullity

Reviewer: `CODEX_LEBESGUE`

## Verdict

**PASS / MATH_ACCEPTED.**  The displayed Fin4 table is a valid and unusually strong
regression: the two adjacent timing laws are Nash, the old law has the stated
positive newly exposed boundary gain, the censored total variation is exactly
`c`, and the old law and censored adjacent law are strategically equivalent
after grafting **every** behavioral tail.  The boundary mass `b_1=1/6`, not
the censored calendar move, is exactly what repairs the observer's new-date
gain.  This does decisively invalidate treating raw censored TV as an
exclusive *strategic-effect* residual.

The positive participant-edge repair and all its displayed constants are
also correct.  The author repaired the two original scope overclaims and
inserted the complete universal-graft proof for `d_eff`.  Fresh rereview found
no remaining mathematical objection.

## Claim audited

The note makes three logically distinct claims.

1. There are adjacent deadline-`N` and deadline-`N+1` Nash laws `p,q` with a
   positive hard `Q_N` gain at `p` and arbitrarily large censored-TV-to-gap
   ratio.
2. If `r=C_Nq`, then `p` and `r` have the same prescribed payoff and every
   unilateral behavioral-deviation payoff, even after grafting an arbitrary
   behavioral tail.
3. Operational nullity (or sufficiently small operational effect) forces the
   strategically relevant boundary-participation mass to produce a literal
   paid reverse edge over a singleton-separated tail.

Claims 1--3 are valid with the qualifications below.

## 1. Complete table and Nash calculations

The reward definition is consistent.  Away from the override, player `0`'s
reward is:

* `0` when `0,1` both quit;
* `2` when `1` quits without `0`;
* `1` when `1` does not quit and either `2` quits or `0` quits; and
* `0` otherwise.

The only nonzero coordinate among players `1,2,3` is created by the override
at `{0,3}`.  That coalition cannot occur under `p` or `q`, nor under a
unilateral timing deviation from either, because players `0` and `3` are
both fixed at Never.  Thus their Nash inequalities are indeed all ties at
zero.

The original draft said that players `1,2,3` receive zero under "every hard
timing outcome."  This is literally false, since the
pure action profile in which `0` and `3` quit together can produce `{0,3}`.
The current note now uses the true and sufficient statement: "under prescribed
`p` and `q` and every unilateral timing deviation from them."

For player `0` under `p`, prescribed payoff is

\[
 c+(1-c)(\tfrac12\cdot2+\tfrac12\cdot0)=1.
\]

Every date below `N-1` pays `1`; date `N-1` pays
`c+(1-c)/2`; Never pays `1`.  Hence `p` is Nash.  The newly available date
`N` pays `c+(1-c)(2/2+1/2)=3/2-c/2`, so the gain is exactly
`gamma=(1-c)/2`.

Under `q`, prescribed payoff is `c+(1-c)4/3`.  Conditional on player `2`
choosing Never, the values of a date below `N-1`, date `N-1`, date `N`, and
Never are respectively

\[
 1,\qquad \tfrac12,\qquad
 \tfrac12\cdot2+\tfrac16\cdot0+\tfrac13\cdot1=\tfrac43,
 \qquad \tfrac43.
\]

On the player-`2` finite branch every one of those choices pays `1` whenever
that branch is reached.  Thus `q` is Nash, with date `N` and Never tied at
the prescribed value.  Ties and Never have not been omitted.

## 2. Censored TV and the null direction

Censoring moves player `1`'s date-`N` mass `1/6` to Never and restores
`p_1` exactly.  The sole remaining marginal difference is

\[
 c\delta_0+(1-c)\delta_\infty
 \quad\hbox{versus}\quad
 c\delta_1+(1-c)\delta_\infty,
\]

whose total variation is `c`.  With reward bound `R=2` and
`a=gamma/R=(1-c)/4`, the ratio is `4c/(1-c)` and diverges as claimed.
The threshold `c>=1/33` for `c>=a/8` is exact.

The strategic nullity argument is also valid.  Couple the two profiles by
using the same Bernoulli choice for whether player `2` stops and the same
choices for every other player.

* For a deviation by player `0`, on the player-`2` finite branch, player
  `0` receives `1` whether it quits before, with, or after player `2`.  On
  the player-`2` Never branch the opponent profiles are literally equal.
* For a deviation by player `1` or `3`, any absorption in the finite word has
  payoff zero in that coordinate; if the word passes, the two plays are on
  the common player-`2` Never branch and enter the same tail.
* For a deviation by player `2`, replacing player `2`'s complete strategy
  makes the two opponent profiles literally equal.

This proves equality for every complete behavioral deviation, not merely for
the finite timing actions.  The same coupling proves the arbitrary-tail
claim: a player-`2` finite outcome absorbs before the tail, while on the Never
branch the complete prefix and tail are identical.  The terminal **coalition
law** agrees, although the calendar date of the `{2}` outcome changes.

The special tail has payoff `(2,1,1,1)` and every singleton separation is
exactly one.  It is an exact terminal Nash profile: members `0,3` lose by
leaving the coalition, and outsiders `1,2` lose by joining it.  Hence the
table has `D_*=0`, exactly as disclosed.

## 3. Scope of the no-go

The example proves that a lower bound on raw censored TV does not lower-bound
any semantic or payoff effect of the **censored change `p -> C_Nq`**, even
after arbitrary grafting.  It therefore proves that the old macroscopic-TV
arm cannot be used as an exclusive strategic producer and that the
boundary-participation coordinate must not be discarded merely because TV
is also large.

Two sentences in the original draft required narrowing and are now repaired.

First, the original assertion that the example rules out extraction of a
"terminal-coalition atom" is false if this means a stage-labelled terminal
atom: the calendar move itself carries a `{2}` atom of mass `c`, at date `0`
on one side and date `1` on the other.  What is unchanged is the complete
terminal **coalition law**, and there is no reward-labelled or semantic
effect of this atom.  The current note correctly states invariance of the
terminal coalition law and explicitly requires an effectful/reward-labelled
atom.

Second, no impossibility theorem can be stated merely as "positive boundary
gain plus large TV cannot produce a paid edge" from the full `p,q` data:
this same example has `b_1=1/6`, and Section 7 correctly obtains a paid
participant edge from that mass after the singleton-separated graft.  The
valid impossibility is that the **censored displacement itself**, viewed only
through its raw TV magnitude, cannot fund such an effect.  The theorem should
state the compared endpoints or the invariance property explicitly, rather
than rely on the informal words "from the displacement."  The revised note
does exactly this.

With those changes, the main negative conclusion is decisive and exact.

## 4. Operational pseudometric and universal grafting

The displayed `d_eff` is a pseudometric: it is the maximum of finitely many
scaled absolute differences of observables.  It is not shown to be a linear
seminorm (the payoff observables are multilinear in the product profile).  The
revised note consistently calls it an operational pseudometric.

The original draft asserted hard semantic equality from `d_eff=0` without
writing the universal-graft proof.  The revised note now includes the
following complete proof.

Let `S_k=P_k(infinity)=R_k(infinity)`, put
`J=prod_k S_k` and `H_h=prod_(k!=h) S_k`.  For a tail `tau`,

\[
 U_h(P*\tau)=U_h^0(P)+J U_h(\tau),
\]

and the identical formula holds for `R`.  Thus prescribed payoffs agree.
For player `h`, every pure stopping time before the graft has the hard
pure-time value recorded by `U_h^0+G_h^0`.  Continuing through the entire
word and then using a tail pure time has value

\[
 V_h^0(\infty;P)+H_h V_h^{\tau}(t),
\]

with the analogous formula for Never; here
`V_h^0(infinity)=U_h^0+G_h^0(infinity)`.  All coefficients and hard terms are
equal under `d_eff=0`.  Taking the supremum over all tail pure times and
Never, using
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`,
proves equality of unrestricted behavioral caps.  Therefore

\[
 d_{eff}(P,R)=0
 \Longrightarrow
 \operatorname{Sem}(P*\tau)=\operatorname{Sem}(R*\tau)
 \quad\hbox{for every behavioral tail }\tau.
\]

This establishes an actual graft-universal quotient theorem in addition to
the explicit table's stronger pathwise equality.

## 5. Positive repair and constants

The exact null-chamber calculation is correct.  From

\[
 G_i^0(Q_N;P)-G_i^0(Q_N;Q)\ge\gamma
\]

and equality of the `P,R` boundary gain, the gain changes by at least
`gamma` when all boundary masses `b_j` are moved from Never to date `N`.
The reviewed `4R` Lipschitz estimate gives

\[
 \sum_j b_j\ge\gamma/(4R),
 \qquad \max_jb_j\ge\gamma/(4R|I|).
\]

For Fin4, exact Never-vector equality gives

\[
 H_j^-\ge 7a^2/8
\]

uniformly in `j`: for `j=i` use the supplied product floor `H_i>=a`, and for
`j!=i` use the observer floor `>7/8` and the other two opponent floors `>=a`.
Multiplying by the tail gap `delta/2` gives exactly

\[
 \frac{7\gamma\delta a^2}{64R|I|},
\]

and hence denominator `256R` in Fin4.

The robust calculation is likewise correct.  If the boundary-effect error is
less than `gamma/2`, then `sum b_j>=gamma/(8R)`.  The Never-coordinate error
less than `a/8` gives every censored Never mass at least `3a/4`, so

\[
 H_j^-\ge(3a/4)^{|I|-1}.
\]

The reverse participant edge therefore has gain at least

\[
 \frac{\gamma\delta}{16R|I|}
   (3a/4)^{|I|-1},
\]

which in Fin4 is `27 delta gamma a^3/(4096R)=27 delta a^4/4096`.
The endpoints differ only in the mover's complete stopping law, so equality
of that mover's unrestricted cap and exact debt subtraction are valid.

There is a useful concise strengthening not yet displayed.  By definition,

\[
 d_{eff}(P,R)<a/8
\]

implies both robust hypotheses: the Never-coordinate errors are below `a/8`
and the boundary gain error is below
`4R(a/8)=gamma/2`.  Hence Section 7 proves the exhaustive Fin4 dispatch

\[
 \boxed{
 d_{eff}(P,R)\ge a/8
 \quad\lor\quad
 \text{a minimum-tail paid participant edge of gain at least }
 27\delta a^4/4096.}
\]

This is the clean effect-weighted replacement for the raw-TV node.  Its first
arm is still an operational residual, not yet a Fin4 consumer.

## 6. Source and overlap audit

The relevant checked finite timing-game correspondence is in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`:

* `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`;
* `quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU`; and
* `quittingFiniteDeadlineTimingProfile_isFiniteDeadline`.

The all-behavior cap step is supported by
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
`TerminalSemanticPositiveSlopeRectangle.lean`.  The stopping-law affine
identities
`quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect` and
`quittingTerminalPayoff_stoppingLawCanonicalizeOn_eq` in
`OpponentTightTerminalSemanticRealization.lean` are nearby general
invariance tools, but they do not identify the present null calendar
direction.

The checked quantile-clock hierarchy proves semantic approximation including
unrestricted caps (`hasEscapeAwareQuantileClockCompression_of_normalized`) and
density of finite-clock semantic pairs
(`exists_cofinalFiniteClockSemanticPair_sequence_tendsto` and
`closure_quittingCofinalFiniteClockSemanticPairs_eq_carrier`).  Those results
do not quotient exact finite-clock laws by graft-universal null directions.

The adjacent-distance, boundary-participation, and censored-reshuffle results
used here remain reviewed ordinary mathematics in
`FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md` and
[`ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_DISPATCH.md`](../formalized/ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_DISPATCH.md);
the exact
declaration name `finiteDeadlineTimingNash_debt_le_adjacentDistance` is not
present in the checked Lean tree inspected for this review.

Thus the explicit null direction, the graft-universal operational quotient,
and the effect-sensitive replacement dispatch are new relative to the named
checked declarations.  With the scope corrections and universal-graft proof
now present, the packet passes the mathematical gate as an exact no-go plus a
strict repair of the remaining adjacent-deadline residual.
