# Review of the Fin5 retained-atom/paid-time intersection barrier

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Verdict:** **PASS as an internal local-interface no-go.**  I found no
missing paid/floor consumer.  The result should not be exported as a
conjecture-facing reduction because its separation table deliberately lacks
the ambient terminal witness and positive minimum.

## 1. Pathwise stopping-time formulas

Before absorption, a quitting-game history is the deterministic all-Continue
history.  Thus each survivor's behavioral law is represented by an
independent stopping time in `Nat infinity`, including arbitrary time-varying
hazards and Never mass.  Coupling the finite pure time `s` of `w` and Never
against the same survivor stopping-time vector gives exactly:

- zero difference when `tau<s`, because the same survivor coalition absorbs
  first under both strategies;
- `r_w(K union {w})-r_w(K)` when `tau=s`;
- `r_w({w})-r_w(K)` when `s<tau<infinity`; and
- `r_w({w})` when every survivor Never quits, since the all-Continue outcome
  has zero terminal payoff.

This proves (3.1)--(3.4).  With all rewards in `[-R,R]`, `|X_s|<=2R`.
Moreover `X_s` vanishes off `C_s={tau>=s}`, so a gain at least `Gamma`
implies

\[
\Gamma\le E[X_s]\le2R\Pr(C_s).
\]

In particular `R>0` and the live-mass lower bound in (3.5) is valid.

## 2. Temporal split and heavy-atom threshold

For `t<s`, the retained atom `E` lies in `C_s^c`.  Therefore
`ell<=1-m`, which gives (4.4).

For `s<=t`, `E subset C_s`, and `X_s` is constant there with value
`Delta_E`.  On the rest of the live cylinder it is at most `2R`, hence

\[
\Gamma\le m\Delta_E+2R(\ell-m)
          \le m\Delta_E+2R(1-m).
\]

This proves (4.5).  The strict threshold

\[
m>1-\Gamma/(2R)
\]

simultaneously excludes `t<s` and makes the numerator in (4.6) positive.
No sign assumption on the complementary events was smuggled into this upper
bound.

## 3. The 31-category alternative

The live cylinder has the following finite disintegration:

- 15 nonempty first-quitter coalitions at time exactly `s`;
- 15 nonempty eventual first-quitter coalitions at a time strictly after
  `s`; and
- the all-Never event.

On an after-`s` category, `X_s` depends on the eventual coalition but not on
its exact later date.  Hence it is legitimate to union all later dates.  If
the retained chronological atom lies in one category, deleting that atom
leaves an event on which the value is still constant.  Thus `C_s minus E`
is partitioned into at most 31 constant-value events.

If the retained contribution is below `Gamma/2`, the complement contributes
strictly more than `Gamma/2`.  Some category `F` therefore satisfies

\[
\Pr(F)X_s|_F>\Gamma/(2\cdot31)=\Gamma/62.
\]

Since `Pr(F)<=1`, this gives `X_s|_F>Gamma/62`; since
`X_s|_F<=2R`, it also gives
`Pr(F)>Gamma/(124R)`.  The inequalities are correctly strict.  In the first
arm, `m Delta_E>=Gamma/2`, `Delta_E<=2R`, and `m<=1` give both claims in
(4.8).

The note correctly says that an after-`s` category can be a union over
arbitrarily late dates.  It is a finite **event type**, not necessarily one
finite chronological atom.

## 4. Rational interpolation regression

With source law Always-Quit-at-zero and target law Never, source weight
`delta=1/112` gives each survivor the two-point law

\[
\Pr(T_j=0)=\delta,\qquad \Pr(T_j=\infty)=1-\delta.
\]

The all-four time-zero atom therefore has mass exactly `delta^4`.  Because
every survivor reward coordinate is zero, all four survivor debts are zero.
For `w` Never, the only positive prescribed outcome is the all-four coalition
`J`, so `U_w=delta^4`.

If `w` Quits at time zero, it receives one exactly when every survivor chose
Never, giving `(1-delta)^4`; on the retained atom its increment is
`r_w(I)-r_w(J)=-1`.  If `w` Quits at any `s>=1`, the retained atom is already
absorbed and contributes equally under deviation and baseline, whereas the
all-Never branch pays the solo value one.  The deviation payoff is therefore
`delta^4+(1-delta)^4`, and its gain is `(1-delta)^4`.

Bernoulli's bound `(1-1/112)^4>=27/28>1/2` verifies all stated strict gain
claims.  Thus the example exactly realizes the connector's independent
whole-law interpolation and proves that neither event intersection nor the
correct eventwise sign follows from its local output fields.

## 5. Consumer and scope audit

The general actual-profile terminal-gap theorem can still create a
source-matched paid first-disagreement row and cap-lifted summable port at the
profile, but it ignores the retained atom and retains the inert port arm.
`QuittingPaidRowFloorSafeSource` requires every prescribed coordinate above
punishment; neither Proposition 4.2 event arm supplies that hypothesis.
Likewise, a positive eventwise toggle supplies no endpoint-Nash product root,
reset law, Bellman successor, or decreasing debt/support rank.

The positive-slope rectangle consumers concern a debt change under an
additional stopping-law reset rectangle, not merely a positive terminal
event under one profile, so they do not apply either.  Proposition 4.2(2) is
therefore a quantitative paid endpoint category, not a missed exact-orbit or
floor compiler.

The regression is honestly scoped: it has terminal equilibria and is not a
global Fin5 counterexample.  It refutes only the automatic intersection
implication from the reviewed connector fields.  A use of the terminal
witness at further modified profiles remains possible and would require new
source-preserving stability or rank data.

