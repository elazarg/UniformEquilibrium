# Review of same-profile spare-player cancellation

**Reviewer:** CODEX_CEDAR  
**Date:** 2026-08-25  
**Verdict:** mathematical **PASS** in the explicit supplied-profile scope;
two notation/scope clarifications are required before any reuse.  The verifier
is sound, but the producer hypotheses are absent.  The charge-one branch is
already a direct exact-terminal-Nash consumer; the charge-one edge by itself
does not supply a returned charged path.

## Claim reviewed

The note fixes five players split as two sure base quitters `B`, two free
players `F`, and a spare `s`.  Starting from one actual behavioral source, it
changes only the spare's first marginal.  Endpoint complementarity is assumed
for the two base and two free players, both endpoint payoff vectors lie above
the punishment floor, and the spare-debt budget is assumed.  It claims exact
affine debt cancellation, an exact absorbing root when the spare is
indifferent, and a two-to-one debt-support drop at a positive global minimum
otherwise.

I checked all unrestricted deviations, the endpoint interpolation, the
minimum argument, the sharp interval, and the downstream repository boundary.

## 1. Unrestricted behavioral deviations really collapse to date zero

This is the strongest part of the statement and it is exact.  For a deviation
by either base player, the other base player still Quits surely.  For a
deviation by a free player or the spare, both base players still Quit surely.
Thus every unilateral behavioral replacement leaves first-stage absorption
certain.  No continuation strategy, pure-time deviation, or Never action can
change the resulting payoff after date zero.

Consequently, with opponents fixed, player `i`'s unrestricted cap is exactly

```text
max(Q_i(q), C_i(q)).
```

This is not merely a stationary-deviation screen.  It covers arbitrary
behavioral deviations because every later history has probability zero after
every unilateral replacement.

For fixed prescribed Quit probability `p`, subtracting the prescribed affine
payoff gives exactly

```text
Phi_p(Delta)=(1-p) Delta_+ + p (-Delta)_+.
```

For the spare, `Delta_s=-kappa<=0` and its prescribed rate is `q`, so its debt
is exactly `q*kappa`.

## 2. Cancellation algebra

Conditioning on the spare action gives

```text
Delta_i(q)=(1-q)Delta_i^0+q Delta_i^1.
```

`Phi_p` is convex and nonnegative.  Hence endpoint equalities
`Phi_p(Delta^0)=Phi_p(Delta^1)=0` force the free player's debt to vanish on the
whole interval.  For a sure base quitter,

```text
d_b(q)=(-Delta_b(q))_+=(a_b-q lambda_b)_+.
```

Because `Delta_b^0=-a_b<0` and `Delta_b^1>=0`, one has
`lambda_b>=a_b>0` and

```text
tau_b=a_b/lambda_b in (0,1].
```

Thus `q_*=max tau_b` kills both base debts.  The only remaining debt is
`q_* kappa` at the spare.  The budget conclusion and every constant in the
sharp interval formula follow literally.  In particular, for `epsilon>=0`,
base debt at most `epsilon` is equivalent to
`q >= (a_b-epsilon)/lambda_b`, while spare debt at most `epsilon` is
equivalent to `q<=epsilon/kappa` when `kappa>0`.

The symbol `Expl` in equations (6)--(7) should be defined explicitly as the
maximum coordinate debt.  At the selected point it equals total debt only
because every coordinate except the spare is zero.

## 3. Punishment floor and the exact edge

Immediate absorption makes every prescribed payoff coordinate affine:

```text
u_i(q)=(1-q)u_i^0+q u_i^1.
```

The two endpoint floor inequalities therefore imply the whole segment lies
above the coordinatewise punishment floor.

When `kappa=0`, every unrestricted debt coordinate is zero.  Hence the
prefixed behavior profile is an exact terminal Nash profile:

```text
(quittingGame reward).IsεAsymptoticNash
  (quittingTerminalPayoff reward) 0 profile.
```

The root is exact Nash against **any** declared tail, since every unilateral
replacement still leaves a sure quitter.  Its absorption mass is one.  Put
the actual source payoff `u^0` in the tail state, put `u(q_*)` in the current
state, store the mixed product root at the current state and any boxed root
(for example all-Continue) at the tail state.  The endpoint floor inequalities
then define a literal

```text
QuittingPunishmentFloorAdmissibleEdge
```

with relation orientation

```text
u^0  ->  u(q_*),
```

because `src=edge.tail` and `tgt=edge.current` in
`PunishmentFloorAdmissibleChargedRelation.lean`.  Its absorption charge is one.

There is, however, an important consumer distinction.

* A positive admissible edge alone does not invoke
  `quittingGame_exists_uniformPayoff_of_positive_admissible_return`; that
  theorem also requires a returned path from current back to tail.
* Here no returned path is needed: the actual prefixed profile is itself exact
  terminal Nash.  The checked theorem

  ```text
  quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
  ```

  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  directly makes its own terminal payoff a uniform-equilibrium payoff.

Thus, in any game carrying a positive terminal exploitability gap, the
`kappa=0` branch is impossible.  This is stronger and cleaner than treating
the row merely as an unreturned charge-one edge.

## 4. Global-minimum/support-rank arm

Assume precisely that the semantic pair of the actual source attains the
global minimum of total terminal semantic debt over the carrier.  The
constructed profile is actual and the budget gives

```text
D(sigma^{q_*}) <= D(sigma^0)=D_*.
```

Global minimality gives the reverse inequality, so equality holds.  Since
`D_0=a_{b_0}+a_{b_1}>0`, the case `kappa>0` forces `q_*>0` and the new minimum
has exactly one positive-debt coordinate, the spare.  The support cardinality
therefore drops from two to one.  This proof is correct.

This is a genuine well-founded rank decrease, but it does not itself reach a
checked final compiler.  It permits fresh application of

```text
exists_positiveMinimumDebtTangentFamily_of_pair
```

at a rank-one minimum and therefore starts the checked support-rank machinery
one level lower.  The current terminal theorem remains

```text
reducedSupportRankAlternative_of_positiveMinimumDebt
```

from
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean`.
Its remaining positive-slope, support-entry, and paid-row exits still require
their respective chronological consumers.  No declaration inspected says
that a unique positive debtor alone supplies a uniform payoff.

So the exact downstream statement is:

> `kappa=0` closes immediately by exact terminal Nash; `kappa>0` gives a valid
> two-to-one minimum-support descent, but not conjecture closure.

## 5. Required source/profile clarification

The notation `sigma^0` is used twice: first for the supplied actual profile,
and then for the prefix obtained from its first-stage root followed by a fresh
copy of `sigma^0` after all Continue.  These behavior profiles need not be
literally equal on null histories if the original profile is nonstationary.
They do have exactly the same terminal payoff, best-response caps, and debt,
because both base players Quit surely and this remains true under every
unilateral deviation.

Before formal use, define a separate profile, for example

```text
hatSigma(q) = root(q) then sigma^0,
```

and state explicitly

```text
semanticPair(hatSigma(0)) = semanticPair(sigma^0).
```

Then take the actual source as the continuation of `hatSigma(q)`.  This avoids
claiming literal behavior-profile equality on unreachable histories while
preserving the same-profile semantic provenance used by the theorem.

## 6. Producer boundary

The verifier hypotheses are not produced by the current Fin4 or general
positive-minimum machinery.

They require simultaneously:

1. five distinct roles, including a spare label;
2. two base players who Quit surely at the same actual source;
3. endpoint complementarity at both free coordinates;
4. sign reversal/cancellation for both base coordinates under the same spare
   toggle;
5. floor safety at both endpoints; and
6. the scalar budget `q_* kappa<=D_0`.

The two-sure-player premise is exactly what makes arbitrary behavior collapse
to one stage.  A four-player pair-base source has no automatically unused fifth
label, and the existing pair-base/reset adapters do not produce the two free
endpoint equalities or the common scalar budget.  The theorem therefore does
not presently consume the Fin4 hard residual or prove a five-player existence
result.

The strongest valid classification is:

> **sound conditional same-profile verifier; absent producer.**  If the
> hypotheses can be obtained at an actual positive minimum, the theorem either
> closes by exact terminal Nash or strictly decreases positive-debt-support
> cardinality.  Nothing checked presently supplies those hypotheses from an
> arbitrary game.

## Sources inspected

```text
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean
  quittingTerminalSemanticDebt
  quittingTerminalPayoff_update_sub_le_terminalSemanticDebt

UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean
  isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le

UniformEquilibrium/Quitting/Bellman/Finite/
  PunishmentFloorAdmissibleChargedRelation.lean
  QuittingPunishmentFloorAdmissibleEdge
  quittingPunishmentFloorAdmissibleChargedRelation

UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean
  quittingGame_exists_uniformPayoff_of_positive_admissible_return

UniformEquilibrium/Quitting/Terminal/TargetTail/
  TerminalUniformPayoffSelection.lean
  quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact

UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/
  FlatCirculationSupportRankElimination.lean
  reducedSupportRankAlternative_of_positiveMinimumDebt
```
