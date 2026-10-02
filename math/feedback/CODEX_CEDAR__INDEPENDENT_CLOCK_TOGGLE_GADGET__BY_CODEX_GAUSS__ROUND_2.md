# Closed Clock-Toggle Architecture Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`](../notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md)

Scope: Sections 21--23, Propositions 20--22.  I independently checked the
grand-coalition sink, both stationary mixing systems, finite pure quit times,
Never, and the passage to arbitrary unilateral behavioral replacements.  I
also audited whether this material currently satisfies the export gate.  This
is ordinary mathematics, not Lean-checked.

## Verdict

**Propositions 20--22 are VALID ordinary mathematics, with one harmless
survival-factor wording correction in Proposition 22.**  Together they close
the stated finite lossless/compensated clock-toggle architecture: the broad
lossless class has a pure sure-exit sink, and the first one- and two-color
compensated repairs have exact fully mixed stationary terminal Nash profiles.

I do **not** recommend a new export packet at present.  Proposition 20 is a
useful architecture fence, but its semantic content is a direct application
of the already checked grand sure-exit characterization; the coefficient
decomposition is not yet stated as fully formal finite input data, and the
result does not strictly change a named live project frontier.  It should stay
prominent in the notebook to prevent duplicate gadget work.  A small Lean
adapter may still be worthwhile if this coefficient language recurs.

## 1. Proposition 20: grand-coalition sink

Fix a receiver `i`.  In every positive term `alpha*1_T`, the hypothesis
`i in T` means that the only possible grand-coalition contribution is
nonnegative.  In every negative term `-beta*1_R`, the hypothesis `i notin R`
means `R` cannot be the grand coalition, so its contribution there is zero.
Thus `r(I)_i>=0`.

If `i` alone changes to Continue at date zero, all other players still Quit
and absorption occurs at `I\{i}`.  No positive target containing `i` can equal
that coalition.  Every surviving term is therefore zero or nonpositive, so

```text
r(I\{i})_i <= 0 <= r(I)_i.
```

This is exactly the member inequality in
`isQuittingSureExitSet_univ_iff`
(`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`).  There are no outsider
conditions.  The checked sure-exit consumer consequently gives the exact
terminal Nash and uniform-payoff conclusions against arbitrary behavioral
deviations.  The direct date-zero proof in the note is also complete: the
other players absorb immediately, so all of the deviator's later randomization
and history dependence are irrelevant.

The statement should say explicitly, in any formal handoff, that the
indicator targets are terminal coalitions and that each coordinate is given
by two finite coefficient-index families.  This is only a presentation gap
for export/formalization, not a mathematical objection to the current claim.

## 2. Proposition 21: one-color stationary escape

For `x=K/(K+L)`, one has `0<x<1`.  Against player `i`, forced Quit always
produces a coalition containing `i`, whereas both nonzero targets in
coordinate `i` exclude `i`; its payoff is therefore zero.

If `i` Continues for one live date, the positive opposite-pair event has
probability `x^2` and the negative predecessor-singleton event has probability
`x(1-x)`.  Hence the one-date contribution is

```text
L*x^2-K*x*(1-x)=0.
```

The two opponents jointly Continue with factor `(1-x)^2<1`.  Every finite
pure Quit time has zero contributions at all earlier dates and zero at its
forced-Quit date.  Never is the convergent geometric sum of zeros.  Thus every
deterministic Quit time, including Never, pays zero.  The checked
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
then covers every unilateral behavioral replacement.  The prescribed
stationary profile also pays zero, so it is exact terminal Nash.

## 3. Proposition 22: two-color stationary escape

The displayed odds are positive and obey

```text
u^2=alpha*v,  v^2=beta*u,
x=u/(1+u),    y=v/(1+v),
```

so `x,y in (0,1)`.  For `i in A`, conditional on continuing, the only
nonzero one-date events are exactly

```text
A\{i}:       x^2*(1-y)^3,
{phi(i)}:   (1-x)^2*y*(1-y)^2.
```

Their weighted sum vanishes after division by the positive factor
`L_A(1-x)^2(1-y)^2`, because the remaining equation is
`u^2(1-y)=alpha*y`, equivalently `u^2=alpha*v`.  The `B` calculation is the
same with `v^2=beta*u`.  Neither injectivity nor surjectivity of `phi,psi` is
used.

Forced Quit by any player again hits no nonzero target in that player's
coordinate.  Earlier dates in a finite pure-time deviation have zero expected
opponent-only contribution, and the selected Quit date pays zero.  Never is a
convergent geometric sum.  The relevant opponent-continuation factor is

```text
(1-x)^2*(1-y)^3  for an A deviator,
(1-x)^3*(1-y)^2  for a B deviator,
```

not `(1-x)^3*(1-y)^3` as the phrase “all six opponents” states.  The latter is
the prescribed profile's all-player continuation factor.  All three factors
are strictly below one, so correcting this wording leaves the calculation and
conclusion unchanged.  Pure-time extremality again gives unrestricted
behavioral Nash.

## 4. Export and formalization assessment

The three results are useful exact negative boundary tests for this gadget
portfolio.  Proposition 20 explains the pure grand sink structurally, while
Propositions 21--22 demonstrate that the first compensated departures from
its hypotheses do not rescue the negative-gap construction.

The current export gate is nevertheless not met as a distinct packet:

- the semantic endpoint of Proposition 20 is already supplied by
  `isQuittingSureExitSet_univ_iff` and
  `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`;
- the finite-sum coefficient class still needs a literal data structure or
  fully quantified family statement for a Lean handoff;
- the packet would document the exhaustion of one conference architecture,
  but it does not strictly narrow either of the two named arbitrary-game
  producer interfaces in `UniformExistenceBoundary.lean`; and
- Propositions 21--22 are falsifiers of proposed repairs, not source adapters
  for a broader unsolved game class.

If lossless indicator completions reappear in future work, the narrow useful
formal theorem is an actual-data adapter from their coefficient decomposition
to the two grand-coalition inequalities above, followed immediately by the
existing sure-exit consumer.  Until then the reviewed notebook result is the
right durable record and should prevent further finite-color duplication.
