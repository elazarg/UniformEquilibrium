# Delta review of the residual-transport handoff

Reviewer: CODEX_NOETHER_SUPPORT.

Source: [the handoff](../notes/CODEX_LARCH__UE_RESIDUAL_TRANSPORT_HANDOFF.md),
SHA256 `83ac746f7d4e22c3099f75e759b85622b216dae70bbd55dfdfac50d92ab08302`.

Verdict: sound bounded handoff, with the literal quantifier clarifications
below. No new mathematical result beyond the already reviewed observable-
closure theorem is added. It proposes a concrete supplied-calendar test,
not an arbitrary-game UE producer. No urgent mathematical objection, Lean
build, implementation, or export recommendation arises from this review.

## Exact consumer and sign check

I read both named Lean files through EOF:

- `UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CalendarBellmanResidual.lean`;
- `UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CommonPotentialPayoffBoundary.lean`.

The definition `playerOwnedCalendarPrescribedBellmanResidual` is literally
the state-and-date function f_(i,t)=g_(i,t)+P_t B_i−B_i−u_i. Its expected
sum under PRESCRIBED play has the sign

    Σ E f_(i,t)(X_t)
      =Σ E g_(i,t)(X_t)−T u_i+E B_i(X_T)−B_i(X_0).

Thus a prescribed upper account a_i(T) gives the residual upper budget
a_i(T)+2||B_i||∞. Sublinearity survives this constant addition. Transport
of the SAME residual expectations to deviating history laws supplies the
required account. It does not claim that the deviator's actual stage
rewards themselves have unchanged expectations; their difference is
handled by the separately supplied charge account.

`PlayerOwnedCalendarResidualAccount` quantifies over every player,
behavioral deviation, initial state, and horizon. Its budget depends only
on player and horizon. Consequently the displayed on-path bound must be
uniform over initial states for that structure. Bounds supplied separately
at every state can be replaced by their finite maximum. A bound at just
one entry gives `PlayerOwnedCalendarResidualAccountAt`, as the handoff
correctly says. Neither structure requires a nonnegative budget.

The exact theorem
`eventually_all_finiteAveragePayoff_playerOwnedCalendar_le_target_add`
additionally requires the common analytic owner-scaled potential and the
pointwise upper charge-versus-transition-drift inequalities on the same
valid calendar. It returns one eventual horizon threshold uniform over
players, initial states, and all behavioral deviations. The corresponding
entry theorem is
`eventually_all_finiteAveragePayoff_playerOwnedCalendarAt_le_target_add`.
The handoff does not supply these independent hypotheses or two-sided
on-path target delivery. Its claim of filling only the residual field is
therefore literal.

## Observable test and the proposed experiment

The induction is valid for adaptive deviations: conditional on ANY
history, action-row agreement on W_i makes the next expectation of w
equal to P_t w at the current state. Invariance keeps that function in
W_i, so equal W_i-moments propagate from the same initial state. This
does not equate full state distributions or same-labelled operational
laws, nor justify changing the prescribed calendar by retiming.

For a finite implementation, supply finite coefficient presentations of
the DEVIATION rows as well as the baseline matrices and residuals, or a
finite generating list of row differences. Polynomial P and f alone do
not imply a finite coefficient description of every deviation row. The
named game interface already has finite action spaces. Rational clearing
also needs denominators nonzero on the whole valid parameter range. These
are input requirements for the finite test, not consequences of analytic
germ existence. Under them, closing the span under baseline coefficient
matrices and testing row annihilation is a valid sufficient algorithm;
at most |S| strict rank increases are possible.

The useful experiment is precisely to take one ALREADY SUPPLIED player-
owned calendar and exhibit dim W_i<|S|, a nonzero controlled row difference
annihilating W_i, and the required prescribed account. This would distinguish
observable transport from full-kernel invisibility at that actual calendar.
The handoff does not provide such new data; merely recomputing W_i equal
to the entire function space would add no branch coverage.

## Delta against the previous review

I read the earlier
[FRECHET assessment](CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT__BY_CODEX_FRECHET_CYCLE.md)
and the linked
[LARCH assessment](CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT__BY_CODEX_LARCH.md).
They already check this induction, polynomial closure, exact telescope,
entry distinction, and missing common-potential/target hypotheses. The
63-line handoff consolidates those findings into a practical test and does
not strengthen the theorem or repair a new gap in the consumer. No repeat
of the broader theory audit is needed. The current bounded review ends
here; no new experiment or research line was started.
