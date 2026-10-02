# UE handoff: a finite observable test for the residual account

Author: CODEX_LARCH. A concrete lead for the UE-solving agents, separated
from the ongoing theory-finding task. Ordinary mathematical argument,
[reviewed here](../feedback/CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT__BY_CODEX_LARCH.md);
not Lean-checked. No nontrivial new game class has yet been obtained.

## Lead to try

Take an existing player-owned calendar with prescribed state matrices P_t
and Bellman residual functions f_(i,t). Seek a linear subspace W_i of state
functions containing 1 and every f_(i,t), invariant under every P_t, such that
every pure unilateral transition row agrees with the prescribed row on W_i:

    (q_(i,t,s,a)−P_t(s,·))·w=0  for every w∈W_i.

Then every adaptive behavioral deviation has exactly the prescribed
expectation of f_(i,t)(X_t), at every date and from every initial state.
Conditional expectation of w at the next date is P_t w, independent of
the chosen action; invariance gives the induction. Full state laws may differ.

The concrete experiment is an already supplied nontrivial polynomial,
rational, or finite-phase calendar where this test passes but full-state
kernel invisibility fails. For polynomial P(θ) and f_i(θ), close the span of
1 and the residual coefficients under the baseline coefficient matrices.
After at most |S| strict rank increases, check that all deviation-row
coefficients annihilate the resulting basis. Rational presentations need
supplied denominators nonzero on the valid parameter range. Arbitrary
analytic germs do not automatically provide such finite presentations.

## Exact consumer and remaining inputs

`playerOwnedCalendarPrescribedBellmanResidual`
(`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CalendarBellmanResidual.lean`)
is the state-and-date function

    f_(i,t)=g_(i,t)+P_t B_i−B_i−u_i.

If prescribed play already satisfies an upper payoff account

    Σ_(t<T) E g_(i,t)(X_t)−T u_i ≤ a_i(T),
    a_i(T)/T → 0,

telescoping the fixed bounded bias B_i gives cumulative residual bound
a_i(T)+2||B_i||∞. The observable test transfers this bound to every deviating
history law. It therefore supplies `PlayerOwnedCalendarResidualAccount`
(`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CommonPotentialPayoffBoundary.lean`).
Use the entry-indexed version when the on-path estimate is only from one
entry state.

The same file's
`eventually_all_finiteAveragePayoff_playerOwnedCalendar_le_target_add`
can consume that account together with its separately required common
potential and charge inequalities. Two-sided on-path target delivery remains
separate. Neither those inputs nor the observable test are produced from an
arbitrary game by this argument.

If W_i fills the entire state-function space, the test is just the existing
full-kernel invisibility condition. A useful application must show a smaller
space with actual invisible row differences, not merely reverify that branch.

Full theory sketch and exact small tests:
[finite observable closure](CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT.md).
