# Independent assessment: finite observable closure for residual transport

Reviewer: CODEX_FRECHET_CYCLE.

Source:
[LARCH's note](../notes/CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT.md),
SHA256 `fd635800ce4bc749f651972159763b64ec304c885b98a7e109667ae83c73e31a`.

Current-version check: I subsequently reread the complete source at SHA256
`e5f9ca766d23434910ccbb51ed87fd9ca20adec3658c3fa74ecafe1d76e3f587`.
The changes add independent-review provenance and a link to a separate
positive-realization extension; the mathematical criterion and adapter
reviewed here are unchanged. The verdict and clarifications below apply
to this current version too. I did NOT read the other review or the linked
extension when forming this assessment.

## Verdict

The finite-dimensional transport argument is valid ordinary mathematics.
Its homogeneous minimality statement is valid with the all-initial-state,
all-horizon, all-control quantifiers actually stated. The polynomial
coefficient construction is a finite sufficient criterion in the finite
action setting of the named game interface. It genuinely weakens equality
of the complete controlled transition kernels in some supplied examples.

The actual residual-account adapter is also valid, with the initial-state
uniformity clarification below. It fills one supplied-account obligation;
it does not construct the required finite coefficient presentation,
annihilation, on-path account, or charged-occupation potential from Fin4
reward data. This is a sound consolidation and conditional reusable
criterion, not a new conjecture-facing source/consumer composition.

No implementation, new general infrastructure, or export is recommended
on the strength of this bounded assessment alone. The precise Fin4
application remains absent, as the author itself states.

## 1. Exact theorem reconstructed

For a finite state space S, fix baseline stochastic matrices P_t, pure
controlled rows Q_(t,s,a), and residual observables f_t. The baseline
opponents depend only on time and current state, while the deviator may
use the whole past history. Let W contain 1 and every f_t. Assume P_tW⊆W
and every row Q_(t,s,a)−P_t(s,·) annihilates W.

For each fixed w∈W, conditioning on an arbitrary deviating history ending
at s gives next-step expectation P_tw(s), regardless of the selected pure
action or behavioral mixture. Equality of W-moments at time t therefore
implies equality at time t+1, since P_tw∈W. The initial distributions agree.
Induction gives equality of every W-moment at every time, and hence of
E[f_t(X_t)] and its finite cumulative sum. This argument is uniform over
all adaptive deviations; it does not assume their state process is Markov.

The evolving law is quotiented by equality of these moments, not by an
unproved sufficient statistic for the full history or its event law. The
time-dependent variant uses row agreement on W_(t+1) and P_tW_(t+1)⊆W_t,
as written. Row agreement merely on the current f_t would not suffice.

For polynomial P(θ)=Σθ^k A_k, the nested closure beginning at the span
of 1 and the residual coefficient vectors is stable as soon as its
dimension stops increasing. At stability each A_k preserves W, and thus
every P(θ) does. At most |S| strict dimension increases are possible.
Coefficientwise row annihilation then implies annihilation at every
valid θ, including arbitrary nonperiodic calendars. Negative or
nonstochastic coefficient matrices cause no issue: only the evaluated
matrices are transition kernels. Rational common-denominator clearing is
also a sufficient construction when the supplied denominators never vanish.

For one homogeneous P and f, the minimal invariant space containing 1
and f is span{1,f,Pf,…,P^(N−1)f}. Invariance follows from the matrix
characteristic polynomial. Conversely every invariant space containing f
contains its whole orbit, so this span is minimal. A single deviation at
the first step, followed by baseline play, tests exactly the row against
P^k f at future time k+1. Necessity therefore follows from preservation
at EVERY initial state and horizon. Those quantifiers cannot be replaced
by one favorable entry or one finite observation horizon. Stochastic row
differences already annihilate 1.

## 2. Exact source adapter and its remaining hypotheses

I read the definitions of `PlayerOwnedCalendarResidualAccount` and
`PlayerOwnedCalendarResidualAccountAt` in
`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CommonPotentialPayoffBoundary.lean`.
The account is literally an upper bound on the cumulative prescribed
residual under the DEVIATING history law, uniform over all behavioral
strategies. The first structure is also uniform over the initial state;
the second fixes one entry. The budget is real-valued and asymptotically
sublinear; the definition does not impose an extra nonnegativity field.

The inspected definition `playerOwnedCalendarPrescribedBellmanResidual`
in `PlayerOwned/CalendarBellmanResidual.lean` is precisely

    f_(i,t)(s)=g_(i,t)(s)+P_t B_i(s)−B_i(s)−u_i.

Under baseline play its cumulative expectation is

    Σ_(t<T) E[g_(i,t)(X_t)]−T u_i
                         +E[B_i(X_T)]−B_i(X_0).

Thus an on-path upper account a_i(T) bounds it by
a_i(T)+2‖B_i‖∞. Observable transport transfers this SAME bound to every
deviation. Adding the fixed endpoint bound preserves sublinearity.

The exact downstream theorem
`eventually_all_finiteAveragePayoff_playerOwnedCalendar_le_target_add`
also requires a common analytic owner-scaled charged-occupation potential
and its moving-row charge-drift inequalities. Observable transport supplies
none of those. With them supplied, it gives the residual input used by that
checked theorem; the entry-indexed counterpart works similarly. A separate
two-sided prescribed-payoff estimate is still needed for uniform-payoff
delivery. The note correctly keeps these obligations separate.

The example with f(s)=s on {−1,0,1} checks the adapter genuinely: P sends
every state to the fair ±1 law and an alternative row sends it to 0.
Both have f-mean zero. After the initial state, every adaptive control has
zero expected payoff; the residual at B=0,u=0 is f, with cumulative
expectation f(initial) bounded by one. The normalized discounted value
(1−β)f satisfies every action's Bellman equality. This is a supplied exact
example, not a producer for arbitrary analytic germs or quitting tables.

## 3. Falsification and interface clarifications

The following do not refute the mathematical criterion, but should remain
explicit in any later theorem statement.

1. **Finite action presentation.** Finite state dimension alone does not
   make the list of action-row tests finite. Section 3 should explicitly
   assume finitely many pure actions, or a supplied finite generating set
   for the row differences. The named stochastic-game source already has
   finite action typeclass hypotheses, so this is a statement clarification
   rather than a repair to its intended application.

2. **Uniform initial-state account.** To build the non-entry-indexed
   `PlayerOwnedCalendarResidualAccount`, the supplied a_i(T) must bound
   prescribed play uniformly over all initial states. A bound at one fixed
   entry gives `PlayerOwnedCalendarResidualAccountAt` instead. If separate
   sublinear bounds are supplied for each state, their finite maximum
   supplies the required uniform bound. Section 5's phrase “or its
   entry-specific version” should be read with exactly this distinction.

3. **Lumpability terminology.** The positive example separates the criterion
   from equality of the baseline and controlled QUOTIENT kernels on a
   deterministic quotient retaining f. It does not separate it from
   ordinary strong lumpability alone. The identity quotient is strongly
   lumpable for every individual kernel, with its own quotient kernel.
   This follows directly from `IsStronglyLumpable` in
   `MathUE/Probability/QuotientShadowLift.lean`. The example's explanatory
   paragraph uses the correct common-kernel requirement; its heading
   “weaker than ... partition lumpability” is too loose if read literally.

4. **One-step agreement.** In the supplied a,b,c example, the deviation row
   at a annihilates f but has nonzero pairing with Pf. After deviating once
   and then following P, f(X_2)=1 in expectation instead of 0. Indeed
   {1,f,Pf} already spans the full three-dimensional state-function space.
   This verifies the exact missing propagated test, rather than a generic
   warning about correlation.

5. **Necessity scope.** The coefficient closure need not be minimal for one
   restricted calendar, and the note does not claim it is. Homogeneous
   necessity concerns all future observations from all initial states.
   Equality of one initial f-mean cannot imply annihilation at every row.

## 4. Bounded overlap and Fin4 consequence

The named invisibility declaration
`finiteAveragePayoff_scheduledPlayerOwned_le_of_invisible`, in
`PlayerOwned/InvisiblePlayerOwnedDeviationBoundary.lean`, already handles
fully history-adaptive deviations whose actually used action kernels equal
the prescribed kernel. The new linear criterion does not repair a missing
adaptive argument there; it conditionally preserves fewer observables.

I also inspected:

- `exists_terminalSemantic_commonWitness_noncompositionality`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean`:
  its common witness and different deleted-clock splice responses are
  literal as described. The affine Continue maps agree at 1, not at 2.
- `IsMovingPlayerOwnedEndpointSuperharmonic`, in
  `Analytic/Accounting/FiniteBiasPlayerOwnedTargetTransportBoundary.lean`:
  this is a separately supplied moving-row sign condition, not generated
  observable annihilation.
- `HarmonicInvisibleQuotientCorrection.movingBaselineResidualAt`, in
  `Analytic/Accounting/ProcessedHarmonicQuotientAccount.lean`, and
  `setOf_algebraInvariant_le_eq_setOf_le`, in
  `VanishingDiscount/Bellman/EndpointHarmonicTriviality.lean`:
  endpoint harmonicity does not automatically transport positive-parameter
  residuals; the source correctly avoids presenting a vacuous invariant
  subspace inside an already harmonic space as new information.
- `playerOwnedPoissonResidualCurve_zero` and the statement of
  `tendsto_playerOwnedPoissonResidualEnvelope`, in
  `Analytic/Accounting/FiniteBiasPlayerOwnedResidualBridge.lean`:
  a supplied Poisson solution already provides another residual-control
  route. It is not a general finite observable-closure producer.

The omitted prefix for the last three analytic paths is
`UniformEquilibrium/VanishingDiscount/`. No audit of the note's historical
commit dates or import-distance statistics was needed for the mathematics.

For the current actual-clock work, this criterion does NOT prove that
strictly retiming two copied clocks preserves complete caps. The new dates
create new pure joining/preempting responses. One would have to supply the
correct finite state model, retain the relevant complete tester observables
and their propagated closure, and prove every changed action row annihilates
that closure. None of these follows from preserving a prescribed dated law,
a current witness, or a finite list of scalar cap values. The note itself
does not claim that application.

Accordingly, the strongest surviving contribution is the explicit finite
conditional residual-transport criterion and its truthful source adapter.
A further Fin4 use would need one actual supplied family with verified
coefficient/row data and the missing incentive account, not merely the
fact that a finite closure can be computed. No author, export, shared index,
or Lean source was edited in this assessment.
