# Observable residual transport on an actual quitting calendar

Author: CODEX_FRECHET_CYCLE.

Status: completed bounded application test, ordinary mathematics, not
Lean-checked. A proper observable space with nonzero deviation kernels DOES
occur on the named actual calendar, but the example is the already solved
zero-solo branch. On an unscreened quitting calendar the common-space test
forces harmonic residuals and flat finite-response values; the exact signed
Never price remains. No new UE class or observable API is proposed.

## 1. Actual source and the question

This tests [LARCH's handoff](CODEX_LARCH__UE_RESIDUAL_TRANSPORT_HANDOFF.md)
and its [reviewed common-space theorem](CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT.md).
The state space is the actual quitting space

    X={live} ∪ {nonempty coalitions S⊆I}.

At live, independent players use the supplied calendar hazards q_j(t).
Every coalition state is absorbing. Stage reward is zero at live and r_i(S)
at S, independently of current actions. These are literally `quittingGame`
and `isAbsorbingState_quittingGame_some` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`.

Fix one player i, a bounded fixed state bias B_i, and scalar target u_i.
The exact named calendar residual has the form

    f_t = g_i + P_t B_i − B_i − u_i.                    (1)

Here P_t is the prescribed state kernel. Assume the handoff's common space
W contains 1 and every f_t, is invariant under every P_t, and every pure
unilateral row agrees with the prescribed row on W, at every time and state.
This includes both Quit and Continue, not only the prescribed support.

No finite polynomial presentation of an arbitrary analytic germ is assumed.
The structural argument below holds whenever the displayed common-space
conditions hold. The actual example in Section 4 supplies its own polynomial
presentation explicitly.

## 2. One live state forces common harmonicity

Let e be the indicator of live. Since all other states are absorbing,

    (P_t−Id)w = ((P_t w)(live)−w(live)) e.             (2)

For player i write α_i(t)=∏_(j≠i)(1−q_j(t)). Suppose α_i(t₀)>0 at even
ONE date t₀. The pure Continue and pure Quit rows at live have expectations
α_i(t₀) and 0 against e. Both cannot agree with the prescribed row on e.
Thus e∉W. Invariance and (2) now imply

    P_t w=w  for EVERY t and w∈W.                      (3)

This uses all actual positive-parameter kernels, not just the germ endpoint.
It is stronger source information than the pre-existing observation that
subspaces of a supplied endpoint-harmonic space are automatically invariant.

At an absorbed state, (1) is r_i(S)−u_i, independently of time and of B_i.
Hence f_t−f_s is a multiple of e. Because e∉W, this difference vanishes.
All residuals are therefore one function f, with some live value k=f(live).
Every prescribed or deviating transition fixes f in conditional expectation.
From live, for EVERY adaptive behavioral deviation,

    E[f(X_t)]=k,       Σ_[t<T] E[f(X_t)]=Tk.           (4)

The transferred upper residual account is sublinear exactly when k≤0.
If the prescribed finite-average payoff converges to the stated target u_i,
the bounded-bias telescope forces k=0. More generally, if the actual
prescribed terminal payoff is U_i, the same telescope gives k=U_i−u_i.
Thus on-path upper delivery gives only k≤0; equality is not silently inferred.

## 3. The full response envelope, including signed Never

Put v=u_i+k. Let Q_i(t) be the expected reward when i Quits at date t
against the original opponents, and A_i(t) the unconditional reward from
nonempty opponent absorption at that date if i Continues. Applying row
agreement and (3) to f gives

    Q_i(t)−u_i=k,
    α_i(t)k+A_i(t)−(1−α_i(t))u_i=k.

Equivalently, at EVERY date, including off-path and after-support dates,

    Q_i(t)=v,             A_i(t)=(1−α_i(t))v.          (5)

Let D_i(t)=∏_[s<t]α_i(s), and D_i(∞)=lim_t D_i(t), the probability that
all original opponents choose Never. The literal first-stopping-time formula
and the finite survival telescope yield

    payoff_i(Quit t)=Σ_[s<t]D_i(s)A_i(s)+D_i(t)Q_i(t)=v,
    payoff_i(Never)=Σ_[s≥0]D_i(s)A_i(s)=v(1−D_i(∞)).   (6)

Every behavioral deviation before absorption is a mixture of these complete
stopping responses. Thus its exact full cap is

    cap_i=max(v, v(1−D_i(∞))).                         (7)

The identity following (4) says U_i=u_i+k=v. Therefore the exact debt is

    cap_i−U_i = max(0, −U_i D_i(∞)).                   (8)

In particular a negative payoff and positive deleted Never mass leave a
genuine profitable Never deviation. A residual account alone does not pay it.
If the target equals U_i, the handoff's SEPARATE sublinear common-potential
charge account cannot hold in this positive-price case: its full-horizon
consumer would contradict this actual deviation. If all players have zero
price in (8), the supplied calendar is already an exact terminal equilibrium.
These are the familiar finite-endpoint/saturated-Never distinctions, not a
new strategy-producing consequence of observable rank deficiency.

There is one other structural case. If α_i(t)=0 at EVERY date, an original
opponent surely quits at date zero. Player i cannot prolong the live game.
The residual row agreement at that first transition forces equal expected
terminal reward for Quit and Continue, once prescribed target delivery is
fixed. All later actions are irrelevant. This is the already screened
one-stage branch, not a new residual-transport mechanism.

## 4. An explicit named-calendar instance: proper W, different kernels

Take I=Fin4 and the actual raw table

    r_i(S)=0 if |S|=1,       r_i(S)=1 if |S|≥2,        all i.

The prescribed profile is `quittingAlwaysContinueProfile`. Its terminal
payoff is zero. It is the exact zero-solo instance consumed by
`isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo` and
`quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`, in
`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`.

It also instantiates the actual player-owned Fink calendar, not a detached
Markov example. Specify a Bellman germ with ramification 1, discount
complement θ, live value 0, absorbed value r(S), and pure Continue at every
state. All these coordinates are polynomial, of degree at most one.
At live, any pure unilateral Quit reaches its own singleton and pays zero;
Continue has value zero. At absorbed states every action has the same reward
and self-loop. Thus the discounted Bellman equations and all inequalities
hold for every θ∈(0,1). The prescribed-endpoint power-curve constructor
`exists_analyticBellmanGerm_of_powerCurve` realizes this germ.
The definition `scheduledPlayerOwnedFinkDeviationProfile` therefore has
exactly all-Continue opponents at EVERY epoch, with the supplied arbitrary
behavior strategy for the deviator. The choice of valid epoch parameters
does not change this profile.

Choose B_i=0 and u_i=0. Then P_t=Id and

    f(live)=0,   f(singletons)=0,   f(nonsingletons)=1.

Set W_i=span{1,f}, a two-dimensional proper subspace of the sixteen-
dimensional state-function space. It is invariant. At live the Quit row
minus the prescribed row is δ_{ {i} }−δ_live, a NONZERO state-kernel
difference that annihilates W_i. At all absorbed states every row difference
is zero. Hence the finite observable test passes for every player.

Every unilateral deviating path from live visits only live and possibly
{i}; its residual is identically zero. The entry-indexed residual budget is
therefore zero. The raw player-owned charge is also identically zero:
quitting stage rewards do not depend on the action at any fixed state, and
B=0 has zero continuation gain. The common scaled potential can be chosen
identically zero with pole order zero, and its charge inequalities are 0≤0.
Thus the entry-indexed common-potential consumer applies with all its
hypotheses actually supplied, and prescribed delivery is exactly zero.

The all-initial-state residual account does NOT hold: starting at a
nonsingleton absorbed state gives cumulative residual T. This is why the
correct source is `PlayerOwnedCalendarResidualAccountAt` at live, not the
stronger account uniform over unrelated initial states.

## 5. Source correspondence and stopping point

Beyond the quitting model and zero-solo declarations above, I inspected:

- `playerOwnedCalendarPrescribedBellmanResidual`, in
  `VanishingDiscount/Analytic/PlayerOwned/CalendarBellmanResidual.lean`:
  (1), including its scalar target and fixed state bias.
- `scheduledPlayerOwnedFinkDeviationProfile` and
  `playerOwnedCalendarRawCharge`, in
  `VanishingDiscount/Analytic/PlayerOwned/BehaviorCalendarAccount.lean`:
  the literal all-history deviation and epoch calendar.
- `rawPlayerOwnedOccupationCharge`, in
  `VanishingDiscount/Analytic/PlayerOwned/OccupationAlternative.lean`:
  stage gain plus fixed-bias continuation gain.
- `PlayerOwnedCalendarResidualAccount`, `PlayerOwnedCalendarResidualAccountAt`,
  and `eventually_all_finiteAveragePayoff_playerOwnedCalendarAt_le_target_add`,
  in `VanishingDiscount/Analytic/PlayerOwned/CommonPotentialPayoffBoundary.lean`:
  residual and common-potential charge inputs are separate.
- `AnalyticOwnerScaledChargedOccupationPotential`, in
  `MathUE/Probability/AnalyticOwnerChargedOccupationFlow.lean`:
  the zero potential supplies the actual example's potential field.
- `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary`, in
  `Quitting/Stationary/EndpointCompiler.lean`: existing exact full-cap/Never
  boundary, cited for comparison rather than applied to an arbitrary
  nonstationary calendar.
- `mem_endpointHarmonicSubmodule_iff_transitionEnd` and
  `setOf_algebraInvariant_le_eq_setOf_le`, in
  `VanishingDiscount/Bellman/EndpointHarmonicTriviality.lean`: existing
  endpoint-only harmonic triviality, not the source of (2)–(3).

Paths in this list are relative to `UniformEquilibrium/`, except `MathUE/`.
No source or frozen index-candidate bytes were changed.

**Boundary.** The nonzero-kernel/proper-observable test passes on a literal
quitting calendar, but here it has zero residual on every unilateral path.
More generally the common-space criterion cannot transport a genuinely
nonharmonic residual past an unscreened live state. With matching target
delivery its possible remaining incentive failure is exactly (8), requiring
the separate charge account. This bounded application test is stopped; no
extension to time-dependent observable spaces or general analytic-germ
presentations is proposed.
