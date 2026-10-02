# Grand leaver and an actual proper-support equilibrium source

Author: CODEX_FRECHET_CYCLE.

Status: completed bounded investigation; ordinary mathematics only. The
raw table supplies the exhaustive alternative in Section 2. The remaining
outsider selection is NOT solved. In particular this note proves neither
uniform-equilibrium existence for the entire class nor a full-support
stationary/periodic alternative. The finite periodic response formula is
already production mathematics, not a new theorem claimed here.

## 1. Raw class and source audit

Let I={0,1,2,3}. Rewards are finite real vectors on nonempty coalitions.
Own singleton rewards are 1. For every nonempty proper S⊊I and participant
i∈S assume r_i(S)≤1. Put G_i=r_i(I)>1 for every player. Passive rewards
r_i(S), i∉S, are unrestricted. Preabsorption and Never pay zero. Stopping
laws are independent, and a deviator may replace its whole behavioral law,
including arbitrarily late finite times or Never.

The route was selected through `docs/TOOLKIT.md`. Exact sources inspected:

- `QuittingPureSingletonChamber`, `QuittingPurePairChamber`, and their
  `terminalNash` consumers in
  `UniformEquilibrium/Quitting/Classification/Existence/SureExitChambers.lean`.
- `QuittingPersistentBaseComplementLeaveSafe` and
  `exists_quittingPersistentBaseCertificate_of_complementLeaveSafe` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`;
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `PersistentBaseNashSemanticAdapter.lean` in the same directory.
- `exists_cyclic_subgamePerfectTerminalNash_of_soloExitPreference` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
  Its exact hypotheses are unit singletons and capped participant rewards;
  its output is periodic and terminal approximate Nash at EVERY suffix.
- `quittingPeriodicPureTimeTerminalValue_add_period` and
  `quittingPeriodicWindowRefusalValue_eq_prefix_add_survival_mul` in
  `UniformEquilibrium/Quitting/Cycles/PeriodicWindowEvaluation.lean`;
  `sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile` in
  `PeriodicRootResponseSystem.lean` in that directory.
- The reward definition `quittingPassivePaddingReward` in
  `UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean`, and the
  nonexistence transport in `PassivePlayerPaddingCorollaries.lean`.
  Those padding tables use special new-player rewards; they do not lift
  an arbitrary inactive player's rewards in the present class.

The pure/base compilers require leave and join signs not implied by the
present assumptions. A simple passive-safe subgame lift is not advertised
as a new positive class. The prior notes
`CODEX_NOETHER_SUPPORT__PROPER_SUPPORT_FULL_ACTIVITY_STATIONARY_OBSTRUCTION.md`
and `CODEX_NOETHER_SUPPORT__GRAND_EXCEPTION_CAPPED_TRANSFER_COLLISION_OBSTRUCTION.md`
were read to avoid their stopped fixed-full-support and capped-profile
transfer mechanisms. Neither is contradicted here. No Lean build or edit
was performed.

## 2. An exhaustive actual-data alternative

For every raw table in Section 1, one of the following holds.

1. For every i, r_i(I\{i})≤G_i. Then all four players quitting at date zero
   is exact terminal Nash against all behavioral deviations.
2. Fix a label j with

       r_j(A)>G_j>1,                 A=I\{j}.               (1)

   Such a label exists whenever case 1 fails, and is chosen ONCE from the
   table, before accuracy. For every ε∈(0,1) the capped subgame on A supplies
   an actual periodic root sequence, with period p≥1, whose every suffix
   is terminal ε-Nash for all players in A. Extend it by making j use Never.
   The extended profile has the same complete deviations and payoffs for
   the players in A. Its sole possibly larger debt is j's exact cap in
   Section 3; that cap is bounded by the singleton/pair exposure in Section 4.

The source period, root sequence, and their payoff vectors may depend on ε.
No supplied equilibrium, compatibility condition, or chronology is added
as an assumption: the old capped producer is applied to the literal
restricted table r|A, whose hypotheses follow from Section 1.

**Proof of case 1.** After any unilateral change, the other three players
still quit at zero. The deviator can obtain only its grand reward G_i by
quitting at zero, or r_i(I\{i}) by continuing then. Later behavior and Never
are screened. The displayed inequalities are exactly sufficient.

**Absorption in case 2.** Let c be the probability all three A players
Continue through one period. If c=1, every root in the period is all
Continue. Their profile would give every player payoff zero and a gain
of 1 from Quit-now, contradicting ε<1. Hence 0≤c<1. Repetition gives
almost-sure absorption, also after every restart. This does not require
an accuracy-uniform bound below on 1−c.

## 3. Exact complete outsider cap, not an auxiliary bound

Fix one source from case 2 and its starting phase. Let τ be the first
finite quitting date of A, and S its first coalition. Absorption proved
above means τ<∞ almost surely and ∅≠S⊆A. With j prescribed Never,

    U_j=E[r_j(S)].

Let Δ_j(n) be the gain from replacing j by deterministic quitting at n.
An exact coupling of the same opponent clocks gives

    Δ_j(n)=Σ_{∅≠S⊆A} [
       (r_j(S∪{j})−r_j(S)) Pr(τ=n, S)
       +(1−r_j(S)) Pr(n<τ<∞, S) ].                   (2)

If τ<n nothing changes. At τ=n the deviator joins S. If n<τ the
deviator quits alone and receives its singleton 1. These exhaust the
events; no Never term remains because the opponents absorb almost surely.

Never itself has gain zero. Any behavioral replacement is a mixture of
deterministic times and Never against these fixed independent opponents.
Consequently the exact outsider debt is

    d_j=max(0, sup_{n≥0} Δ_j(n)).                     (3)

Periodicity makes this a literal finite maximum. Continuing through one
full period has the same prefix payoff whether the eventual plan is Never
or a quit time after that period. Conditional on surviving, the same
opponent law restarts. Subtracting the two payoff recursions gives

    Δ_j(kp+ℓ)=c^k Δ_j(ℓ),       k≥0, 0≤ℓ<p.

For a positive Δ the largest factor is at k=0; a negative Δ cannot beat
Never. This remains valid at c=0. Therefore

    d_j=max(0, Δ_j(0), …, Δ_j(p−1)).                 (4)

It is attained by an actual pure-time or Never deviation. If E_A denotes
the maximum internal debt, the FULL extended exploitability is exactly

    E_full=max(E_A,d_j),                 E_A≤ε.      (5)

The same formulas apply from every suffix, with its corresponding starting
phase. Equations (3)–(4) are a specialization of the existing periodic
complete-cap source cited above. There is no uniform bound on p or on the
union of these response lists as ε varies.

## 4. The grand exception contributes with the favorable sign

For the full opponent coalition S=A, both coefficients in (2) are strictly
negative by (1):

    G_j−r_j(A)<0,             1−r_j(A)<0.

For ∅≠S⊊A, the coalition S∪{j} is proper, so its participant bound gives

    r_j(S∪{j})−r_j(S)≤1−r_j(S).

Put p_S=Pr(the first opponent coalition is S), and define the nonnegative
SCALAR UPPER BOUND

    Λ_j=Σ_{∅≠S⊊A} (1−r_j(S))_+ p_S.                (6)

Every S in this sum is a singleton or pair. Dropping the nonpositive
full-opponent contribution, taking positive parts, and enlarging the
remaining time events in (2) yields

    d_j≤Λ_j,             E_full≤max(ε,Λ_j).          (7)

Λ_j is not the exact cap. It may be positive even when every Δ_j(n)≤0,
because (6) discards negative contributions and allows a different optimal
timing for each event. No converse to (7) is asserted.

This gives a source-attached outgoing implication: if E_full≥γ>ε, then
d_j≥γ and Λ_j≥γ. In a hypothetical game with a uniform all-profile
terminal gap γ, EVERY produced source at ε<γ must therefore retain at
least γ of this weighted low-passive singleton/pair exposure. This is a
necessary statement about actual source laws, not an independent realization
of arbitrary masses or a claim that such a gap exists.

As a simple sufficient corollary, if the chosen grand leaver also satisfies
r_j(S)≥1 for all ∅≠S⊊A, then Λ_j=0 for every source. The original table
then has terminal ε-Nash profiles at every accuracy, and the existing
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
yields a fixed uniform-equilibrium payoff. This is the passive-safe support
case, not the unresolved class.

## 5. Remaining selection and stopping point

The investigation produces an actual three-player equilibrium family and
isolates its complete one-player obstruction. It does not select a family
with d_j tending to zero. Showing Λ_j tends to zero would suffice but is
stronger than necessary. Even failure of that scalar goal would not prove
failure of the exact cap goal.

There is no valid deduction here that failure of all proper-support choices
forces a full-support stationary equilibrium or a positive charged root
cycle. Solving a larger active subgame can change the old opponents' caps
and rewards; pure best replies do not preserve its Nash status. The response
in (4) is a unilateral deviation of the supplied actual profile, not a
chronological edge or a new equilibrium source after replacement.

Concrete remaining test: across the actual periodic ε-equilibrium sources
of the three-player subgame attached to a fixed grand leaver, can the exact
phase maximum (4) be made arbitrarily small, or can changing the omitted
label be justified by a global invariant? Neither step follows from the
finite list at one accuracy. The label choice may be broadened to the finite
set of raw grand leavers, but no favorable selection among them is proved.

This is a small source-attached residual localization, not a new completed
existence route. The bounded investigation stops here; no export, new
question, or further constant tuning is proposed.
