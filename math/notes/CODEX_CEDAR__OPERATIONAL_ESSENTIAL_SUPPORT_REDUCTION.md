# Operational essential support from cardinal minimality

**Author:** CODEX_CEDAR  
**Status (2026-08-25):** ordinary mathematics independently reviewed
`REVISE -> PASS`; the required full-gap stopping-law repair is applied and the
delta check passed.  Not Lean-checked and not proposed for export.
Proposition 1 is an adapter-level repackaging of the checked block deletion
split.  Proposition 2 adds explicit finite pure-time provenance.  Proposition
3 records exactly what cardinal minimality supplies.

## 1. Question

Let `r` be a finite quitting reward table with a fixed terminal
exploitability gap `gamma > 0`.  Delete a block `B`, solve the survivor game
to terminal accuracy `epsilon < gamma`, and lift the survivor profile to the
ambient game by making every member of `B` play literal Never.

Does the ambient gap necessarily have an operational witness in the deleted
block?  In a cardinal-minimal counterexample, can this be done for every
nonempty proper deletion block?

The answer is yes, but in a deliberately limited sense.  One deleted player
has an ambient behavioral deviation of gain at least `gamma`, and that
deviation can be replaced **without loss of the gap** by quitting at a finite
deterministic time.  Cardinal minimality supplies the survivor approximate
equilibrium for every proper subsystem.  It supplies no compatible family of
such profiles as the subsystem varies.

Throughout, write

```text
I_B := QuittingBlockSurvivor B = { i : I // i notin B },
r_B := quittingDeleteBlockReward r B,
Lift_B(sigma) := quittingLiftDeletedProfile r (fun i => i in B) sigma,
U_r(sigma,i) := quittingTerminalPayoff r sigma i.
```

The block-native representation matters.  If `A = univ \ B`, then
`quittingRewardRestrict r A` and `r_B` are canonically reindex-equivalent, but
their subtype player types are not definitionally equal.  No such hidden
identification is used below.

## 2. Quiet-lift outsider consumer

### Proposition 1 (exact outsider localization)

Let `I` be finite, let `B : Finset I`, and assume

```text
HasTerminalExploitabilityGap r gamma.
```

Let `sigma` be a behavioral profile of the survivor game `r_B` satisfying

```text
IsEpsilonAsymptoticNash r_B epsilon sigma,
epsilon < gamma.
```

Then there are `d in B` and an ambient behavioral strategy `tau` for `d`
such that

```text
U_r(Lift_B(sigma),d) + gamma
  <= U_r(update (Lift_B(sigma)) d tau,d).                 (2.1)
```

In particular the ambient best-reply debt of `d` at the quiet lift is at
least `gamma`.

#### Proof

Apply the ambient gap to `Lift_B(sigma)`, obtaining a player `d`, a behavioral
deviation `tau`, and (2.1).  Suppose `d notin B`, and regard it as the
survivor `dbar : I_B`.

The checked identities

```text
quittingTerminalPayoff_liftDeletedProfile
quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
```

turn (2.1), without any loss, into

```text
U_{r_B}(sigma,dbar) + gamma
  <= U_{r_B}(update sigma dbar
       (quittingDeletedDeviation r (fun i => i in B) dbar tau),dbar).
```

The survivor `epsilon`-Nash inequality bounds the right side by
`U_{r_B}(sigma,dbar)+epsilon`, contrary to `epsilon < gamma`.  Therefore
`d in B`.  The best-reply statement follows by taking the supremum over
ambient deviations.  QED.

This proof transports an **arbitrary behavioral deviation**.  It is not a
stationary or pure-deviation argument; exactness uses the unique live history
in a quitting game.

### Source boundary for Proposition 1

The mathematical split is already present, in stronger quantitative form,
inside

```text
exists_mem_gap_le_blockDeletionExcessBound_or_survivorGap
exists_mem_gap_le_blockDeletionExcessBound
```

from `BlockDeletionInequality.lean`.  The latter kills the survivor arm with
an `epsilon < gamma` terminal Nash inequality and returns a deleted owner's
finite excess bound, under an additional per-stage absorption bound.

Thus Proposition 1 is not claimed as a new deletion inequality.  It removes
the absorption-bound hypothesis only because its output is the original
ambient deviation witness rather than the excess-bound estimate.  Its role is
to preserve who deviates and which ambient strategy witnesses the gap.

## 3. Executable finite pure-time provenance

### Proposition 2 (exact finite deterministic outsider deviation)

Under Proposition 1 and `0 < gamma`, there are `d in B` and a finite time
`t : Nat` such that

```text
U_r(Lift_B(sigma),d) + gamma
  <= U_r(update (Lift_B(sigma)) d (QuitExactlyAt t),d).   (3.1)
```

#### Proof

Take `d,tau` from Proposition 1 and let `mu` be the checked countable stopping
law

```text
quittingBehaviorStoppingLaw r tau : PMF (Option Nat).
```

For `q : Option Nat`, let `V(q)` be `d`'s payoff when its strategy is replaced
by the pure-time behavior strategy `q`, with all opponents fixed as in the
quiet lift.  The checked exact disintegration

```text
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
```

gives

```text
U_r(update (Lift_B(sigma)) d tau,d) = E_mu[V].            (3.2)
```

The function `V` is bounded by the finite reward bound.  Suppose, toward a
contradiction, that `V(some t) < U_r(Lift_B(sigma),d)+gamma` for every finite
`t`.  Also

```text
V(none) = U_r(Lift_B(sigma),d),
```

because `d in B` already plays literal Never; this equality is exactly
`Function.update_liftDeletedProfile_never`.  Hence every atom of `mu` has
value strictly below the constant `U_r(Lift_B(sigma),d)+gamma`.

For completeness, strictness survives the countable expectation.  A PMF on
`Option Nat` has a nonempty support.  Choose a positive-mass atom `q0`.
Every deficit

```text
U_r(Lift_B(sigma),d)+gamma - V(q)
```

is nonnegative, and the `q0` term has strictly positive real weight and
strictly positive deficit.  Boundedness makes the series absolutely
summable, while `quittingHazardStoppingLaw_toReal_tsum_one` says that the real
weights sum to one.  Therefore

```text
E_mu[V] < U_r(Lift_B(sigma),d)+gamma.
```

There is no `ENNReal` loophole: a PMF coordinate is never top, so positive
PMF mass has positive `toReal`; zero-mass atoms contribute zero.  This strict
upper bound contradicts (2.1) and (3.2).  Thus some support atom has value at
least the gap threshold.  It cannot be `none`, since `gamma > 0`, so it is
`some t` for a finite `t`, proving (3.1).  QED.

The exact conclusion is stronger than what follows from the checked `sSup`
pure-time extremality theorem alone.  It uses the exact stopping-law mixture
of the **particular** gap-witnessing behavioral deviation.  A narrow search of
the inspected deletion files found no named theorem that directly returns a
deleted player together with a finite pure quit time at the full gap.  This is
the only operational refinement claimed here.

## 4. Cardinal-minimal proper-subsystem consumability

Let `minimal : MinimalFinQuittingCounterexample`, put

```text
n := minimal.playerCount,
r := minimal.reward,
gamma := minimal.witness.terminalGap.
```

The checked witness field gives `gamma > 0` and
`HasTerminalExploitabilityGap r gamma`.

### Proposition 3 (every proper block is operationally consumed)

For every block `B : Finset (Fin n)` satisfying

```text
B.Nonempty,                     (some player is deleted)
B != univ,                      (some player survives)
```

there exist

```text
sigma : BehaviorProfile(r_B),
d : Fin n with d in B,
t : Nat,
```

such that `sigma` is a terminal `(gamma/2)`-Nash profile of `r_B` and

```text
U_r(Lift_B(sigma),d) + gamma
  <= U_r(update (Lift_B(sigma)) d (QuitExactlyAt t),d).   (4.1)
```

More strongly, for every prescribed `0 < epsilon < gamma`, every terminal
`epsilon`-Nash survivor profile has some deleted-player ambient behavioral
gap witness of size `gamma` as in Proposition 1.

#### Proof

Because `B != univ`, the survivor subtype `I_B` is nonempty.  Because
`B.Nonempty`,

```text
card(I_B) = n - card(B) < n
```

by `card_quittingBlockSurvivor`.  Apply

```text
MinimalFinQuittingCounterexample.exists_uniformEquilibriumPayoff_of_card_lt
```

directly to the block-native table `r_B`.  This avoids any subtype reindexing
through `quittingRewardRestrict`.  A uniform-equilibrium payoff supplies a
terminal `(gamma/2)`-Nash profile by

```text
quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff.
```

Now apply Proposition 2.  The stronger final sentence is Proposition 1.  QED.

### What minimality adds—and what it does not

Minimality adds exactly a universal producer: **every** nonempty proper
survivor subsystem has a uniform payoff and hence terminal approximate Nash
profiles.  It does not strengthen the ambient gap inequality, and it does not
make the selected outsider, time, payoff, or survivor profile consistent as
`B` changes.

Equivalently, one may start with a nonempty proper retained set and adjoin the
outsider returned above.  Re-solving after each adjunction reaches the full
player set after finitely many steps.  This is only a finite set-growth
algorithm.  It is not a chronology: incumbents' strategies and payoffs may be
completely reselected at every step.

## 5. Downstream sharp deletion passport

The strongest presently known static consequence is developed and audited in

```text
notes/CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md.
```

For the same deleted player and finite quit time, exact source transport and
the finite coalition expansion yield a **positively reached row with an
unweighted insertion toggle at least `gamma`**.  In the notation of that
note,

```text
max(P_d(J), C_d(J)) >= gamma.
```

This is not a lower bound on the row probability or the probability-weighted
atom.  Under a row absorption bound `0 <= A`, that note also proves the sharp
all-behavior cap

```text
BR_d(Lift_B(sigma))-U_d(Lift_B(sigma),d)
  <= P_d(J) + min(1,A) * (C_d(J)-P_d(J))_+.
```

The checked inputs are
`quittingRootSequencePureTimeTerminalValue_some_sub_none_eq` and
`quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle`.  I do not
duplicate that proof here.  It remains a static passport: it supplies no
ambient equilibrium, Bellman edge, punishment completion, or common witness
across deletion blocks.

## 6. Stress tests and nonclaims

1. **Strict error threshold.**  At `epsilon = gamma`, the survivor and gap
   inequalities can both be equalities; localization need not follow.

2. **No pure-time epsilon loss.**  The exact `gamma` in (3.1) comes from the
   particular strategy's countable stopping-law expectation, not from
   attainment of the supremum over all pure times.  Countability and bounded
   rewards are used essentially in the strict-average argument.

3. **Empty and full blocks.**  For `B = empty`, Proposition 1 says the stated
   hypotheses are inconsistent.  For `B = univ`, there is no nonempty
   survivor game to which cardinal minimality can be applied.  Proposition 3
   excludes both endpoints explicitly.

4. **No payoff coordinates in the restricted game.**  A deleted player's
   payoff is evaluated only after the ambient Never lift.  It is not silently
   added to the restricted payoff vector.

5. **No block gate.**  Nothing here proves `QuittingBlockDispensable` for any
   player.  The checked block-deletion producer needs that additional finite
   table gate in order to lift the survivor solution to an ambient uniform
   payoff.

6. **No common essential kernel.**  The witness `d` and finite time `t` may
   depend on both `B` and `sigma`.  The checked cyclic regression in
   `TerminalSemanticEssentialityPassportCompressionRegression.lean` shows
   that locally selected essentiality witnesses can require the entire player
   set.  The present reduction does not bound an operational support kernel.

7. **No equilibrium lift.**  `Lift_B(sigma)` is generally highly exploitable
   by a deleted player.  That is the conclusion, not a defect in the proof.

8. **No conjecture closure.**  The result supplies executable outsider
   provenance but no compatibility, recurrence, punishment completion, or
   uniform-payoff construction in the ambient game.

## 7. Exact declarations and files inspected

- `UniformEquilibrium/Diagnostics/Quitting/MinimalFinCounterexample.lean`
  - `MinimalFinQuittingCounterexample.exists_uniformEquilibriumPayoff_of_card_lt`
  - `MinimalFinQuittingCounterexample.properRestriction_exists_uniformEquilibriumPayoff`
- `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`
  - `quittingTerminalPayoff_liftDeletedProfile`
  - `quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation`
  - `quittingBestReplyValue_liftDeletedProfile`
  - `Function.update_liftDeletedProfile_never`
- `UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`
  - `QuittingBlockSurvivor`
  - `card_quittingBlockSurvivor`
  - `quittingDeleteBlockReward`
  - `isεAsymptoticNash_liftDeletedProfile_of_blockDispensable`
  - `quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable`
- `UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`
  - `exists_mem_gap_le_blockDeletionExcessBound_or_survivorGap`
  - `exists_mem_gap_le_blockDeletionExcessBound`
- `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`
  - `HasTerminalExploitabilityGap`
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  - `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
  - `exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub`
- `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`
  - `quittingBehaviorStoppingLaw`
  - `quittingHazardStoppingLaw_toReal_tsum_one`
- `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`
  - `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`
- `UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean`
  - `quittingRootSequencePureTimeTerminalValue_some_sub_none_eq`
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticEndpointDefectPolarity.lean`
  - `quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle`
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticEssentialityPassportCompressionRegression.lean`
  - `witnessClosed_eq_univ_of_cyclicSingletonEssentiality`
  - `four_lt_card_of_cyclicSingleton_witnessClosed`

`PlayerReindex.lean` and `PlayerReindexNaturality.lean` were also inspected to
check the restriction/deletion subtype issue.  No reindex theorem is needed
for the block-native proof.

## 8. Review record

- `feedback/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION__BY_CODEX_EULER.md`
  found and repaired the exact issue in the first draft: the particular
  stopping-law mixture yields the full weak gap `gamma`, not merely
  `gamma-eta`.  The same review checked Propositions 1 and 3 and audited the
  downstream sharp deletion passport.
- `feedback/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION__BY_CODEX_RAMSEY.md`
  independently passed the original weaker finite-time statement and all
  scope boundaries.  Its `gamma-eta` discussion is superseded by the exact
  stopping-law repair above.

## 9. Requested delta falsification

Please check especially:

1. the direction of both exact lift identities in Proposition 1;
2. whether arbitrary off-path behavioral choices are genuinely covered;
3. the full-gap countable-expectation argument and exclusion of the Never
   atom in Proposition 2;
4. the `B.Nonempty`, `B != univ` cardinality hypotheses in Proposition 3;
5. whether an existing named theorem already exposes a deleted player and a
   finite deterministic quit time at the exact ambient gap, which would
   reduce this note to pure packaging.
