/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodicWindowEvaluation
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanCapPureTimeStop
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import UniformEquilibrium.Quitting.Cycles.PeriodicPureTimeBellman
import UniformEquilibrium.Quitting.Terminal.TargetTail.FiniteChainTerminalCompiler
import UniformEquilibrium.Quitting.Cycles.CompanionTransport
import MathUE.DirectedTransport.MaxAffine.Scalar

/-!
# The max-linear response system of a periodic root cycle

Fix a period `K` and a cycle `cycle : Fin K → ι → PMF Bool` of one-stage
Boolean product rows.  The behavior profile
`quittingCyclicBehaviorProfile reward cycle phase` replays those rows forever.
Any number of players may randomize at a stage, so the rows range over the
whole periodic product class, not only over rows with a single mover.

A *response solution* is a phase-indexed family `W` satisfying, at every phase
and player,

`W k i = max (quit branch at phase k) (continue branch at phase k using W (k+1))`,

where the quit branch is `quittingRootQuitPayoff` — the value of quitting at
this stage, averaged over the co-quitters that the other players realize at
the *same* stage — and the continue branch is `quittingRootContinuePayoff`.
The quit branch is the player's own solo row only when no opponent moves at
that phase.

The results below identify a response solution with the repository's Bellman
cap along the periodic live path, and cap every deviation by it:

* every deterministic stopping date inside one pass is capped
  (`quittingPeriodicWindowPhaseStopValue_le_of_isQuittingCyclicResponseSolution`);
* never quitting is capped as soon as the solution coordinate is nonnegative on
  the branch where the deviator's opponents never absorb over one turn
  (`quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution_of_nonneg`),
  that branch running through the refusal identity
  `quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted`;
* the table-level admissibility disjunction supplies that nonnegativity
  (`quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution_of_admissible`);
* hence the exact finite best-response statistic is capped
  (`quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution_of_nonneg`),
  and by `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` that
  statistic already dominates every behavior deviation.

## Main definitions

* `quittingCyclicResponseCap` — the exact finite best-response statistic
* `IsQuittingCyclicResponseSolution` — the max-linear response system

## Main results

* `quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted` — the
  refusal identity
* `quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution_of_nonneg`
* `sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile` — the cap is
  the supremum over all behavior deviations
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℕ}
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## One-stage endpoints of a single row -/

/-- The repository's one-stage companion map is the maximum of the two
endpoints of the row. -/
theorem quittingRootCompanionMap_eq_max_endpoints
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCompanionMap reward root who (tail who) =
      max (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who) := by
  rw [quittingRootCompanionMap, quittingRootQuitPayoff_eq_deletedQuitValue,
    quittingRootContinuePayoff_eq_deleted]

/-! ## The periodic profile and its on-path value -/

omit [DecidableEq ι] in
/-- The periodic profile's live roots repeat with its period. -/
theorem quittingProfileLiveRoot_cyclicBehaviorProfile_add_period
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingCyclicBehaviorProfile reward cycle phase) (time + K) =
      quittingProfileLiveRoot reward
        (quittingCyclicBehaviorProfile reward cycle phase) time := by
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile,
    quittingCyclicRootSequence_add_period]

/-- Opponent survival of `who` over one full turn of the cycle. -/
theorem quittingOpponentSurvivalWeight_cyclic_period
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingOpponentSurvivalWeight (quittingCyclicRootSequence cycle phase) who 0 K =
      ∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who := by
  rw [quittingOpponentSurvivalWeight_cyclicRootSequence, quittingCyclicOrbit_zero,
    quittingCyclicPrefixWeight_card]

/-! ## The response system -/

/-- The exact finite best-response statistic of the periodic profile of
`cycle` started at `phase`: the better of never quitting and of quitting at one
of the finitely many phases of the first pass. -/
def quittingCyclicResponseCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) [NeZero K] (phase : Fin K) (who : ι) : ℝ :=
  quittingPeriodicWindowBestResponseValue reward
    (quittingCyclicRootSequence cycle phase) who K

/-- **The response cap is the supremum over all behavior deviations.**  The
supremum of the deviator's payoff over its whole behavior strategy space is
attained on the countable family of deterministic stopping dates, and equals
the finite periodic statistic. -/
theorem sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) [NeZero K] (phase : Fin K) (who : ι) :
    sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who ↦
        quittingTerminalPayoff reward
          (Function.update (quittingCyclicBehaviorProfile reward cycle phase) who
            deviation) who) =
      quittingCyclicResponseCap reward cycle phase who := by
  rw [sSup_range_quittingTerminalPayoff_update_eq_periodicWindow reward
    (quittingCyclicBehaviorProfile reward cycle phase) who K
    (quittingProfileLiveRoot_cyclicBehaviorProfile_add_period reward cycle phase),
    quittingCyclicResponseCap, quittingProfileLiveRoot_cyclicBehaviorProfile]

/-- **The max-linear response system.**  At every phase the value of the best
reply is the larger of quitting now — averaged over the co-quitters realized at
the same stage — and continuing into the next phase's value. -/
def IsQuittingCyclicResponseSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (W : Fin K → Payoff ι) : Prop :=
  ∀ (phase : Fin K) (who : ι),
    W phase who =
      max (quittingRootQuitPayoff reward (W (finRotate K phase))
            (cycle phase) who)
        (quittingRootContinuePayoff reward (W (finRotate K phase))
          (cycle phase) who)

variable {cycle : Fin K → ι → PMF Bool} {W : Fin K → Payoff ι}

/-- A response solution is a fixed point of the one-stage companion map at
every phase. -/
theorem quittingRootCompanionMap_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι) :
    quittingRootCompanionMap reward (cycle phase) who
        (W (finRotate K phase) who) = W phase who := by
  rw [quittingRootCompanionMap_eq_max_endpoints reward
    (W (finRotate K phase)) (cycle phase) who]
  exact (hW phase who).symm

/-- **A response solution is a Bellman cap.**  Read along the periodic live
path, a solution of the max-linear system is exactly the repository's live
Bellman cap at every coordinate. -/
theorem isQuittingLiveBellmanCap_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι) :
    IsQuittingLiveBellmanCap reward (quittingCyclicRootSequence cycle phase) who
      (fun time ↦ W (quittingCyclicOrbit phase time) who) := by
  intro time
  have hnext : quittingCyclicOrbit phase (time + 1) =
      finRotate K (quittingCyclicOrbit phase time) :=
    quittingCyclicOrbit_succ phase time
  rw [quittingLiveBellmanValue, hnext,
    ← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
      (quittingCyclicRootSequence cycle phase) who
      (W (finRotate K (quittingCyclicOrbit phase time))) time,
    ← quittingRootContinuePayoff_eq_fixedOpponents reward
      (quittingCyclicRootSequence cycle phase) who
      (W (finRotate K (quittingCyclicOrbit phase time))) time]
  exact hW (quittingCyclicOrbit phase time) who

/-- Every deterministic stopping date inside one pass is capped by a response
solution. -/
theorem quittingPeriodicWindowPhaseStopValue_le_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι) (stop : Fin K) :
    quittingPeriodicWindowPhaseStopValue reward
        (quittingCyclicRootSequence cycle phase) who stop ≤ W phase who := by
  have hbound :=
    quittingRootSequencePureTimeTerminalValue_le_of_bellmanSupersolution reward
      (quittingCyclicRootSequence cycle phase) who
      (fun time ↦ W (quittingCyclicOrbit phase time) who)
      (isQuittingLiveBellmanCap_of_isQuittingCyclicResponseSolution hW phase
        who).supersolution
      0 stop.val
  simpa [quittingPeriodicWindowPhaseStopValue] using hbound

/-- A response solution is a fixed point of the one-turn composite of the
companion map. -/
theorem quittingCompanionComposite_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι) (start fuel : ℕ) :
    quittingCompanionComposite reward (quittingCyclicRootSequence cycle phase) who
        start fuel (W (quittingCyclicOrbit phase (start + fuel)) who) =
      W (quittingCyclicOrbit phase start) who := by
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      rw [quittingCompanionComposite_succ,
        show start + (fuel + 1) = start + 1 + fuel from by omega, ih (start + 1),
        show quittingCyclicOrbit phase (start + 1) =
          finRotate K (quittingCyclicOrbit phase start) from
            quittingCyclicOrbit_succ phase start]
      exact quittingRootCompanionMap_of_isQuittingCyclicResponseSolution hW
        (quittingCyclicOrbit phase start) who

/-- A finite segment of a periodic response solution is transported exactly
by the composite of its one-stage companion labels. -/
theorem quittingCompanionLabelList_apply_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι) (start fuel : ℕ) :
    (Math.MaxAffineTransport.Label.compList
      (quittingCompanionLabelList reward
        (quittingCyclicRootSequence cycle phase) who start fuel)).apply
          (W (quittingCyclicOrbit phase (start + fuel)) who) =
      W (quittingCyclicOrbit phase start) who := by
  rw [← quittingCompanionComposite_eq_compList_apply]
  exact quittingCompanionComposite_of_isQuittingCyclicResponseSolution
    hW phase who start fuel

/-- Every coordinate of a periodic response solution is a fixed point of its
one-turn max-affine holonomy. -/
theorem quittingCompanionLabelCycle_fixed_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι) :
    (Math.MaxAffineTransport.Label.compList
      (quittingCompanionLabelList reward
        (quittingCyclicRootSequence cycle phase) who 0 K)).apply
          (W phase who) = W phase who := by
  simpa only [zero_add, quittingCyclicOrbit_zero, quittingCyclicOrbit_card] using
    (quittingCompanionLabelList_apply_of_isQuittingCyclicResponseSolution
      hW phase who 0 K)

/-- On a contractive coordinate, the generic scalar max-affine formula gives
the response value explicitly from the one-turn companion label. -/
theorem quittingCyclicResponseSolution_eq_companionLabel_fixedPoint
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι)
    (hcontract : (∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1) :
    let label := Math.MaxAffineTransport.Label.compList
      (quittingCompanionLabelList reward
        (quittingCyclicRootSequence cycle phase) who 0 K)
    W phase who =
      max (label.floor.unbotD (label.shift / (1 - label.slope)))
        (label.shift / (1 - label.slope)) := by
  dsimp only
  let label := Math.MaxAffineTransport.Label.compList
    (quittingCompanionLabelList reward
      (quittingCyclicRootSequence cycle phase) who 0 K)
  have hfixed : label.apply (W phase who) = W phase who :=
    quittingCompanionLabelCycle_fixed_of_isQuittingCyclicResponseSolution
      hW phase who
  have hslope : label.slope < 1 := by
    rw [Math.MaxAffineTransport.Label.slope_compList_eq_pathSlope,
      quittingCompanionLabelList_pathSlope,
      quittingOpponentSurvivalWeight_cyclic_period]
    exact hcontract
  exact (Math.MaxAffineTransport.Label.apply_eq_self_iff_of_slope_lt_one
    label hslope (W phase who)).mp hfixed

/-- **Never quitting is capped by a response solution.**  The hypothesis is
that the deviator's opponents absorb with positive probability over one turn of
the cycle. -/
theorem quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι)
    (hcontract : (∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence cycle phase) who ≤ W phase who := by
  have hfixed : quittingCompanionComposite reward
      (quittingCyclicRootSequence cycle phase) who 0 K (W phase who) =
        W phase who := by
    have hcomposite := quittingCompanionComposite_of_isQuittingCyclicResponseSolution
      hW phase who 0 K
    rwa [zero_add, quittingCyclicOrbit_card, quittingCyclicOrbit_zero] at hcomposite
  have hpos : 0 < K := phase.pos
  obtain ⟨pred, hpred⟩ : ∃ pred, K = pred + 1 := ⟨K - 1, by omega⟩
  subst hpred
  refine quittingRootSequencePureTimeTerminalValue_none_le_of_fixed reward
    (quittingCyclicRootSequence cycle phase) who pred
    (fun k ↦ quittingCyclicRootSequence_add_period cycle phase k) hfixed ?_
  rw [quittingOpponentSurvivalWeight_cyclic_period]
  exact hcontract


/-! ## The refusal identity -/

/-- The cycle with `who` forced to continue at every phase. -/
def quittingCyclicDeletedCycle (cycle : Fin K → ι → PMF Bool) (who : ι) :
    Fin K → ι → PMF Bool :=
  fun k ↦ Function.update (cycle k) who (PMF.pure false)

/-- Opponent survival of `who` at one phase is the plain survival mass of the
deleted row at that phase. -/
theorem quittingStationaryContinueMass_quittingCyclicDeletedCycle
    (cycle : Fin K → ι → PMF Bool) (who : ι) (k : Fin K) :
    quittingStationaryContinueMass (quittingCyclicDeletedCycle cycle who k) =
      quittingStationaryFixedOpponentsContinueMass (cycle k) who := rfl

/-- **The refusal identity.**  Never quitting against the periodic profile of
`cycle` is worth exactly the on-path value of the cycle in which `who` is
deleted, that is, forced to continue at every phase.  No absorption hypothesis
is used. -/
theorem quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence cycle phase) who =
      quittingCyclicTerminalValue reward (quittingCyclicDeletedCycle cycle who)
        phase who := by
  have hroots : quittingRootSequenceUpdate (quittingCyclicRootSequence cycle phase)
      who (quittingPureTimeHazard none) =
    quittingCyclicRootSequence (quittingCyclicDeletedCycle cycle who) phase := by
    funext time
    rw [quittingRootSequenceUpdate, quittingPureTimeHazard_none]
    rfl
  rw [quittingPeriodicWindowRefusalValue, quittingRootSequencePureTimeTerminalValue,
    quittingRootSequenceHazardTerminalValue, hroots, quittingCyclicTerminalValue]

/-- On the non-contracting branch every deleted phase mass is one. -/
theorem quittingStationaryFixedOpponentsContinueMass_eq_one_of_not_contracts
    {cycle : Fin K → ι → PMF Bool} {who : ι}
    (hcontracts : ¬ (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1)
    (k : Fin K) :
    quittingStationaryFixedOpponentsContinueMass (cycle k) who = 1 := by
  have hsurvival :=
    quittingOpponentSurvivalWeight_cyclicRootSequence_eq_one_of_not_contracts cycle k
      who hcontracts 1
  simpa [quittingOpponentSurvivalWeight] using hsurvival

/-- On the non-contracting branch the deleted cycle is the all-continue row at
every phase. -/
theorem quittingCyclicDeletedCycle_eq_allContinueRoot_of_not_contracts
    {cycle : Fin K → ι → PMF Bool} {who : ι}
    (hcontracts : ¬ (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1)
    (k : Fin K) :
    quittingCyclicDeletedCycle cycle who k =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  funext player
  exact eq_pure_false_of_quittingStationaryContinueMass_eq_one
    (quittingStationaryFixedOpponentsContinueMass_eq_one_of_not_contracts hcontracts k)
    player

/-- **Refusal on the non-contracting branch.**  When the deviator's opponents
never absorb, the deleted cycle never absorbs either, so refusal is worth
zero. -/
theorem quittingPeriodicWindowRefusalValue_eq_zero_of_not_contracts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {cycle : Fin K → ι → PMF Bool} (phase : Fin K) {who : ι}
    (hcontracts : ¬ (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1) :
    quittingPeriodicWindowRefusalValue reward
      (quittingCyclicRootSequence cycle phase) who = 0 := by
  rw [quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted,
    quittingCyclicTerminalValue]
  refine quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from reward _ who 0
    fun time _ ↦ ?_
  exact quittingCyclicDeletedCycle_eq_allContinueRoot_of_not_contracts hcontracts _

/-- **The quit branch on the non-contracting branch.**  When the deviator's
opponents never absorb, quitting now is worth exactly the deviator's own solo
row. -/
theorem quittingRootQuitPayoff_eq_solo_of_not_contracts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {cycle : Fin K → ι → PMF Bool} (phase : Fin K) {who : ι}
    (hcontracts : ¬ (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1) :
    quittingRootQuitPayoff reward tail (cycle phase) who =
      reward (quittingSingletonTerminal who) who := by
  have hdeleted :=
    quittingCyclicDeletedCycle_eq_allContinueRoot_of_not_contracts hcontracts phase
  have hupdate : Function.update (cycle phase) who (PMF.pure true) =
      Function.update (quittingAllContinueRoot : ι → PMF Bool) who (PMF.pure true) := by
    rw [← hdeleted, quittingCyclicDeletedCycle, Function.update_idem]
  rw [quittingRootQuitPayoff, hupdate, quittingRootExpectedPayoff_allContinue_update_true]

/-! ## The cap under a nonnegative degenerate coordinate -/

/-- **Never quitting is capped by a response solution.**  On the contracting
branch this is the fixed-point bound; on the non-contracting branch refusal is
worth zero, so a nonnegative solution coordinate is all that the bound
needs. -/
theorem quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution_of_nonneg
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι)
    (hnonneg : ¬ (∏ k : Fin K,
        quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1 →
      0 ≤ W phase who) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence cycle phase) who ≤ W phase who := by
  by_cases hcontract : (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1
  · exact quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution hW
      phase who hcontract
  · rw [quittingPeriodicWindowRefusalValue_eq_zero_of_not_contracts reward phase
      hcontract]
    exact hnonneg hcontract

/-- **Never quitting is capped by a response solution, under admissibility.**
Admissibility supplies the degenerate coordinate's nonnegativity: on the
non-contracting branch quitting now is worth the deviator's own solo row, which
the solution dominates. -/
theorem quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution_of_admissible
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin K)
    (who : ι)
    (hadmissible : IsQuittingCycleZeroDeviationMismatchAt reward cycle who) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence cycle phase) who ≤ W phase who := by
  refine quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution_of_nonneg
    hW phase who fun hcontract ↦ ?_
  have hsolo : 0 ≤ reward (quittingSingletonTerminal who) who :=
    hadmissible.resolve_left hcontract
  have hquit := le_max_left
    (quittingRootQuitPayoff reward (W (finRotate K phase)) (cycle phase) who)
    (quittingRootContinuePayoff reward (W (finRotate K phase)) (cycle phase) who)
  rw [← hW phase who,
    quittingRootQuitPayoff_eq_solo_of_not_contracts reward _ phase hcontract] at hquit
  linarith

/-- **The exact finite best-response statistic is capped by a response
solution.**  The hypothesis is needed only on the branch where the deviator's
opponents never absorb over one turn, and there it asks only that the solution
coordinate be nonnegative.  Together with
`quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` this caps
every behavior deviation, not only the stopping times. -/
theorem quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution_of_nonneg
    [NeZero K] (hW : IsQuittingCyclicResponseSolution reward cycle W)
    (phase : Fin K) (who : ι)
    (hnonneg : ¬ (∏ k : Fin K,
        quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1 →
      0 ≤ W phase who) :
    quittingCyclicResponseCap reward cycle phase who ≤ W phase who := by
  refine max_le
    (quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution_of_nonneg
      hW phase who hnonneg) ?_
  refine Finset.sup'_le _ _ fun stop _ ↦ ?_
  exact quittingPeriodicWindowPhaseStopValue_le_of_isQuittingCyclicResponseSolution
    hW phase who stop

/-- **The exact finite best-response statistic is capped, under
admissibility.**  The hypothesis is the admissibility disjunction at the
deviating coordinate: either its opponents absorb over one turn, or its own
solo row is nonnegative. -/
theorem quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution
    [NeZero K] (hW : IsQuittingCyclicResponseSolution reward cycle W)
    (phase : Fin K) (who : ι)
    (hadmissible : IsQuittingCycleZeroDeviationMismatchAt reward cycle who) :
    quittingCyclicResponseCap reward cycle phase who ≤ W phase who := by
  refine max_le
    (quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution_of_admissible
      hW phase who hadmissible) ?_
  refine Finset.sup'_le _ _ fun stop _ ↦ ?_
  exact quittingPeriodicWindowPhaseStopValue_le_of_isQuittingCyclicResponseSolution
    hW phase who stop

end GameTheory
