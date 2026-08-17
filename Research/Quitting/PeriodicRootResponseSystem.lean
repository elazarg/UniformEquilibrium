/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanCapPureTimeStop
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.PeriodicPureTimeBellman

/-!
# The max-linear response system of a periodic root cycle

Fix a period `m + 1` and a cycle `cycle : Fin (m + 1) → ι → PMF Bool` of
one-stage Boolean product rows.  The behavior profile
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
* never quitting is capped, provided the deviator's opponents absorb over one
  turn with positive probability
  (`quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution`);
* hence the exact finite best-response statistic is capped
  (`quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution`), and by
  `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` that
  statistic already dominates every behavior deviation.

The last section is the necessary-condition direction: a
`QuittingCounterexampleRegime` forces every periodic cycle to leave some player
a gain of at least the regime's terminal gap over the on-path value, measured
either by the exact finite cap or by any response solution.

## Main definitions

* `quittingCyclicResponseCap` — the exact finite best-response statistic
* `IsQuittingCyclicResponseSolution` — the max-linear response system

## Main results

* `quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution`
* `QuittingCounterexampleRegime.exists_quittingCyclicCap_gain`
* `QuittingCounterexampleRegime.exists_quittingCyclicResponse_gain`
* `isEmpty_counterexampleRegime_of_quittingCyclicResponseCap_le`
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
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
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1)) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingCyclicBehaviorProfile reward cycle phase) (time + (m + 1)) =
      quittingProfileLiveRoot reward
        (quittingCyclicBehaviorProfile reward cycle phase) time := by
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile,
    quittingCyclicRootSequence_add_period]

/-- Opponent survival of `who` over one full turn of the cycle. -/
theorem quittingOpponentSurvivalWeight_cyclic_period
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1)) (who : ι) :
    quittingOpponentSurvivalWeight (quittingCyclicRootSequence cycle phase) who 0
        (m + 1) =
      ∏ cyclePhase : Fin (m + 1),
        quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who := by
  rw [quittingOpponentSurvivalWeight_cyclicRootSequence, quittingCyclicOrbit_zero,
    quittingCyclicPrefixWeight_card]

/-! ## The response system -/

/-- The exact finite best-response statistic of the periodic profile of
`cycle` started at `phase`: the better of never quitting and of quitting at one
of the finitely many phases of the first pass. -/
def quittingCyclicResponseCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1)) (who : ι) : ℝ :=
  quittingPeriodicWindowBestResponseValue reward
    (quittingCyclicRootSequence cycle phase) who (m + 1)

/-- **The response cap is the supremum over all behavior deviations.**  The
supremum of the deviator's payoff over its whole behavior strategy space is
attained on the countable family of deterministic stopping dates, and equals
the finite periodic statistic. -/
theorem sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1)) (who : ι) :
    sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who ↦
        quittingTerminalPayoff reward
          (Function.update (quittingCyclicBehaviorProfile reward cycle phase) who
            deviation) who) =
      quittingCyclicResponseCap reward cycle phase who := by
  rw [sSup_range_quittingTerminalPayoff_update_eq_periodicWindow reward
    (quittingCyclicBehaviorProfile reward cycle phase) who (m + 1)
    (quittingProfileLiveRoot_cyclicBehaviorProfile_add_period reward cycle phase),
    quittingCyclicResponseCap, quittingProfileLiveRoot_cyclicBehaviorProfile]

/-- **The max-linear response system.**  At every phase the value of the best
reply is the larger of quitting now — averaged over the co-quitters realized at
the same stage — and continuing into the next phase's value. -/
def IsQuittingCyclicResponseSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin (m + 1) → ι → PMF Bool) (W : Fin (m + 1) → Payoff ι) : Prop :=
  ∀ (phase : Fin (m + 1)) (who : ι),
    W phase who =
      max (quittingRootQuitPayoff reward (W (finRotate (m + 1) phase))
            (cycle phase) who)
        (quittingRootContinuePayoff reward (W (finRotate (m + 1) phase))
          (cycle phase) who)

variable {cycle : Fin (m + 1) → ι → PMF Bool} {W : Fin (m + 1) → Payoff ι}

/-- A response solution is a fixed point of the one-stage companion map at
every phase. -/
theorem quittingRootCompanionMap_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin (m + 1))
    (who : ι) :
    quittingRootCompanionMap reward (cycle phase) who
        (W (finRotate (m + 1) phase) who) = W phase who := by
  rw [quittingRootCompanionMap_eq_max_endpoints reward
    (W (finRotate (m + 1) phase)) (cycle phase) who]
  exact (hW phase who).symm

/-- **A response solution is a Bellman cap.**  Read along the periodic live
path, a solution of the max-linear system is exactly the repository's live
Bellman cap at every coordinate. -/
theorem isQuittingLiveBellmanCap_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin (m + 1))
    (who : ι) :
    IsQuittingLiveBellmanCap reward (quittingCyclicRootSequence cycle phase) who
      (fun time ↦ W (quittingCyclicOrbit phase time) who) := by
  intro time
  have hnext : quittingCyclicOrbit phase (time + 1) =
      finRotate (m + 1) (quittingCyclicOrbit phase time) :=
    quittingCyclicOrbit_succ phase time
  rw [quittingLiveBellmanValue, hnext,
    ← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
      (quittingCyclicRootSequence cycle phase) who
      (W (finRotate (m + 1) (quittingCyclicOrbit phase time))) time,
    ← quittingRootContinuePayoff_eq_fixedOpponents reward
      (quittingCyclicRootSequence cycle phase) who
      (W (finRotate (m + 1) (quittingCyclicOrbit phase time))) time]
  exact hW (quittingCyclicOrbit phase time) who

/-- Every deterministic stopping date inside one pass is capped by a response
solution. -/
theorem quittingPeriodicWindowPhaseStopValue_le_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin (m + 1))
    (who : ι) (stop : Fin (m + 1)) :
    quittingPeriodicWindowPhaseStopValue reward
        (quittingCyclicRootSequence cycle phase) who stop ≤ W phase who := by
  have hbound := quittingRootSequencePureTimeTerminalValue_le_of_bellmanCap reward
    (quittingCyclicRootSequence cycle phase) who
    (fun time ↦ W (quittingCyclicOrbit phase time) who)
    (isQuittingLiveBellmanCap_of_isQuittingCyclicResponseSolution hW phase who)
    0 stop.val
  simpa [quittingPeriodicWindowPhaseStopValue] using hbound

/-- A response solution is a fixed point of the one-turn composite of the
companion map. -/
theorem quittingCompanionComposite_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin (m + 1))
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
          finRotate (m + 1) (quittingCyclicOrbit phase start) from
            quittingCyclicOrbit_succ phase start]
      exact quittingRootCompanionMap_of_isQuittingCyclicResponseSolution hW
        (quittingCyclicOrbit phase start) who

/-- **Never quitting is capped by a response solution.**  The hypothesis is
that the deviator's opponents absorb with positive probability over one turn of
the cycle. -/
theorem quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin (m + 1))
    (who : ι)
    (hcontract : (∏ cyclePhase : Fin (m + 1),
      quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1) :
    quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence cycle phase) who ≤ W phase who := by
  have hfixed : quittingCompanionComposite reward
      (quittingCyclicRootSequence cycle phase) who 0 (m + 1) (W phase who) =
        W phase who := by
    have hcomposite := quittingCompanionComposite_of_isQuittingCyclicResponseSolution
      hW phase who 0 (m + 1)
    rwa [zero_add, quittingCyclicOrbit_card, quittingCyclicOrbit_zero] at hcomposite
  refine quittingRootSequencePureTimeTerminalValue_none_le_of_fixed reward
    (quittingCyclicRootSequence cycle phase) who m
    (fun k ↦ quittingCyclicRootSequence_add_period cycle phase k) hfixed ?_
  rw [quittingOpponentSurvivalWeight_cyclic_period]
  exact hcontract

/-- **The exact finite best-response statistic is capped by a response
solution.**  Together with
`quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` this caps
every behavior deviation, not only the stopping times. -/
theorem quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution
    (hW : IsQuittingCyclicResponseSolution reward cycle W) (phase : Fin (m + 1))
    (who : ι)
    (hcontract : (∏ cyclePhase : Fin (m + 1),
      quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1) :
    quittingCyclicResponseCap reward cycle phase who ≤ W phase who := by
  refine max_le
    (quittingPeriodicWindowRefusalValue_le_of_isQuittingCyclicResponseSolution hW
      phase who hcontract) ?_
  refine Finset.sup'_le _ _ fun stop _ ↦ ?_
  exact quittingPeriodicWindowPhaseStopValue_le_of_isQuittingCyclicResponseSolution
    hW phase who stop

/-! ## The necessary condition -/

namespace QuittingCounterexampleRegime

/-- **Every periodic cycle is exposed at the full terminal gap.**  A
counterexample regime leaves some player a gain of at least its terminal gap
over the cycle's on-path value, measured by the exact finite best-response
statistic. -/
theorem exists_quittingCyclicCap_gain
    (regime : QuittingCounterexampleRegime reward)
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1)) :
    ∃ who,
      quittingCyclicTerminalValue reward cycle phase who + regime.terminalGap ≤
        quittingCyclicResponseCap reward cycle phase who := by
  obtain ⟨who, hgain⟩ := regime.exists_periodicCap_gain
    (quittingCyclicBehaviorProfile reward cycle phase) (m + 1)
    (quittingProfileLiveRoot_cyclicBehaviorProfile_add_period reward cycle phase)
  refine ⟨who, ?_⟩
  rw [quittingTerminalPayoff_cyclicBehaviorProfile] at hgain
  rw [quittingCyclicResponseCap]
  rwa [quittingProfileLiveRoot_cyclicBehaviorProfile] at hgain

/-- **The periodic necessary condition.**  A counterexample regime leaves some
player a behavior deviation against the periodic profile of `cycle` whose
supremum value beats the cycle's on-path value by at least the regime's
terminal gap.  No absorption hypothesis on the cycle is used. -/
theorem exists_quittingCyclicDeviationSup_gain
    (regime : QuittingCounterexampleRegime reward)
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1)) :
    ∃ who,
      quittingCyclicTerminalValue reward cycle phase who + regime.terminalGap ≤
        sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who ↦
          quittingTerminalPayoff reward
            (Function.update (quittingCyclicBehaviorProfile reward cycle phase) who
              deviation) who) := by
  obtain ⟨who, hgain⟩ := regime.exists_quittingCyclicCap_gain cycle phase
  exact ⟨who, by
    rwa [sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile]⟩

/-- **The same statement read through the max-linear system.**  If `W` solves
the response system and every player's opponents absorb over one turn, a
counterexample regime forces some player's response value to beat the on-path
value by at least the terminal gap. -/
theorem exists_quittingCyclicResponse_gain
    (regime : QuittingCounterexampleRegime reward)
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1))
    {W : Fin (m + 1) → Payoff ι}
    (hW : IsQuittingCyclicResponseSolution reward cycle W)
    (hcontract : ∀ who, (∏ cyclePhase : Fin (m + 1),
      quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who) < 1) :
    ∃ who,
      quittingCyclicTerminalValue reward cycle phase who + regime.terminalGap ≤
        W phase who := by
  obtain ⟨who, hgain⟩ := regime.exists_quittingCyclicCap_gain cycle phase
  exact ⟨who, hgain.trans
    (quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution hW phase who
      (hcontract who))⟩

end QuittingCounterexampleRegime

/-- A cycle whose exact finite best-response statistic never beats its on-path
value rules out every counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_quittingCyclicResponseCap_le
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1))
    (hcap : ∀ who, quittingCyclicResponseCap reward cycle phase who ≤
      quittingCyclicTerminalValue reward cycle phase who) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime ↦ ?_⟩
  obtain ⟨who, hgain⟩ := regime.exists_quittingCyclicCap_gain cycle phase
  have hpos := regime.terminalGap_pos
  linarith [hcap who]

end GameTheory
