/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicGreenDebt

/-!
# Unrestricted deviation caps for approximate-Nash cycles

For a periodic product-root profile, local Nash defects computed against the
actual next-phase terminal values control the complete behavioral deviation
debt.  The denominator is the literal probability that at least one opponent
quits during a period.  No atom cover, stationary-deviation restriction, or
bounded stopping horizon is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Local approximate Nash against the actual cyclic continuation bounds the
unrestricted behavioral terminal debt by the period length times the local
error, divided by one-period opponent absorption. -/
theorem quittingRootSequenceTerminalDebt_cyclic_le_card_mul_error_div_opponentAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) {error : ℝ} (herror : 0 ≤ error)
    (hnash : ∀ phase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle (finRotate K phase))
        error (cycle phase))
    (initial : Fin K) (who : ι)
    (hcontracts : (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1) :
    quittingRootSequenceTerminalDebt reward
        (quittingCyclicRootSequence cycle initial) who 0 ≤
      (K : ℝ) * error /
        (1 - ∏ phase : Fin K,
          quittingStationaryFixedOpponentsContinueMass (cycle phase) who) := by
  let roots := quittingCyclicRootSequence cycle initial
  let survival := ∏ phase : Fin K,
    quittingStationaryFixedOpponentsContinueMass (cycle phase) who
  have hdefect : ∀ time,
      quittingRootSequenceActualCoordinateDefect reward roots who time ≤ error := by
    intro time
    rw [show roots = quittingCyclicRootSequence cycle initial by rfl,
      quittingRootSequenceActualCoordinateDefect_cyclic_eq]
    exact (isεQuittingRootNash_iff_coordinateNashDefect_le
      reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K (quittingCyclicOrbit initial time)))
        error (cycle (quittingCyclicOrbit initial time))).1
          (hnash (quittingCyclicOrbit initial time)) who
  have hsum :
      (∑ offset ∈ Finset.range K,
        quittingOpponentSurvivalWeight roots who 0 offset *
          quittingRootSequenceActualCoordinateDefect reward roots who offset) ≤
        (K : ℝ) * error := by
    calc
      (∑ offset ∈ Finset.range K,
          quittingOpponentSurvivalWeight roots who 0 offset *
            quittingRootSequenceActualCoordinateDefect reward roots who offset) ≤
          ∑ _offset ∈ Finset.range K, error := by
        apply Finset.sum_le_sum
        intro offset _
        have hweightNonneg :=
          quittingOpponentSurvivalWeight_nonneg roots who 0 offset
        have hweightLeOne :=
          quittingOpponentSurvivalWeight_le_one roots who 0 offset
        calc
          quittingOpponentSurvivalWeight roots who 0 offset *
                quittingRootSequenceActualCoordinateDefect reward roots who offset ≤
              quittingOpponentSurvivalWeight roots who 0 offset * error :=
            mul_le_mul_of_nonneg_left (hdefect offset) hweightNonneg
          _ ≤ 1 * error := mul_le_mul_of_nonneg_right hweightLeOne herror
          _ = error := one_mul _
      _ = (K : ℝ) * error := by simp
  have hweight : quittingOpponentSurvivalWeight roots who 0 K = survival := by
    rw [show roots = quittingCyclicRootSequence cycle initial by rfl,
      quittingOpponentSurvivalWeight_cyclicRootSequence]
    simp only [quittingCyclicOrbit_zero, quittingCyclicPrefixWeight_card]
    rfl
  have hperiod : quittingRootSequenceTerminalDebt reward roots who K =
      quittingRootSequenceTerminalDebt reward roots who 0 := by
    rw [show roots = quittingCyclicRootSequence cycle initial by rfl]
    exact quittingRootSequenceTerminalDebt_cyclic_card reward cycle initial who
  have hfinite :=
    quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_tail
      reward roots who 0 K
  simp only [zero_add] at hfinite
  rw [hweight, hperiod] at hfinite
  have hdenominator : 0 < 1 - survival := sub_pos.mpr hcontracts
  change quittingRootSequenceTerminalDebt reward roots who 0 ≤ _
  apply (le_div_iff₀ hdenominator).2
  nlinarith [hsum]

/-- The same cap stated for the literal periodic behavior profile and its
playerwise terminal deviation debt. -/
theorem quittingTerminalDeviationDebt_cyclicBehaviorProfile_le_card_mul_error_div_opponentAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) {error : ℝ} (herror : 0 ≤ error)
    (hnash : ∀ phase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle (finRotate K phase))
        error (cycle phase))
    (initial : Fin K) (who : ι)
    (hcontracts : (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1) :
    quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward cycle initial) who ≤
      (K : ℝ) * error /
        (1 - ∏ phase : Fin K,
          quittingStationaryFixedOpponentsContinueMass (cycle phase) who) := by
  simpa [quittingRootSequenceTerminalDebt, quittingCyclicBehaviorProfile] using
    quittingRootSequenceTerminalDebt_cyclic_le_card_mul_error_div_opponentAbsorption
      reward cycle herror hnash initial who hcontracts

end GameTheory
