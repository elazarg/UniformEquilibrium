/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardFiniteCalendar
import UniformEquilibrium.Quitting.Cycles.PeriodicFiniteHorizonRate

/-!
# Explicit horizon errors for infinite paired-collision profiles

The generic cyclic opponent-clock estimate gives an absolute terminal-versus-
average error for every actual behavioral deviation, not just an upper bound
for prescribed play. The same estimates hold at every literal live suffix.
The admissible rates give the uniform constants `8000 / 271` for delivery and
deviation comparison and `16000 / 271` for finite-horizon regret.
-/

noncomputable section

namespace GameTheory.PairedCollisionReward.PeriodicRates

variable {c : ℝ} (rates : PeriodicRates c)

/-- One cycle of survival after deleting the deviating player's own clock. -/
def opponentCycleMass (who : Player) : ℝ :=
  if who.val < 2 then rates.primary * rates.secondary ^ 2
  else rates.primary ^ 2 * rates.secondary

theorem opponentCycleMass_lt_one (who : Player) : rates.opponentCycleMass who < 1 := by
  simpa only [rates.cycle_opponentMass, opponentCycleMass] using rates.cycle_contracts who

theorem opponentCycleMass_le_uniform (who : Player) :
    rates.opponentCycleMass who ≤ (729 : ℝ) / 1000 := by
  have ha : rates.primary ≤ (9 : ℝ) / 10 := rates.primary_lt.le
  have hb : rates.secondary ≤ (9 : ℝ) / 10 := by
    linarith [rates.secondary_lt_primary]
  have ha2 := pow_le_pow_left₀ rates.primary_pos.le ha 2
  have hb2 := pow_le_pow_left₀ rates.secondary_pos.le hb 2
  unfold opponentCycleMass
  split_ifs
  · have h := mul_le_mul ha hb2 (sq_nonneg rates.secondary) (by norm_num)
    norm_num at h ⊢
    exact h
  · have h := mul_le_mul ha2 hb rates.secondary_pos.le (by norm_num)
    norm_num at h ⊢
    exact h

/-- The explicit player-specific constant retains the actual deleted-player cycle mass. -/
def horizonConstant (who : Player) : ℝ := 8 / (1 - rates.opponentCycleMass who)

theorem horizonConstant_le_uniform (who : Player) :
    rates.horizonConstant who ≤ (8000 : ℝ) / 271 := by
  have hgap : 0 < 1 - rates.opponentCycleMass who := by
    linarith [rates.opponentCycleMass_lt_one who]
  unfold horizonConstant
  apply (div_le_iff₀ hgap).mpr
  nlinarith [rates.opponentCycleMass_le_uniform who]

theorem profile_opponentClock_le (phase : Fin 2) (who : Player) (horizon : ℕ) :
    quittingOpponentLiveCesaro (reward c) (rates.profile phase) who horizon ≤
      (2 / (1 - rates.opponentCycleMass who)) / (horizon : ℝ) := by
  simpa only [profile, rates.cycle_opponentMass, opponentCycleMass, Nat.cast_ofNat] using
    quittingOpponentLiveCesaro_cyclicBehaviorProfile_le
      (reward c) rates.cycleRoot phase who horizon (rates.cycle_contracts who)

/-- The absolute comparison covers arbitrary behavioral replacements and signed rewards. -/
theorem profile_horizonDeviation_absolute (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (who : Player)
    (deviation : (quittingGame (reward c)).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame (reward c)).finiteAveragePayoff none horizon
        (Function.update (rates.profile phase) who deviation) who -
      quittingTerminalPayoff (reward c)
        (Function.update (rates.profile phase) who deviation) who| ≤
      rates.horizonConstant who / (horizon : ℝ) := by
  have herror := abs_finiteAveragePayoff_sub_terminal_le_opponentLiveCesaro
    (reward c) (Function.update (rates.profile phase) who deviation) who horizon hhorizon
    4 (by norm_num) (fun terminal => abs_reward_le_four hc terminal who)
  have hclock : quittingOpponentLiveCesaro (reward c)
      (Function.update (rates.profile phase) who deviation) who horizon =
      quittingOpponentLiveCesaro (reward c) (rates.profile phase) who horizon := by
    simp only [quittingOpponentLiveCesaro, quittingOpponentOnlyProfile, Function.update_idem]
  rw [hclock] at herror
  calc
    _ ≤ 4 * quittingOpponentLiveCesaro (reward c) (rates.profile phase) who horizon := herror
    _ ≤ 4 * ((2 / (1 - rates.opponentCycleMass who)) / (horizon : ℝ)) :=
      mul_le_mul_of_nonneg_left (rates.profile_opponentClock_le phase who horizon)
        (by norm_num)
    _ = rates.horizonConstant who / (horizon : ℝ) := by unfold horizonConstant; ring

theorem profile_horizonDelivery (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (who : Player) (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame (reward c)).finiteAveragePayoff none horizon (rates.profile phase) who -
      rates.cycleValue phase who| ≤ rates.horizonConstant who / (horizon : ℝ) := by
  simpa only [Function.update_eq_self, rates.profile_terminalPayoff] using
    rates.profile_horizonDeviation_absolute hc phase who (rates.profile phase who)
      horizon hhorizon

theorem profile_horizonDeviation_absolute_uniform (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (who : Player)
    (deviation : (quittingGame (reward c)).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame (reward c)).finiteAveragePayoff none horizon
        (Function.update (rates.profile phase) who deviation) who -
      quittingTerminalPayoff (reward c)
        (Function.update (rates.profile phase) who deviation) who| ≤
      ((8000 : ℝ) / 271) / (horizon : ℝ) :=
  (rates.profile_horizonDeviation_absolute hc phase who deviation horizon hhorizon).trans
    (div_le_div_of_nonneg_right (rates.horizonConstant_le_uniform who) (Nat.cast_nonneg _))

theorem profile_horizonDelivery_uniform (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (who : Player) (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame (reward c)).finiteAveragePayoff none horizon (rates.profile phase) who -
      rates.cycleValue phase who| ≤ ((8000 : ℝ) / 271) / (horizon : ℝ) :=
  (rates.profile_horizonDelivery hc phase who horizon hhorizon).trans
    (div_le_div_of_nonneg_right (rates.horizonConstant_le_uniform who) (Nat.cast_nonneg _))

theorem profile_horizonNash_uniform (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame (reward c)).IsεHorizonNash none horizon
      (((16000 : ℝ) / 271) / (horizon : ℝ)) (rates.profile phase) := by
  intro who deviation
  have hdev := (abs_le.mp (rates.profile_horizonDeviation_absolute_uniform
    hc phase who deviation horizon hhorizon)).2
  have hon := (abs_le.mp
    (rates.profile_horizonDelivery_uniform hc phase who horizon hhorizon)).1
  have hterminal := rates.profile_isExactTerminalNash hc phase who deviation
  rw [rates.profile_terminalPayoff] at hterminal
  have hdouble : ((16000 : ℝ) / 271) / (horizon : ℝ) =
      2 * (((8000 : ℝ) / 271) / (horizon : ℝ)) := by ring
  rw [hdouble]
  linarith

/-- Literal suffixes have the same absolute all-deviation comparison, uniformly in the cut. -/
theorem allSuffix_horizonDeviation_absolute (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (start : ℕ) (who : Player)
    (deviation : (quittingGame (reward c)).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame (reward c)).finiteAveragePayoff none horizon
        (Function.update (quittingRootSequenceProfile (reward c)
          (quittingCyclicRootSequence rates.cycleRoot phase) start) who deviation) who -
      quittingTerminalPayoff (reward c)
        (Function.update (quittingRootSequenceProfile (reward c)
          (quittingCyclicRootSequence rates.cycleRoot phase) start) who deviation) who| ≤
      ((8000 : ℝ) / 271) / (horizon : ℝ) := by
  rw [rates.profile_suffix]
  exact rates.profile_horizonDeviation_absolute_uniform hc _ who deviation horizon hhorizon

theorem allSuffix_horizonDelivery (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (start : ℕ) (who : Player)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame (reward c)).finiteAveragePayoff none horizon
        (quittingRootSequenceProfile (reward c)
          (quittingCyclicRootSequence rates.cycleRoot phase) start) who -
      rates.cycleValue (quittingCyclicOrbit phase start) who| ≤
      ((8000 : ℝ) / 271) / (horizon : ℝ) := by
  rw [rates.profile_suffix]
  exact rates.profile_horizonDelivery_uniform hc _ who horizon hhorizon

theorem allSuffix_horizonNash (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (phase : Fin 2) (start horizon : ℕ) (hhorizon : 0 < horizon) :
    (quittingGame (reward c)).IsεHorizonNash none horizon
      (((16000 : ℝ) / 271) / (horizon : ℝ))
      (quittingRootSequenceProfile (reward c)
        (quittingCyclicRootSequence rates.cycleRoot phase) start) := by
  rw [rates.profile_suffix]
  exact rates.profile_horizonNash_uniform hc _ horizon hhorizon

end GameTheory.PairedCollisionReward.PeriodicRates
