/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.InteriorApproximateNashCyclicProfile

/-!
# Absorption alternatives for interior cyclic profiles

This file records the two quantitative residual regimes of an interior cyclic
block without attaching extra strategic conclusions.  Positive own-player
absorption uniformly controls every outsider's complete behavioral debt.  If
both the selected player's own and opponent absorption vanish, the sum of all
displayed hazards vanishes, even when the periods vary.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Joint survival probability through one turn of a cyclic product profile. -/
def quittingCyclicJointSurvivalMass
    {K : ℕ} (cycle : Fin K → ι → PMF Bool) : ℝ :=
  ∏ phase : Fin K, quittingStationaryContinueMass (cycle phase)

/-- Sum of every displayed playerwise Quit probability in one turn. -/
def quittingCyclicTotalHazard
    {K : ℕ} (cycle : Fin K → ι → PMF Bool) : ℝ :=
  ∑ phase : Fin K, ∑ who : ι, (cycle phase who true).toReal

/-- Joint cyclic survival factors into a selected player's own survival and
the survival of all of that player's opponents. -/
theorem quittingCyclicJointSurvivalMass_eq_opponents_mul_player
    {K : ℕ} (cycle : Fin K → ι → PMF Bool) (who : ι) :
    quittingCyclicJointSurvivalMass cycle =
      (1 - quittingCyclicOpponentAbsorptionMass cycle who) *
        (1 - quittingCyclicPlayerAbsorptionMass cycle who) := by
  unfold quittingCyclicJointSurvivalMass
    quittingCyclicOpponentAbsorptionMass
    quittingCyclicPlayerAbsorptionMass
  rw [sub_sub_cancel, sub_sub_cancel]
  calc
    (∏ phase : Fin K, quittingStationaryContinueMass (cycle phase)) =
        ∏ phase : Fin K,
          (quittingStationaryFixedOpponentsContinueMass
              (cycle phase) who *
            (cycle phase who false).toReal) := by
      apply Finset.prod_congr rfl
      intro phase _
      exact quittingStationaryContinueMass_eq_forcedContinue_mul_own
        (cycle phase) who
    _ = (∏ phase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle phase) who) *
        ∏ phase : Fin K, (cycle phase who false).toReal := by
      rw [Finset.prod_mul_distrib]

/-- A player's probability of quitting during a turn is bounded by the
opponent-absorption probability seen by every distinct outsider. -/
theorem quittingCyclicPlayerAbsorptionMass_le_opponentAbsorptionMass_of_ne
    {K : ℕ} (cycle : Fin K → ι → PMF Bool)
    {owner outsider : ι} (hne : owner ≠ outsider) :
    quittingCyclicPlayerAbsorptionMass cycle owner ≤
      quittingCyclicOpponentAbsorptionMass cycle outsider := by
  unfold quittingCyclicPlayerAbsorptionMass
    quittingCyclicOpponentAbsorptionMass
  apply sub_le_sub_left
  apply Finset.prod_le_prod
  · intro phase _
    exact quittingStationaryFixedOpponentsContinueMass_nonneg
      (cycle phase) outsider
  · intro phase _
    have hcontinue := quittingStationaryContinueMass_le_ownContinueProbability
      (Function.update (cycle phase) outsider (PMF.pure false)) owner
    rw [Function.update_of_ne hne] at hcontinue
    exact hcontinue

/-- A positive lower bound on one player's own period absorption gives every
distinct outsider a complete behavioral deviation cap with the same
denominator. -/
theorem InteriorApproximateNashCyclicBlock.outsiderTerminalDeviationDebt_le
    [Nontrivial ι]
    {m : ℕ} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error absorptionFloor : ℝ} (herror : 0 ≤ error)
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (initial : Fin (m + 1)) {owner outsider : ι}
    (hne : owner ≠ outsider) (hfloor : 0 < absorptionFloor)
    (howner : absorptionFloor ≤
      quittingCyclicPlayerAbsorptionMass block.cycle owner) :
    quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward block.cycle initial) outsider ≤
      ((m + 1 : ℕ) : ℝ) * error / absorptionFloor := by
  have hdenominator : absorptionFloor ≤
      quittingCyclicOpponentAbsorptionMass block.cycle outsider :=
    howner.trans
      (quittingCyclicPlayerAbsorptionMass_le_opponentAbsorptionMass_of_ne
        block.cycle hne)
  have hdenominatorPos : 0 <
      quittingCyclicOpponentAbsorptionMass block.cycle outsider :=
    hfloor.trans_le hdenominator
  have hcap := block.terminalDeviationDebt_le herror initial outsider
  unfold quittingCyclicOpponentAbsorptionMass at hcap hdenominatorPos hdenominator
  have hnumerator : 0 ≤ ((m + 1 : ℕ) : ℝ) * error :=
    mul_nonneg (Nat.cast_nonneg _) herror
  calc
    quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward block.cycle initial) outsider ≤
        ((m + 1 : ℕ) : ℝ) * error /
          (1 - ∏ phase : Fin (m + 1),
            quittingStationaryFixedOpponentsContinueMass
              (block.cycle phase) outsider) := hcap
    _ ≤ ((m + 1 : ℕ) : ℝ) * error / absorptionFloor := by
      exact div_le_div_of_nonneg_left hnumerator hfloor hdenominator

omit [DecidableEq ι] in
/-- The total displayed hazard of a finite cyclic word is bounded by player
count times the negative logarithm of its one-turn joint survival. -/
theorem quittingCyclicTotalHazard_le_neg_card_mul_log_jointSurvival
    {K : ℕ} (cycle : Fin K → ι → PMF Bool)
    (hcontinue : ∀ phase who, 0 < (cycle phase who false).toReal) :
    quittingCyclicTotalHazard cycle ≤
      -(Fintype.card ι : ℝ) * Real.log
        (quittingCyclicJointSurvivalMass cycle) := by
  have hphasePositive : ∀ phase,
      0 < quittingStationaryContinueMass (cycle phase) := by
    intro phase
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    exact Finset.prod_pos fun who _ ↦ hcontinue phase who
  have hquitLe : ∀ phase who,
      (cycle phase who true).toReal ≤
        quittingRootAbsorptionMass (cycle phase) := by
    intro phase who
    have hcontinueLe :=
      quittingStationaryContinueMass_le_ownContinueProbability
        (cycle phase) who
    have hsum :=
      quittingRoot_continueProbability_add_quitProbability
        (cycle phase) who
    unfold quittingRootAbsorptionMass
    linarith
  have htotalLe : quittingCyclicTotalHazard cycle ≤
      (Fintype.card ι : ℝ) *
        ∑ phase : Fin K, quittingRootAbsorptionMass (cycle phase) := by
    unfold quittingCyclicTotalHazard
    calc
      (∑ phase : Fin K, ∑ who : ι,
          (cycle phase who true).toReal) ≤
          ∑ phase : Fin K, ∑ _who : ι,
            quittingRootAbsorptionMass (cycle phase) := by
        apply Finset.sum_le_sum
        intro phase _
        exact Finset.sum_le_sum fun who _ ↦ hquitLe phase who
      _ = (Fintype.card ι : ℝ) *
          ∑ phase : Fin K, quittingRootAbsorptionMass (cycle phase) := by
        simp [Finset.mul_sum]
  have habsorptionLog :
      (∑ phase : Fin K, quittingRootAbsorptionMass (cycle phase)) ≤
        -Real.log (quittingCyclicJointSurvivalMass cycle) := by
    have hpoint : ∀ phase,
        quittingRootAbsorptionMass (cycle phase) ≤
          -Real.log (quittingStationaryContinueMass (cycle phase)) := by
      intro phase
      rw [quittingRootAbsorptionMass]
      have hlog := Real.log_le_sub_one_of_pos (hphasePositive phase)
      linarith
    calc
      (∑ phase : Fin K, quittingRootAbsorptionMass (cycle phase)) ≤
          ∑ phase : Fin K,
            -Real.log (quittingStationaryContinueMass (cycle phase)) :=
        Finset.sum_le_sum fun phase _ ↦ hpoint phase
      _ = -Real.log (quittingCyclicJointSurvivalMass cycle) := by
        unfold quittingCyclicJointSurvivalMass
        rw [Real.log_prod (fun phase _ ↦ (hphasePositive phase).ne')]
        simp
  calc
    quittingCyclicTotalHazard cycle ≤
        (Fintype.card ι : ℝ) *
          ∑ phase : Fin K, quittingRootAbsorptionMass (cycle phase) :=
      htotalLe
    _ ≤ (Fintype.card ι : ℝ) *
        (-Real.log (quittingCyclicJointSurvivalMass cycle)) :=
      mul_le_mul_of_nonneg_left habsorptionLog (Nat.cast_nonneg _)
    _ = -(Fintype.card ι : ℝ) * Real.log
        (quittingCyclicJointSurvivalMass cycle) := by ring

omit [DecidableEq ι] in
/-- Every cyclic total hazard is nonnegative. -/
theorem quittingCyclicTotalHazard_nonneg
    {K : ℕ} (cycle : Fin K → ι → PMF Bool) :
    0 ≤ quittingCyclicTotalHazard cycle := by
  unfold quittingCyclicTotalHazard
  positivity

/-- If one selected player's own and opponent absorption both vanish, then
the total displayed hazard vanishes.  The periods may vary. -/
theorem tendsto_zero_quittingCyclicTotalHazard_of_player_and_opponents
    (period : ℕ → ℕ)
    (cycle : ∀ n, Fin (period n + 1) → ι → PMF Bool)
    (who : ι)
    (hcontinue : ∀ n phase player,
      0 < (cycle n phase player false).toReal)
    (hopponents : Tendsto (fun n ↦
      quittingCyclicOpponentAbsorptionMass (cycle n) who)
      atTop (nhds 0))
    (hplayer : Tendsto (fun n ↦
      quittingCyclicPlayerAbsorptionMass (cycle n) who)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ quittingCyclicTotalHazard (cycle n))
      atTop (nhds 0) := by
  have hopponentSurvival : Tendsto (fun n ↦
      1 - quittingCyclicOpponentAbsorptionMass (cycle n) who)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hopponents
  have hplayerSurvival : Tendsto (fun n ↦
      1 - quittingCyclicPlayerAbsorptionMass (cycle n) who)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hplayer
  have hjoint : Tendsto (fun n ↦
      quittingCyclicJointSurvivalMass (cycle n)) atTop (nhds 1) := by
    have hproduct := hopponentSurvival.mul hplayerSurvival
    simpa only [one_mul] using hproduct.congr'
      (Filter.Eventually.of_forall fun n ↦
        (quittingCyclicJointSurvivalMass_eq_opponents_mul_player
          (cycle n) who).symm)
  have hlog : Tendsto (fun n ↦
      -(Fintype.card ι : ℝ) * Real.log
        (quittingCyclicJointSurvivalMass (cycle n))) atTop (nhds 0) := by
    have hlogRaw :=
      (Real.continuousAt_log one_ne_zero).tendsto.comp hjoint
    simpa using hlogRaw.const_mul (-(Fintype.card ι : ℝ))
  apply squeeze_zero
  · exact fun n ↦ quittingCyclicTotalHazard_nonneg (cycle n)
  · exact fun n ↦
      quittingCyclicTotalHazard_le_neg_card_mul_log_jointSurvival
        (cycle n) (hcontinue n)
  · exact hlog

end GameTheory
