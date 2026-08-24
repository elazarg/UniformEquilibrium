/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedWitnessRegimes
import UniformEquilibrium.Quitting.Classification.LCP.StationaryEquilibrium
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Deleted-clock compactification of stationary prefixes

A stationarily generated witness repeats one product root through a finite
prefix and then changes to a punishment sequence.  Replacing that switched
sequence by the stationary repetition changes prescribed payoff only on the
joint-survival event.  Against a unilateral behavioral deviation, the change
is controlled instead by that player's deleted, or opponent, survival clock.

Consequently, if every deleted clock through a vanishing-error family's actual
prefix tends to zero, the repeated roots themselves form stationary
approximate equilibria at every positive accuracy.  This is a genuine `S.1`
producer.  It does not cover the exceptional-owner regime in which one
player's deleted clock remains positive.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A Nash bound for a finite stationary prefix transports to the stationary
repetition when all player-deleted survival probabilities through the prefix
have one common upper bound.  The conclusion still covers arbitrary
time-dependent hazards, hence arbitrary behavioral deviations. -/
theorem isεQuittingStationaryNash_of_stationaryPrefixNash_of_deletedSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (horizon : ℕ)
    (punishment : ℕ → ι → PMF Bool) {error survivalCap : ℝ}
    (hnash : IsεQuittingRootSequenceNash reward error
      (quittingStationaryPrefixThenRoots root horizon punishment))
    (hsurvival : ∀ who,
      quittingOpponentSurvivalWeight (fun _ ↦ root) who 0 (horizon + 1) ≤
        survivalCap) :
    IsεQuittingStationaryNash reward
      (error + 4 * quittingRewardBound reward * survivalCap) root := by
  let switched := quittingStationaryPrefixThenRoots root horizon punishment
  let stationary : ℕ → ι → PMF Bool := fun _ ↦ root
  have hprefix : ∀ time, time < horizon + 1 → switched time = stationary time := by
    intro time htime
    dsimp only [switched, stationary]
    exact quittingStationaryPrefixThenRoots_of_le root horizon punishment
      (by omega : time ≤ horizon)
  have hrootNash : IsεQuittingRootSequenceNash reward
      (error + 4 * quittingRewardBound reward * survivalCap) stationary := by
    intro who hazard
    have hreward : ∀ terminal player,
        |reward terminal player| ≤ quittingRewardBound reward :=
      abs_reward_le_quittingRewardBound reward
    have hdeviation :=
      abs_quittingRootSequenceHazardTerminalValue_sub_le_of_prefix_eq
        reward switched stationary who hazard (horizon + 1) hreward hprefix
    have hprescribed :=
      abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq
        reward switched stationary who (horizon + 1) hreward hprefix
    have hjoint : quittingJointSurvivalWeight stationary 0 (horizon + 1) ≤
        survivalCap :=
      (quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
        stationary who 0 (horizon + 1)).trans (hsurvival who)
    have hbound := quittingRewardBound_nonneg reward
    have hdeviation' :
        quittingRootSequenceHazardTerminalValue reward stationary who hazard 0 ≤
          quittingRootSequenceHazardTerminalValue reward switched who hazard 0 +
            2 * quittingRewardBound reward * survivalCap := by
      have habs := neg_le_of_abs_le hdeviation
      have hscaled : 2 * quittingRewardBound reward *
            quittingOpponentSurvivalWeight stationary who 0 (horizon + 1) ≤
          2 * quittingRewardBound reward * survivalCap :=
        mul_le_mul_of_nonneg_left (hsurvival who)
          (mul_nonneg (by norm_num) hbound)
      linarith
    have hprescribed' :
        quittingRootSequenceTerminalValue reward switched who 0 ≤
          quittingRootSequenceTerminalValue reward stationary who 0 +
            2 * quittingRewardBound reward * survivalCap := by
      have habs := le_of_abs_le hprescribed
      have hscaled : 2 * quittingRewardBound reward *
            quittingJointSurvivalWeight stationary 0 (horizon + 1) ≤
          2 * quittingRewardBound reward * survivalCap :=
        mul_le_mul_of_nonneg_left hjoint
          (mul_nonneg (by norm_num) hbound)
      linarith
    linarith [hnash who hazard]
  apply (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward _ stationary).mp
    at hrootNash
  have hprofile : quittingRootSequenceProfile reward stationary 0 =
      quittingStationaryProfile reward root := rfl
  rw [hprofile] at hrootNash
  exact hrootNash

/-- Vanishing deleted clocks through the actual stationary-prefix witnesses
produce the stationary branch at every positive accuracy. -/
theorem quittingStationaryεEquilibriumExistence_of_stationaryPrefix_deletedClocks
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (hdeleted : ∀ who, Tendsto
      (fun n ↦ quittingOpponentSurvivalWeight
        (fun _ ↦ family.root (subsequence n)) who 0
          (family.horizon (subsequence n) + 1)) atTop (nhds 0)) :
    QuittingStationaryεEquilibriumExistence reward := by
  intro target htarget
  let sourceError : ℕ → ℝ := fun n ↦ 2 * family.error (subsequence n)
  have hsourceError : Tendsto sourceError atTop (nhds 0) := by
    simpa [sourceError] using tendsto_const_nhds.mul
      (family.error_tendsto_zero.comp hsubsequence.tendsto_atTop)
  let survivalCap := target / (8 * (quittingRewardBound reward + 1))
  have hbound := quittingRewardBound_nonneg reward
  have hdenom : 0 < 8 * (quittingRewardBound reward + 1) := by positivity
  have hcap : 0 < survivalCap := div_pos htarget hdenom
  have herrorSmall : ∀ᶠ n in atTop, sourceError n < target / 2 :=
    (tendsto_order.1 hsourceError).2 (target / 2) (half_pos htarget)
  have hdeletedSmall : ∀ᶠ n in atTop, ∀ who,
      quittingOpponentSurvivalWeight
        (fun _ ↦ family.root (subsequence n)) who 0
          (family.horizon (subsequence n) + 1) < survivalCap := by
    apply Filter.eventually_all.mpr
    intro who
    exact (tendsto_order.1 (hdeleted who)).2 survivalCap hcap
  obtain ⟨n, herrorN, hdeletedN⟩ :=
    (herrorSmall.and hdeletedSmall).exists
  have htransport :=
    isεQuittingStationaryNash_of_stationaryPrefixNash_of_deletedSurvival
      reward (family.root (subsequence n)) (family.horizon (subsequence n))
        (family.punishment (subsequence n)) (family.nash (subsequence n))
        (fun who ↦ (hdeletedN who).le)
  have hsurvivalCost :
      4 * quittingRewardBound reward * survivalCap < target / 2 := by
    have hfactor : quittingRewardBound reward <
        quittingRewardBound reward + 1 := by linarith
    have hscalePos : 0 < 4 * survivalCap := mul_pos (by norm_num) hcap
    have hscaled : 4 * survivalCap * quittingRewardBound reward <
        4 * survivalCap * (quittingRewardBound reward + 1) :=
      mul_lt_mul_of_pos_left hfactor hscalePos
    have heq : 4 * (quittingRewardBound reward + 1) * survivalCap =
        target / 2 := by
      dsimp only [survivalCap]
      field_simp
      ring
    nlinarith
  refine ⟨family.root (subsequence n), htransport.mono ?_⟩
  dsimp only [sourceError] at herrorN
  linarith

end GameTheory
