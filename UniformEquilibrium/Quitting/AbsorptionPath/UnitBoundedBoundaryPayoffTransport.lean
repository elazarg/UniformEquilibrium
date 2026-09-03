/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.AKRSSequentialPerfectionDecoder
import UniformEquilibrium.Quitting.AbsorptionPath.WeakPathConvergence

/-!
# Payoff transport between unit-bounded path boundaries

The existing arbitrary-boundary payoff identities only need terminal
coordinate continuity at clock one.  Unit-bounded total mass supplies that
continuity directly, without a global no-terminal-jump hypothesis.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The payoff immediately before a nonterminal boundary of a unit-bounded
path lies in the coordinate reward box. -/
theorem abs_absorptionPathPreBoundaryPayoff_le_rewardBound_of_unitBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path)
    {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    (hboundary : time ∈ partitionBoundaryTimes path)
    (htimeOne : time < 1) (player : ι) :
    |absorptionPathPreBoundaryPayoff reward path time player| ≤
      quittingRewardBound reward := by
  let weight := fun terminal : {S : Finset ι // S.Nonempty} ↦
    (path.1.value 1 terminal - path.1.leftValue time terminal) /
      (1 - time)
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hleftTotal : pathLeftTotal path.1 time = time :=
    pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hboundary
  have htotalOne : pathTotal path.1 1 = 1 :=
    pathTotal_one_eq_one_of_unitBoundedTotalMass path hbounded
  have hweightNonneg (terminal : {S : Finset ι // S.Nonempty}) :
      0 ≤ weight terminal := by
    apply div_nonneg
    · have hmono := path.1.leftValue_mono terminal htime hone htime.2
      rw [← value_one_eq_leftValue_one_of_unitBoundedTotalMass path
        hbounded terminal] at hmono
      exact sub_nonneg.mpr hmono
    · exact (sub_pos.mpr htimeOne).le
  have hweightSum : (∑ terminal, weight terminal) = 1 := by
    unfold weight
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    change (pathTotal path.1 1 - pathLeftTotal path.1 time) /
      (1 - time) = 1
    rw [htotalOne, hleftTotal]
    exact div_self (ne_of_gt (sub_pos.mpr htimeOne))
  unfold absorptionPathPreBoundaryPayoff
  rw [Finset.sum_div]
  calc
    |∑ terminal, ((path.1.value 1 terminal -
        path.1.leftValue time terminal) * reward terminal player) /
          (1 - time)| =
        |∑ terminal, weight terminal * reward terminal player| := by
      congr 1
      apply Finset.sum_congr rfl
      intro terminal _
      unfold weight
      ring
    _ ≤ ∑ terminal, |weight terminal * reward terminal player| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ terminal, weight terminal * |reward terminal player| := by
      apply Finset.sum_congr rfl
      intro terminal _
      rw [abs_mul, abs_of_nonneg (hweightNonneg terminal)]
    _ ≤ ∑ terminal, weight terminal * quittingRewardBound reward := by
      apply Finset.sum_le_sum
      intro terminal _
      exact mul_le_mul_of_nonneg_left
        (abs_reward_le_quittingRewardBound reward terminal player)
        (hweightNonneg terminal)
    _ = quittingRewardBound reward := by
      rw [← Finset.sum_mul, hweightSum, one_mul]

/-- Ordered nonterminal boundaries of a unit-bounded path satisfy the local
`2 M p` payoff-transport estimate. -/
theorem abs_absorptionPathPreBoundaryPayoff_sub_le_two_mul_pathCellAbsorption_of_unitBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path)
    {start stop : ℝ} (hstart : start ∈ Icc (0 : ℝ) 1)
    (hstop : stop ∈ Icc (0 : ℝ) 1) (hstartStop : start ≤ stop)
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hstopBoundary : stop ∈ partitionBoundaryTimes path)
    (hstartOne : start < 1) (hstopOne : stop < 1) (player : ι) :
    |absorptionPathPreBoundaryPayoff reward path start player -
        absorptionPathPreBoundaryPayoff reward path stop player| ≤
      2 * quittingRewardBound reward *
        pathCellAbsorption path.1 start stop := by
  let p := pathCellAbsorption path.1 start stop
  let current := absorptionPathPreBoundaryPayoff reward path start player
  let next := absorptionPathPreBoundaryPayoff reward path stop player
  let contribution :=
    ∑ terminal : {S : Finset ι // S.Nonempty},
      pathCellLaw path.1 start stop terminal.1 * reward terminal player
  have hbellman : current = contribution + (1 - p) * next :=
    absorptionPathPreBoundaryPayoff_boundaryCell_eq reward path
      hstartBoundary hstopBoundary hstartOne hstopOne player
  have hcontribution : |contribution| ≤ quittingRewardBound reward * p :=
    abs_pathBoundaryCellAbsorbingContribution_le reward path hstart hstop
      hstartStop hstartOne player
  have hnext : |next| ≤ quittingRewardBound reward :=
    abs_absorptionPathPreBoundaryPayoff_le_rewardBound_of_unitBounded
      reward path hbounded hstop hstopBoundary hstopOne player
  have hpNonneg : 0 ≤ p := by
    unfold p pathCellAbsorption
    exact div_nonneg
      (sub_nonneg.mpr (pathLeftTotal_mono path.1 hstart hstop hstartStop))
      (sub_nonneg.mpr hstartOne.le)
  change |current - next| ≤ 2 * quittingRewardBound reward * p
  rw [hbellman]
  have hrearrange : contribution + (1 - p) * next - next =
      contribution - p * next := by ring
  rw [hrearrange]
  calc
    |contribution - p * next| ≤ |contribution| + |p * next| :=
      abs_sub _ _
    _ ≤ quittingRewardBound reward * p +
        p * quittingRewardBound reward := by
      apply add_le_add hcontribution
      rw [abs_mul, abs_of_nonneg hpNonneg]
      exact mul_le_mul_of_nonneg_left hnext hpNonneg
    _ = 2 * quittingRewardBound reward * p := by ring

/-- At a nonterminal jump of a unit-bounded path, the pre-jump payoff is the
successor payoff of the literal normalized jump row and its post-jump tail. -/
theorem absorptionPathPreBoundaryPayoff_eq_jumpRootSuccessorPayoff_of_unitBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path)
    {time : ℝ} (htime : time ∈ pathJumps path.1)
    (htotal : pathTotal path.1 time < 1) :
    absorptionPathPreBoundaryPayoff reward path time =
      quittingRootSuccessorPayoff reward
        (absorptionPathPayoff reward path time)
        (absorptionPathJumpRoot path time) := by
  have htimeOne : time < 1 :=
    (lt_pathTotal_of_mem_pathJumps path htime).trans htotal
  have hleftTotal : pathLeftTotal path.1 time = time :=
    pathLeftTotal_eq_of_mem_pathJumps path htime
  have htotalBoundary : pathTotal path.1 time ∈
      partitionBoundaryTimes path :=
    pathTotal_mem_partitionBoundaryTimes path hbounded htime.1
  have habsorption : quittingRootAbsorptionMass
      (absorptionPathJumpRoot path time) =
        (pathTotal path.1 time - time) / (1 - time) := by
    rw [copiedJumpRoot_absorption_eq_pathCellAbsorption path hbounded
      htime rfl]
    unfold pathCellAbsorption
    rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path htotalBoundary,
      hleftTotal]
  have hcontribution (player : ι) :
      quittingRootAbsorbingContribution reward
          (absorptionPathJumpRoot path time) player =
        (∑ terminal : {S : Finset ι // S.Nonempty},
          pathJump path.1 time terminal * reward terminal player) /
            (1 - time) := by
    rw [quittingRootAbsorbingContribution_eq_sum_nonemptyCoalitionMass]
    change (∑ terminal : {S : Finset ι // S.Nonempty},
      quittingRootCoalitionMass (absorptionPathJumpRoot path time)
        terminal.1 * reward terminal player) = _
    simp_rw [copiedJumpRoot_coalitionMass path htime]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro terminal _
    ring
  funext player
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    hcontribution player]
  rw [show quittingStationaryContinueMass
      (absorptionPathJumpRoot path time) =
        1 - quittingRootAbsorptionMass
          (absorptionPathJumpRoot path time) by
    unfold quittingRootAbsorptionMass
    ring]
  rw [habsorption]
  unfold absorptionPathPreBoundaryPayoff absorptionPathPayoff
  rw [if_pos htime.1, if_pos htotal]
  have htimeDenom : 1 - time ≠ 0 := ne_of_gt (sub_pos.mpr htimeOne)
  have htotalDenom : 1 - pathTotal path.1 time ≠ 0 :=
    ne_of_gt (sub_pos.mpr htotal)
  simp_rw [show ∀ terminal : {S : Finset ι // S.Nonempty},
      pathJump path.1 time terminal =
        path.1.value time terminal - path.1.leftValue time terminal from
    fun _ ↦ rfl]
  simp_rw [Finset.sum_div]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro terminal _
  field_simp [htimeDenom, htotalDenom]
  ring

end GameTheory.QuittingAbsorptionPath
