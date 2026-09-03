/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.UnitBoundedBoundaryPayoffTransport

/-!
# Positive-singleton estimates on arbitrary path boundary cells

Sequential perfection for one player bounds the payoff before any nonterminal
boundary cell whose singleton coordinate increases.  The estimate uses only
unit-bounded total mass and the two literal endpoints of the cell.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If one player's singleton coordinate increases between two nonterminal
path boundaries, that player's payoff before the first boundary is at most
the singleton reward, the sequential-perfection error, and the local
`6 M p` absorption error. -/
theorem absorptionPathPreBoundaryPayoff_le_singletonReward_add_error_add_six_mul_cellAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path)
    (player : ι) (error : ℝ)
    (hperfect : IsPlayerSequentiallyPerfectAbsorptionPath
      reward path player error)
    {start stop : ℝ}
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hstopBoundary : stop ∈ partitionBoundaryTimes path)
    (hstartStop : start < stop) (hstopOne : stop < 1)
    (hincrement : path.1.leftValue start
        ⟨{player}, Finset.singleton_nonempty player⟩ <
      path.1.leftValue stop
        ⟨{player}, Finset.singleton_nonempty player⟩) :
    absorptionPathPreBoundaryPayoff reward path start player ≤
      reward (quittingSingletonTerminal player) player + error +
        6 * quittingRewardBound reward *
          pathCellAbsorption path.1 start stop := by
  let p := pathCellAbsorption path.1 start stop
  let M := quittingRewardBound reward
  let singleton : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  have hstartMem : start ∈ Icc (0 : ℝ) 1 :=
    hstartBoundary.elim And.left And.left
  have hstopMem : stop ∈ Icc (0 : ℝ) 1 :=
    hstopBoundary.elim And.left And.left
  have hstartOne : start < 1 := hstartStop.trans hstopOne
  have hpNonneg : 0 ≤ p := by
    unfold p pathCellAbsorption
    exact div_nonneg
      (sub_nonneg.mpr (pathLeftTotal_mono path.1 hstartMem hstopMem
        hstartStop.le))
      (sub_nonneg.mpr hstartOne.le)
  have hMNonneg : 0 ≤ M := quittingRewardBound_nonneg reward
  rcases exists_positiveSingletonJump_or_pathTimeRightDerivative_pos path
      hbounded hstartMem hstopMem hstartStop player hincrement with
    hjump | hcontinuous
  · obtain ⟨time, htimeCell, hsingletonJump⟩ := hjump
    have htimeMem : time ∈ Icc (0 : ℝ) 1 :=
      ⟨hstartMem.1.trans htimeCell.1, htimeCell.2.le.trans hstopMem.2⟩
    have htimeOne : time < 1 := htimeCell.2.trans hstopOne
    have htimeJump : time ∈ pathJumps path.1 :=
      ⟨htimeMem, singleton, ne_of_gt hsingletonJump⟩
    have htimeBoundary : time ∈ partitionBoundaryTimes path :=
      Or.inl htimeJump
    have htimeLeStop : time ≤ stop := htimeCell.2.le
    have htimeTotal : pathTotal path.1 time < 1 := by
      have hle := pathTotal_le_pathLeftTotal_of_lt path.1
        htimeMem hstopMem htimeCell.2
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
        hstopBoundary] at hle
      exact hle.trans_lt hstopOne
    let partialAbsorption := pathCellAbsorption path.1 start time
    have hpartialLe : partialAbsorption ≤ p := by
      unfold partialAbsorption p pathCellAbsorption
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path htimeBoundary,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstartBoundary,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary]
      exact (div_le_div_iff_of_pos_right (sub_pos.mpr hstartOne)).2 <| by
        linarith [htimeLeStop]
    have htransport :=
      abs_absorptionPathPreBoundaryPayoff_sub_le_two_mul_pathCellAbsorption_of_unitBounded
        reward path hbounded hstartMem htimeMem htimeCell.1
        hstartBoundary htimeBoundary hstartOne htimeOne player
    have hpreEq :=
      absorptionPathPreBoundaryPayoff_eq_jumpRootSuccessorPayoff_of_unitBounded
        reward path hbounded htimeJump htimeTotal
    have hrow := hperfect.1 time htimeJump htimeTotal
    have hsingletonMass : 0 < quittingRootCoalitionMass
        (absorptionPathJumpRoot path time) {player} := by
      rw [copiedJumpRoot_coalitionMass path htimeJump singleton]
      exact div_pos hsingletonJump (sub_pos.mpr htimeOne)
    have hquitProbability : 0 <
        ((absorptionPathJumpRoot path time) player true).toReal :=
      hsingletonMass.trans_le
        (quittingRootCoalitionMass_le_quitProbability_of_mem
          (absorptionPathJumpRoot path time) {player} player (by simp))
    have hquitUsed :
        (absorptionPathJumpRoot path time) player true ≠ 0 := by
      intro hzero
      simp [hzero] at hquitProbability
    have hsuccessorLeQuitAddError :
        quittingRootSuccessorPayoff reward
            (absorptionPathPayoff reward path time)
            (absorptionPathJumpRoot path time) player ≤
          quittingRootQuitPayoff reward
              (absorptionPathPayoff reward path time)
              (absorptionPathJumpRoot path time) player + error := by
      have hsupport := hrow.2.2.1 hquitUsed
      linarith
    have hquitError :=
      abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
        reward (absorptionPathPayoff reward path time)
        (absorptionPathJumpRoot path time) player M
        (abs_reward_le_quittingRewardBound reward)
    have habsorptionLe : quittingRootAbsorptionMass
        (absorptionPathJumpRoot path time) ≤ p :=
      absorptionPathJumpRoot_absorption_le_enclosingBoundaryCell path
        hbounded hstartBoundary hstopBoundary hstartOne htimeJump htimeCell
    have hopponentLe : quittingRootOpponentAbsorptionMass
        (absorptionPathJumpRoot path time) player ≤ p :=
      (quittingRootOpponentAbsorptionMass_le_absorptionMass _ _).trans
        habsorptionLe
    have hfactor : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMNonneg
    change absorptionPathPreBoundaryPayoff reward path start player ≤
      reward (quittingSingletonTerminal player) player + error + 6 * M * p
    have htransportUpper :
        absorptionPathPreBoundaryPayoff reward path start player ≤
          absorptionPathPreBoundaryPayoff reward path time player +
            2 * M * partialAbsorption := by
      linarith [le_of_abs_le htransport]
    have hquitUpper : quittingRootQuitPayoff reward
        (absorptionPathPayoff reward path time)
        (absorptionPathJumpRoot path time) player ≤
      reward (quittingSingletonTerminal player) player + 2 * M * p := by
      have hraw := le_of_abs_le hquitError
      nlinarith [mul_le_mul_of_nonneg_left hopponentLe hfactor]
    rw [hpreEq] at htransportUpper
    nlinarith [mul_le_mul_of_nonneg_left hpartialLe hfactor,
      hsuccessorLeQuitAddError, hquitUpper]
  · obtain ⟨time, htimeCell, htimePath, hderivative⟩ := hcontinuous
    have htimeMem : time ∈ Icc (0 : ℝ) 1 := htimePath.1
    have htimeOne : time < 1 := htimeCell.2.trans hstopOne
    have htimeBoundary : time ∈ partitionBoundaryTimes path :=
      Or.inr htimePath
    have htimeLeStop : time ≤ stop := htimeCell.2.le
    have htimeTotal : pathTotal path.1 time < 1 := by
      have hle := pathTotal_le_pathLeftTotal_of_lt path.1
        htimeMem hstopMem htimeCell.2
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
        hstopBoundary] at hle
      exact hle.trans_lt hstopOne
    let partialAbsorption := pathCellAbsorption path.1 start time
    have hpartialLe : partialAbsorption ≤ p := by
      unfold partialAbsorption p pathCellAbsorption
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path htimeBoundary,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstartBoundary,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary]
      exact (div_le_div_iff_of_pos_right (sub_pos.mpr hstartOne)).2 <| by
        linarith [htimeLeStop]
    have htransport :=
      abs_absorptionPathPreBoundaryPayoff_sub_le_two_mul_pathCellAbsorption_of_unitBounded
        reward path hbounded hstartMem htimeMem htimeCell.1
        hstartBoundary htimeBoundary hstartOne htimeOne player
    have hpathUpper : absorptionPathPayoff reward path time player ≤
        reward (quittingSingletonTerminal player) player + error := by
      have hraw := hperfect.2 time htimePath htimeOne.ne
      have hupper := hraw.2 (by simpa only [singleton] using hderivative)
      simpa [quittingSingletonTerminal] using hupper
    have hpreUpper : absorptionPathPreBoundaryPayoff reward path time player ≤
        absorptionPathPayoff reward path time player + 2 * M * p := by
      by_cases htimeJump : time ∈ pathJumps path.1
      · have hpreEq :=
          absorptionPathPreBoundaryPayoff_eq_jumpRootSuccessorPayoff_of_unitBounded
            reward path hbounded htimeJump htimeTotal
        have htailBound : |absorptionPathPayoff reward path time player| ≤
            M := by
          unfold absorptionPathPayoff
          rw [if_pos htimeMem, if_pos htimeTotal]
          let weight := fun terminal : {S : Finset ι // S.Nonempty} ↦
            (path.1.value 1 terminal - path.1.value time terminal) /
              (1 - pathTotal path.1 time)
          have hweightNonneg (terminal : {S : Finset ι // S.Nonempty}) :
              0 ≤ weight terminal := by
            exact div_nonneg
              (sub_nonneg.mpr (path.1.monotone terminal htimeMem
                (by norm_num) htimeMem.2))
              (sub_nonneg.mpr htimeTotal.le)
          have htotalOne : pathTotal path.1 1 = 1 :=
            pathTotal_one_eq_one_of_unitBoundedTotalMass path hbounded
          have hweightSum : (∑ terminal, weight terminal) = 1 := by
            unfold weight
            rw [← Finset.sum_div, Finset.sum_sub_distrib]
            change (pathTotal path.1 1 - pathTotal path.1 time) /
              (1 - pathTotal path.1 time) = 1
            rw [htotalOne]
            exact div_self (ne_of_gt (sub_pos.mpr htimeTotal))
          rw [Finset.sum_div]
          calc
            |∑ terminal, ((path.1.value 1 terminal -
                path.1.value time terminal) * reward terminal player) /
                  (1 - pathTotal path.1 time)| =
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
            _ ≤ ∑ terminal, weight terminal * M := by
              apply Finset.sum_le_sum
              intro terminal _
              exact mul_le_mul_of_nonneg_left
                (abs_reward_le_quittingRewardBound reward terminal player)
                (hweightNonneg terminal)
            _ = M := by rw [← Finset.sum_mul, hweightSum, one_mul]
        have hsuccessorError :=
          abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
            reward (absorptionPathPayoff reward path time)
            (absorptionPathJumpRoot path time) player M
            (abs_reward_le_quittingRewardBound reward) htailBound
        have habsorptionLe : quittingRootAbsorptionMass
            (absorptionPathJumpRoot path time) ≤ p :=
          absorptionPathJumpRoot_absorption_le_enclosingBoundaryCell path
            hbounded hstartBoundary hstopBoundary hstartOne htimeJump
            htimeCell
        have hfactor : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMNonneg
        rw [hpreEq]
        nlinarith [le_of_abs_le hsuccessorError,
          mul_le_mul_of_nonneg_left habsorptionLe hfactor]
      · rw [absorptionPathPreBoundaryPayoff_eq_absorptionPathPayoff_of_pathTime_not_jump
          reward path htimePath htimeOne.ne htimeJump]
        exact le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (by norm_num) hMNonneg) hpNonneg)
    change absorptionPathPreBoundaryPayoff reward path start player ≤
      reward (quittingSingletonTerminal player) player + error + 6 * M * p
    have htransportUpper :
        absorptionPathPreBoundaryPayoff reward path start player ≤
          absorptionPathPreBoundaryPayoff reward path time player +
            2 * M * partialAbsorption := by
      linarith [le_of_abs_le htransport]
    have hfactor : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMNonneg
    nlinarith [mul_le_mul_of_nonneg_left hpartialLe hfactor,
      hpreUpper, hpathUpper]

end GameTheory.QuittingAbsorptionPath
