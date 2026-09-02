/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.AKRSPartitionDecoder
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound
import UniformEquilibrium.Quitting.Root.BoundedEndpoint

/-!
# Sequential-perfection estimates for the AKRS partition decoder

This module proves the literal local estimates corresponding to published
bounds (20)--(22).  In particular, positive singleton mass is transported to
either a supported jump or a positive continuous-clock rate, and hence to the
reverse entrance estimate used by the support decoder.  The final existence
consumer belongs to the classification layer.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Topology
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingAbsorptionPath

omit [Nonempty ι] in
/-- The path payoff immediately before every finite partition cut stays in
the coordinate reward box. -/
theorem abs_absorptionPathPreBoundaryPayoff_partitionCut_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    (stage : ℕ) (player : ι) :
    |absorptionPathPreBoundaryPayoff reward path
        (partitionCut path resolution stage) player| ≤
      quittingRewardBound reward := by
  let time := partitionCut path resolution stage
  let weight := fun terminal : {S : Finset ι // S.Nonempty} =>
    (path.1.value 1 terminal - path.1.leftValue time terminal) / (1 - time)
  have hresolutionOne : 1 ≤ resolution := by omega
  have htimeMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne stage
  have htimeOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolution stage
  have htimeBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne stage
  have hleftTotal : pathLeftTotal path.1 time = time :=
    pathLeftTotal_eq_of_mem_partitionBoundaryTimes path htimeBoundary
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have htotalOne : pathTotal path.1 1 = 1 := by
    exact le_antisymm (hpathTotal 1 hone) (path.property.1 1 hone)
  have hweightNonneg (terminal : {S : Finset ι // S.Nonempty}) :
      0 ≤ weight terminal := by
    apply div_nonneg
    · have hmono := path.1.leftValue_mono terminal htimeMem hone htimeMem.2
      rw [← value_one_eq_leftValue_one_of_noTerminalTotalJump path hpathTotal
        hnoTerminalJump terminal] at hmono
      exact sub_nonneg.mpr hmono
    · exact (sub_pos.mpr htimeOne).le
  have hweightSum : (∑ terminal, weight terminal) = 1 := by
    unfold weight
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    change (pathTotal path.1 1 - pathLeftTotal path.1 time) / (1 - time) = 1
    rw [htotalOne, hleftTotal]
    exact div_self (ne_of_gt (sub_pos.mpr htimeOne))
  unfold absorptionPathPreBoundaryPayoff
  simp_rw [Finset.sum_div]
  calc
    |∑ terminal,
        ((path.1.value 1 terminal - path.1.leftValue
            (partitionCut path resolution stage) terminal) *
          reward terminal player) /
            (1 - partitionCut path resolution stage)| =
        |∑ terminal, weight terminal * reward terminal player| := by
      congr 1
      apply Finset.sum_congr rfl
      intro terminal _
      unfold weight time
      ring
    _ ≤
        ∑ terminal, |weight terminal * reward terminal player| := by
      simpa only using Finset.abs_sum_le_sum_abs
        (fun terminal : {S : Finset ι // S.Nonempty} =>
          weight terminal * reward terminal player) Finset.univ
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

omit [Nonempty ι] in
/-- The literal pre-boundary payoff satisfies the exact Bellman identity
across every selected partition cell. -/
theorem absorptionPathPreBoundaryPayoff_partitionCell_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    (stage : ℕ) (player : ι) :
    absorptionPathPreBoundaryPayoff reward path
        (partitionCut path resolution stage) player =
      partitionPathCellAbsorbingContribution reward path resolution stage
          player +
        (1 - pathCellAbsorption path.1
          (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1))) *
        absorptionPathPreBoundaryPayoff reward path
          (partitionCut path resolution (stage + 1)) player := by
  let start := partitionCut path resolution stage
  let stop := partitionCut path resolution (stage + 1)
  have hresolutionOne : 1 ≤ resolution := by omega
  have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne stage
  have hstopBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne (stage + 1)
  have hstartOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolution stage
  have hstopOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolution (stage + 1)
  have hsurvival := one_sub_pathCellAbsorption_of_boundaries path
    hstartBoundary hstopBoundary hstartOne
  unfold absorptionPathPreBoundaryPayoff
    partitionPathCellAbsorbingContribution
  simp_rw [pathCellLaw_nonempty]
  rw [hsurvival]
  simp_rw [Finset.sum_div]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro terminal _
  have hstartDenom : 1 - start ≠ 0 := ne_of_gt (sub_pos.mpr hstartOne)
  have hstopDenom : 1 - stop ≠ 0 := ne_of_gt (sub_pos.mpr hstopOne)
  dsimp only [start, stop] at hstartDenom hstopDenom ⊢
  field_simp
  ring

omit [Nonempty ι] in
/-- The absolute absorbing payoff contribution of one selected path cell is
bounded by the reward box times that cell's conditional absorption. -/
theorem abs_partitionPathCellAbsorbingContribution_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    (stage : ℕ) (player : ι) :
    |partitionPathCellAbsorbingContribution reward path resolution stage
        player| ≤
      quittingRewardBound reward *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
  let start := partitionCut path resolution stage
  let stop := partitionCut path resolution (stage + 1)
  have hresolutionOne : 1 ≤ resolution := by omega
  have hstartMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne stage
  have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne (stage + 1)
  have hstartOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolution stage
  have hstartStop : start ≤ stop := by
    exact monotone_partitionCut path hpathTotal resolution hresolutionOne
      (Nat.le_succ stage)
  have hlawNonneg (terminal : {S : Finset ι // S.Nonempty}) :
      0 ≤ pathCellLaw path.1 start stop terminal.1 :=
    pathCellLaw_nonneg_of_nonempty path.1 hstartMem hstopMem hstartStop
      hstartOne terminal
  unfold partitionPathCellAbsorbingContribution
  calc
    |∑ terminal : {S : Finset ι // S.Nonempty},
        pathCellLaw path.1
            (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1)) terminal.1 *
          reward terminal player| ≤
        ∑ terminal : {S : Finset ι // S.Nonempty},
          |pathCellLaw path.1 start stop terminal.1 *
            reward terminal player| := by
      simpa only [start, stop] using Finset.abs_sum_le_sum_abs
        (fun terminal : {S : Finset ι // S.Nonempty} ↦
          pathCellLaw path.1 start stop terminal.1 *
            reward terminal player) Finset.univ
    _ = ∑ terminal : {S : Finset ι // S.Nonempty},
          pathCellLaw path.1 start stop terminal.1 *
            |reward terminal player| := by
      apply Finset.sum_congr rfl
      intro terminal _
      rw [abs_mul, abs_of_nonneg (hlawNonneg terminal)]
    _ ≤ ∑ terminal : {S : Finset ι // S.Nonempty},
          pathCellLaw path.1 start stop terminal.1 *
            quittingRewardBound reward := by
      apply Finset.sum_le_sum
      intro terminal _
      exact mul_le_mul_of_nonneg_left
        (abs_reward_le_quittingRewardBound reward terminal player)
        (hlawNonneg terminal)
    _ = quittingRewardBound reward *
        pathCellAbsorption path.1 start stop := by
      rw [← Finset.sum_mul, sum_pathCellLaw_nonempty]
      ring
    _ = quittingRewardBound reward *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by rfl

/-- Across a selected path cell, the two literal continuation payoffs differ
by at most twice the reward bound times conditional absorption.  This is the
pre-boundary part of the published local estimate (20). -/
theorem abs_absorptionPathPreBoundaryPayoff_partitionCut_sub_succ_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (stage : ℕ) (player : ι) :
    |absorptionPathPreBoundaryPayoff reward path
          (partitionCut path resolution stage) player -
        absorptionPathPreBoundaryPayoff reward path
          (partitionCut path resolution (stage + 1)) player| ≤
      2 * quittingRewardBound reward *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
  let p := pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  let current := absorptionPathPreBoundaryPayoff reward path
    (partitionCut path resolution stage) player
  let next := absorptionPathPreBoundaryPayoff reward path
    (partitionCut path resolution (stage + 1)) player
  let contribution := partitionPathCellAbsorbingContribution reward path
    resolution stage player
  have hbellman : current = contribution + (1 - p) * next := by
    exact absorptionPathPreBoundaryPayoff_partitionCell_eq reward path
      hpathTotal hnoTerminalJump resolution (by omega) stage player
  have hcontribution : |contribution| ≤ quittingRewardBound reward * p := by
    exact abs_partitionPathCellAbsorbingContribution_le reward path hpathTotal
      hnoTerminalJump resolution (by omega) stage player
  have hnext : |next| ≤ quittingRewardBound reward := by
    exact abs_absorptionPathPreBoundaryPayoff_partitionCut_le_rewardBound
      reward path hpathTotal hnoTerminalJump resolution (by omega)
      (stage + 1) player
  have hpNonneg : 0 ≤ p := by
    dsimp only [p]
    rw [← partitionCellRoot_absorption_exact path hpathTotal
      hnoTerminalJump resolution hresolution
      (hasPartitionSmallCellCollisionDomination path hpathTotal
        hnoTerminalJump resolution hresolution) stage]
    exact quittingRootAbsorptionMass_nonneg _
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

/-- At every decoded partition row, the pure-Quit endpoint differs from the
singleton reward by at most twice the reward bound times cell absorption. -/
theorem abs_partitionCellRoot_quitPayoff_sub_singletonReward_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (player : ι) :
    |quittingRootQuitPayoff reward
          (quittingRootSequenceTailVector reward
            (partitionCellRoots path hpathTotal hnoTerminalJump resolution
              hresolution hcollision) (stage + 1))
          (partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision stage) player -
        reward (quittingSingletonTerminal player) player| ≤
      2 * quittingRewardBound reward *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let root := roots stage
  let tail := quittingRootSequenceTailVector reward roots (stage + 1)
  let p := pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  have hbase :
      |quittingRootQuitPayoff reward tail root player -
          reward (quittingSingletonTerminal player) player| ≤
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass root player :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward tail root player (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
  have hopponent : quittingRootOpponentAbsorptionMass root player ≤ p := by
    exact (quittingRootOpponentAbsorptionMass_le_absorptionMass root player).trans_eq
      (partitionCellRoot_absorption_exact path hpathTotal hnoTerminalJump
        resolution hresolution hcollision stage)
  have hfactor : 0 ≤ 2 * quittingRewardBound reward :=
    mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
  change |quittingRootQuitPayoff reward tail root player -
      reward (quittingSingletonTerminal player) player| ≤
    2 * quittingRewardBound reward * p
  exact hbase.trans (mul_le_mul_of_nonneg_left hopponent hfactor)

/-- At every decoded partition row, the pure-Continue endpoint differs from
the actual decoded suffix by at most twice the reward bound times cell
absorption. -/
theorem abs_partitionCellRoot_continuePayoff_sub_tail_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (player : ι) :
    |quittingRootContinuePayoff reward
          (quittingRootSequenceTailVector reward
            (partitionCellRoots path hpathTotal hnoTerminalJump resolution
              hresolution hcollision) (stage + 1))
          (partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision stage) player -
        quittingRootSequenceTailVector reward
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) (stage + 1) player| ≤
      2 * quittingRewardBound reward *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let root := roots stage
  let tail := quittingRootSequenceTailVector reward roots (stage + 1)
  let p := pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  have htail : |tail player| ≤ quittingRewardBound reward := by
    exact abs_quittingRootSequenceTerminalValue_le reward roots player
      (stage + 1) (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  have hbase :=
    abs_quittingRootContinuePayoff_sub_tail_le_two_mul_opponentAbsorptionMass
      reward tail root player (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward) htail
  have hopponent : quittingRootOpponentAbsorptionMass root player ≤ p := by
    exact (quittingRootOpponentAbsorptionMass_le_absorptionMass root player).trans_eq
      (partitionCellRoot_absorption_exact path hpathTotal hnoTerminalJump
        resolution hresolution hcollision stage)
  have hfactor : 0 ≤ 2 * quittingRewardBound reward :=
    mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
  change |quittingRootContinuePayoff reward tail root player - tail player| ≤
    2 * quittingRewardBound reward * p
  exact hbase.trans (mul_le_mul_of_nonneg_left hopponent hfactor)

/-- At every decoded partition row, its prescribed mixed payoff differs
from the actual decoded suffix by at most twice the reward bound times cell
absorption. -/
theorem abs_partitionCellRoot_successorPayoff_sub_tail_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (player : ι) :
    |quittingRootSuccessorPayoff reward
          (quittingRootSequenceTailVector reward
            (partitionCellRoots path hpathTotal hnoTerminalJump resolution
              hresolution hcollision) (stage + 1))
          (partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision stage) player -
        quittingRootSequenceTailVector reward
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) (stage + 1) player| ≤
      2 * quittingRewardBound reward *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let root := roots stage
  let tail := quittingRootSequenceTailVector reward roots (stage + 1)
  let p := pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  have htail : |tail player| ≤ quittingRewardBound reward := by
    exact abs_quittingRootSequenceTerminalValue_le reward roots player
      (stage + 1) (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  have hbase := abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
    reward tail root player (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward) htail
  have habsorption : quittingRootAbsorptionMass root = p :=
    partitionCellRoot_absorption_exact path hpathTotal hnoTerminalJump
      resolution hresolution hcollision stage
  change |quittingRootSuccessorPayoff reward tail root player - tail player| ≤
    2 * quittingRewardBound reward * p
  simpa only [habsorption] using hbase

omit [Nonempty ι] in
/-- At a literal path jump, the payoff immediately before the jump is exactly
the Bellman successor payoff of the copied jump root and the post-jump path
continuation. -/
theorem absorptionPathPreBoundaryPayoff_eq_jumpRootSuccessorPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    {time : ℝ} (htime : time ∈ pathJumps path.1) :
    absorptionPathPreBoundaryPayoff reward path time =
      quittingRootSuccessorPayoff reward
        (absorptionPathPayoff reward path time)
        (absorptionPathJumpRoot path time) := by
  have htimeOne : time < 1 :=
    (lt_pathTotal_of_mem_pathJumps path htime).trans_le
      (hpathTotal time htime.1)
  have htotalOne : pathTotal path.1 time < 1 :=
    hnoTerminalJump time htime
  have hleftTotal : pathLeftTotal path.1 time = time :=
    pathLeftTotal_eq_of_mem_pathJumps path htime
  have htotalBoundary : pathTotal path.1 time ∈
      partitionBoundaryTimes path :=
    pathTotal_mem_partitionBoundaryTimes path hpathTotal htime.1
  have habsorption : quittingRootAbsorptionMass
      (absorptionPathJumpRoot path time) =
        (pathTotal path.1 time - time) / (1 - time) := by
    rw [copiedJumpRoot_absorption_eq_pathCellAbsorption path hpathTotal
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
  rw [if_pos htime.1, if_pos htotalOne]
  have htimeDenom : 1 - time ≠ 0 := ne_of_gt (sub_pos.mpr htimeOne)
  have htotalDenom : 1 - pathTotal path.1 time ≠ 0 :=
    ne_of_gt (sub_pos.mpr htotalOne)
  have hjumpExpansion (terminal : {S : Finset ι // S.Nonempty}) :
      pathJump path.1 time terminal =
        path.1.value time terminal - path.1.leftValue time terminal := rfl
  simp_rw [hjumpExpansion]
  simp_rw [Finset.sum_div]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro terminal _
  field_simp [htimeDenom, htotalDenom]
  ring

omit [Nonempty ι] in
/-- At a continuous-clock boundary with no coordinate jump, the post-time
path payoff and the pre-boundary payoff coincide literally. -/
theorem absorptionPathPreBoundaryPayoff_eq_absorptionPathPayoff_of_pathTime_not_jump
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ pathTimes path.1)
    (htimeOne : time ≠ 1) (hnotJump : time ∉ pathJumps path.1) :
    absorptionPathPreBoundaryPayoff reward path time =
      absorptionPathPayoff reward path time := by
  have htimeLtOne : time < 1 := lt_of_le_of_ne htime.1.2 htimeOne
  have htotalOne : pathTotal path.1 time < 1 := by
    rw [htime.2]
    exact htimeLtOne
  have hcoordinate (terminal : {S : Finset ι // S.Nonempty}) :
      path.1.value time terminal = path.1.leftValue time terminal := by
    have hjumpZero : pathJump path.1 time terminal = 0 := by
      by_contra hne
      exact hnotJump ⟨htime.1, terminal, hne⟩
    unfold pathJump at hjumpZero
    linarith
  unfold absorptionPathPreBoundaryPayoff absorptionPathPayoff
  rw [if_pos htime.1, if_pos htotalOne, htime.2]
  funext player
  congr 1
  apply Finset.sum_congr rfl
  intro terminal _
  rw [hcoordinate terminal]

omit [Nonempty ι] in
/-- A jump at the entrance of a later left-limit cell contributes no more
conditional absorption than the whole cell. -/
theorem absorptionPathJumpRoot_absorption_le_pathCellAbsorption
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    {start stop : ℝ} (hstart : start ∈ pathJumps path.1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1) (hstartStop : start < stop) :
    quittingRootAbsorptionMass (absorptionPathJumpRoot path start) ≤
      pathCellAbsorption path.1 start stop := by
  have hstartOne : start < 1 := hstartStop.trans_le hstop.2
  have htotalLeLeft : pathTotal path.1 start ≤
      pathLeftTotal path.1 stop :=
    pathTotal_le_pathLeftTotal_of_lt path.1 hstart.1 hstop hstartStop
  rw [copiedJumpRoot_absorption_eq_pathCellAbsorption path hpathTotal
    hstart rfl]
  unfold pathCellAbsorption
  rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
      (pathTotal_mem_partitionBoundaryTimes path hpathTotal hstart.1),
    pathLeftTotal_eq_of_mem_pathJumps path hstart]
  exact (div_le_div_iff_of_pos_right (sub_pos.mpr hstartOne)).2 <| by
    linarith

omit [Nonempty ι] in
/-- Sequential perfection at the entrance boundary gives the published
singleton lower estimate, with the jump case paying only the local `2 M p`
endpoint error and the continuous no-jump case exact. -/
theorem singletonReward_le_absorptionPathPreBoundaryPayoff_add_localError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hperfect : IsSequentiallyPerfectAbsorptionPath reward path 0)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    (stage : ℕ) (player : ι) :
    reward (quittingSingletonTerminal player) player ≤
      absorptionPathPreBoundaryPayoff reward path
          (partitionCut path resolution stage) player +
        2 * quittingRewardBound reward *
          pathCellAbsorption path.1 (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1)) := by
  let start := partitionCut path resolution stage
  let stop := partitionCut path resolution (stage + 1)
  let p := pathCellAbsorption path.1 start stop
  have hresolutionOne : 1 ≤ resolution := by omega
  have hstartMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne stage
  have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne (stage + 1)
  have hstartOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolution stage
  have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne stage
  have hstartStop : start < stop := by
    rw [show stop = partitionCut path resolution (stage + 1) by rfl,
      show start = partitionCut path resolution stage by rfl,
      partitionCut_succ]
    exact lt_nextPartitionCut path hpathTotal resolution hresolution
      ⟨hstartMem.1, hstartOne⟩ hstartBoundary
  by_cases hjump : start ∈ pathJumps path.1
  · have hrow := (hperfect player).1 start hjump
      (hnoTerminalJump start hjump)
    have hquitLe : quittingRootQuitPayoff reward
        (absorptionPathPayoff reward path start)
        (absorptionPathJumpRoot path start) player ≤
      quittingRootSuccessorPayoff reward
        (absorptionPathPayoff reward path start)
        (absorptionPathJumpRoot path start) player := by
      simpa using hrow.1
    have hquitError :=
      abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
        reward (absorptionPathPayoff reward path start)
        (absorptionPathJumpRoot path start) player
        (quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward)
    have hopponent : quittingRootOpponentAbsorptionMass
        (absorptionPathJumpRoot path start) player ≤ p := by
      exact
        (quittingRootOpponentAbsorptionMass_le_absorptionMass
          (absorptionPathJumpRoot path start) player).trans
          (absorptionPathJumpRoot_absorption_le_pathCellAbsorption path
            hpathTotal hjump hstopMem hstartStop)
    have hfactor : 0 ≤ 2 * quittingRewardBound reward :=
      mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
    have hsingletonLeQuit : reward (quittingSingletonTerminal player) player ≤
        quittingRootQuitPayoff reward (absorptionPathPayoff reward path start)
          (absorptionPathJumpRoot path start) player +
            2 * quittingRewardBound reward *
              quittingRootOpponentAbsorptionMass
                (absorptionPathJumpRoot path start) player := by
      linarith [neg_le_of_abs_le hquitError]
    have hpre := absorptionPathPreBoundaryPayoff_eq_jumpRootSuccessorPayoff
      reward path hpathTotal hnoTerminalJump hjump
    change reward (quittingSingletonTerminal player) player ≤
      absorptionPathPreBoundaryPayoff reward path start player +
        2 * quittingRewardBound reward * p
    rw [hpre]
    exact hsingletonLeQuit.trans <| add_le_add hquitLe
      (mul_le_mul_of_nonneg_left hopponent hfactor)
  · have htime : start ∈ pathTimes path.1 := hstartBoundary.resolve_left hjump
    have hlower := (hperfect player).2 start htime hstartOne.ne
    have heq :=
      absorptionPathPreBoundaryPayoff_eq_absorptionPathPayoff_of_pathTime_not_jump
        reward path htime hstartOne.ne hjump
    have hpNonneg : 0 ≤ p := by
      unfold p pathCellAbsorption
      exact div_nonneg
        (sub_nonneg.mpr (pathLeftTotal_mono path.1 hstartMem hstopMem
          hstartStop.le))
        (sub_nonneg.mpr hstartOne.le)
    have herrorNonneg : 0 ≤
        2 * quittingRewardBound reward * p :=
      mul_nonneg
        (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
        hpNonneg
    change reward (quittingSingletonTerminal player) player ≤
      absorptionPathPreBoundaryPayoff reward path start player +
        2 * quittingRewardBound reward * p
    rw [heq]
    have hexact : reward (quittingSingletonTerminal player) player ≤
        absorptionPathPayoff reward path start player := by
      simpa [quittingSingletonTerminal] using hlower.1
    linarith

/-- The lower sequential-perfection clause at the cell entrance implies the
decoded Continue-support endpoint inequality.  This is the literal content
of published estimate (21), with one actual-tail decoder error. -/
theorem partitionCellRoot_endpointDifference_le_continueSupportError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hperfect : IsSequentiallyPerfectAbsorptionPath reward path 0)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (player : ι) :
    quittingRootEndpointDifference reward
        (quittingRootSequenceTailVector reward
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) (stage + 1))
        (partitionCellRoot path hpathTotal hnoTerminalJump resolution
          hresolution hcollision stage) player ≤
      8 * quittingRewardBound reward *
          pathCellAbsorption path.1 (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1)) +
        partitionDecoderPayoffErrorCoefficient reward resolution := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let root := roots stage
  let tail := quittingRootSequenceTailVector reward roots (stage + 1)
  let p := pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  let M := quittingRewardBound reward
  let e := partitionDecoderPayoffErrorCoefficient reward resolution
  let singleton := reward (quittingSingletonTerminal player) player
  let current := absorptionPathPreBoundaryPayoff reward path
    (partitionCut path resolution stage) player
  let next := absorptionPathPreBoundaryPayoff reward path
    (partitionCut path resolution (stage + 1)) player
  let quit := quittingRootQuitPayoff reward tail root player
  let continuePayoff := quittingRootContinuePayoff reward tail root player
  have hlower : singleton ≤ current + 2 * M * p := by
    exact singletonReward_le_absorptionPathPreBoundaryPayoff_add_localError
      reward path hpathTotal hperfect hnoTerminalJump resolution (by omega)
      stage player
  have hquit : |quit - singleton| ≤ 2 * M * p := by
    exact abs_partitionCellRoot_quitPayoff_sub_singletonReward_le reward path
      hpathTotal hnoTerminalJump resolution hresolution hcollision stage player
  have hcurrent : |current - next| ≤ 2 * M * p := by
    exact abs_absorptionPathPreBoundaryPayoff_partitionCut_sub_succ_le reward
      path hpathTotal hnoTerminalJump resolution hresolution stage player
  have htail : |tail player - next| ≤ e := by
    exact abs_partitionCellRoots_terminalValue_sub_preBoundaryPayoff_le reward
      path hpathTotal hnoTerminalJump resolution hresolution hcollision
      (stage + 1) player
  have hcontinue : |continuePayoff - tail player| ≤ 2 * M * p := by
    exact abs_partitionCellRoot_continuePayoff_sub_tail_le reward path
      hpathTotal hnoTerminalJump resolution hresolution hcollision stage player
  change quit - continuePayoff ≤ 8 * M * p + e
  linarith [le_of_abs_le hquit, le_of_abs_le hcurrent,
    neg_le_of_abs_le htail, neg_le_of_abs_le hcontinue]

/-- If positive source singleton mass supplies the published reverse entrance
estimate, the supported-Quit endpoint inequality follows with constant
`12 M p` and one actual-tail decoder error.  The separate producer of the
reverse entrance estimate is the only remaining analytic seam in (22). -/
theorem neg_quittingRootEndpointDifference_le_quitSupportError_of_reverseEntrance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (player : ι)
    (hreverse : absorptionPathPreBoundaryPayoff reward path
        (partitionCut path resolution stage) player ≤
      reward (quittingSingletonTerminal player) player +
        6 * quittingRewardBound reward *
          pathCellAbsorption path.1 (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1))) :
    -partitionDecoderPayoffErrorCoefficient reward resolution -
        12 * quittingRewardBound reward *
          pathCellAbsorption path.1 (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1)) ≤
      quittingRootEndpointDifference reward
        (quittingRootSequenceTailVector reward
          (partitionCellRoots path hpathTotal hnoTerminalJump resolution
            hresolution hcollision) (stage + 1))
        (partitionCellRoot path hpathTotal hnoTerminalJump resolution
          hresolution hcollision stage) player := by
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  let root := roots stage
  let tail := quittingRootSequenceTailVector reward roots (stage + 1)
  let p := pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  let M := quittingRewardBound reward
  let e := partitionDecoderPayoffErrorCoefficient reward resolution
  let singleton := reward (quittingSingletonTerminal player) player
  let current := absorptionPathPreBoundaryPayoff reward path
    (partitionCut path resolution stage) player
  let next := absorptionPathPreBoundaryPayoff reward path
    (partitionCut path resolution (stage + 1)) player
  let quit := quittingRootQuitPayoff reward tail root player
  let continuePayoff := quittingRootContinuePayoff reward tail root player
  have hquit : |quit - singleton| ≤ 2 * M * p := by
    exact abs_partitionCellRoot_quitPayoff_sub_singletonReward_le reward path
      hpathTotal hnoTerminalJump resolution hresolution hcollision stage player
  have hcurrent : |current - next| ≤ 2 * M * p := by
    exact abs_absorptionPathPreBoundaryPayoff_partitionCut_sub_succ_le reward
      path hpathTotal hnoTerminalJump resolution hresolution stage player
  have htail : |tail player - next| ≤ e := by
    exact abs_partitionCellRoots_terminalValue_sub_preBoundaryPayoff_le reward
      path hpathTotal hnoTerminalJump resolution hresolution hcollision
      (stage + 1) player
  have hcontinue : |continuePayoff - tail player| ≤ 2 * M * p := by
    exact abs_partitionCellRoot_continuePayoff_sub_tail_le reward path
      hpathTotal hnoTerminalJump resolution hresolution hcollision stage player
  change -e - 12 * M * p ≤ quit - continuePayoff
  change current ≤ singleton + 6 * M * p at hreverse
  linarith [neg_le_of_abs_le hquit, neg_le_of_abs_le hcurrent,
    le_of_abs_le htail, le_of_abs_le hcontinue]

omit [Nonempty ι] in
/-- Support-local endpoint optimality is monotone in its common tolerance. -/
theorem IsQuittingRootSupportApproxNash.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool} {ε ε' : ℝ}
    (hsource : IsQuittingRootSupportApproxNash reward tail ε root)
    (hle : ε ≤ ε') :
    IsQuittingRootSupportApproxNash reward tail ε' root := by
  intro player
  constructor
  · intro hquit
    linarith [(hsource player).1 hquit]
  · intro hcontinue
    linarith [(hsource player).2 hcontinue]

/-- The exact remaining analytic producer in published estimate (22):
positive singleton mass in a selected cell yields the reverse entrance
estimate.  AKRS proves this by the small-jump/interior-differentiability
split; keeping it literal prevents the decoder from silently assuming it. -/
def HasPartitionPositiveSingletonReverseEntranceEstimate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (resolution : ℕ) : Prop :=
  ∀ stage player,
    0 < pathCellLaw path.1 (partitionCut path resolution stage)
      (partitionCut path resolution (stage + 1)) {player} →
    absorptionPathPreBoundaryPayoff reward path
        (partitionCut path resolution stage) player ≤
      reward (quittingSingletonTerminal player) player +
        6 * quittingRewardBound reward *
          pathCellAbsorption path.1 (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1))

/-- Uniform row tolerance obtained from estimates (20)--(22). -/
def partitionSupportError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (resolution : ℕ) : ℝ :=
  12 * quittingRewardBound reward * partitionSmallCellError resolution +
    partitionDecoderPayoffErrorCoefficient reward resolution

omit [DecidableEq ι] [Nonempty ι] in
theorem partitionDecoderPayoffErrorCoefficient_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (resolution : ℕ) (hresolution : 3 ≤ resolution) :
    0 ≤ partitionDecoderPayoffErrorCoefficient reward resolution := by
  unfold partitionDecoderPayoffErrorCoefficient
  have hcoordinate : 0 ≤ akrsSmallCellCoordinateConstant ι := by
    unfold akrsSmallCellCoordinateConstant
    exact_mod_cast Nat.zero_le (2 ^ Fintype.card ι)
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward))
      hcoordinate)
    (partitionSmallCellError_pos resolution hresolution).le

/-- Once the published positive-singleton reverse-entrance producer is
supplied, every decoded row is support-optimal at the one uniform resolution
tolerance.  Copied jumps use exact path perfection; small cells use the
literal estimates (20)--(22). -/
theorem partitionCellRoot_supportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hperfect : IsSequentiallyPerfectAbsorptionPath reward path 0)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (hreverse : HasPartitionPositiveSingletonReverseEntranceEstimate
      reward path resolution)
    (stage : ℕ) :
    IsQuittingRootSupportApproxNash reward
      (quittingRootSequenceTailVector reward
        (partitionCellRoots path hpathTotal hnoTerminalJump resolution
          hresolution hcollision) (stage + 1))
      (partitionSupportError reward resolution)
      (partitionCellRoot path hpathTotal hnoTerminalJump resolution
        hresolution hcollision stage) := by
  let p := pathCellAbsorption path.1
    (partitionCut path resolution stage)
    (partitionCut path resolution (stage + 1))
  let M := quittingRewardBound reward
  let smallError := partitionSmallCellError resolution
  let decoderError := partitionDecoderPayoffErrorCoefficient reward resolution
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hsmallError : 0 ≤ smallError :=
    (partitionSmallCellError_pos resolution hresolution).le
  have hdecoderError : 0 ≤ decoderError :=
    partitionDecoderPayoffErrorCoefficient_nonneg reward resolution hresolution
  rcases partitionCellRoot_source path hpathTotal hnoTerminalJump resolution
      hresolution hcollision stage with hcopied | hsmall
  · obtain ⟨hjump, hstopTotal, hroot⟩ := hcopied
    have hsource := partitionCellRoot_supportApproxNash_of_copiedJump reward
      path hpathTotal hperfect hnoTerminalJump resolution hresolution
      hcollision stage hjump hstopTotal hroot
    apply hsource.mono
    change decoderError ≤ 12 * M * smallError + decoderError
    have hextra : 0 ≤
        12 * quittingRewardBound reward * partitionSmallCellError resolution :=
      mul_nonneg
        (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
        (partitionSmallCellError_pos resolution hresolution).le
    linarith
  · obtain ⟨cell, packet, hcellStart, hcellStop, hroot⟩ := hsmall
    have hpLe : p ≤ smallError := by
      dsimp only [p, smallError]
      simpa only [hcellStart, hcellStop] using cell.absorption_le
    have hpNonneg : 0 ≤ p := by
      dsimp only [p]
      rw [← partitionCellRoot_absorption_exact path hpathTotal
        hnoTerminalJump resolution hresolution hcollision stage]
      exact quittingRootAbsorptionMass_nonneg _
    have hscale : 12 * M * p ≤ 12 * M * smallError := by
      exact mul_le_mul_of_nonneg_left hpLe
        (mul_nonneg (by norm_num) hM)
    intro player
    constructor
    · intro hquit
      have hcellPositive :=
        partitionCellRoot_quitProbability_pos_imp_pathCellLaw_singleton_pos
          path hpathTotal hnoTerminalJump resolution hresolution hcollision
          stage player hquit
      have hreversePlayer := hreverse stage player hcellPositive
      have hlower :=
        neg_quittingRootEndpointDifference_le_quitSupportError_of_reverseEntrance
          reward path hpathTotal hnoTerminalJump resolution hresolution
          hcollision stage player hreversePlayer
      unfold partitionSupportError
      dsimp only [decoderError, smallError, M] at hscale ⊢
      linarith
    · intro _hcontinue
      have hupper :=
        partitionCellRoot_endpointDifference_le_continueSupportError reward path
          hpathTotal hperfect hnoTerminalJump resolution hresolution hcollision
          stage player
      have hscaleEight : 8 * M * p ≤ 12 * M * smallError := by
        have hleft : 8 * M * p ≤ 12 * M * p := by nlinarith
        exact hleft.trans hscale
      unfold partitionSupportError
      dsimp only [decoderError, smallError, M] at hscaleEight ⊢
      linarith

omit [DecidableEq ι] [Nonempty ι] in
/-- The uniform row tolerance vanishes along the shifted integer
resolutions used by the decoder. -/
theorem tendsto_partitionSupportError_add_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto (fun rank : ℕ => partitionSupportError reward (rank + 3))
      atTop (nhds 0) := by
  have hbase : Tendsto (fun rank : ℕ => 1 / ((rank : ℝ) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto
      (fun rank : ℕ => partitionSmallCellError (rank + 3))
      atTop (nhds 0) := by
    unfold partitionSmallCellError
    convert hshift using 1
    funext rank
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one]
    ring
  let coefficient : ℝ :=
    12 * quittingRewardBound reward +
      Fintype.card {S : Finset ι // S.Nonempty} *
        quittingRewardBound reward * akrsSmallCellCoordinateConstant ι
  have hconstant : Tendsto (fun _ : ℕ => coefficient) atTop
      (nhds coefficient) := tendsto_const_nhds
  have hscaled : Tendsto (fun rank : ℕ =>
      coefficient * partitionSmallCellError (rank + 3)) atTop (nhds 0) := by
    simpa only [mul_zero] using hconstant.mul hsmall
  refine hscaled.congr' (Filter.Eventually.of_forall fun rank => ?_)
  unfold coefficient partitionSupportError
    partitionDecoderPayoffErrorCoefficient
  ring


omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Use the actual coordinate before the right endpoint and its left limit at
the endpoint. -/
def singletonCoordinateCellValue
    (path : CadlagPath (ι := ι))
    (singleton : {S : Finset ι // S.Nonempty})
    (stop time : ℝ) : ℝ :=
  if time = stop then path.leftValue stop singleton
  else path.value time singleton

omit [Nonempty ι] in
/-- A positive singleton increment on a path cell is witnessed either by a
positive singleton jump or by positive lower-right rate at a continuous clock
point.  This is the analytic split used in AKRS estimate (22). -/
theorem exists_positiveSingletonJump_or_pathTimeRightDerivative_pos
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    {start stop : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1) (hstartStop : start < stop)
    (player : ι)
    (hincrement : path.1.leftValue start
        ⟨{player}, Finset.singleton_nonempty player⟩ <
      path.1.leftValue stop
        ⟨{player}, Finset.singleton_nonempty player⟩) :
    (∃ time ∈ Set.Ico start stop,
      0 < pathJump path.1 time
        ⟨{player}, Finset.singleton_nonempty player⟩) ∨
    (∃ time ∈ Set.Ico start stop, time ∈ pathTimes path.1 ∧
      0 < pathRightDerivative path.1 time
        ⟨{player}, Finset.singleton_nonempty player⟩) := by
  let singleton : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  let cellValue := singletonCoordinateCellValue path.1 singleton stop
  by_contra hnot
  push Not at hnot
  have hnoJump (point : ℝ) (hpoint : point ∈ Set.Ico start stop) :
      pathJump path.1 point singleton ≤ 0 := by
    simpa only [singleton] using hnot.1 point hpoint
  have hnoDerivative (point : ℝ) (hpoint : point ∈ Set.Ico start stop)
      (hclock : point ∈ pathTimes path.1) :
      pathRightDerivative path.1 point singleton ≤ 0 := by
    simpa only [singleton] using hnot.2 point hpoint hclock
  have hright (point : ℝ) (hpoint : point ∈ Set.Ico start stop) :
      Tendsto cellValue (nhdsWithin point (Set.Icc point stop))
        (nhds (cellValue point)) := by
    have hdomain : Set.Icc point stop ⊆ Set.Icc point 1 := by
      intro later hlater
      exact ⟨hlater.1, hlater.2.trans hstop.2⟩
    have hraw :=
      (path.1.right_continuous singleton point
        ⟨hstart.1.trans hpoint.1, hpoint.2.le.trans hstop.2⟩).mono_left
          (nhdsWithin_mono point hdomain)
    have hpointNeStop : point ≠ stop := ne_of_lt hpoint.2
    have heq : ∀ᶠ later in nhdsWithin point (Set.Icc point stop),
        cellValue later = path.1.value later singleton := by
      filter_upwards [mem_inf_of_left (Iio_mem_nhds hpoint.2)]
        with later hlater
      simp only [Set.mem_Iio] at hlater
      simp only [cellValue, singletonCoordinateCellValue,
        if_neg (ne_of_lt hlater)]
    have htarget : cellValue point = path.1.value point singleton := by
      simp only [cellValue, singletonCoordinateCellValue,
        if_neg hpointNeStop]
    rw [htarget]
    exact hraw.congr' (Filter.EventuallyEq.symm heq)
  have hleft (point : ℝ) (hpoint : point ∈ Set.Ioc start stop) :
      Tendsto cellValue (nhdsWithin point (Set.Ico start point))
        (nhds (path.1.leftValue point singleton)) := by
    have hdomain : Set.Ico start point ⊆
        Set.Icc (0 : ℝ) point \ {point} := by
      intro earlier hearler
      exact ⟨⟨hstart.1.trans hearler.1, hearler.2.le⟩, hearler.2.ne⟩
    have hraw :=
      (path.1.left_limit singleton point
        ⟨hstart.1.trans hpoint.1.le, hpoint.2.trans hstop.2⟩).mono_left
          (nhdsWithin_mono point hdomain)
    have heq : ∀ᶠ earlier in nhdsWithin point (Set.Ico start point),
        cellValue earlier = path.1.value earlier singleton := by
      filter_upwards [self_mem_nhdsWithin] with earlier hearler
      simp only [cellValue, singletonCoordinateCellValue,
        if_neg (ne_of_lt (hearler.2.trans_le hpoint.2))]
    exact hraw.congr' (Filter.EventuallyEq.symm heq)
  have hjump (point : ℝ) (hpoint : point ∈ Set.Ioc start stop) :
      cellValue point ≤ path.1.leftValue point singleton := by
    rcases hpoint.2.eq_or_lt with rfl | hpointStop
    · simp [cellValue, singletonCoordinateCellValue]
    · have hpointIco : point ∈ Set.Ico start stop :=
        ⟨hpoint.1.le, hpointStop⟩
      have hbound := hnoJump point hpointIco
      simp only [cellValue, singletonCoordinateCellValue,
        if_neg (ne_of_lt hpointStop)]
      unfold pathJump at hbound
      linarith
  have hstartLe : cellValue start ≤
      path.1.leftValue start singleton := by
    have hbound := hnoJump start ⟨le_rfl, hstartStop⟩
    simp only [cellValue, singletonCoordinateCellValue,
      if_neg (ne_of_lt hstartStop)]
    unfold pathJump at hbound
    linarith
  have hslope (point : ℝ) (hpoint : point ∈ Set.Ico start stop)
      (rate : ℝ) (hrate : 0 < rate) :
      ∃ᶠ later in nhdsWithin point (Set.Ioo point stop),
        slope cellValue point later < rate := by
    have hpointIcc : point ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hstart.1.trans hpoint.1, hpoint.2.le.trans hstop.2⟩
    have hpointNeStop : point ≠ stop := ne_of_lt hpoint.2
    by_cases hclock : point ∈ pathTimes path.1
    · let coordinateSlope := fun later : ℝ ↦
        (path.1.value later singleton - path.1.value point singleton) /
          (later - point)
      have hbounded : ∃ᶠ later in nhdsWithin point (Set.Ioo point stop),
          coordinateSlope later ≤ 2 := by
        simpa only [coordinateSlope] using
          frequently_coordinateSlope_le_two_of_mem_pathTimes path hpathTotal
            hclock hpoint.2 hstop.2 singleton
      have hcobounded :
          (nhdsWithin point (Set.Ioo point stop)).IsCoboundedUnder
            (· ≥ ·) coordinateSlope :=
        Filter.IsCoboundedUnder.of_frequently_le hbounded
      have hfilters : nhdsWithin point (Set.Ioo point stop) =
          nhdsWithin point (Set.Ioo point 1) := by
        rw [nhdsWithin_Ioo_eq_nhdsGT hpoint.2,
          nhdsWithin_Ioo_eq_nhdsGT (hpoint.2.trans_le hstop.2)]
      have hliminf : Filter.liminf coordinateSlope
          (nhdsWithin point (Set.Ioo point stop)) ≤ 0 := by
        rw [hfilters]
        simpa only [coordinateSlope, pathRightDerivative] using
          hnoDerivative point hpoint hclock
      have hfrequent : ∃ᶠ later in nhdsWithin point (Set.Ioo point stop),
          coordinateSlope later < rate := by
        apply frequently_lt_of_liminf_lt hcobounded
        exact hliminf.trans_lt hrate
      have hwithMem := hfrequent.and_eventually self_mem_nhdsWithin
      apply hwithMem.mono
      intro later hlater
      have hlaterMem : later ∈ Set.Ioo point stop := hlater.2
      have hcellPoint : cellValue point = path.1.value point singleton := by
        simp only [cellValue, singletonCoordinateCellValue,
          if_neg hpointNeStop]
      have hcellLater : cellValue later = path.1.value later singleton := by
        simp only [cellValue, singletonCoordinateCellValue,
          if_neg (ne_of_lt hlaterMem.2)]
      rw [slope_def_field, hcellPoint, hcellLater]
      exact hlater.1
    · have hpointLtTotal : point < pathTotal path.1 point :=
        lt_of_le_of_ne (path.property.1 point hpointIcc) <| by
          intro heq
          exact hclock ⟨hpointIcc, heq.symm⟩
      letI : (nhdsWithin point (Set.Ioo point stop)).NeBot :=
        left_nhdsWithin_Ioo_neBot hpoint.2
      have heventually : ∀ᶠ later in nhdsWithin point (Set.Ioo point stop),
          later < pathTotal path.1 point :=
        mem_inf_of_left (Iio_mem_nhds hpointLtTotal)
      have hzero : ∀ᶠ later in nhdsWithin point (Set.Ioo point stop),
          slope cellValue point later = 0 := by
        filter_upwards [heventually, self_mem_nhdsWithin]
          with later hlaterTotal hlaterMem
        have hlaterIcc : later ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨hpointIcc.1.trans hlaterMem.1.le,
            hlaterMem.2.le.trans hstop.2⟩
        have htotalEq := pathTotal_eq_of_le_of_lt_pathTotal path
          hpointIcc hlaterIcc hlaterMem.1.le hlaterTotal
        have hcoordinateEq := CadlagPath.value_eq_of_total_eq path.1
          (earlier := point) (later := later) hpointIcc hlaterIcc
          hlaterMem.1.le htotalEq singleton
        rw [slope_def_field]
        simp only [cellValue, singletonCoordinateCellValue,
          if_neg hpointNeStop, if_neg (ne_of_lt hlaterMem.2),
          hcoordinateEq, sub_self, zero_div]
      exact (hzero.mono fun later heq => heq.symm ▸ hrate).frequently
  have hend :=
    endpoint_le_of_rightContinuous_leftLimit_noUpwardJump_liminfSlope_nonpos
      hstartStop.le hstartLe hright hleft hjump hslope
  have hcellStop : cellValue stop = path.1.leftValue stop singleton := by
    simp [cellValue, singletonCoordinateCellValue]
  rw [hcellStop] at hend
  exact (not_le_of_gt hincrement) hend

omit [Nonempty ι] in
/-- Exact Bellman identity for arbitrary ordered path boundaries, not only
the canonical partition cuts. -/
theorem absorptionPathPreBoundaryPayoff_boundaryCell_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    {start stop : ℝ}
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hstopBoundary : stop ∈ partitionBoundaryTimes path)
    (hstartOne : start < 1) (hstopOne : stop < 1) (player : ι) :
    absorptionPathPreBoundaryPayoff reward path start player =
      (∑ terminal : {S : Finset ι // S.Nonempty},
          pathCellLaw path.1 start stop terminal.1 * reward terminal player) +
        (1 - pathCellAbsorption path.1 start stop) *
          absorptionPathPreBoundaryPayoff reward path stop player := by
  have hsurvival := one_sub_pathCellAbsorption_of_boundaries path
    hstartBoundary hstopBoundary hstartOne
  unfold absorptionPathPreBoundaryPayoff
  simp_rw [pathCellLaw_nonempty]
  rw [hsurvival]
  simp_rw [Finset.sum_div]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro terminal _
  have hstartDenom : 1 - start ≠ 0 := ne_of_gt (sub_pos.mpr hstartOne)
  have hstopDenom : 1 - stop ≠ 0 := ne_of_gt (sub_pos.mpr hstopOne)
  field_simp [hstartDenom, hstopDenom]
  ring

omit [Nonempty ι] in
/-- The literal absorbing reward of an arbitrary valid boundary cell is
bounded by reward size times its conditional absorption. -/
theorem abs_pathBoundaryCellAbsorbingContribution_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    {start stop : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1) (hstartStop : start ≤ stop)
    (hstartOne : start < 1) (player : ι) :
    |∑ terminal : {S : Finset ι // S.Nonempty},
        pathCellLaw path.1 start stop terminal.1 * reward terminal player| ≤
      quittingRewardBound reward * pathCellAbsorption path.1 start stop := by
  have hlawNonneg (terminal : {S : Finset ι // S.Nonempty}) :
      0 ≤ pathCellLaw path.1 start stop terminal.1 :=
    pathCellLaw_nonneg_of_nonempty path.1 hstart hstop hstartStop hstartOne
      terminal
  calc
    |∑ terminal : {S : Finset ι // S.Nonempty},
        pathCellLaw path.1 start stop terminal.1 * reward terminal player| ≤
        ∑ terminal : {S : Finset ι // S.Nonempty},
          |pathCellLaw path.1 start stop terminal.1 * reward terminal player| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ terminal : {S : Finset ι // S.Nonempty},
          pathCellLaw path.1 start stop terminal.1 *
            |reward terminal player| := by
      apply Finset.sum_congr rfl
      intro terminal _
      rw [abs_mul, abs_of_nonneg (hlawNonneg terminal)]
    _ ≤ ∑ terminal : {S : Finset ι // S.Nonempty},
          pathCellLaw path.1 start stop terminal.1 *
            quittingRewardBound reward := by
      apply Finset.sum_le_sum
      intro terminal _
      exact mul_le_mul_of_nonneg_left
        (abs_reward_le_quittingRewardBound reward terminal player)
        (hlawNonneg terminal)
    _ = quittingRewardBound reward * pathCellAbsorption path.1 start stop := by
      rw [← Finset.sum_mul, sum_pathCellLaw_nonempty]
      ring

omit [Nonempty ι] in
/-- Arbitrary ordered path boundaries satisfy the same local `2 M p`
continuation transport estimate as canonical partition cuts. -/
theorem abs_absorptionPathPreBoundaryPayoff_sub_le_two_mul_pathCellAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    {start stop : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1) (hstartStop : start ≤ stop)
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
  have hnext : |next| ≤ quittingRewardBound reward := by
    let weight := fun terminal : {S : Finset ι // S.Nonempty} =>
      (path.1.value 1 terminal - path.1.leftValue stop terminal) / (1 - stop)
    have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have htotalOne : pathTotal path.1 1 = 1 :=
      le_antisymm (hpathTotal 1 hone) (path.property.1 1 hone)
    have hleftTotal : pathLeftTotal path.1 stop = stop :=
      pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary
    have hweightNonneg (terminal : {S : Finset ι // S.Nonempty}) :
        0 ≤ weight terminal := by
      apply div_nonneg
      · have hmono := path.1.leftValue_mono terminal hstop hone hstop.2
        rw [← value_one_eq_leftValue_one_of_noTerminalTotalJump path
          hpathTotal hnoTerminalJump terminal] at hmono
        exact sub_nonneg.mpr hmono
      · exact (sub_pos.mpr hstopOne).le
    have hweightSum : (∑ terminal, weight terminal) = 1 := by
      unfold weight
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      change (pathTotal path.1 1 - pathLeftTotal path.1 stop) /
        (1 - stop) = 1
      rw [htotalOne, hleftTotal]
      exact div_self (ne_of_gt (sub_pos.mpr hstopOne))
    unfold next absorptionPathPreBoundaryPayoff
    rw [Finset.sum_div]
    calc
      |∑ terminal, ((path.1.value 1 terminal -
          path.1.leftValue stop terminal) * reward terminal player) /
            (1 - stop)| =
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

omit [Nonempty ι] in
/-- A jump inside an enclosing valid boundary cell has conditional
absorption no larger than the enclosing cell's conditional absorption. -/
theorem absorptionPathJumpRoot_absorption_le_enclosingBoundaryCell
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    {start stop time : ℝ}
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hstopBoundary : stop ∈ partitionBoundaryTimes path)
    (hstartOne : start < 1) (htime : time ∈ pathJumps path.1)
    (htimeCell : time ∈ Set.Ico start stop) :
    quittingRootAbsorptionMass (absorptionPathJumpRoot path time) ≤
      pathCellAbsorption path.1 start stop := by
  have hstopMem : stop ∈ Set.Icc (0 : ℝ) 1 :=
    hstopBoundary.elim And.left And.left
  have htimeStop : time < stop := htimeCell.2
  have htimeOne : time < 1 := htimeStop.trans_le hstopMem.2
  have htotalLeStop : pathTotal path.1 time ≤
      pathLeftTotal path.1 stop :=
    pathTotal_le_pathLeftTotal_of_lt path.1 htime.1 hstopMem htimeStop
  have hleftStart : pathLeftTotal path.1 start = start :=
    pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstartBoundary
  have hleftStop : pathLeftTotal path.1 stop = stop :=
    pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary
  rw [copiedJumpRoot_absorption_eq_pathCellAbsorption path hpathTotal
    htime rfl]
  unfold pathCellAbsorption
  rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
      (pathTotal_mem_partitionBoundaryTimes path hpathTotal htime.1),
    pathLeftTotal_eq_of_mem_pathJumps path htime, hleftStart, hleftStop]
  apply (div_le_div_iff₀ (sub_pos.mpr htimeOne)
    (sub_pos.mpr hstartOne)).2
  have hfactor : 0 ≤ (time - start) * (1 - stop) :=
    mul_nonneg (sub_nonneg.mpr htimeCell.1)
      (sub_nonneg.mpr hstopMem.2)
  nlinarith

omit [Nonempty ι] in
/-- Sequential perfection supplies the positive-singleton reverse-entrance
estimate at every selected partition cell.  The jump and continuous-rate
witnesses are exactly those produced by
`exists_positiveSingletonJump_or_pathTimeRightDerivative_pos`. -/
theorem hasPartitionPositiveSingletonReverseEntranceEstimate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hperfect : IsSequentiallyPerfectAbsorptionPath reward path 0)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution) :
    HasPartitionPositiveSingletonReverseEntranceEstimate
      reward path resolution := by
  intro stage player hcellPositive
  let start := partitionCut path resolution stage
  let stop := partitionCut path resolution (stage + 1)
  let p := pathCellAbsorption path.1 start stop
  let M := quittingRewardBound reward
  let singleton : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hstartMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne stage
  have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne (stage + 1)
  have hstartOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolutionTwo stage
  have hstopOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolutionTwo (stage + 1)
  have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne stage
  have hstopBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne (stage + 1)
  have hstartStop : start < stop := by
    rw [show stop = partitionCut path resolution (stage + 1) by rfl,
      show start = partitionCut path resolution stage by rfl,
      partitionCut_succ]
    exact lt_nextPartitionCut path hpathTotal resolution hresolutionTwo
      ⟨hstartMem.1, hstartOne⟩ hstartBoundary
  have hincrement : path.1.leftValue start singleton <
      path.1.leftValue stop singleton := by
    have hpositive : 0 <
        (path.1.leftValue stop singleton -
          path.1.leftValue start singleton) / (1 - start) := by
      change 0 < pathCellLaw path.1 start stop singleton.1 at hcellPositive
      rw [pathCellLaw_nonempty path.1 start stop singleton] at hcellPositive
      exact hcellPositive
    rcases (div_pos_iff.mp hpositive) with hpos | hneg
    · linarith
    · exact False.elim ((not_lt_of_ge (sub_pos.mpr hstartOne).le) hneg.2)
  have hpNonneg : 0 ≤ p := by
    unfold p pathCellAbsorption
    exact div_nonneg
      (sub_nonneg.mpr (pathLeftTotal_mono path.1 hstartMem hstopMem
        hstartStop.le))
      (sub_nonneg.mpr hstartOne.le)
  have hMNonneg : 0 ≤ M := quittingRewardBound_nonneg reward
  rcases exists_positiveSingletonJump_or_pathTimeRightDerivative_pos path
      hpathTotal hstartMem hstopMem hstartStop player hincrement with
    hjump | hcontinuous
  · obtain ⟨time, htimeCell, hsingletonJump⟩ := hjump
    have htimeMem : time ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hstartMem.1.trans htimeCell.1, htimeCell.2.le.trans hstopMem.2⟩
    have htimeOne : time < 1 := htimeCell.2.trans hstopOne
    have htimeLeStop : time ≤ stop := by
      simpa only [stop] using htimeCell.2.le
    have htimeJump : time ∈ pathJumps path.1 :=
      ⟨htimeMem, singleton, ne_of_gt hsingletonJump⟩
    have htimeBoundary : time ∈ partitionBoundaryTimes path :=
      Or.inl htimeJump
    let partialAbsorption := pathCellAbsorption path.1 start time
    have hpartialLe : partialAbsorption ≤ p := by
      unfold partialAbsorption p pathCellAbsorption
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path htimeBoundary,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstartBoundary,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary]
      exact (div_le_div_iff_of_pos_right (sub_pos.mpr hstartOne)).2 <| by
        linarith [htimeLeStop]
    have hpartialNonneg : 0 ≤ partialAbsorption := by
      unfold partialAbsorption pathCellAbsorption
      exact div_nonneg
        (sub_nonneg.mpr (pathLeftTotal_mono path.1 hstartMem htimeMem
          htimeCell.1))
        (sub_nonneg.mpr hstartOne.le)
    have htransport :=
      abs_absorptionPathPreBoundaryPayoff_sub_le_two_mul_pathCellAbsorption
        reward path hpathTotal hnoTerminalJump hstartMem htimeMem
        htimeCell.1 hstartBoundary htimeBoundary hstartOne htimeOne player
    have hpreEq :=
      absorptionPathPreBoundaryPayoff_eq_jumpRootSuccessorPayoff reward path
        hpathTotal hnoTerminalJump htimeJump
    have hrow := (hperfect player).1 time htimeJump
      (hnoTerminalJump time htimeJump)
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
    have hsuccessorLeQuit :
        quittingRootSuccessorPayoff reward
            (absorptionPathPayoff reward path time)
            (absorptionPathJumpRoot path time) player ≤
          quittingRootQuitPayoff reward
            (absorptionPathPayoff reward path time)
            (absorptionPathJumpRoot path time) player := by
      simpa using hrow.2.2.1 hquitUsed
    have hquitError :=
      abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
        reward (absorptionPathPayoff reward path time)
        (absorptionPathJumpRoot path time) player M
        (abs_reward_le_quittingRewardBound reward)
    have habsorptionLe : quittingRootAbsorptionMass
        (absorptionPathJumpRoot path time) ≤ p := by
      exact absorptionPathJumpRoot_absorption_le_enclosingBoundaryCell path
        hpathTotal hstartBoundary hstopBoundary hstartOne htimeJump htimeCell
    have hopponentLe : quittingRootOpponentAbsorptionMass
        (absorptionPathJumpRoot path time) player ≤ p :=
      (quittingRootOpponentAbsorptionMass_le_absorptionMass _ _).trans
        habsorptionLe
    have hfactor : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMNonneg
    change absorptionPathPreBoundaryPayoff reward path start player ≤
      reward (quittingSingletonTerminal player) player + 6 * M * p
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
      hsuccessorLeQuit, hquitUpper]
  · obtain ⟨time, htimeCell, htimePath, hderivative⟩ := hcontinuous
    have htimeMem : time ∈ Set.Icc (0 : ℝ) 1 := htimePath.1
    have htimeOne : time < 1 := htimeCell.2.trans hstopOne
    have htimeLeStop : time ≤ stop := by
      simpa only [stop] using htimeCell.2.le
    have htimeBoundary : time ∈ partitionBoundaryTimes path :=
      Or.inr htimePath
    let partialAbsorption := pathCellAbsorption path.1 start time
    have hpartialLe : partialAbsorption ≤ p := by
      unfold partialAbsorption p pathCellAbsorption
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path htimeBoundary,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstartBoundary,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary]
      exact (div_le_div_iff_of_pos_right (sub_pos.mpr hstartOne)).2 <| by
        linarith [htimeLeStop]
    have htransport :=
      abs_absorptionPathPreBoundaryPayoff_sub_le_two_mul_pathCellAbsorption
        reward path hpathTotal hnoTerminalJump hstartMem htimeMem
        htimeCell.1 hstartBoundary htimeBoundary hstartOne htimeOne player
    have hpathUpper : absorptionPathPayoff reward path time player ≤
        reward (quittingSingletonTerminal player) player := by
      have hraw := (hperfect player).2 time htimePath htimeOne.ne
      have hupper := hraw.2 (by simpa only [singleton] using hderivative)
      simpa [quittingSingletonTerminal] using hupper
    have hpreUpper : absorptionPathPreBoundaryPayoff reward path time player ≤
        absorptionPathPayoff reward path time player + 2 * M * p := by
      by_cases htimeJump : time ∈ pathJumps path.1
      · have hpreEq :=
          absorptionPathPreBoundaryPayoff_eq_jumpRootSuccessorPayoff reward path
            hpathTotal hnoTerminalJump htimeJump
        have htailBound : |absorptionPathPayoff reward path time player| ≤
            M := by
          have htimeTotal := hnoTerminalJump time htimeJump
          unfold absorptionPathPayoff
          rw [if_pos htimeMem, if_pos htimeTotal]
          let weight := fun terminal : {S : Finset ι // S.Nonempty} =>
            (path.1.value 1 terminal - path.1.value time terminal) /
              (1 - pathTotal path.1 time)
          have hweightNonneg (terminal : {S : Finset ι // S.Nonempty}) :
              0 ≤ weight terminal := by
            exact div_nonneg
              (sub_nonneg.mpr (path.1.monotone terminal htimeMem
                (by norm_num) htimeMem.2))
              (sub_nonneg.mpr htimeTotal.le)
          have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
          have htotalOne : pathTotal path.1 1 = 1 :=
            le_antisymm (hpathTotal 1 hone) (path.property.1 1 hone)
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
            (absorptionPathJumpRoot path time) ≤ p := by
          exact absorptionPathJumpRoot_absorption_le_enclosingBoundaryCell path
            hpathTotal hstartBoundary hstopBoundary hstartOne htimeJump htimeCell
        have hfactor : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMNonneg
        rw [hpreEq]
        nlinarith [le_of_abs_le hsuccessorError,
          mul_le_mul_of_nonneg_left habsorptionLe hfactor]
      · rw [absorptionPathPreBoundaryPayoff_eq_absorptionPathPayoff_of_pathTime_not_jump
          reward path htimePath htimeOne.ne htimeJump]
        exact le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (by norm_num) hMNonneg) hpNonneg)
    change absorptionPathPreBoundaryPayoff reward path start player ≤
      reward (quittingSingletonTerminal player) player + 6 * M * p
    have htransportUpper :
        absorptionPathPreBoundaryPayoff reward path start player ≤
          absorptionPathPreBoundaryPayoff reward path time player +
            2 * M * partialAbsorption := by
      linarith [le_of_abs_le htransport]
    have hfactor : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMNonneg
    nlinarith [mul_le_mul_of_nonneg_left hpartialLe hfactor,
      hpreUpper, hpathUpper]

end QuittingAbsorptionPath
end GameTheory
