/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.PassiveRowFourFixture
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.StrictInversePassiveRowCycle
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonDeletedPath
import UniformEquilibrium.Quitting.Cycles.SoloRootSequenceValues
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Quitting.Cycles.VariableSingletonCalendar
import UniformEquilibrium.Quitting.Cycles.RationalSingletonCalendar

/-!
# Actual quiet-child floor and joining boundary examples

The active child has the packet's literal three-player singleton matrix and
zero own singleton levels. Its nonsingleton rewards remain arbitrary. The
existing right-cycle producer and canonical deletion lift construct the source.
Every positive equal mesh and every arbitrary positive phase-length rational
calendar preserve the negative-row outsider's Never value minus one and
immediate-Quit value zero. A zero-row outsider has actual Never value zero;
joining a sole owner pays its actual hazard times the pair reward. The
tolerance-selected rational source derives its own joining cap. No parent
floor or nonnegative row-factorization certificate is used.
-/

noncomputable section

namespace GameTheory.PassiveRowJoiningBoundary

open QuittingLCPClassification _root_.Math.LinearProgramming
open _root_.Math.LinearProgramming.ThreeCycleInverseFormulas

abbrev Reward := PassiveRowFourFixture.Reward

def outsideBlock : Finset (Fin 4) := {3}

private abbrev Child := QuittingBlockSurvivor outsideBlock

private def childEquiv : Fin 3 ≃ Child where
  toFun who := ⟨who.castSucc, by simpa [outsideBlock] using Fin.castSucc_ne_last who⟩
  invFun who := who.1.castPred (by simpa [outsideBlock] using who.2)
  left_inv who := by simp
  right_inv who := by
    apply Subtype.ext
    exact Fin.castSucc_castPred who.1 (by simpa [outsideBlock] using who.2)

private def labeledReward (reward : Reward) : QuittingReward3 :=
  quittingRewardReindex childEquiv.symm (quittingDeleteReward reward (· ∈ outsideBlock))

private theorem labeledSolo_eq (reward : Reward) (owner who : Fin 3) :
    quittingSoloReward (labeledReward reward) owner who =
      quittingSoloReward reward owner.castSucc who.castSucc := by
  have hreindex : quittingSoloReward (labeledReward reward) owner who =
      quittingSoloReward (quittingDeleteReward reward (· ∈ outsideBlock))
        (childEquiv owner) (childEquiv who) := by
    simp [labeledReward, quittingSoloReward, quittingRewardReindex, quittingCoalitionEquiv]
  rw [hreindex]
  exact quittingDeleteReward_singletonTerminal reward (· ∈ outsideBlock) _ _

/-- Literal zero-baseline active singleton data; child nonsingletons are unrestricted. -/
def HasChildSingletons (reward : Reward) : Prop :=
  ∀ who owner : Fin 3, quittingSoloReward reward owner.castSucc who.castSucc =
    PassiveRowFourFixture.childMatrix who owner

private theorem labeledSolo_of_child (reward : Reward) (hchild : HasChildSingletons reward)
    (owner who : Fin 3) :
    quittingSoloReward (labeledReward reward) owner who =
      PassiveRowFourFixture.childMatrix who owner := by
  rw [labeledSolo_eq]
  exact hchild who owner

private theorem rightCycle (reward : Reward) (hchild : HasChildSingletons reward) :
    RightSingletonCycle (labeledReward reward) := by
  refine rightSingletonCycle_of_directedSoloMatrix (labeledReward reward)
    1 2 2 1 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [cycleGap]) ?_
  funext who owner
  rw [normalizedSoloMatrix_eq_soloReward_sub, labeledSolo_eq, labeledSolo_eq,
    hchild, hchild]
  fin_cases who <;> fin_cases owner <;>
    norm_num [PassiveRowFourFixture.childMatrix, PassiveRowFourFixture.matrix,
      directedCycleMatrix]

/-- Reuse the existing right-cycle certificate on the literal deleted reward. -/
def childCertificate (reward : Reward) (hchild : HasChildSingletons reward) :
    BalancedSingletonCycleCertificate (L := 3)
      (quittingDeleteReward reward (· ∈ outsideBlock)) :=
  RightSingletonCycle.toBalancedCertificate_reindex
    (quittingDeleteReward reward (· ∈ outsideBlock)) childEquiv.symm (rightCycle reward hchild)

private theorem labeled_rightAlpha_eq_half (reward : Reward)
    (hchild : HasChildSingletons reward) : rightAlpha (labeledReward reward) = 1 / 2 := by
  norm_num [rightAlpha, rightDelta, rightP, rightQ, rightR, rightS, rightT, rightU,
    labeledSolo_of_child reward hchild, PassiveRowFourFixture.childMatrix,
    PassiveRowFourFixture.matrix]

private theorem labeled_rightCoarse_zero_one (reward : Reward)
    (hchild : HasChildSingletons reward) : rightCoarse (labeledReward reward) 0 1 = 1 := by
  norm_num [rightCoarse, labeled_rightAlpha_eq_half reward hchild,
    labeledSolo_of_child reward hchild, PassiveRowFourFixture.childMatrix,
    PassiveRowFourFixture.matrix]

/-- The actual quiet extension of each positive child subdivision, starting at phase zero. -/
def roots (reward : Reward) (hchild : HasChildSingletons reward) (m : ℕ) (hm : 0 < m) :
    ℕ → Fin 4 → PMF Bool :=
  (childCertificate reward hchild).deletedRootSequence outsideBlock m
    (quittingSingletonMeshInitialPhase (childCertificate reward hchild).initial m hm)

/-- The actual surviving owner at the queried date of the constructed mesh source. -/
def active (reward : Reward) (hchild : HasChildSingletons reward)
    (m : ℕ) (hm : 0 < m) (time : ℕ) : Child :=
  (childCertificate reward hchild).owner (quittingSingletonMeshBlock
    (quittingCyclicOrbit
      (quittingSingletonMeshInitialPhase (childCertificate reward hchild).initial m hm) time))

private theorem roots_solo (reward : Reward) (hchild : HasChildSingletons reward)
    (m : ℕ) (hm : 0 < m) (time : ℕ) (other : Fin 4)
    (hne : other ≠ (active reward hchild m hm time).1) :
    roots reward hchild m hm time other = PMF.pure false :=
  (childCertificate reward hchild).deletedRootSequence_solo outsideBlock m _ time other hne

private theorem outside_ne_active (reward : Reward) (hchild : HasChildSingletons reward)
    (m : ℕ) (hm : 0 < m) (time : ℕ) :
    (3 : Fin 4) ≠ (active reward hchild m hm time).1 := by
  intro hequal
  apply (active reward hchild m hm time).2
  simp [outsideBlock, ← hequal]

private theorem never_eq_terminalValue (reward : Reward)
    (source : ℕ → Fin 4 → PMF Bool) (who : Fin 4)
    (hcontinue : ∀ time, source time who = PMF.pure false) (start : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward source who none start =
      quittingRootSequenceTerminalValue reward source who start := by
  unfold quittingRootSequencePureTimeTerminalValue quittingRootSequenceHazardTerminalValue
  have hupdate : quittingRootSequenceUpdate source who (quittingPureTimeHazard none) =
      source := by
    funext time
    rw [quittingRootSequenceUpdate, quittingPureTimeHazard_none, ← hcontinue time]
    exact Function.update_eq_self who (source time)
  rw [hupdate]

private theorem terminalValue_neg_coordinate_of_solo
    (reward : Reward) (source : ℕ → Fin 4 → PMF Bool) (owner : ℕ → Fin 4)
    (hsolo : ∀ time other, other ≠ owner time → source time other = PMF.pure false)
    (outside inside : Fin 4)
    (hrow : ∀ time, quittingSoloReward reward (owner time) outside =
      -quittingSoloReward reward (owner time) inside) (start : ℕ) :
    quittingRootSequenceTerminalValue reward source outside start =
      -quittingRootSequenceTerminalValue reward source inside start := by
  rw [quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution,
    quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution, ← tsum_neg]
  apply tsum_congr
  intro offset
  rw [eq_quittingSoloStationaryRoot_of_others_continue (hsolo (start + offset)),
    quittingRootAbsorbingContribution_solo, quittingRootAbsorbingContribution_solo,
    hrow]
  ring

private theorem terminalValue_zero_of_solo
    (reward : Reward) (source : ℕ → Fin 4 → PMF Bool) (owner : ℕ → Fin 4)
    (hsolo : ∀ time other, other ≠ owner time → source time other = PMF.pure false)
    (outside : Fin 4)
    (hrow : ∀ time, quittingSoloReward reward (owner time) outside = 0) (start : ℕ) :
    quittingRootSequenceTerminalValue reward source outside start = 0 := by
  rw [quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  have hzero (offset : ℕ) : quittingRootAbsorbingContribution reward
      (source (start + offset)) outside = 0 := by
    rw [eq_quittingSoloStationaryRoot_of_others_continue (hsolo (start + offset)),
      quittingRootAbsorbingContribution_solo, hrow, mul_zero]
  simp [hzero]

private theorem initial_child_one_value (reward : Reward) (hchild : HasChildSingletons reward)
    (m : ℕ) (hm : 0 < m) :
    quittingRootSequenceTerminalValue reward (roots reward hchild m hm) 1 0 = 1 := by
  have hactual := (childCertificate reward hchild).deletedRootSequence_terminalValue_eq
    outsideBlock m hm
    (quittingSingletonMeshInitialPhase (childCertificate reward hchild).initial m hm)
    0 (childEquiv 1)
  change quittingRootSequenceTerminalValue reward (roots reward hchild m hm) 1 0 = _
    at hactual
  rw [quittingCyclicOrbit_zero, quittingSingletonArcCycleValue_initialPhase] at hactual
  rw [hactual]
  change rightCoarse (labeledReward reward) 0 1 = 1
  exact labeled_rightCoarse_zero_one reward hchild

/-- The failing outside row has the packet's literal signed inverse weight. -/
theorem negative_row_inverse_weight :
    Matrix.vecMul (![(-2 : ℝ), 0, 1]) PassiveRowFourFixture.childMatrix⁻¹ =
      ![0, -1, 0] := by
  rw [PassiveRowFourFixture.childMatrix_inverse]
  funext column
  fin_cases column <;> norm_num [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

/-- Dropping the outside floor gives gain one in every positive child subdivision.
The two displayed payoffs are actual pure-time terminal values of the constructed source. -/
theorem negative_row_immediate_quit_gain_one (reward : Reward)
    (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 =
      (![(-2 : ℝ), 0, 1]) owner)
    (hown : quittingSoloReward reward 3 3 = 0)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = 0)
    (m : ℕ) (hm : 0 < m) :
    quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm) 3 none 0 = -1 ∧
      quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
        3 (some 0) 0 = 0 ∧
      quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
          3 (some 0) 0 -
        quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
          3 none 0 = 1 := by
  have hactiveRow (time : ℕ) : quittingSoloReward reward
      (active reward hchild m hm time).1 3 =
      -quittingSoloReward reward (active reward hchild m hm time).1 1 := by
    obtain ⟨owner, hequal⟩ := childEquiv.surjective (active reward hchild m hm time)
    rw [← hequal]
    change quittingSoloReward reward owner.castSucc 3 =
      -quittingSoloReward reward owner.castSucc (1 : Fin 3).castSucc
    rw [hrow, hchild]
    fin_cases owner <;>
      norm_num [PassiveRowFourFixture.childMatrix, PassiveRowFourFixture.matrix]
  have hnever : quittingRootSequencePureTimeTerminalValue reward
      (roots reward hchild m hm) 3 none 0 = -1 := by
    rw [never_eq_terminalValue reward _ 3
      (fun time => roots_solo reward hchild m hm time 3
        (outside_ne_active reward hchild m hm time))]
    rw [terminalValue_neg_coordinate_of_solo reward _
      (fun time => (active reward hchild m hm time).1)
      (roots_solo reward hchild m hm) 3 1 hactiveRow, initial_child_one_value]
  have hquit : quittingRootSequencePureTimeTerminalValue reward
      (roots reward hchild m hm) 3 (some 0) 0 = 0 := by
    rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
      quittingFixedOpponentsQuitValue_eq_of_soloRoot reward _
        (roots_solo reward hchild m hm 0) (outside_ne_active reward hchild m hm 0)]
    obtain ⟨owner, hequal⟩ := childEquiv.surjective (active reward hchild m hm 0)
    have hcollision : quittingSingletonCollisionReward reward
        (active reward hchild m hm 0).1 3 = 0 := by
      rw [← hequal]
      exact hpair owner
    rw [hown, hcollision]
    ring
  exact ⟨hnever, hquit, by rw [hquit, hnever]; norm_num⟩

/-- With outside singleton row zero, Never pays zero at every actual suffix,
and quitting at the current date pays the sole owner's actual hazard times `R`. -/
theorem zero_row_joining_values (reward : Reward) (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R)
    (m : ℕ) (hm : 0 < m) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
        3 none time = 0 ∧
      quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
        3 (some time) time =
        (roots reward hchild m hm time (active reward hchild m hm time).1 true).toReal * R := by
  have hactiveRow (date : ℕ) : quittingSoloReward reward
      (active reward hchild m hm date).1 3 = 0 := by
    obtain ⟨owner, hequal⟩ := childEquiv.surjective (active reward hchild m hm date)
    rw [← hequal]
    exact hrow owner
  constructor
  · rw [never_eq_terminalValue reward _ 3
      (fun date => roots_solo reward hchild m hm date 3
        (outside_ne_active reward hchild m hm date))]
    exact terminalValue_zero_of_solo reward _
      (fun date => (active reward hchild m hm date).1)
      (roots_solo reward hchild m hm) 3 hactiveRow time
  · rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
      quittingFixedOpponentsQuitValue_eq_of_soloRoot reward _
        (roots_solo reward hchild m hm time) (outside_ne_active reward hchild m hm time)]
    obtain ⟨owner, hequal⟩ := childEquiv.surjective (active reward hchild m hm time)
    have hcollision : quittingSingletonCollisionReward reward
        (active reward hchild m hm time).1 3 = R := by
      rw [← hequal]
      exact hpair owner
    rw [hown, hcollision]
    ring

/-- A cap on the actual active-owner hazard gives the packet's exact joining bound. -/
theorem zero_row_joining_gain_le (reward : Reward) (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ) (hR : 0 < R)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R)
    (m : ℕ) (hm : 0 < m) (time : ℕ) (delta : ℝ)
    (hhazard : (roots reward hchild m hm time
      (active reward hchild m hm time).1 true).toReal ≤ delta) :
    quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
        3 (some time) time -
      quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
        3 none time ≤ R * delta := by
  obtain ⟨hnever, hquit⟩ := zero_row_joining_values reward hchild hrow hown R hpair m hm time
  rw [hquit, hnever, sub_zero, mul_comm R]
  exact mul_le_mul_of_nonneg_right hhazard hR.le

/-- The exact gain at an arbitrary finite date includes its actual reach probability.
This uses the existing pure-time response identity rather than a local value premise. -/
theorem zero_row_finite_time_gain_eq (reward : Reward) (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R)
    (m : ℕ) (hm : 0 < m) (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
        3 (some (start + fuel)) start -
      quittingRootSequencePureTimeTerminalValue reward (roots reward hchild m hm)
        3 none start =
      quittingOpponentSurvivalWeight (roots reward hchild m hm) 3 start fuel *
        ((roots reward hchild m hm (start + fuel)
          (active reward hchild m hm (start + fuel)).1 true).toReal * R) := by
  obtain ⟨hnever, hquit⟩ :=
    zero_row_joining_values reward hchild hrow hown R hpair m hm (start + fuel)
  have hlocal := quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
    reward (roots reward hchild m hm) 3 (start + fuel) 0
  simp only [Nat.add_zero, quittingOpponentSurvivalWeight, Finset.range_zero,
    Finset.prod_empty, one_mul] at hlocal
  rw [hquit, hnever, sub_zero] at hlocal
  rw [quittingRootSequencePureTimeTerminalValue_some_sub_none_eq, ← hlocal]


/-- Literal unequal-length rational-function calendar with the outsider prescribed Never. -/
def variableRoots (reward : Reward) (hchild : HasChildSingletons reward)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) : ℕ → Fin 4 → PMF Bool :=
  quittingExtendDeletedRoots (· ∈ outsideBlock)
    (quittingCyclicRootSequence ((childCertificate reward hchild).variableRoot length)
      ((childCertificate reward hchild).variableInitial length hlen))

/-- The actual child owner in the unequal-length source. -/
def variableActive (reward : Reward) (hchild : HasChildSingletons reward)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) (time : ℕ) : Child :=
  (childCertificate reward hchild).owner
    (BalancedSingletonCycleCertificate.variableCoordinates length
      (quittingCyclicOrbit ((childCertificate reward hchild).variableInitial length hlen) time)).1

private theorem variableRoots_solo (reward : Reward) (hchild : HasChildSingletons reward)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) (time : ℕ) (other : Fin 4)
    (hne : other ≠ (variableActive reward hchild length hlen time).1) :
    variableRoots reward hchild length hlen time other = PMF.pure false := by
  by_cases hdeleted : other ∈ outsideBlock
  · exact quittingExtendDeletedRoots_of_deleted (· ∈ outsideBlock) _ time hdeleted
  · have hne' : (⟨other, hdeleted⟩ : Child) ≠
        variableActive reward hchild length hlen time := by
      intro hequal
      exact hne (congrArg Subtype.val hequal)
    change variableRoots reward hchild length hlen time (⟨other, hdeleted⟩ : Child).1 = _
    unfold variableRoots
    rw [quittingExtendDeletedRoots_apply]
    exact (childCertificate reward hchild).variableRoot_solo length _
      ⟨other, hdeleted⟩ hne'

private theorem variableOutside_ne_active (reward : Reward) (hchild : HasChildSingletons reward)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) (time : ℕ) :
    (3 : Fin 4) ≠ (variableActive reward hchild length hlen time).1 := by
  intro hequal
  apply (variableActive reward hchild length hlen time).2
  simp [outsideBlock, ← hequal]

private theorem variable_initial_child_one_value
    (reward : Reward) (hchild : HasChildSingletons reward)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) :
    quittingRootSequenceTerminalValue reward (variableRoots reward hchild length hlen) 1 0 = 1 := by
  change quittingRootSequenceTerminalValue reward
    (variableRoots reward hchild length hlen) (childEquiv 1).1 0 = 1
  unfold variableRoots
  rw [quittingRootSequenceTerminalValue_extendDeletedRoots,
    (childCertificate reward hchild).variable_rootSequence_terminalValue_eq length hlen,
    quittingCyclicOrbit_zero, (childCertificate reward hchild).variableValue_initial length hlen]
  change rightCoarse (labeledReward reward) 0 1 = 1
  exact labeled_rightCoarse_zero_one reward hchild
/-- Dropping the outside floor gives gain one in every positive unequal-length child subdivision.
The two displayed payoffs are actual pure-time terminal values of the constructed source. -/
theorem variable_negative_row_immediate_quit_gain_one (reward : Reward)
    (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 =
      (![(-2 : ℝ), 0, 1]) owner)
    (hown : quittingSoloReward reward 3 3 = 0)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = 0)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) :
    quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen) 3
      none 0 = -1 ∧
      quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
        3 (some 0) 0 = 0 ∧
      quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
          3 (some 0) 0 -
        quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
          3 none 0 = 1 := by
  have hactiveRow (time : ℕ) : quittingSoloReward reward
      (variableActive reward hchild length hlen time).1 3 =
      -quittingSoloReward reward (variableActive reward hchild length hlen time).1 1 := by
    obtain ⟨owner, hequal⟩ := childEquiv.surjective (variableActive reward hchild length hlen time)
    rw [← hequal]
    change quittingSoloReward reward owner.castSucc 3 =
      -quittingSoloReward reward owner.castSucc (1 : Fin 3).castSucc
    rw [hrow, hchild]
    fin_cases owner <;>
      norm_num [PassiveRowFourFixture.childMatrix, PassiveRowFourFixture.matrix]
  have hnever : quittingRootSequencePureTimeTerminalValue reward
      (variableRoots reward hchild length hlen) 3 none 0 = -1 := by
    rw [never_eq_terminalValue reward _ 3
      (fun time => variableRoots_solo reward hchild length hlen time 3
        (variableOutside_ne_active reward hchild length hlen time))]
    rw [terminalValue_neg_coordinate_of_solo reward _
      (fun time => (variableActive reward hchild length hlen time).1)
      (variableRoots_solo reward hchild length hlen) 3 1 hactiveRow,
        variable_initial_child_one_value]
  have hquit : quittingRootSequencePureTimeTerminalValue reward
      (variableRoots reward hchild length hlen) 3 (some 0) 0 = 0 := by
    rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
      quittingFixedOpponentsQuitValue_eq_of_soloRoot reward _
        (variableRoots_solo reward hchild length hlen 0) (variableOutside_ne_active reward hchild
          length hlen 0)]
    obtain ⟨owner, hequal⟩ := childEquiv.surjective (variableActive reward hchild length hlen 0)
    have hcollision : quittingSingletonCollisionReward reward
        (variableActive reward hchild length hlen 0).1 3 = 0 := by
      rw [← hequal]
      exact hpair owner
    rw [hown, hcollision]
    ring
  exact ⟨hnever, hquit, by rw [hquit, hnever]; norm_num⟩

/-- With outside singleton row zero, Never pays zero at every actual suffix,
and quitting at the current date pays the sole owner's actual hazard times `R`. -/
theorem variable_zero_row_joining_values (reward : Reward) (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
        3 none time = 0 ∧
      quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
        3 (some time) time =
        (variableRoots reward hchild length hlen time (variableActive reward hchild length hlen
          time).1 true).toReal * R := by
  have hactiveRow (date : ℕ) : quittingSoloReward reward
      (variableActive reward hchild length hlen date).1 3 = 0 := by
    obtain ⟨owner, hequal⟩ := childEquiv.surjective (variableActive reward hchild length hlen date)
    rw [← hequal]
    exact hrow owner
  constructor
  · rw [never_eq_terminalValue reward _ 3
      (fun date => variableRoots_solo reward hchild length hlen date 3
        (variableOutside_ne_active reward hchild length hlen date))]
    exact terminalValue_zero_of_solo reward _
      (fun date => (variableActive reward hchild length hlen date).1)
      (variableRoots_solo reward hchild length hlen) 3 hactiveRow time
  · rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
      quittingFixedOpponentsQuitValue_eq_of_soloRoot reward _
        (variableRoots_solo reward hchild length hlen time) (variableOutside_ne_active reward
          hchild length hlen time)]
    obtain ⟨owner, hequal⟩ := childEquiv.surjective (variableActive reward hchild length hlen time)
    have hcollision : quittingSingletonCollisionReward reward
        (variableActive reward hchild length hlen time).1 3 = R := by
      rw [← hequal]
      exact hpair owner
    rw [hown, hcollision]
    ring

/-- A cap on the actual variableActive-owner hazard gives the packet's exact joining bound. -/
theorem variable_zero_row_joining_gain_le (reward : Reward) (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ) (hR : 0 < R)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) (time : ℕ) (delta : ℝ)
    (hhazard : (variableRoots reward hchild length hlen time
      (variableActive reward hchild length hlen time).1 true).toReal ≤ delta) :
    quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
        3 (some time) time -
      quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
        3 none time ≤ R * delta := by
  obtain ⟨hnever, hquit⟩ := variable_zero_row_joining_values reward hchild hrow hown R hpair
    length hlen time
  rw [hquit, hnever, sub_zero, mul_comm R]
  exact mul_le_mul_of_nonneg_right hhazard hR.le

/-- The exact gain at an arbitrary finite date includes its actual reach probability.
This uses the existing pure-time response identity rather than a local value premise. -/
theorem variable_zero_row_finite_time_gain_eq (reward : Reward) (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R)
    (length : Fin 3 → ℕ) (hlen : ∀ p, 0 < length p) (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
        3 (some (start + fuel)) start -
      quittingRootSequencePureTimeTerminalValue reward (variableRoots reward hchild length hlen)
        3 none start =
      quittingOpponentSurvivalWeight (variableRoots reward hchild length hlen) 3 start fuel *
        ((variableRoots reward hchild length hlen (start + fuel)
          (variableActive reward hchild length hlen (start + fuel)).1 true).toReal * R) := by
  obtain ⟨hnever, hquit⟩ :=
    variable_zero_row_joining_values reward hchild hrow hown R hpair length hlen (start + fuel)
  have hlocal := quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
    reward (variableRoots reward hchild length hlen) 3 (start + fuel) 0
  simp only [Nat.add_zero, quittingOpponentSurvivalWeight, Finset.range_zero,
    Finset.prod_empty, one_mul] at hlocal
  rw [hquit, hnever, sub_zero] at hlocal
  rw [quittingRootSequencePureTimeTerminalValue_some_sub_none_eq, ← hlocal]

/-- One date per phase leaves a literal positive joining gain `R / 2`. -/
theorem coarse_zero_row_joining_gain_eq_half (reward : Reward)
    (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ) (hR : 0 < R)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R) :
    let source := variableRoots reward hchild (fun _ => 1) (fun _ => by decide)
    quittingRootSequencePureTimeTerminalValue reward source 3 (some 0) 0 -
        quittingRootSequencePureTimeTerminalValue reward source 3 none 0 = R / 2 ∧
      0 < quittingRootSequencePureTimeTerminalValue reward source 3 (some 0) 0 -
        quittingRootSequencePureTimeTerminalValue reward source 3 none 0 := by
  dsimp only
  let certificate := childCertificate reward hchild
  have hhalf : (variableRoots reward hchild (fun _ => 1) (fun _ => by decide) 0
      (variableActive reward hchild (fun _ => 1) (fun _ => by decide) 0).1 true).toReal =
      1 / 2 := by
    unfold variableRoots
    rw [quittingExtendDeletedRoots_apply]
    simp only [quittingCyclicRootSequence, variableActive, quittingCyclicOrbit_zero]
    rw [certificate.variableRoot_quitMass]
    simp only [BalancedSingletonCycleCertificate.variableInitial,
      BalancedSingletonCycleCertificate.variableCoordinates_phase]
    change Math.rationalArcHazard (rightAlpha (labeledReward reward)) 1 0 = 1 / 2
    rw [labeled_rightAlpha_eq_half reward hchild]
    norm_num [Math.rationalArcHazard]
  obtain ⟨hnever, hquit⟩ := variable_zero_row_joining_values reward hchild hrow hown R hpair
    (fun _ => 1) (fun _ => by decide) 0
  rw [hquit, hnever, hhalf, sub_zero]
  constructor
  · ring
  · exact mul_pos (by norm_num) hR

/-- The literal tolerance-selected rational calendar, lifted by canonical deletion. -/
def rationalRoots (reward : Reward) (hchild : HasChildSingletons reward) (delta : ℝ) :
    ℕ → Fin 4 → PMF Bool :=
  quittingExtendDeletedRoots (· ∈ outsideBlock)
    (quittingCyclicRootSequence ((childCertificate reward hchild).rationalRoot delta)
      ((childCertificate reward hchild).rationalInitial delta))

private theorem rationalRoots_eq_variableRoots
    (reward : Reward) (hchild : HasChildSingletons reward) (delta : ℝ) :
    rationalRoots reward hchild delta =
      variableRoots reward hchild ((childCertificate reward hchild).rationalLength delta)
        ((childCertificate reward hchild).rationalLength_pos delta) := rfl

/-- The actual chronological owner of the tolerance-selected calendar. -/
def rationalActive (reward : Reward) (hchild : HasChildSingletons reward)
    (delta : ℝ) (time : ℕ) : Child :=
  variableActive reward hchild ((childCertificate reward hchild).rationalLength delta)
    ((childCertificate reward hchild).rationalLength_pos delta) time

/-- The exact floor falsifier also uses the literal tolerance-selected rational source. -/
theorem rational_negative_row_immediate_quit_gain_one (reward : Reward)
    (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 =
      (![(-2 : ℝ), 0, 1]) owner)
    (hown : quittingSoloReward reward 3 3 = 0)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = 0) (delta : ℝ) :
    quittingRootSequencePureTimeTerminalValue reward (rationalRoots reward hchild delta)
        3 none 0 = -1 ∧
      quittingRootSequencePureTimeTerminalValue reward (rationalRoots reward hchild delta)
        3 (some 0) 0 = 0 ∧
      quittingRootSequencePureTimeTerminalValue reward (rationalRoots reward hchild delta)
          3 (some 0) 0 -
        quittingRootSequencePureTimeTerminalValue reward (rationalRoots reward hchild delta)
          3 none 0 = 1 := by
  simpa only [rationalRoots_eq_variableRoots] using
    variable_negative_row_immediate_quit_gain_one reward hchild hrow hown hpair
      ((childCertificate reward hchild).rationalLength delta)
      ((childCertificate reward hchild).rationalLength_pos delta)

/-- Actual Never and joining values on the tolerance-selected rational-function source. -/
theorem rational_zero_row_joining_values (reward : Reward) (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R) (delta : ℝ) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward (rationalRoots reward hchild delta)
        3 none time = 0 ∧
      quittingRootSequencePureTimeTerminalValue reward (rationalRoots reward hchild delta)
        3 (some time) time =
        (rationalRoots reward hchild delta time
          (rationalActive reward hchild delta time).1 true).toReal * R := by
  simpa only [rationalRoots_eq_variableRoots, rationalActive] using
    variable_zero_row_joining_values reward hchild hrow hown R hpair
      ((childCertificate reward hchild).rationalLength delta)
      ((childCertificate reward hchild).rationalLength_pos delta) time

/-- The rational producer itself supplies the hazard cap, so the actual joining gain
is at most `R * delta` without a supplied continuation or hazard premise. -/
theorem rational_zero_row_joining_gain_le (reward : Reward) (hchild : HasChildSingletons reward)
    (hrow : ∀ owner : Fin 3, quittingSoloReward reward owner.castSucc 3 = 0)
    (hown : quittingSoloReward reward 3 3 = 0) (R : ℝ) (hR : 0 < R)
    (hpair : ∀ owner : Fin 3,
      quittingSingletonCollisionReward reward owner.castSucc 3 = R)
    (delta : ℝ) (hdelta : 0 < delta) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward (rationalRoots reward hchild delta)
        3 (some time) time -
      quittingRootSequencePureTimeTerminalValue reward (rationalRoots reward hchild delta)
        3 none time ≤ R * delta := by
  let certificate := childCertificate reward hchild
  have hactual : (variableRoots reward hchild (certificate.rationalLength delta)
      (certificate.rationalLength_pos delta) time
      (variableActive reward hchild (certificate.rationalLength delta)
        (certificate.rationalLength_pos delta) time).1 true).toReal ≤ delta := by
    unfold variableRoots
    rw [quittingExtendDeletedRoots_apply]
    let phase := quittingCyclicOrbit
      (certificate.variableInitial (certificate.rationalLength delta)
        (certificate.rationalLength_pos delta)) time
    change ((certificate.variableRoot (certificate.rationalLength delta) phase)
      (certificate.owner (BalancedSingletonCycleCertificate.variableCoordinates
        (certificate.rationalLength delta) phase).1) true).toReal ≤ delta
    rw [certificate.variableRoot_quitMass]
    exact Math.rationalArcHazard_le_tolerance
      (certificate.hazard_nonneg _) (certificate.hazard_lt_one _) hdelta _
  simpa only [rationalRoots_eq_variableRoots] using
    variable_zero_row_joining_gain_le reward hchild hrow hown R hR hpair
      (certificate.rationalLength delta) (certificate.rationalLength_pos delta) time delta hactual

end GameTheory.PassiveRowJoiningBoundary
