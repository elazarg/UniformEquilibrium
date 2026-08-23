/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.SmallHazardExpectation
import MathUE.FiniteCyclicVariation
import MathUE.LinearProgramming.R0Margin
import Mathlib.Logic.Equiv.Fin.Rotate
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Vanishing returned product blocks force a homogeneous singleton solution

A returned block is a nonempty finite cycle of product roots together with a
payoff annotation at each phase.  This file measures aggregate absolute
Bellman error and the two probability-weighted endpoint regrets.  If both are
little-o of the block's vanishing total Quit hazard, then the normalized
singleton matrix has a homogeneous simplex solution.  The phase count may
vary without a common bound.

This is an algebraic obstruction for supplied finite rows.  It does not
construct a block or promote local endpoint tests to an unrestricted
behavioral equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct Math.LinearProgramming
  QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A positive-length finite cycle of product roots and phase payoffs.  The
number of phases is `extraPhases + 1`, so no separate nonemptiness proof is
carried by consumers. -/
structure QuittingReturnedProductBlock (ι : Type) where
  extraPhases : ℕ
  root : Fin (extraPhases + 1) → ι → PMF Bool
  value : Fin (extraPhases + 1) → Payoff ι

namespace QuittingReturnedProductBlock

variable (block : QuittingReturnedProductBlock ι)

/-- The next phase, including the return seam. -/
def next (phase : Fin (block.extraPhases + 1)) :
    Fin (block.extraPhases + 1) :=
  finRotate (block.extraPhases + 1) phase

/-- Playerwise Quit probability at one phase. -/
def hazard (phase : Fin (block.extraPhases + 1)) (who : ι) : ℝ :=
  (block.root phase who true).toReal

/-- Total hazard in one phase. -/
def phaseHazard (phase : Fin (block.extraPhases + 1)) : ℝ :=
  ∑ who : ι, block.hazard phase who

/-- Total first-order hazard accumulated around the returned block. -/
def totalHazard : ℝ :=
  ∑ phase : Fin (block.extraPhases + 1), block.phaseHazard phase

/-- Cumulative first-order hazard owned by one player. -/
def cumulativeHazard (who : ι) : ℝ :=
  ∑ phase : Fin (block.extraPhases + 1), block.hazard phase who

/-- Aggregate absolute Bellman residual. -/
def bellmanError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  ∑ phase : Fin (block.extraPhases + 1), ∑ who : ι,
    |block.value phase who -
      quittingRootSuccessorPayoff reward (block.value (block.next phase))
        (block.root phase) who|

/-- The sum of the exact pure-Quit and pure-Continue endpoint regrets. -/
def endpointRegret
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  ∑ phase : Fin (block.extraPhases + 1), ∑ who : ι,
    (max 0 ((block.root phase who false).toReal *
      quittingRootEndpointDifference reward
        (block.value (block.next phase)) (block.root phase) who) +
    max 0 (-(block.root phase who true).toReal *
      quittingRootEndpointDifference reward
        (block.value (block.next phase)) (block.root phase) who))

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem hazard_nonneg (phase : Fin (block.extraPhases + 1)) (who : ι) :
    0 ≤ block.hazard phase who :=
  ENNReal.toReal_nonneg

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem hazard_le_one (phase : Fin (block.extraPhases + 1)) (who : ι) :
    block.hazard phase who ≤ 1 := by
  unfold hazard
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((block.root phase who).coe_le_one true)

omit [DecidableEq ι] [Nonempty ι] in
theorem phaseHazard_nonneg (phase : Fin (block.extraPhases + 1)) :
    0 ≤ block.phaseHazard phase :=
  Finset.sum_nonneg fun who _ => block.hazard_nonneg phase who

omit [DecidableEq ι] [Nonempty ι] in
theorem totalHazard_nonneg : 0 ≤ block.totalHazard :=
  Finset.sum_nonneg fun phase _ => block.phaseHazard_nonneg phase

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem cumulativeHazard_nonneg (who : ι) :
    0 ≤ block.cumulativeHazard who :=
  Finset.sum_nonneg fun phase _ => block.hazard_nonneg phase who

omit [DecidableEq ι] [Nonempty ι] in
theorem sum_cumulativeHazard :
    ∑ who : ι, block.cumulativeHazard who = block.totalHazard := by
  unfold cumulativeHazard totalHazard phaseHazard
  rw [Finset.sum_comm]

/-- Normalize cumulative owner hazards into a simplex direction. -/
def normalizedHazard (hpositive : 0 < block.totalHazard) :
    stdSimplex ℝ ι := by
  refine ⟨fun who => block.cumulativeHazard who / block.totalHazard,
    fun who => div_nonneg (block.cumulativeHazard_nonneg who)
      hpositive.le, ?_⟩
  rw [← Finset.sum_div, block.sum_cumulativeHazard,
    div_self hpositive.ne']

omit [DecidableEq ι] [Nonempty ι] in
theorem bellmanError_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ block.bellmanError reward :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [Nonempty ι] in
theorem endpointRegret_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ block.endpointRegret reward := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (le_max_left _ _) (le_max_left _ _)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem quitRates_eq_hazard (phase : Fin (block.extraPhases + 1)) :
    quittingRootQuitRates (block.root phase) = block.hazard phase :=
  rfl

end QuittingReturnedProductBlock

/-! ## One-row estimates -/

omit [DecidableEq ι] [Nonempty ι] in
theorem quittingStationaryContinueMass_eq_continueMass_quitRates
    (root : ι → PMF Bool) :
    quittingStationaryContinueMass root =
      continueMass (quittingRootQuitRates root) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  unfold continueMass quittingRootQuitRates
  apply Finset.prod_congr rfl
  intro who _
  rw [pmfBool_false_toReal]

omit [DecidableEq ι] [Nonempty ι] in
theorem quittingRootAbsorptionMass_le_sum_quitRates
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root ≤ ∑ who, quittingRootQuitRates root who := by
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_continueMass_quitRates]
  linarith [one_sub_sum_le_continueMass (quittingRootQuitRates root)
    (fun _ => ENNReal.toReal_nonneg)
    (fun who => ENNReal.toReal_mono ENNReal.one_ne_top
      ((root who).coe_le_one true))]

omit [DecidableEq ι] [Nonempty ι] in
theorem abs_quittingRootSuccessorPayoff_sub_tail_le_sum_quitRates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : |tail who| ≤ M) :
    |quittingRootSuccessorPayoff reward tail root who - tail who| ≤
      2 * M * ∑ owner, quittingRootQuitRates root owner := by
  exact (abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
    reward tail root who M hreward htail).trans
      (mul_le_mul_of_nonneg_left
        (quittingRootAbsorptionMass_le_sum_quitRates root)
        (mul_nonneg (by norm_num) (quittingRewardCoordinateBound_nonneg_of_player
          reward who hreward)))

omit [Nonempty ι] in
theorem abs_quittingRootEndpointDifference_sub_solo_sub_tail_le_sum_quitRates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : |tail who| ≤ M) :
    |quittingRootEndpointDifference reward tail root who -
        (reward (quittingSingletonTerminal who) who - tail who)| ≤
      4 * M * ∑ owner, quittingRootQuitRates root owner := by
  let forced := Function.update root who (PMF.pure false)
  have hquit :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward tail root who M hreward
  have hcontinue :=
    abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward tail forced who M hreward htail
  have hforced : quittingRootAbsorptionMass forced ≤
      ∑ owner, quittingRootQuitRates root owner := by
    refine (quittingRootAbsorptionMass_le_sum_quitRates forced).trans ?_
    apply Finset.sum_le_sum
    intro owner _
    by_cases howner : owner = who
    · subst owner
      simp [forced, quittingRootQuitRates]
    · simp [forced, quittingRootQuitRates, howner]
  have hopponent : quittingRootOpponentAbsorptionMass root who ≤
      ∑ owner, quittingRootQuitRates root owner := by
    change quittingRootAbsorptionMass forced ≤ _
    exact hforced
  have hcontinueDef : quittingRootSuccessorPayoff reward tail forced who =
      quittingRootContinuePayoff reward tail root who := rfl
  rw [hcontinueDef] at hcontinue
  rw [quittingRootEndpointDifference]
  calc
    |(quittingRootQuitPayoff reward tail root who -
          quittingRootContinuePayoff reward tail root who) -
        (reward (quittingSingletonTerminal who) who - tail who)| =
      |(quittingRootQuitPayoff reward tail root who -
          reward (quittingSingletonTerminal who) who) -
        (quittingRootContinuePayoff reward tail root who - tail who)| := by ring_nf
    _ ≤ |quittingRootQuitPayoff reward tail root who -
          reward (quittingSingletonTerminal who) who| +
        |quittingRootContinuePayoff reward tail root who - tail who| := abs_sub _ _
    _ ≤ 2 * M * (∑ owner, quittingRootQuitRates root owner) +
        2 * M * (∑ owner, quittingRootQuitRates root owner) :=
      add_le_add
        (hquit.trans (mul_le_mul_of_nonneg_left hopponent
          (mul_nonneg (by norm_num)
            (quittingRewardCoordinateBound_nonneg_of_player reward who hreward))))
        (hcontinue.trans (mul_le_mul_of_nonneg_left hforced
          (mul_nonneg (by norm_num)
            (quittingRewardCoordinateBound_nonneg_of_player reward who hreward))))
    _ = 4 * M * ∑ owner, quittingRootQuitRates root owner := by ring

/-- Scalar terminal table obtained from one quitting reward coordinate. -/
def quittingRootScalarTerminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (coalition : Finset ι) : ℝ :=
  if h : coalition.Nonempty then reward ⟨coalition, h⟩ who else 0

omit [Nonempty ι] in
/-- The repository root successor is literally the generic finite Bernoulli
expectation of the scalar terminal table. -/
theorem quittingRootSuccessorPayoff_eq_smallHazardExpectation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      smallHazardExpectation (quittingRootScalarTerminal reward who)
        (tail who) (quittingRootQuitRates root) := by
  have habsorbing : quittingRootAbsorbingContribution reward root who =
      ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
        coalitionMass (quittingRootQuitRates root) coalition *
          quittingRootScalarTerminal reward who coalition := by
    rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
    change (∑ coalition,
      coalitionMass (quittingRootQuitRates root) coalition *
        quittingProjectiveCoalitionReward reward coalition who) = _
    rw [← Finset.add_sum_erase Finset.univ
      (fun coalition : Finset ι =>
        coalitionMass (quittingRootQuitRates root) coalition *
          quittingProjectiveCoalitionReward reward coalition who)
      (Finset.mem_univ ∅)]
    simp only [quittingProjectiveCoalitionReward_empty, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro coalition hcoalition
    have hnonempty : coalition.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hcoalition)
    simp [quittingRootScalarTerminal, quittingProjectiveCoalitionReward, hnonempty]
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    habsorbing,
    quittingStationaryContinueMass_eq_continueMass_quitRates]
  unfold smallHazardExpectation
  ring

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem quittingRootScalarTerminal_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) :
    quittingRootScalarTerminal reward who {owner} =
      reward (quittingSingletonTerminal owner) who := by
  simp [quittingRootScalarTerminal, quittingSingletonTerminal]

omit [Nonempty ι] in
/-- A generic simplex residual of the normalized singleton matrix is the
singleton-reward barycenter minus the player's own singleton payoff. -/
theorem singletonLCPResidual_normalizedSoloMatrix_eq_singletonBarycenter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (direction : stdSimplex ℝ ι) (who : ι) :
    singletonLCPResidual (normalizedSoloMatrix reward) direction who =
      (∑ owner, (direction : ι → ℝ) owner *
        reward (quittingSingletonTerminal owner) who) -
      reward (quittingSingletonTerminal who) who := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold singletonLCPResidual wsum dotProduct quittingProjectiveLCPMatrix
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hmass : ∑ owner, direction owner = 1 := direction.property.2
  rw [hmass, one_mul]
  rfl

omit [Nonempty ι] in
/-- The exact product successor has the singleton linearization prescribed by
the raw Quit rates, with a quadratic error uniform over bounded tails and
terminal rewards. -/
theorem abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : |tail who| ≤ M) :
    |quittingRootSuccessorPayoff reward tail root who - tail who -
        ∑ owner, quittingRootQuitRates root owner *
          (reward (quittingSingletonTerminal owner) who - tail who)| ≤
      2 * M * (∑ owner, quittingRootQuitRates root owner) ^ 2 := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  rw [quittingRootSuccessorPayoff_eq_smallHazardExpectation]
  have hbound :=
    abs_smallHazardExpectation_sub_tail_sub_linearization_le
      (quittingRootScalarTerminal reward who) (tail who)
      (quittingRootQuitRates root) hM hM htail
      (fun coalition hcoalition => by
        simp [quittingRootScalarTerminal, hcoalition,
          hreward ⟨coalition, hcoalition⟩ who])
      (fun _ => ENNReal.toReal_nonneg)
      (fun owner => ENNReal.toReal_mono ENNReal.one_ne_top
        ((root owner).coe_le_one true))
  simp only [smallHazardLinearization,
    quittingRootScalarTerminal_singleton] at hbound
  calc
    |_ - _ - _| ≤ (M / 2 + 3 * M / 2) *
        (∑ owner, quittingRootQuitRates root owner) ^ 2 := hbound
    _ = 2 * M * (∑ owner, quittingRootQuitRates root owner) ^ 2 := by ring

namespace QuittingReturnedProductBlock

variable (block : QuittingReturnedProductBlock ι)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Cyclic rotation preserves the sum of any scalar phase annotation. -/
theorem sum_comp_next (f : Fin (block.extraPhases + 1) → ℝ) :
    ∑ phase, f (block.next phase) = ∑ phase, f phase := by
  exact Function.Bijective.sum_comp
    (finRotate (block.extraPhases + 1)).bijective f

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The signed phase increments telescope exactly around a returned block. -/
theorem sum_value_sub_next (who : ι) :
    ∑ phase, (block.value phase who - block.value (block.next phase) who) = 0 := by
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr
    (block.sum_comp_next (fun phase => block.value phase who)).symm

omit [DecidableEq ι] [Nonempty ι] in
/-- One coordinate of the signed aggregate Bellman residual is controlled by
the declared aggregate absolute residual. -/
theorem abs_sum_bellmanResidual_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    |∑ phase, (block.value phase who -
        quittingRootSuccessorPayoff reward (block.value (block.next phase))
          (block.root phase) who)| ≤ block.bellmanError reward := by
  calc
    |∑ phase, (block.value phase who -
        quittingRootSuccessorPayoff reward (block.value (block.next phase))
          (block.root phase) who)| ≤
      ∑ phase, |block.value phase who -
        quittingRootSuccessorPayoff reward (block.value (block.next phase))
          (block.root phase) who| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ block.bellmanError reward := by
      unfold bellmanError
      apply Finset.sum_le_sum
      intro phase _
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun player => |block.value phase player -
          quittingRootSuccessorPayoff reward
            (block.value (block.next phase)) (block.root phase) player|)
        (fun player _ => abs_nonneg _) (Finset.mem_univ who)

omit [DecidableEq ι] [Nonempty ι] in
/-- The quadratic row hazards aggregate below the square of total block
hazard, uniformly in the number of phases. -/
theorem sum_phaseHazard_sq_le :
    ∑ phase, block.phaseHazard phase ^ 2 ≤ block.totalHazard ^ 2 := by
  exact sum_sq_le_sq_sum block.phaseHazard block.phaseHazard_nonneg

omit [Nonempty ι] in
/-- Summing the exact singleton linearizations around the returned block
leaves only aggregate Bellman error and a quadratic product-law remainder. -/
theorem abs_sum_singletonLinearization_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M) (who : ι) :
    |∑ phase, ∑ owner, block.hazard phase owner *
        (reward (quittingSingletonTerminal owner) who -
          block.value (block.next phase) who)| ≤
      block.bellmanError reward + 2 * M * block.totalHazard ^ 2 := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  let linear : Fin (block.extraPhases + 1) → ℝ := fun phase =>
    ∑ owner, block.hazard phase owner *
      (reward (quittingSingletonTerminal owner) who -
        block.value (block.next phase) who)
  let successorMove : Fin (block.extraPhases + 1) → ℝ := fun phase =>
    quittingRootSuccessorPayoff reward (block.value (block.next phase))
      (block.root phase) who - block.value (block.next phase) who
  let residual : Fin (block.extraPhases + 1) → ℝ := fun phase =>
    block.value phase who -
      quittingRootSuccessorPayoff reward (block.value (block.next phase))
        (block.root phase) who
  have hrow : ∀ phase, |successorMove phase - linear phase| ≤
      2 * M * block.phaseHazard phase ^ 2 := by
    intro phase
    simpa [successorMove, linear, QuittingReturnedProductBlock.hazard,
      QuittingReturnedProductBlock.phaseHazard, quittingRootQuitRates] using
      (abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le
        reward (block.value (block.next phase)) (block.root phase) who
        hreward (hvalue (block.next phase) who))
  have htelescope : (∑ phase, successorMove phase) =
      -(∑ phase, residual phase) := by
    have hcycle := block.sum_value_sub_next who
    have hsum : (∑ phase, successorMove phase) +
        ∑ phase, residual phase = 0 := by
      rw [← Finset.sum_add_distrib]
      calc
        (∑ phase, (successorMove phase + residual phase)) =
            ∑ phase, (block.value phase who -
              block.value (block.next phase) who) := by
          apply Finset.sum_congr rfl
          intro phase _
          dsimp [successorMove, residual]
          ring
        _ = 0 := hcycle
    linarith
  have hsplit : (∑ phase, linear phase) =
      (∑ phase, (linear phase - successorMove phase)) +
        ∑ phase, successorMove phase := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro phase _
    ring
  change |∑ phase, linear phase| ≤ _
  calc
    |∑ phase, linear phase| = |(∑ phase,
        (linear phase - successorMove phase)) +
          ∑ phase, successorMove phase| := by rw [hsplit]
    _ ≤ |∑ phase, (linear phase - successorMove phase)| +
        |∑ phase, successorMove phase| := by
      exact abs_add_le _ _
    _ ≤ (∑ phase, |linear phase - successorMove phase|) +
        block.bellmanError reward := by
      apply add_le_add (Finset.abs_sum_le_sum_abs _ _)
      rw [htelescope, abs_neg]
      exact block.abs_sum_bellmanResidual_le reward who
    _ ≤ (∑ phase, 2 * M * block.phaseHazard phase ^ 2) +
        block.bellmanError reward := by
      gcongr with phase
      simpa [abs_sub_comm] using hrow phase
    _ ≤ 2 * M * block.totalHazard ^ 2 + block.bellmanError reward := by
      rw [← Finset.mul_sum]
      have hcoefficient : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
      have hsquare := mul_le_mul_of_nonneg_left
        block.sum_phaseHazard_sq_le hcoefficient
      simpa [add_comm] using
        (add_le_add_right hsquare (block.bellmanError reward))
    _ = block.bellmanError reward + 2 * M * block.totalHazard ^ 2 := by ring

omit [DecidableEq ι] [Nonempty ι] in
/-- The entire changing-length block has diameter controlled by total hazard
and aggregate Bellman error; no factor depending on the phase count occurs. -/
theorem abs_value_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (source target : Fin (block.extraPhases + 1)) (who : ι) :
    |block.value source who - block.value target who| ≤
      block.bellmanError reward + 2 * M * block.totalHazard := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  calc
    |block.value source who - block.value target who| ≤
        ∑ phase, |block.value (block.next phase) who -
          block.value phase who| := by
      simpa [QuittingReturnedProductBlock.next] using
        (Math.abs_sub_le_sum_abs_finRotate
          (fun phase => block.value phase who) source target)
    _ ≤ ∑ phase,
        (|block.value phase who -
            quittingRootSuccessorPayoff reward
              (block.value (block.next phase)) (block.root phase) who| +
          2 * M * block.phaseHazard phase) := by
      apply Finset.sum_le_sum
      intro phase _
      have hmove := abs_quittingRootSuccessorPayoff_sub_tail_le_sum_quitRates
        reward (block.value (block.next phase)) (block.root phase) who
        hreward (hvalue (block.next phase) who)
      have hmove' : |quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value (block.next phase) who| ≤
          2 * M * block.phaseHazard phase := by
        change _ ≤ 2 * M * ∑ owner,
          quittingRootQuitRates (block.root phase) owner
        exact hmove
      have htriangle : |block.value (block.next phase) who -
          block.value phase who| ≤
          |block.value phase who -
            quittingRootSuccessorPayoff reward
              (block.value (block.next phase)) (block.root phase) who| +
          |quittingRootSuccessorPayoff reward
              (block.value (block.next phase)) (block.root phase) who -
            block.value (block.next phase) who| := by
        calc
          |_ - _| = |block.value phase who -
              block.value (block.next phase) who| := abs_sub_comm _ _
          _ = |(block.value phase who -
              quittingRootSuccessorPayoff reward
                (block.value (block.next phase)) (block.root phase) who) +
            (quittingRootSuccessorPayoff reward
                (block.value (block.next phase)) (block.root phase) who -
              block.value (block.next phase) who)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      exact htriangle.trans (add_le_add (le_refl _) hmove')
    _ = (∑ phase, |block.value phase who -
          quittingRootSuccessorPayoff reward
            (block.value (block.next phase)) (block.root phase) who|) +
        2 * M * block.totalHazard := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    _ ≤ block.bellmanError reward + 2 * M * block.totalHazard := by
      gcongr
      unfold bellmanError
      apply Finset.sum_le_sum
      intro phase _
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun player => |block.value phase player -
          quittingRootSuccessorPayoff reward
            (block.value (block.next phase)) (block.root phase) player|)
        (fun player _ => abs_nonneg _) (Finset.mem_univ who)

omit [Nonempty ι] in
/-- The normalized cumulative singleton barycenter is close to the phase-zero
anchor.  This is the quantitative returned-block telescope used in the
compactness proof. -/
theorem abs_normalizedSingletonBarycenter_sub_anchor_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hpositive : 0 < block.totalHazard) (who : ι) :
    |∑ owner, (block.normalizedHazard hpositive : ι → ℝ) owner *
        (reward (quittingSingletonTerminal owner) who - block.value 0 who)| ≤
      block.bellmanError reward / block.totalHazard +
        2 * M * block.totalHazard +
        (block.bellmanError reward + 2 * M * block.totalHazard) := by
  let aggregateTail : ℝ :=
    ∑ phase, ∑ owner, block.hazard phase owner *
      (reward (quittingSingletonTerminal owner) who -
        block.value (block.next phase) who)
  let aggregateAnchor : ℝ :=
    ∑ phase, ∑ owner, block.hazard phase owner *
      (reward (quittingSingletonTerminal owner) who - block.value 0 who)
  have htail := block.abs_sum_singletonLinearization_le reward hreward hvalue who
  change |aggregateTail| ≤ _ at htail
  have hvariation : ∀ phase,
      |block.value (block.next phase) who - block.value 0 who| ≤
        block.bellmanError reward + 2 * M * block.totalHazard :=
    fun phase => block.abs_value_sub_le reward hreward hvalue
      (block.next phase) 0 who
  have hanchorSub : |aggregateAnchor - aggregateTail| ≤
      block.totalHazard *
        (block.bellmanError reward + 2 * M * block.totalHazard) := by
    calc
      |aggregateAnchor - aggregateTail| =
          |∑ phase, ∑ owner, block.hazard phase owner *
            (block.value (block.next phase) who - block.value 0 who)| := by
        unfold aggregateAnchor aggregateTail
        rw [← Finset.sum_sub_distrib]
        apply congrArg abs
        apply Finset.sum_congr rfl
        intro phase _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro owner _
        ring
      _ ≤ ∑ phase, ∑ owner, block.hazard phase owner *
          |block.value (block.next phase) who - block.value 0 who| := by
        calc
          |∑ phase, ∑ owner, _| ≤ ∑ phase, |∑ owner, _| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ phase, ∑ owner,
              |block.hazard phase owner *
                (block.value (block.next phase) who - block.value 0 who)| := by
            gcongr with phase
            exact Finset.abs_sum_le_sum_abs _ _
          _ = ∑ phase, ∑ owner, block.hazard phase owner *
              |block.value (block.next phase) who - block.value 0 who| := by
            apply Finset.sum_congr rfl
            intro phase _
            apply Finset.sum_congr rfl
            intro owner _
            rw [abs_mul, abs_of_nonneg (block.hazard_nonneg phase owner)]
      _ ≤ ∑ phase, ∑ owner, block.hazard phase owner *
          (block.bellmanError reward + 2 * M * block.totalHazard) := by
        apply Finset.sum_le_sum
        intro phase _
        apply Finset.sum_le_sum
        intro owner _
        exact mul_le_mul_of_nonneg_left (hvariation phase)
          (block.hazard_nonneg phase owner)
      _ = block.totalHazard *
          (block.bellmanError reward + 2 * M * block.totalHazard) := by
        calc
          (∑ phase, ∑ owner, block.hazard phase owner *
              (block.bellmanError reward + 2 * M * block.totalHazard)) =
              ∑ phase, block.phaseHazard phase *
                (block.bellmanError reward + 2 * M * block.totalHazard) := by
            apply Finset.sum_congr rfl
            intro phase _
            rw [← Finset.sum_mul]
            rfl
          _ = block.totalHazard *
              (block.bellmanError reward + 2 * M * block.totalHazard) := by
            rw [← Finset.sum_mul]
            rfl
  have hanchor : |aggregateAnchor| ≤
      block.bellmanError reward + 2 * M * block.totalHazard ^ 2 +
      block.totalHazard *
        (block.bellmanError reward + 2 * M * block.totalHazard) := by
    calc
      |aggregateAnchor| = |(aggregateAnchor - aggregateTail) + aggregateTail| := by
        congr 1
        ring
      _ ≤ |aggregateAnchor - aggregateTail| + |aggregateTail| := abs_add_le _ _
      _ ≤ _ := by
        simpa [add_comm] using add_le_add hanchorSub htail
  have hnormalized :
      (∑ owner, (block.normalizedHazard hpositive : ι → ℝ) owner *
        (reward (quittingSingletonTerminal owner) who - block.value 0 who)) =
        aggregateAnchor / block.totalHazard := by
    have hnumerator : (∑ owner, block.cumulativeHazard owner *
        (reward (quittingSingletonTerminal owner) who - block.value 0 who)) =
        aggregateAnchor := by
      unfold aggregateAnchor cumulativeHazard
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro phase _
      rw [Finset.sum_mul]
    change (∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
      (reward (quittingSingletonTerminal owner) who - block.value 0 who)) = _
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hnumerator]
  rw [hnormalized, abs_div, abs_of_pos hpositive]
  apply (div_le_div_of_nonneg_right hanchor hpositive.le).trans_eq
  field_simp [hpositive.ne']

omit [Nonempty ι] in
/-- Either probability-weighted endpoint regret at a displayed row is at
most the aggregate endpoint regret of the block. -/
theorem row_endpointRegret_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (phase : Fin (block.extraPhases + 1)) (who : ι) :
    max 0 ((block.root phase who false).toReal *
        quittingRootEndpointDifference reward
          (block.value (block.next phase)) (block.root phase) who) +
      max 0 (-(block.root phase who true).toReal *
        quittingRootEndpointDifference reward
          (block.value (block.next phase)) (block.root phase) who) ≤
      block.endpointRegret reward := by
  unfold endpointRegret
  have hplayer := Finset.single_le_sum
    (s := (Finset.univ : Finset ι))
    (f := fun player =>
      (max 0 ((block.root phase player false).toReal *
        quittingRootEndpointDifference reward
          (block.value (block.next phase)) (block.root phase) player) +
      max 0 (-(block.root phase player true).toReal *
        quittingRootEndpointDifference reward
          (block.value (block.next phase)) (block.root phase) player)))
    (fun player _ => add_nonneg (le_max_left _ _) (le_max_left _ _))
    (Finset.mem_univ who)
  have hphase := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun displayedPhase => ∑ player,
      (max 0 ((block.root displayedPhase player false).toReal *
        quittingRootEndpointDifference reward
          (block.value (block.next displayedPhase))
          (block.root displayedPhase) player) +
      max 0 (-(block.root displayedPhase player true).toReal *
        quittingRootEndpointDifference reward
          (block.value (block.next displayedPhase))
          (block.root displayedPhase) player)))
    (fun displayedPhase _ => Finset.sum_nonneg fun _ _ =>
      add_nonneg (le_max_left _ _) (le_max_left _ _))
    (Finset.mem_univ phase)
  exact hplayer.trans hphase

omit [Nonempty ι] in
/-- One common error controls, at every phase, endpoint difference plus the
normalized cumulative singleton-LCP residual. -/
theorem abs_endpointDifference_add_normalizedResidual_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hpositive : 0 < block.totalHazard)
    (phase : Fin (block.extraPhases + 1)) (who : ι) :
    |quittingRootEndpointDifference reward
        (block.value (block.next phase)) (block.root phase) who +
      singletonLCPResidual (normalizedSoloMatrix reward)
        (block.normalizedHazard hpositive) who| ≤
      (block.bellmanError reward / block.totalHazard +
        2 * M * block.totalHazard +
        (block.bellmanError reward + 2 * M * block.totalHazard)) +
      (block.bellmanError reward + 2 * M * block.totalHazard) +
      4 * M * block.totalHazard := by
  let difference := quittingRootEndpointDifference reward
    (block.value (block.next phase)) (block.root phase) who
  let residual := singletonLCPResidual (normalizedSoloMatrix reward)
    (block.normalizedHazard hpositive) who
  let solo := reward (quittingSingletonTerminal who) who
  let anchor := block.value 0 who
  let tail := block.value (block.next phase) who
  let barycenter := ∑ owner,
    (block.normalizedHazard hpositive : ι → ℝ) owner *
      reward (quittingSingletonTerminal owner) who
  have hbary := block.abs_normalizedSingletonBarycenter_sub_anchor_le
    reward hreward hvalue hpositive who
  have hbary' : |barycenter - anchor| ≤
      block.bellmanError reward / block.totalHazard +
        2 * M * block.totalHazard +
        (block.bellmanError reward + 2 * M * block.totalHazard) := by
    have heq : (∑ owner,
        (block.normalizedHazard hpositive : ι → ℝ) owner *
          (reward (quittingSingletonTerminal owner) who - anchor)) =
        barycenter - anchor := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      have hmass : ∑ owner, (block.normalizedHazard hpositive) owner = 1 :=
        (block.normalizedHazard hpositive).property.2
      rw [hmass, one_mul]
    rw [← heq]
    simpa [anchor] using hbary
  have hbaryEq : residual = barycenter - solo := by
    simpa [residual, barycenter] using
      singletonLCPResidual_normalizedSoloMatrix_eq_singletonBarycenter
        reward (block.normalizedHazard hpositive) who
  have htail := block.abs_value_sub_le reward hreward hvalue
    (block.next phase) 0 who
  have hdifference :=
    abs_quittingRootEndpointDifference_sub_solo_sub_tail_le_sum_quitRates
      reward (block.value (block.next phase)) (block.root phase) who
      hreward (hvalue (block.next phase) who)
  have hphaseHazard : block.phaseHazard phase ≤ block.totalHazard :=
    Finset.single_le_sum (fun displayedPhase _ =>
      block.phaseHazard_nonneg displayedPhase) (Finset.mem_univ phase)
  have hdifference' : |difference - (solo - tail)| ≤
      4 * M * block.totalHazard := by
    apply hdifference.trans
    change 4 * M * block.phaseHazard phase ≤ _
    exact mul_le_mul_of_nonneg_left hphaseHazard
      (mul_nonneg (by norm_num)
        (quittingRewardCoordinateBound_nonneg_of_player reward who hreward))
  change |difference + residual| ≤ _
  rw [hbaryEq]
  have hsplit : difference + (barycenter - solo) =
      (barycenter - anchor) + (anchor - tail) +
        (difference - (solo - tail)) := by ring
  rw [hsplit]
  calc
    |(barycenter - anchor) + (anchor - tail) +
        (difference - (solo - tail))| ≤
      |(barycenter - anchor) + (anchor - tail)| +
        |difference - (solo - tail)| := abs_add_le _ _
    _ ≤ (|barycenter - anchor| + |anchor - tail|) +
        |difference - (solo - tail)| :=
      by simpa [add_comm] using
        add_le_add_right (abs_add_le (barycenter - anchor) (anchor - tail))
          |difference - (solo - tail)|
    _ ≤ _ := add_le_add (add_le_add hbary'
      (by simpa [anchor, tail, abs_sub_comm] using htail)) hdifference'

/-- Quantitative homogeneous violation bound for one returned block. -/
theorem homogeneousViolation_normalizedHazard_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hpositive : 0 < block.totalHazard)
    (hhalf : block.totalHazard ≤ 1 / 2) :
    homogeneousViolation (normalizedSoloMatrix reward)
        (block.normalizedHazard hpositive : ι → ℝ) ≤
      let η :=
        (block.bellmanError reward / block.totalHazard +
          2 * M * block.totalHazard +
          (block.bellmanError reward + 2 * M * block.totalHazard)) +
        (block.bellmanError reward + 2 * M * block.totalHazard) +
        4 * M * block.totalHazard
      (η + block.endpointRegret reward / block.totalHazard) +
        Fintype.card ι * (η + 2 * block.endpointRegret reward) := by
  let direction := block.normalizedHazard hpositive
  let residual := fun who => singletonLCPResidual
    (normalizedSoloMatrix reward) direction who
  let η :=
    (block.bellmanError reward / block.totalHazard +
      2 * M * block.totalHazard +
      (block.bellmanError reward + 2 * M * block.totalHazard)) +
    (block.bellmanError reward + 2 * M * block.totalHazard) +
    4 * M * block.totalHazard
  have hM := quittingRewardCoordinateBound_nonneg_of_player
    reward (Classical.arbitrary ι) hreward
  have hη : 0 ≤ η := by
    dsimp only [η]
    have hBS : 0 ≤ block.bellmanError reward / block.totalHazard :=
      div_nonneg (block.bellmanError_nonneg reward) hpositive.le
    have hMS : 0 ≤ M * block.totalHazard := mul_nonneg hM hpositive.le
    have hB := block.bellmanError_nonneg reward
    linarith
  have hclose : ∀ phase who,
      |quittingRootEndpointDifference reward
        (block.value (block.next phase)) (block.root phase) who +
        residual who| ≤ η := fun phase who => by
    simpa [η, residual, direction] using
      block.abs_endpointDifference_add_normalizedResidual_le
        reward hreward hvalue hpositive phase who
  have hnegative : ∀ who, -residual who ≤
      η + 2 * block.endpointRegret reward := by
    intro who
    let phase : Fin (block.extraPhases + 1) := 0
    let difference := quittingRootEndpointDifference reward
      (block.value (block.next phase)) (block.root phase) who
    have hpPlayer : block.hazard phase who ≤ block.phaseHazard phase :=
      Finset.single_le_sum (fun player _ => block.hazard_nonneg phase player)
        (Finset.mem_univ who)
    have hpPhase : block.phaseHazard phase ≤ block.totalHazard :=
      Finset.single_le_sum (fun displayedPhase _ =>
        block.phaseHazard_nonneg displayedPhase) (Finset.mem_univ phase)
    have hp : block.hazard phase who ≤ block.totalHazard :=
      hpPlayer.trans hpPhase
    have hcontinue : 1 / 2 ≤ (block.root phase who false).toReal := by
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (block.root phase) who
      change (block.root phase who true).toReal ≤ block.totalHazard at hp
      linarith
    have hrow := block.row_endpointRegret_le reward phase who
    have hproduct : (block.root phase who false).toReal * difference ≤
        block.endpointRegret reward := by
      apply (le_max_right 0 _).trans
      exact (le_add_of_nonneg_right (le_max_left _ _)).trans hrow
    have hdifference : difference ≤ 2 * block.endpointRegret reward := by
      by_cases hnonpos : difference ≤ 0
      · linarith [block.endpointRegret_nonneg reward]
      · have hpos : 0 < difference := lt_of_not_ge hnonpos
        nlinarith [mul_pos (lt_of_lt_of_le (by norm_num) hcontinue) hpos]
    have hlower := (abs_le.mp (hclose phase who)).1
    dsimp only [difference] at hdifference
    linarith
  have hraw : ∑ phase, ∑ who, block.hazard phase who * residual who ≤
      η * block.totalHazard + block.endpointRegret reward := by
    calc
      _ ≤ ∑ phase, ∑ who,
          (block.hazard phase who * η +
            max 0 (-(block.hazard phase who *
              quittingRootEndpointDifference reward
                (block.value (block.next phase))
                (block.root phase) who))) := by
        apply Finset.sum_le_sum
        intro phase _
        apply Finset.sum_le_sum
        intro who _
        have hupper := (abs_le.mp (hclose phase who)).2
        have hp := block.hazard_nonneg phase who
        have hmul := mul_le_mul_of_nonneg_left hupper hp
        calc
          block.hazard phase who * residual who ≤
              block.hazard phase who * η -
                block.hazard phase who *
                  quittingRootEndpointDifference reward
                    (block.value (block.next phase))
                    (block.root phase) who := by linarith
          _ ≤ block.hazard phase who * η +
              max 0 (-(block.hazard phase who *
                quittingRootEndpointDifference reward
                  (block.value (block.next phase))
                  (block.root phase) who)) := by
            linarith [le_max_right 0 (-(block.hazard phase who *
              quittingRootEndpointDifference reward
                (block.value (block.next phase))
                (block.root phase) who))]
      _ ≤ η * block.totalHazard + block.endpointRegret reward := by
        calc
          (∑ phase, ∑ who,
              (block.hazard phase who * η +
                max 0 (-(block.hazard phase who *
                  quittingRootEndpointDifference reward
                    (block.value (block.next phase))
                    (block.root phase) who)))) =
              (∑ phase, ∑ who, block.hazard phase who * η) +
              ∑ phase, ∑ who, max 0 (-(block.hazard phase who *
                quittingRootEndpointDifference reward
                  (block.value (block.next phase))
                  (block.root phase) who)) := by
            simp_rw [Finset.sum_add_distrib]
          _ ≤ η * block.totalHazard + block.endpointRegret reward := by
            apply add_le_add
            · calc
                (∑ phase, ∑ who, block.hazard phase who * η) =
                    ∑ phase, block.phaseHazard phase * η := by
                  apply Finset.sum_congr rfl
                  intro phase _
                  rw [← Finset.sum_mul]
                  rfl
                _ = block.totalHazard * η := by
                  rw [← Finset.sum_mul]
                  rfl
                _ = η * block.totalHazard := by ring
              exact le_rfl
            · unfold endpointRegret
              apply Finset.sum_le_sum
              intro phase _
              apply Finset.sum_le_sum
              intro who _
              have hfirst : 0 ≤ max 0
                  ((block.root phase who false).toReal *
                    quittingRootEndpointDifference reward
                      (block.value (block.next phase))
                      (block.root phase) who) := le_max_left _ _
              unfold QuittingReturnedProductBlock.hazard
              rw [neg_mul]
              exact le_add_of_nonneg_left hfirst
  have hdirection : (∑ who, (direction : ι → ℝ) who * residual who) =
      (∑ phase, ∑ who, block.hazard phase who * residual who) /
        block.totalHazard := by
    change (∑ who, (block.cumulativeHazard who / block.totalHazard) *
      residual who) = _
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    apply congrArg (fun z => z / block.totalHazard)
    unfold cumulativeHazard
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro phase _
    rw [Finset.sum_mul]
  have hquadratic : ∑ who, (direction : ι → ℝ) who * residual who ≤
      η + block.endpointRegret reward / block.totalHazard := by
    rw [hdirection]
    apply (div_le_div_of_nonneg_right hraw hpositive.le).trans_eq
    field_simp [hpositive.ne']
  unfold homogeneousViolation
  change max 0 (∑ who, (direction : ι → ℝ) who * residual who) +
      ∑ who, max 0 (-residual who) ≤ _
  apply add_le_add
  · exact max_le (add_nonneg hη (div_nonneg
      (block.endpointRegret_nonneg reward) hpositive.le)) hquadratic
  · calc
      (∑ who, max 0 (-residual who)) ≤
          ∑ _who : ι, (η + 2 * block.endpointRegret reward) := by
        apply Finset.sum_le_sum
        intro who _
        exact max_le (add_nonneg hη (mul_nonneg (by norm_num)
          (block.endpointRegret_nonneg reward))) (hnegative who)
      _ = Fintype.card ι * (η + 2 * block.endpointRegret reward) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- A returned block's normalized hazard has homogeneous violation controlled
by its relative semantic error and its total hazard.  The bound is independent
of the number of phases. -/
theorem homogeneousViolation_normalizedHazard_le_relative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hpositive : 0 < block.totalHazard)
    (hhalf : block.totalHazard ≤ 1 / 2) :
    homogeneousViolation (normalizedSoloMatrix reward)
        (block.normalizedHazard hpositive : ι → ℝ) ≤
      3 * ((Fintype.card ι : ℝ) + 1) *
          ((block.bellmanError reward + block.endpointRegret reward) /
            block.totalHazard) +
        10 * ((Fintype.card ι : ℝ) + 1) * M * block.totalHazard := by
  let B := block.bellmanError reward
  let E := block.endpointRegret reward
  let S := block.totalHazard
  let d : ℝ := Fintype.card ι
  let X := (B + E) / S
  have hB : 0 ≤ B := block.bellmanError_nonneg reward
  have hE : 0 ≤ E := block.endpointRegret_nonneg reward
  have hS : 0 < S := hpositive
  have hM : 0 ≤ M := quittingRewardCoordinateBound_nonneg_of_player
    reward (Classical.arbitrary ι) hreward
  have hX : 0 ≤ X := div_nonneg (add_nonneg hB hE) hS.le
  have hXeq : X = B / S + E / S := by
    dsimp only [X]
    rw [add_div]
  have hBdiv : B / S ≤ X := by
    rw [hXeq]
    exact le_add_of_nonneg_right (div_nonneg hE hS.le)
  have hEdiv : E / S ≤ X := by
    rw [hXeq]
    exact le_add_of_nonneg_left (div_nonneg hB hS.le)
  have hBmul : B ≤ X * S := by
    rw [div_mul_cancel₀ (B + E) hS.ne']
    exact le_add_of_nonneg_right hE
  have hEmul : E ≤ X * S := by
    rw [div_mul_cancel₀ (B + E) hS.ne']
    exact le_add_of_nonneg_left hB
  have hBsmall : 2 * B ≤ X := by
    have hXS : X * S ≤ X / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hhalf hX]
    linarith
  have hEsmall : 2 * E ≤ X := by
    have hXS : X * S ≤ X / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hhalf hX]
    linarith
  have hbase := block.homogeneousViolation_normalizedHazard_le
    reward hreward hvalue hpositive hhalf
  calc
    homogeneousViolation (normalizedSoloMatrix reward)
        (block.normalizedHazard hpositive : ι → ℝ) ≤
      (d + 1) * (B / S + 2 * B + 10 * M * S) +
        E / S + 2 * d * E := by
          apply hbase.trans_eq
          dsimp only [B, E, S, d]
          ring
    _ ≤ 3 * (d + 1) * X + 10 * (d + 1) * M * S := by
      have hd : 0 ≤ d := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hBdiv (by positivity : 0 ≤ d + 1),
        mul_le_mul_of_nonneg_left hBsmall (by positivity : 0 ≤ d + 1),
        mul_le_mul_of_nonneg_left hEsmall hd]
    _ = _ := rfl

/-- Explicit uniform relative semantic-error gap when the normalized singleton
matrix has no homogeneous simplex solution.  Both constants are computable
from the `R₀` margin and the common payoff bound. -/
theorem relativeError_gap_of_noHomogeneous
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hno : ¬HasHomogeneousSimplexSolution (normalizedSoloMatrix reward))
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hpositive : 0 < block.totalHazard)
    (hsmall : block.totalHazard ≤
      min (1 / 2)
        (r0Margin (normalizedSoloMatrix reward) /
          (20 * ((Fintype.card ι : ℝ) + 1) * (M + 1)))) :
    r0Margin (normalizedSoloMatrix reward) /
        (6 * ((Fintype.card ι : ℝ) + 1)) * block.totalHazard ≤
      block.bellmanError reward + block.endpointRegret reward := by
  let matrix := normalizedSoloMatrix reward
  let r := r0Margin matrix
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let S := block.totalHazard
  let X := (block.bellmanError reward + block.endpointRegret reward) / S
  have hR0 : IsR0Matrix matrix :=
    (isR0Matrix_iff_not_singletonLCPFeasible matrix).2 hno
  have hr : 0 < r := (r0Margin_pos_iff_isR0Matrix matrix).2 hR0
  have hD : 0 < D := by dsimp only [D]; positivity
  have hM : 0 ≤ M := quittingRewardCoordinateBound_nonneg_of_player
    reward (Classical.arbitrary ι) hreward
  have hS : 0 < S := hpositive
  have hhalf : S ≤ 1 / 2 := hsmall.trans (min_le_left _ _)
  have hden : 0 < 20 * D * (M + 1) :=
    mul_pos (mul_pos (by norm_num) hD) (by linarith)
  have hsmallMargin : S ≤ r / (20 * D * (M + 1)) :=
    hsmall.trans (min_le_right _ _)
  have hsmallCross : S * (20 * D * (M + 1)) ≤ r :=
    (le_div_iff₀ hden).mp hsmallMargin
  have hfactor : 0 ≤ 20 * D * S := by positivity
  have hMle : 20 * D * S * M ≤ 20 * D * S * (M + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hfactor
  have hcurvature : 10 * D * M * S ≤ r / 2 := by
    have hreordered : 20 * D * S * (M + 1) ≤ r := by
      nlinarith [hsmallCross]
    nlinarith [hMle]
  have hmargin := r0Margin_le matrix
    (block.normalizedHazard hpositive).property
  have hupper := block.homogeneousViolation_normalizedHazard_le_relative
    reward hreward hvalue hpositive hhalf
  have hlower : r ≤ homogeneousViolation matrix
      (block.normalizedHazard hpositive).val := by
    simpa only [r] using hmargin
  have hupper' : homogeneousViolation matrix
      (block.normalizedHazard hpositive).val ≤
        3 * D * X + 10 * D * M * S := by
    change homogeneousViolation matrix
      (block.normalizedHazard hpositive).val ≤
        3 * D * X + 10 * D * M * S at hupper
    exact hupper
  have hhalfMargin : r / 2 ≤ 3 * D * X := by
    linarith [hlower.trans hupper', hcurvature]
  have hrelative : r / (6 * D) ≤ X := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hD)]
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hrelative hS.le
  dsimp only [X] at hscaled
  rw [div_mul_cancel₀ _ hS.ne'] at hscaled
  simpa only [matrix, r, D, S] using hscaled

/-- Qualitative form of the explicit relative gap: some positive hazard scale
and some positive relative-error constant work uniformly over every finite
phase count. -/
theorem exists_pos_relativeError_gap_of_noHomogeneous
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hno : ¬HasHomogeneousSimplexSolution (normalizedSoloMatrix reward)) :
    ∃ δ > 0, ∃ c > 0, ∀ block : QuittingReturnedProductBlock ι,
      (∀ phase who, |block.value phase who| ≤ M) →
      0 < block.totalHazard → block.totalHazard ≤ δ →
      c * block.totalHazard ≤
        block.bellmanError reward + block.endpointRegret reward := by
  let matrix := normalizedSoloMatrix reward
  let r := r0Margin matrix
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let δ := min (1 / 2) (r / (20 * D * (M + 1)))
  let c := r / (6 * D)
  have hr : 0 < r := (r0Margin_pos_iff_isR0Matrix matrix).2
    ((isR0Matrix_iff_not_singletonLCPFeasible matrix).2 hno)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hM : 0 ≤ M := quittingRewardCoordinateBound_nonneg_of_player
    reward (Classical.arbitrary ι) hreward
  have hδ : 0 < δ := lt_min (by norm_num)
    (div_pos hr (mul_pos (mul_pos (by norm_num) hD) (by linarith)))
  have hc : 0 < c := div_pos hr (mul_pos (by norm_num) hD)
  refine ⟨δ, hδ, c, hc, ?_⟩
  intro candidate hvalue hpositive hsmall
  exact candidate.relativeError_gap_of_noHomogeneous reward hreward hno
    hvalue hpositive (by simpa only [δ, r, matrix, D] using hsmall)

/-- Canonical-bound form of the uniform gap.  Callers need only bound the
phase values; the finite terminal reward bound is internalized. -/
theorem exists_pos_relativeError_gap_of_noHomogeneous_of_valueBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {K : ℝ}
    (hno : ¬HasHomogeneousSimplexSolution (normalizedSoloMatrix reward)) :
    ∃ δ > 0, ∃ c > 0, ∀ block : QuittingReturnedProductBlock ι,
      (∀ phase who, |block.value phase who| ≤ K) →
      0 < block.totalHazard → block.totalHazard ≤ δ →
      c * block.totalHazard ≤
        block.bellmanError reward + block.endpointRegret reward := by
  let M := max K (quittingRewardBound reward)
  have hreward : ∀ S player, |reward S player| ≤ M := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans
      (le_max_right K (quittingRewardBound reward))
  obtain ⟨δ, hδ, c, hc, hgap⟩ :=
    exists_pos_relativeError_gap_of_noHomogeneous reward hreward hno
  refine ⟨δ, hδ, c, hc, ?_⟩
  intro block hvalue hpositive hsmall
  apply hgap block (fun phase who =>
    (hvalue phase who).trans (le_max_left K (quittingRewardBound reward)))
    hpositive hsmall

/-- **Arbitrary-horizon tangent obstruction.**  If returned product blocks
have vanishing total hazard and both aggregate semantic errors are little-o
of that hazard, the normalized singleton matrix has a homogeneous simplex
solution.  Phase counts may vary arbitrarily. -/
theorem hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (blocks : ℕ → QuittingReturnedProductBlock ι) {K : ℝ}
    (hvalue : ∀ n phase who, |(blocks n).value phase who| ≤ K)
    (hpositive : ∀ n, 0 < (blocks n).totalHazard)
    (hvanish : Tendsto (fun n => (blocks n).totalHazard) atTop (nhds 0))
    (hbellman : Tendsto (fun n =>
      (blocks n).bellmanError reward / (blocks n).totalHazard) atTop (nhds 0))
    (hendpoint : Tendsto (fun n =>
      (blocks n).endpointRegret reward / (blocks n).totalHazard) atTop (nhds 0)) :
    HasHomogeneousSimplexSolution (normalizedSoloMatrix reward) := by
  by_contra hno
  obtain ⟨δ, hδ, c, hc, hgap⟩ :=
    exists_pos_relativeError_gap_of_noHomogeneous_of_valueBound
      reward (K := K) hno
  have hratio : Tendsto (fun n =>
      (blocks n).bellmanError reward / (blocks n).totalHazard +
        (blocks n).endpointRegret reward / (blocks n).totalHazard)
      atTop (nhds 0) := by
    simpa only [zero_add] using hbellman.add hendpoint
  obtain ⟨n, hsmall, hratioSmall⟩ :=
    (hvanish.eventually (Iio_mem_nhds hδ)).and
      (hratio.eventually (Iio_mem_nhds hc)) |>.exists
  have hgapN := hgap (blocks n) (hvalue n) (hpositive n) hsmall.le
  have hdivided : c ≤
      ((blocks n).bellmanError reward + (blocks n).endpointRegret reward) /
        (blocks n).totalHazard := by
    rw [le_div_iff₀ (hpositive n)]
    exact hgapN
  rw [add_div] at hdivided
  linarith

end QuittingReturnedProductBlock

end GameTheory
