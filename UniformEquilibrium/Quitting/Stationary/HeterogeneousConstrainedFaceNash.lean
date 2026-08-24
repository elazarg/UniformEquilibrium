/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Boundary.Analytic.WeightedContinueMassBound
import UniformEquilibrium.Quitting.Stationary.FaceNumerator
import UniformEquilibrium.Quitting.Stationary.Gain

/-!
# Heterogeneous constrained stationary face Nash roots

This module provides a player-dependent compact stationary box.  Player
`who` chooses a hazard in `[lower who, 1]`; the auxiliary payoff is its hazard
times the division-free stationary face numerator.  Since that numerator is
independent of the player's own hazard, compact barycentric Nash existence
gives exactly the constrained best-response inequalities.

The final lemmas expose the production bridges from a real hazard row to the
corresponding Boolean product root.  They identify deleted Continue mass,
positive absorption, and stationary gain without importing diagnostic code.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.PMFProduct
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite simplex barycenter of points in `[lower, 1]`. -/
def heterogeneousRateBarycenter (lower : ℝ) (_hlower : lower ≤ 1)
    (n : ℕ) (weight : stdSimplex ℝ (Fin (n + 1)))
    (point : Fin (n + 1) → Set.Icc lower 1) : Set.Icc lower 1 := by
  refine ⟨∑ action, weight.val action * (point action).val, ?_, ?_⟩
  · calc
      lower = ∑ action, weight.val action * lower := by
        rw [← Finset.sum_mul, weight.property.2, one_mul]
      _ ≤ ∑ action, weight.val action * (point action).val := by
        exact Finset.sum_le_sum fun action _ =>
          mul_le_mul_of_nonneg_left (point action).property.1
            (weight.property.1 action)
  · calc
      (∑ action, weight.val action * (point action).val) ≤
          ∑ action, weight.val action * 1 := by
        exact Finset.sum_le_sum fun action _ =>
          mul_le_mul_of_nonneg_left (point action).property.2
            (weight.property.1 action)
      _ = 1 := by
        rw [← Finset.sum_mul, weight.property.2, one_mul]

/-- The interval barycenter is continuous in its weights. -/
theorem continuous_heterogeneousRateBarycenter
    (lower : ℝ) (hlower : lower ≤ 1) (n : ℕ)
    (point : Fin (n + 1) → Set.Icc lower 1) :
    Continuous fun weight : stdSimplex ℝ (Fin (n + 1)) =>
      heterogeneousRateBarycenter lower hlower n weight point := by
  apply Continuous.subtype_mk
  apply continuous_finsetSum
  intro action _
  exact ((continuous_apply action).comp continuous_subtype_val).mul continuous_const

/-- The face numerator ignores the selected player's own coordinate. -/
theorem heterogeneousFaceNumerator_update_self
    (r : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι) (rate : ℝ) :
    quittingFaceNumerator r (Function.update hazard who rate) who =
      quittingFaceNumerator r hazard who := by
  unfold quittingFaceNumerator
  rw [continueMassExcl_update_self', sigmaValue_update_self,
    excludedValue_update_self]

/-- Off-self agreement preserves the selected face numerator. -/
theorem heterogeneousFaceNumerator_congr_off_self
    (r : Finset ι → ι → ℝ) (firstRow secondRow : ι → ℝ) (who : ι)
    (hagree : ∀ other, other ≠ who → firstRow other = secondRow other) :
    quittingFaceNumerator r firstRow who =
      quittingFaceNumerator r secondRow who := by
  have hrow : firstRow = Function.update secondRow who (firstRow who) := by
    funext other
    by_cases hother : other = who
    · subst other
      simp
    · rw [Function.update_of_ne hother]
      exact hagree other hother
  rw [hrow, heterogeneousFaceNumerator_update_self]

/-- The auxiliary stationary game with a player-dependent lower hazard. -/
def heterogeneousStationaryFaceGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower : ι → ℝ) (hlower : ∀ who, lower who ≤ 1) :
    CompactBarycentricGame where
  Player := ι
  Strategy := fun who => Set.Icc (lower who) 1
  compactStrategy := fun _ => inferInstance
  nonemptyStrategy := fun who => ⟨⟨lower who, le_rfl, hlower who⟩⟩
  payoff := fun profile who =>
    (profile who).val * quittingFaceNumerator (weightOfReward reward)
      (fun player => (profile player).val) who
  payoffContinuous := fun who => by
    have hprofile : Continuous
        (fun profile : ∀ who, Set.Icc (lower who) 1 =>
          fun player => (profile player).val) := by
      apply continuous_pi
      intro player
      exact continuous_subtype_val.comp (continuous_apply player)
    exact (continuous_subtype_val.comp (continuous_apply who)).mul
      ((continuous_quittingFaceNumerator (weightOfReward reward) who).comp
        hprofile)
  barycenter := fun who n weight point =>
    heterogeneousRateBarycenter (lower who) (hlower who) n weight point
  barycenterContinuous := fun who n point =>
    continuous_heterogeneousRateBarycenter (lower who) (hlower who) n point
  payoffBarycentric := by
    intro profile who n weight point
    let hazard : ι → ℝ := fun player => (profile player).val
    let coefficient := quittingFaceNumerator (weightOfReward reward) hazard who
    have hcoefficient : ∀ action,
        quittingFaceNumerator (weightOfReward reward)
          (fun player =>
            ((Function.update profile who (point action)) player).val) who =
          coefficient := by
      intro action
      apply heterogeneousFaceNumerator_congr_off_self
      intro other hother
      simp [hazard, Function.update_of_ne hother]
    have hbaryCoefficient :
        quittingFaceNumerator (weightOfReward reward)
          (fun player =>
            ((Function.update profile who
              (heterogeneousRateBarycenter
                (lower who) (hlower who) n weight point)) player).val) who =
          coefficient := by
      apply heterogeneousFaceNumerator_congr_off_self
      intro other hother
      simp [hazard, Function.update_of_ne hother]
    simp only [Function.update_self]
    rw [hbaryCoefficient]
    change
      (heterogeneousRateBarycenter
          (lower who) (hlower who) n weight point).val * coefficient =
        ∑ action, weight action *
          ((point action).val *
            quittingFaceNumerator (weightOfReward reward)
              (fun player =>
                ((Function.update profile who (point action)) player).val) who)
    simp_rw [hcoefficient]
    unfold heterogeneousRateBarycenter
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro action _
    rw [show weight action = weight.val action by rfl]
    ring

/-- A stationary auxiliary Nash root exists for player-dependent compact
intervals `[lower who, 1]`. -/
theorem exists_heterogeneousStationaryFaceNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower : ι → ℝ) (hlower : ∀ who, lower who ≤ 1) :
    ∃ hazard : ι → ℝ,
      (∀ who, lower who ≤ hazard who) ∧
      (∀ who, hazard who ≤ 1) ∧
      ∀ who rate, lower who ≤ rate → rate ≤ 1 →
        rate * quittingFaceNumerator (weightOfReward reward) hazard who ≤
          hazard who *
            quittingFaceNumerator (weightOfReward reward) hazard who := by
  obtain ⟨profile, hnash⟩ :=
    (heterogeneousStationaryFaceGame reward lower hlower).exists_nash
  let hazard : ι → ℝ := fun who => (profile who).val
  refine ⟨hazard, fun who => (profile who).property.1,
    fun who => (profile who).property.2, ?_⟩
  intro who rate hrate0 hrate1
  let deviation : Set.Icc (lower who) 1 := ⟨rate, hrate0, hrate1⟩
  have hbest := hnash who deviation
  dsimp only [heterogeneousStationaryFaceGame] at hbest
  simp only [Function.update_self] at hbest
  let deviatedHazard : ι → ℝ := fun player =>
    ((Function.update profile who deviation) player).val
  have hcoefficient : quittingFaceNumerator (weightOfReward reward)
      deviatedHazard who =
        quittingFaceNumerator (weightOfReward reward) hazard who := by
    apply heterogeneousFaceNumerator_congr_off_self
    intro other hother
    have hupdate : Function.update profile who deviation other = profile other :=
      @Function.update_of_ne ι (fun player => Set.Icc (lower player) 1)
        (heterogeneousStationaryFaceGame reward lower hlower).decidablePlayer
        other who hother deviation profile
    exact congrArg Subtype.val hupdate
  change deviation.val * quittingFaceNumerator (weightOfReward reward)
      deviatedHazard who ≤
    (profile who).val * quittingFaceNumerator (weightOfReward reward)
      hazard who at hbest
  rw [hcoefficient] at hbest
  simpa only [deviation, hazard] using hbest

/-! ## Real-hazard to Boolean-root bridges -/

/-- The fixed-opponent Continue mass of a hazard-converted root is the
corresponding deleted product. -/
theorem fixedOpponentsContinueMass_rootOfHazard_eq_continueMassExcl
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (rootOfHazard hazard hhazard0 hhazard1) who =
      continueMassExcl hazard who := by
  let root := rootOfHazard hazard hhazard0 hhazard1
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  change (∏ player, ((Function.update root who (PMF.pure false)) player
    (quittingAllContinueAction player)).toReal) = _
  rw [← Finset.mul_prod_erase Finset.univ
    (fun player => ((Function.update root who (PMF.pure false)) player
      (quittingAllContinueAction player)).toReal) (Finset.mem_univ who)]
  simp only [quittingAllContinueAction, Function.update_self, PMF.pure_apply,
    if_true, ENNReal.toReal_one, one_mul, continueMassExcl]
  apply Finset.prod_congr rfl
  intro other hother
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]
  simp [root, rootOfHazard]

/-- One positive hazard coordinate makes the converted root absorb with
positive one-stage probability. -/
theorem rootAbsorptionMass_rootOfHazard_pos_of_coordinate
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1)
    {who : ι} (hhazardPos : 0 < hazard who) :
    0 < quittingRootAbsorptionMass
      (rootOfHazard hazard hhazard0 hhazard1) := by
  let root := rootOfHazard hazard hhazard0 hhazard1
  have hmass : quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
    quittingStationaryContinueMass_le_one
      (Function.update root who (PMF.pure false))
  have hidentity := quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul
    root who
  have hcontinue : (root who false).toReal = 1 - hazard who := by
    simp [root, rootOfHazard]
  rw [hcontinue] at hidentity
  have hownNonneg : 0 ≤ 1 - hazard who := by
    linarith [hhazard1 who]
  have hproduct :
      (1 - hazard who) *
          quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    calc
      (1 - hazard who) *
          quittingStationaryFixedOpponentsContinueMass root who ≤
          (1 - hazard who) * 1 :=
        mul_le_mul_of_nonneg_left hmass hownNonneg
      _ < 1 := by linarith
  rw [hidentity]
  linarith

/-- The real-hazard face numerator is the game-facing stationary gain of the
corresponding Boolean product root. -/
theorem stationaryGain_rootOfHazard_eq_faceNumerator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1) (who : ι) :
    quittingStationaryGain reward
        (rootOfHazard hazard hhazard0 hhazard1) who =
      quittingFaceNumerator (weightOfReward reward) hazard who := by
  let root := rootOfHazard hazard hhazard0 hhazard1
  have hrootHazard : hazardOfRoot root = hazard :=
    hazardOfRoot_rootOfHazard hazard hhazard0 hhazard1
  have hquit : quittingStationaryFixedOpponentsQuitValue reward root who =
      sigmaValue (weightOfReward reward) hazard who := by
    have hfixed := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (fun _ => root) who (0 : Payoff ι) 0
    have hsigma := quittingRootQuitPayoff_eq_sigmaValue
      reward (0 : Payoff ι) root who
    simpa [quittingStationaryFixedOpponentsQuitValue, hrootHazard] using
      hfixed.symm.trans hsigma
  have hcontinue :
      quittingStationaryFixedOpponentsContinueReward reward root who =
        excludedValue (weightOfReward reward) hazard who := by
    have hfixed := quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who (0 : Payoff ι) 0
    have hgamma := quittingRootContinuePayoff_eq_gammaValue
      reward (0 : Payoff ι) root who
    have hvalue : quittingRootContinuePayoff reward (0 : Payoff ι) root who =
        quittingStationaryFixedOpponentsContinueReward reward root who := by
      simpa [quittingStationaryFixedOpponentsContinueReward,
        quittingStationaryFixedOpponentsContinueMass] using hfixed
    rw [hvalue] at hgamma
    simpa [gammaValue, hrootHazard] using hgamma
  have hmass : quittingStationaryFixedOpponentsContinueMass root who =
      continueMassExcl hazard who :=
    fixedOpponentsContinueMass_rootOfHazard_eq_continueMassExcl
      hazard hhazard0 hhazard1 who
  unfold quittingStationaryGain quittingFaceNumerator
  rw [hquit, hcontinue, hmass]

end GameTheory
