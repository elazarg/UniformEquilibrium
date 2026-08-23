/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProducer
import UniformEquilibrium.Quitting.Classification.LCP.ProjectiveQBarBehavioralDecoder
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary

/-!
# Homogeneous witnesses supported on production-normal owners

A non-vertex homogeneous singleton witness already produces a stationary
uniform-equilibrium payoff.  If instead one coordinate has simplex mass one,
the residual is its normalized singleton column.  Nonnegativity of that
column and production normality of the owner give the checked no-harm
singleton producer.

This dispatch does not require a standard-Q or residual-hard hypothesis.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Any homogeneous witness whose positive owners cover their punishment
floors produces a uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι)
    (hresidual : ∀ who,
      0 ≤ singletonLCPResidual (normalizedSoloMatrix reward) weight who)
    (hcomplementary : ∀ who,
      weight.val who *
        singletonLCPResidual (normalizedSoloMatrix reward) weight who = 0)
    (hnormal : ∀ owner, 0 < weight.val owner →
      quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_cases hnonvertex : ∀ who, weight.val who < 1
  · exact exists_uniformEquilibriumPayoff_of_nonvertexHomogeneousWitness
      reward weight hresidual hcomplementary hnonvertex
  · push Not at hnonvertex
    obtain ⟨owner, hownerLower⟩ := hnonvertex
    have hownerUpper : weight.val owner ≤ 1 := by
      exact (Finset.single_le_sum (fun who _ ↦ weight.property.1 who)
        (Finset.mem_univ owner)).trans_eq weight.property.2
    have howner : weight.val owner = 1 := le_antisymm hownerUpper hownerLower
    have hownerPos : 0 < weight.val owner := by rw [howner]; norm_num
    have hcolumn : ∀ who, 0 ≤ normalizedSoloMatrix reward who owner := by
      intro who
      rw [← singletonLCPResidual_eq_column_of_weight_eq_one
        (normalizedSoloMatrix reward) weight howner who]
      exact hresidual who
    have hnoHarm : ∀ who,
        quittingSoloReward reward who who ≤
          quittingSoloReward reward owner who := by
      intro who
      have hentry := hcolumn who
      rw [normalizedSoloMatrix_eq_soloReward_sub] at hentry
      linarith
    apply exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner reward
    exact ⟨owner, hnoHarm, hnormal owner hownerPos⟩

/-- A zero normalized singleton drift at a boundary-tight, production-normal
support already solves the game.  This is the exact zero-exclusion statement
needed before strict separation of the late drift simplex. -/
theorem exists_uniformEquilibriumPayoff_of_zero_boundaryDrift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : Payoff ι) (weight : stdSimplex ℝ ι)
    (hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ boundary who)
    (hsupport : ∀ owner, 0 < weight.val owner →
      boundary owner = reward (quittingSingletonTerminal owner) owner)
    (hnormal : ∀ owner,
      boundary owner = reward (quittingSingletonTerminal owner) owner →
        quittingPunishmentValue reward owner ≤
          reward (quittingSingletonTerminal owner) owner)
    (hzero : ∀ who,
      boundary who - reward (quittingSingletonTerminal who) who -
        singletonLCPResidual (normalizedSoloMatrix reward) weight who = 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hresidual : ∀ who,
      0 ≤ singletonLCPResidual (normalizedSoloMatrix reward) weight who := by
    intro who
    linarith [hsolo who, hzero who]
  have hcomplementary : ∀ who,
      weight.val who *
        singletonLCPResidual (normalizedSoloMatrix reward) weight who = 0 := by
    intro who
    by_cases hweight : weight.val who = 0
    · simp [hweight]
    · have hweightPos : 0 < weight.val who :=
        lt_of_le_of_ne (weight.property.1 who) (Ne.symm hweight)
      have htight := hsupport who hweightPos
      have hresidualZero :
          singletonLCPResidual (normalizedSoloMatrix reward) weight who = 0 := by
        linarith [hzero who]
      rw [hresidualZero, mul_zero]
  apply exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal
    reward weight hresidual hcomplementary
  intro owner howner
  exact hnormal owner (hsupport owner howner)

end QuittingLCPClassification
end GameTheory
