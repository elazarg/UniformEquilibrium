/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearAlgebra.FiniteConePositiveAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNonnegativeWeightChamber

/-!
# Supported social costates or sparse reward improvements

This is the game-semantic wrapper around the finite cone alternative.  Its
sparse arm is a correlated reward-moment certificate only; it carries no
behavioral realization or deviation cap.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Reward above the player's own singleton at one terminal outcome. -/
def quittingTerminalOutcomeSingletonSurplus
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (outcome : QuittingTerminalOutcome ι) (who : ι) : ℝ :=
  quittingTerminalOutcomeReward reward outcome who -
    reward (quittingSingletonTerminal who) who

/-- A strictly positive social costate on one fixed player support. -/
structure QuittingSupportedStrictSocialCostate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) where
  weight : {who // who ∈ players} → ℝ
  positive : ∀ who, 0 < weight who
  singletonValue_nonnegative :
    0 ≤ ∑ who, weight who *
      reward (quittingSingletonTerminal who.1) who.1
  terminalSurplus_nonpositive :
    ∀ terminal : {S : Finset ι // S.Nonempty},
      (∑ who, weight who *
        (reward terminal who.1 -
          reward (quittingSingletonTerminal who.1) who.1)) ≤ 0

/-- A probability law on literal terminal outcomes whose reward moment weakly
improves every coordinate in one support and strictly improves at least one.
The positive law support has conic cardinality at most the player support. -/
structure QuittingSupportedSparseRewardImprovement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) where
  law : QuittingTerminalOutcome ι → ℝ
  law_nonnegative : ∀ outcome, 0 ≤ law outcome
  law_sum_eq_one : ∑ outcome, law outcome = 1
  coordinate_nonnegative : ∀ who : {who // who ∈ players},
    0 ≤ ∑ outcome, law outcome *
      quittingTerminalOutcomeSingletonSurplus reward outcome who.1
  coordinate_positive : ∃ who : {who // who ∈ players},
    0 < ∑ outcome, law outcome *
      quittingTerminalOutcomeSingletonSurplus reward outcome who.1
  support_card_le : Fintype.card {outcome // law outcome ≠ 0} ≤ players.card

namespace QuittingSupportedStrictSocialCostate

/-- Forget the reward-table names and retain the exact low cone separator. -/
def toStrictPositiveNonpositiveCovector
    {players : Finset ι}
    (costate : QuittingSupportedStrictSocialCostate reward players) :
    Math.LinearAlgebra.StrictPositiveNonpositiveCovector
      (fun outcome (who : {who // who ∈ players}) ↦
        quittingTerminalOutcomeSingletonSurplus reward outcome who.1) where
  weight := costate.weight
  positive := costate.positive
  generator_nonpositive := by
    intro outcome
    cases outcome with
    | none =>
        have hsingleton := costate.singletonValue_nonnegative
        unfold dotProduct quittingTerminalOutcomeSingletonSurplus
        calc
          (∑ x, (quittingTerminalOutcomeReward reward none x.1 -
                reward (quittingSingletonTerminal x.1) x.1) *
              costate.weight x) =
              -(∑ x, costate.weight x *
                reward (quittingSingletonTerminal x.1) x.1) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro who _
            simp only [quittingTerminalOutcomeReward, Pi.zero_apply]
            ring
          _ ≤ 0 := neg_nonpos.mpr hsingleton
    | some terminal =>
        simpa [dotProduct, quittingTerminalOutcomeSingletonSurplus,
          quittingTerminalOutcomeReward, mul_comm] using
          costate.terminalSurplus_nonpositive terminal

end QuittingSupportedStrictSocialCostate

namespace QuittingSupportedSparseRewardImprovement

/-- Forget reward-table names and retain the exact low sparse cone object. -/
def toSparseProbabilityConeImprovement
    {players : Finset ι}
    (improvement : QuittingSupportedSparseRewardImprovement reward players) :
    Math.LinearAlgebra.SparseProbabilityConeImprovement
      (fun outcome (who : {who // who ∈ players}) ↦
        quittingTerminalOutcomeSingletonSurplus reward outcome who.1) where
  weight := improvement.law
  weight_nonnegative := improvement.law_nonnegative
  weight_sum_eq_one := improvement.law_sum_eq_one
  value_nonnegative := improvement.coordinate_nonnegative
  value_positive := improvement.coordinate_positive
  support_card_le := by
    simpa only [Fintype.card_coe] using improvement.support_card_le

end QuittingSupportedSparseRewardImprovement

omit [DecidableEq ι] in
/-- For a fixed player support, exactly one of the strictly positive social
costate chamber and the sparse correlated reward improvement exists. -/
theorem xor_supportedStrictSocialCostate_or_sparseRewardImprovement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    Xor (Nonempty (QuittingSupportedStrictSocialCostate reward players))
      (Nonempty (QuittingSupportedSparseRewardImprovement reward players)) := by
  let vector : QuittingTerminalOutcome ι →
      {who // who ∈ players} → ℝ :=
    fun outcome who ↦
      quittingTerminalOutcomeSingletonSurplus reward outcome who.1
  rcases
      Math.LinearAlgebra.xor_strictPositiveNonpositiveCovector_or_sparseNonnegativeConeImprovement
        vector with hcostate | himprovement
  · left
    obtain ⟨⟨separator⟩, hnotImprovement⟩ := hcostate
    let costate : QuittingSupportedStrictSocialCostate reward players := {
      weight := separator.weight
      positive := separator.positive
      singletonValue_nonnegative := by
        have hnever := separator.generator_nonpositive none
        have hrearrange :
            dotProduct (vector none) separator.weight =
              -(∑ who, separator.weight who *
                reward (quittingSingletonTerminal who.1) who.1) := by
          unfold dotProduct vector quittingTerminalOutcomeSingletonSurplus
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro who _
          simp only [quittingTerminalOutcomeReward, Pi.zero_apply]
          ring
        rw [hrearrange] at hnever
        linarith
      terminalSurplus_nonpositive := fun terminal ↦ by
        have hterminal := separator.generator_nonpositive (some terminal)
        have hrearrange :
            dotProduct (vector (some terminal)) separator.weight =
              ∑ who, separator.weight who *
                (reward terminal who.1 -
                  reward (quittingSingletonTerminal who.1) who.1) := by
          unfold dotProduct vector quittingTerminalOutcomeSingletonSurplus
          apply Finset.sum_congr rfl
          intro who _
          simp only [quittingTerminalOutcomeReward]
          ring
        rwa [hrearrange] at hterminal }
    refine ⟨⟨costate⟩, ?_⟩
    rintro ⟨improvement⟩
    let normalized := improvement.toSparseProbabilityConeImprovement
    let raw : Math.LinearAlgebra.SparseNonnegativeConeImprovement vector := {
      coefficient := normalized.weight
      coefficient_nonnegative := normalized.weight_nonnegative
      value_nonnegative := normalized.value_nonnegative
      value_positive := normalized.value_positive
      support_card_le := normalized.support_card_le }
    exact hnotImprovement ⟨raw⟩
  · right
    obtain ⟨⟨raw⟩, hnotCostate⟩ := himprovement
    let normalized := raw.normalized
    let improvement : QuittingSupportedSparseRewardImprovement reward players := {
      law := normalized.weight
      law_nonnegative := normalized.weight_nonnegative
      law_sum_eq_one := normalized.weight_sum_eq_one
      coordinate_nonnegative := normalized.value_nonnegative
      coordinate_positive := normalized.value_positive
      support_card_le := by
        simpa only [Fintype.card_coe] using normalized.support_card_le }
    refine ⟨⟨improvement⟩, ?_⟩
    rintro ⟨costate⟩
    exact hnotCostate ⟨costate.toStrictPositiveNonpositiveCovector⟩

end GameTheory
