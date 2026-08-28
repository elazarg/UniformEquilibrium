/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourRationalRewardApproximation
import Research.Quitting.TerminalExploitabilityRewardRobustness
import UniformEquilibrium.Quitting.RewardBound

/-!
# Positive-infimum rational approximation for Fin4 reward tables

The sharp reward-table robustness estimate makes strict positivity of global
terminal exploitability stable under a sufficiently close rational
approximation.  For an arbitrary finite real reward table, the canonical
finite reward bound supplies an explicit positive normalization scale first.

The resulting code occurs at a literal finite index of the fair executable
reward-code enumeration.  This module makes no semidecision or termination
claim.
-/

noncomputable section

namespace GameTheory

/-- A fair-enumeration entry which is normalized, uniformly close to a fixed
real reward table, and still has positive global terminal exploitability. -/
structure FinFourPositiveRationalRewardApproximation
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (delta : ℝ) where
  index : ℕ
  code : RationalFinFourRewardCode
  candidateAt_eq : RationalFinFourRewardCode.candidateAt index = some code
  normalized_eq_true : code.normalized = true
  close : ∀ terminal observer,
    |code.realReward terminal observer - reward terminal observer| < delta
  exploitabilityInf_pos :
    0 < quittingTerminalExploitabilityInf code.realReward

/-- Positivity survives every normalized rational approximation whose
uniform error is less than half of the original exploitability infimum. -/
theorem nonempty_finFourPositiveRationalRewardApproximation
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnormalized : ∀ terminal observer, |reward terminal observer| ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta)
    (hmargin : 2 * delta < quittingTerminalExploitabilityInf reward) :
    Nonempty (FinFourPositiveRationalRewardApproximation reward delta) := by
  obtain ⟨index, code, hindex, hnormalizedCode, hclose⟩ :=
    exists_rationalFinFourRewardCandidateAt_normalized_eq_true_near
      reward hnormalized hdelta
  have hrobust :
      |quittingTerminalExploitabilityInf code.realReward -
          quittingTerminalExploitabilityInf reward| ≤ 2 * delta := by
    apply abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close
      code.realReward reward hdelta.le
    intro terminal observer
    exact (hclose terminal observer).le
  have hcodePositive :
      0 < quittingTerminalExploitabilityInf code.realReward := by
    have hlower := (abs_le.mp hrobust).1
    linarith
  exact ⟨⟨index, code, hindex, hnormalizedCode, hclose, hcodePositive⟩⟩

/-- Every normalized real Fin4 reward table with positive global terminal
exploitability has a normalized rational code at a finite fair-enumeration
index with positive global terminal exploitability. -/
theorem exists_normalizedRationalFinFourRewardCode_exploitabilityInf_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnormalized : ∀ terminal observer, |reward terminal observer| ≤ 1)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward) :
    ∃ index code,
      RationalFinFourRewardCode.candidateAt index = some code ∧
      code.normalized = true ∧
      0 < quittingTerminalExploitabilityInf code.realReward := by
  let delta := quittingTerminalExploitabilityInf reward / 4
  have hdelta : 0 < delta := by
    exact div_pos hpositive (by norm_num)
  have hmargin : 2 * delta < quittingTerminalExploitabilityInf reward := by
    dsimp [delta]
    linarith
  obtain ⟨approximation⟩ :=
    nonempty_finFourPositiveRationalRewardApproximation
      reward hnormalized hdelta hmargin
  exact ⟨approximation.index, approximation.code,
    approximation.candidateAt_eq, approximation.normalized_eq_true,
    approximation.exploitabilityInf_pos⟩

/-! ## Canonical positive normalization -/

/-- A positive denominator dominating every coordinate of a finite Fin4
reward table. -/
def finFourRewardNormalizationDenominator
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : ℝ :=
  max 1 (quittingRewardBound reward)

/-- The explicit positive scale used to normalize an arbitrary Fin4 reward
table. -/
def finFourRewardNormalizationScale
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : ℝ :=
  (finFourRewardNormalizationDenominator reward)⁻¹

/-- The canonically scaled real reward table. -/
def normalizedFinFourReward
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  scaleQuittingReward (finFourRewardNormalizationScale reward) reward

theorem finFourRewardNormalizationDenominator_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    0 < finFourRewardNormalizationDenominator reward := by
  exact lt_of_lt_of_le zero_lt_one
    (le_max_left 1 (quittingRewardBound reward))

theorem finFourRewardNormalizationScale_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    0 < finFourRewardNormalizationScale reward := by
  exact inv_pos.mpr (finFourRewardNormalizationDenominator_pos reward)

/-- The explicit scaled table lies in the unit reward box. -/
theorem abs_normalizedFinFourReward_le_one
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (observer : Fin 4) :
    |normalizedFinFourReward reward terminal observer| ≤ 1 := by
  rw [normalizedFinFourReward, scaleQuittingReward_apply, abs_mul,
    abs_of_pos (finFourRewardNormalizationScale_pos reward)]
  unfold finFourRewardNormalizationScale
  apply inv_mul_le_one_of_le₀
  · exact (abs_reward_le_quittingRewardBound reward terminal observer).trans
      (le_max_right 1 (quittingRewardBound reward))
  · exact (finFourRewardNormalizationDenominator_pos reward).le

/-- Exact global-infimum homogeneity for the canonical normalization. -/
theorem quittingTerminalExploitabilityInf_normalizedFinFourReward
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    quittingTerminalExploitabilityInf (normalizedFinFourReward reward) =
      finFourRewardNormalizationScale reward *
        quittingTerminalExploitabilityInf reward := by
  exact quittingTerminalExploitabilityInf_scaleQuittingReward
    (finFourRewardNormalizationScale_pos reward).le reward

/-- Canonical positive normalization preserves strict positivity exactly. -/
theorem quittingTerminalExploitabilityInf_normalizedFinFourReward_pos_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    0 < quittingTerminalExploitabilityInf (normalizedFinFourReward reward) ↔
      0 < quittingTerminalExploitabilityInf reward := by
  exact quittingTerminalExploitabilityInf_scaleQuittingReward_pos_iff
    (finFourRewardNormalizationScale_pos reward) reward

/-- Every arbitrary real Fin4 reward table with positive global terminal
exploitability can first be positively normalized and then approximated by a
normalized rational fair-enumeration entry which retains positivity. -/
theorem exists_scaledNormalizedRationalFinFourRewardCode_exploitabilityInf_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hpositive : 0 < quittingTerminalExploitabilityInf reward) :
    ∃ index code,
      RationalFinFourRewardCode.candidateAt index = some code ∧
      code.normalized = true ∧
      0 < quittingTerminalExploitabilityInf code.realReward ∧
      ∀ terminal observer,
        |code.realReward terminal observer -
            normalizedFinFourReward reward terminal observer| <
          quittingTerminalExploitabilityInf
              (normalizedFinFourReward reward) / 4 := by
  have hnormalizedPositive :
      0 < quittingTerminalExploitabilityInf
        (normalizedFinFourReward reward) :=
    (quittingTerminalExploitabilityInf_normalizedFinFourReward_pos_iff
      reward).2 hpositive
  let delta := quittingTerminalExploitabilityInf
    (normalizedFinFourReward reward) / 4
  have hdelta : 0 < delta := div_pos hnormalizedPositive (by norm_num)
  have hmargin : 2 * delta <
      quittingTerminalExploitabilityInf (normalizedFinFourReward reward) := by
    dsimp [delta]
    linarith
  obtain ⟨approximation⟩ :=
    nonempty_finFourPositiveRationalRewardApproximation
      (normalizedFinFourReward reward)
      (abs_normalizedFinFourReward_le_one reward)
      hdelta hmargin
  exact ⟨approximation.index, approximation.code,
    approximation.candidateAt_eq, approximation.normalized_eq_true,
    approximation.exploitabilityInf_pos, approximation.close⟩

end GameTheory
