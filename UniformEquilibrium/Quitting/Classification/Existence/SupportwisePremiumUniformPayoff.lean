/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PerfectSequenceExtraction
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumNormalization
import UniformEquilibrium.Quitting.Terminal.TerminalAffineNashTransfer

/-!
# Uniform payoff from supportwise weighted quitting premiums

Nonnegative own singleton rewards are shifted by half the requested error and
then normalized playerwise to one.  Supportwise balance survives the exact
normalization.  The unit producer gives a literal periodic root sequence;
positive scaling and the sharp terminal-shift transfer return that same root
sequence to the original table with every suffix still approximate Nash.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Supportwise weighted premium balance and nonnegative own singleton rewards
produce a literal periodic root sequence whose every suffix is a terminal
approximate Nash profile of the original game. -/
theorem exists_periodic_allSuffix_terminalNash_of_supportwiseBalance
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (period : ℕ), 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      ∀ start,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε
          (quittingRootSequenceProfile reward roots start) := by
  let shift : ℝ := ε / 2
  let scale : Payoff ι := fun player =>
    reward (quittingSingletonTerminal player) player + shift
  let totalScale : ℝ := ∑ player, scale player
  let normalized := quittingPlayerwiseUnitNormalization reward shift
  have hshift : 0 < shift := by
    dsimp [shift]
    linarith
  have hscale : ∀ player, 0 < scale player := fun player => by
    dsimp [scale]
    exact add_pos_of_nonneg_of_pos (hsingleton player) hshift
  have htotalScale : 0 < totalScale := by
    let player : ι := Classical.choice inferInstance
    dsimp only [totalScale]
    exact Finset.sum_pos' (fun who _ => (hscale who).le)
      ⟨player, Finset.mem_univ player, hscale player⟩
  have hscale_le_total : ∀ player, scale player ≤ totalScale := by
    intro player
    dsimp only [totalScale]
    exact Finset.single_le_sum (fun who _ => (hscale who).le)
      (Finset.mem_univ player)
  have hunit : QuittingUnitSoloExit normalized := by
    intro player
    exact quittingPlayerwiseUnitNormalization_singleton
      reward hshift hsingleton player
  have hnormalizedBalanced :
      IsSupportwiseBalancedQuittingPremiumTable normalized :=
    supportwiseBalance_playerwiseUnitNormalization
      reward hshift hsingleton hbalanced
  have hlowRoot : HasLowActiveQuittingRootQuitPayoff normalized :=
    hasLowActiveQuittingRootQuitPayoff_of_supportwiseBalance
      normalized hunit hnormalizedBalanced
  have hnormalizedError : 0 < shift / totalScale :=
    div_pos hshift htotalScale
  obtain ⟨roots, period, hperiod0, hperiodic, hnash⟩ :=
    exists_cyclic_subgamePerfectTerminalNash_of_lowActiveQuitPayoff
      hunit hlowRoot hnormalizedError
  have hscaleError : ∀ player, scale player * (shift / totalScale) ≤ shift := by
    intro player
    have hmul := mul_le_mul_of_nonneg_right (hscale_le_total player)
      (div_nonneg hshift.le htotalScale.le)
    have hcancel : totalScale * (shift / totalScale) = shift := by
      field_simp [htotalScale.ne']
    rwa [hcancel] at hmul
  have hnashScaled :=
    quittingRootSequence_allSuffix_terminalNash_playerwiseScale
      normalized scale roots (fun player => (hscale player).le) hnash hscaleError
  have hscaledReward :
      quittingPlayerwiseAffineReward normalized scale 0 =
        quittingPlayerwiseAffineReward reward 1 (fun _ => shift) := by
    funext terminal player
    have hscaleNe : scale player ≠ 0 := (hscale player).ne'
    simp only [quittingPlayerwiseAffineReward, Pi.zero_apply, Pi.one_apply,
      add_zero, one_mul]
    dsimp only [normalized, quittingPlayerwiseUnitNormalization]
    change scale player * ((reward terminal player + shift) / scale player) =
      reward terminal player + shift
    exact mul_div_cancel₀ _ hscaleNe
  rw [hscaledReward] at hnashScaled
  have hnashOriginal :=
    quittingRootSequence_allSuffix_terminalNash_of_nonnegative_terminalShift
      reward (fun _ => shift) roots (fun _ => hshift.le) (fun _ => le_rfl)
      hnashScaled
  refine ⟨roots, period, hperiod0, hperiodic, ?_⟩
  have herr : shift + shift = ε := by
    dsimp [shift]
    ring
  simpa [herr] using hnashOriginal

/-- The terminal approximate profiles at every positive error select one
fixed uniform-equilibrium payoff of the original table. -/
theorem exists_uniformEquilibriumPayoff_of_supportwiseBalance
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  obtain ⟨roots, _period, _hperiod0, _hperiodic, hterminal⟩ :=
    exists_periodic_allSuffix_terminalNash_of_supportwiseBalance
      reward hsingleton hbalanced hε
  exact ⟨quittingRootSequenceProfile reward roots 0, hterminal 0⟩

end GameTheory
