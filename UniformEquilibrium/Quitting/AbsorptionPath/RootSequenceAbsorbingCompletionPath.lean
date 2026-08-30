/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.DiscreteRootSequencePath
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionDiagonal
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile

/-!
# Absorption-path adapter for late sure-solo completions

This module connects the finite discrete absorption-path constructor to the
actual late sure-solo completion and its diagonal family.  It also identifies
the endpoint of any finite-hit-zero path with the generated root sequence's
terminal law and reward moment.

No path compactness, path convergence, fixed completion owner, or sequential
perfection is asserted.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingFiniteRootSequenceAbsorption

variable {roots : ℕ → ι → PMF Bool}

omit [Nonempty ι] in
private theorem indicator_absorbingContribution
    (terminal : {S : Finset ι // S.Nonempty})
    (root : ι → PMF Bool) (observer : ι) :
    quittingRootAbsorbingContribution
        (quittingTerminalCoalitionIndicatorReward terminal) root observer =
      quittingRootCoalitionMass root terminal.1 := by
  rw [quittingRootAbsorbingContribution_eq_sum_nonemptyCoalitionMass]
  rw [Finset.sum_eq_single terminal]
  · simp [quittingTerminalCoalitionIndicatorReward]
    unfold quittingRootCoalitionMass quittingRootQuitRates hazardOfRoot
    rfl
  · intro candidate _ hne
    simp [quittingTerminalCoalitionIndicatorReward, hne]
  · simp

/-- The endpoint coordinate of a finite-hit-zero path is the actual terminal
coalition probability of the generated root-sequence profile. -/
theorem value_one_eq_terminalOutcomeMass_some
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) :
    certificate.absorptionPath.1.value 1 terminal =
      quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward roots 0) (some terminal) := by
  change certificate.cadlagPath.value 1 terminal = _
  rw [certificate.value_cadlagPath_one]
  let indicator := quittingTerminalCoalitionIndicatorReward terminal
  let observer := Classical.choice ‹Nonempty ι›
  rw [quittingTerminalOutcomeMass_rootSequence_some_eq_indicatorValue
    reward roots terminal observer]
  rw [quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
    indicator roots observer (certificate.cutoff + 1)]
  rw [show quittingJointSurvivalWeight roots 0 (certificate.cutoff + 1) = 0
    from certificate.survival_zero, zero_mul, add_zero]
  rw [quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
  apply Eq.symm
  apply Finset.sum_congr rfl
  intro stage _
  rw [indicator_absorbingContribution]
  rfl

/-- Finite survival zero removes the `Never` atom from the actual terminal
law. -/
theorem terminalOutcomeMass_none_eq_zero
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward roots 0) none = 0 := by
  have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward
    (quittingRootSequenceProfile reward roots 0)
  have hsum := hsimplex.2
  rw [Fintype.sum_option] at hsum
  have hfinite : (∑ terminal,
      quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward roots 0) (some terminal)) = 1 := by
    calc
      (∑ terminal, quittingTerminalOutcomeMass reward
          (quittingRootSequenceProfile reward roots 0) (some terminal)) =
          ∑ terminal, certificate.cadlagPath.value 1 terminal := by
        apply Finset.sum_congr rfl
        intro terminal _
        exact (certificate.value_one_eq_terminalOutcomeMass_some
          reward terminal).symm
      _ = pathTotal certificate.cadlagPath 1 := rfl
      _ = 1 := certificate.pathTotal_cadlagPath_one
  linarith

/-- The endpoint path mass has exactly the prescribed terminal reward
moment of the generated root-sequence profile. -/
theorem sum_value_one_mul_reward
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (∑ terminal, certificate.absorptionPath.1.value 1 terminal *
      reward terminal who) =
      quittingRootSequenceTerminalValue reward roots who 0 := by
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass reward
      (quittingRootSequenceProfile reward roots 0)) who
  unfold quittingRootSequenceTerminalValue
  rw [← hmoment]
  unfold quittingTerminalRewardMoment quittingTerminalOutcomeReward
  rw [Fintype.sum_option]
  simp only [Pi.zero_apply, mul_zero, zero_add]
  simp_rw [certificate.value_one_eq_terminalOutcomeMass_some reward]

end QuittingFiniteRootSequenceAbsorption

end GameTheory.QuittingAbsorptionPath

/-! ## Completion adapters -/

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingRootSequenceLateSureSoloCompletion

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {lowerBound : ℕ} {ε d M : ℝ}

/-- The finite-zero certificate carried by a late sure-solo completion. -/
def finiteAbsorptionCertificate
    (completion : QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M) :
    QuittingAbsorptionPath.QuittingFiniteRootSequenceAbsorption
      (quittingLateSureSoloRoots roots completion.owner completion.cutoff) where
  cutoff := completion.cutoff
  survival_zero := completion.jointSurvival_cutoff_succ_eq_zero

/-- The ordinary discrete absorption path of the actual completed root
sequence. -/
def absorptionPath
    (completion : QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M) :
    QuittingAbsorptionPath.AbsorptionPath (ι := ι) :=
  completion.finiteAbsorptionCertificate.absorptionPath

end QuittingRootSequenceLateSureSoloCompletion

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}

/-- The discrete absorption path at one diagonal completion rank. -/
def absorptionPath
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) : QuittingAbsorptionPath.AbsorptionPath (ι := ι) :=
  (diagonal.completion rank).absorptionPath

/-- The diagonal path endpoint is the actual completed terminal law. -/
theorem absorptionPath_value_one_eq_completedTerminalOutcomeMass
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    (diagonal.absorptionPath rank).1.value 1 terminal =
      quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward (diagonal.completedRoots rank) 0)
        (some terminal) := by
  exact (diagonal.completion rank).finiteAbsorptionCertificate
    |>.value_one_eq_terminalOutcomeMass_some reward terminal

/-- The diagonal path endpoint has the actual completed prescribed payoff. -/
theorem absorptionPath_sum_value_one_mul_reward
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) (who : ι) :
    (∑ terminal, (diagonal.absorptionPath rank).1.value 1 terminal *
      reward terminal who) =
      quittingRootSequenceTerminalValue reward
        (diagonal.completedRoots rank) who 0 := by
  exact (diagonal.completion rank).finiteAbsorptionCertificate
    |>.sum_value_one_mul_reward reward who

/-- The completed diagonal terminal law has literally zero `Never` mass. -/
theorem completedTerminalOutcomeMass_none_eq_zero
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) :
    quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward (diagonal.completedRoots rank) 0)
        none = 0 := by
  exact (diagonal.completion rank).finiteAbsorptionCertificate
    |>.terminalOutcomeMass_none_eq_zero reward

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory
