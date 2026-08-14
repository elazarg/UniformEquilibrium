/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.OwnShiftCycleExactification
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium
import UniformEquilibrium.Quitting.Cycles.ExactCycleStrata
import GameTheory.Concepts.Stochastic.Models.Quitting.UniformPayoffExistenceClosure

/-!
# Exact-cycle strata: Research residuals

The canonical own-shift feedback and exactification system is proved in
`UniformEquilibrium.Quitting.Cycles.OwnShiftCycleExactification`.  This file
keeps the Research-specific solved stratum using landed admissibility and the
small phase-conflict regressions; it makes no density claim.
-/

noncomputable section

namespace GameTheory
namespace CycleStrataExperiment

open StochasticGame Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The two Research strata -/

/-- The Research stratum accepted by the landed cyclic behavioral compiler:
raw exactness plus genuine absorption and landed admissibility. -/
def IsSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι) : Prop :=
  _root_.GameTheory.IsRawExactQuittingCycle reward cycle value ∧
    (∏ phase : Fin K, quittingStationaryContinueMass (cycle phase)) < 1 ∧
    IsQuittingCycleAdmissible reward cycle

theorem isZeroAsymptoticNash_of_isSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (h : IsSolvedExactQuittingCycle reward cycle value) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  exact isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_admissible
    reward cycle value phase h.1.1 h.1.2 h.2.1 h.2.2

/-- A table in the Research solved stratum has a uniform-equilibrium payoff.
This is a consumer of landed admissibility, not a density theorem. -/
theorem exists_uniformEquilibriumPayoff_of_isSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (h : IsSolvedExactQuittingCycle reward cycle value) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  exact ⟨quittingCyclicBehaviorProfile reward cycle phase,
    (isZeroAsymptoticNash_of_isSolvedExactQuittingCycle
      reward cycle value phase h).mono hε.le⟩

/-- If every reward-table neighborhood contains a Research solved cycle,
reward perturbation closure gives a uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_arbitrarily_close_solvedCycles
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hdense : ∀ η : ℝ, 0 < η →
      ∃ nearby : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ S who, |nearby S who - reward S who| ≤ η) ∧
          ∃ K : ℕ, ∃ _ : Fin K,
            ∃ cycle : Fin K → ι → PMF Bool, ∃ value : Fin K → Payoff ι,
              IsSolvedExactQuittingCycle nearby cycle value) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards
    reward
  intro η hη
  obtain ⟨nearby, hnearby, K, phase, cycle, value, hsolved⟩ := hdense η hη
  exact ⟨nearby, hnearby,
    exists_uniformEquilibriumPayoff_of_isSolvedExactQuittingCycle
      nearby cycle value phase hsolved⟩

/-! ## Exact phase-conflict regressions -/

/-- Two frozen-tail phases can be exactified independently: their demanded
shifts may simply disagree. -/
theorem twoPhases_independently_exactifiable :
    ∃ d₀ d₁ : ℝ, (1 + d₀ = 0) ∧ (-1 + d₁ = 0) := by
  exact ⟨-1, 1, by norm_num, by norm_num⟩

/-- The same two demands cannot be met by one common table shift, even before
cyclic value feedback is imposed. -/
theorem twoPhases_not_exactifiable_by_common_shift :
    ¬ ∃ d : ℝ, (1 + d = 0) ∧ (-1 + d = 0) := by
  rintro ⟨d, h₀, h₁⟩
  linarith

/-- With a two-phase half-survival feedback recurrence, allowing the cyclic
values to recompute still does not reconcile the opposing phase demands. -/
theorem twoPhase_halfSurvival_feedback_conflict :
    ¬ ∃ d a₀ a₁ : ℝ,
      a₀ = (1 / 2 : ℝ) * a₁ + (1 / 2 : ℝ) * d ∧
      a₁ = (1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * d ∧
      1 + d - a₁ = 0 ∧
      -1 + d - a₀ = 0 := by
  rintro ⟨d, a₀, a₁, h₀, h₁, hg₀, hg₁⟩
  linarith

theorem commonShift_halfResidual_lowerBound (d : ℝ) :
    (1 / 2 : ℝ) ≤ max |d| |1 + d| := by
  have htriangle : (1 : ℝ) ≤ |d| + |1 + d| := by
    calc
      (1 : ℝ) = |(1 + d) - d| := by norm_num
      _ ≤ |1 + d| + |d| := abs_sub _ _
      _ = |d| + |1 + d| := add_comm _ _
  have h₀ := le_max_left |d| |1 + d|
  have h₁ := le_max_right |d| |1 + d|
  linarith

theorem commonShift_halfResidual_attained :
    max |(-1 / 2 : ℝ)| |1 + (-1 / 2 : ℝ)| = 1 / 2 := by
  norm_num

end CycleStrataExperiment
end GameTheory
