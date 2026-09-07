import UniformEquilibrium.Quitting.Paths.FiniteUnpreemptedSoloExit
import UniformEquilibrium.Quitting.Paths.FiniteWordWeakExclusionDescent

/-! # Finite selection under weak singleton exclusion -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Weak singleton exclusion with nonnegative singleton rewards always
selects an actual finite word of arbitrarily small complete-deviation debt.
The proof separates the literal unpreempted solo exit from the all-preempted
cap-threshold renewal. -/
theorem exists_finiteWord_debtSum_le_of_weakExclusion_nonnegativeSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε := by
  let M := quittingRewardBound reward + 1
  have hM : 0 < M := by
    dsimp only [M]
    linarith [quittingRewardBound_nonneg reward]
  have hreward : ∀ terminal player, |reward terminal player| ≤ M := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans (by
      dsimp only [M]
      linarith)
  by_cases hpreempted : ∀ owner, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker
  · exact exists_finiteWord_debtSum_le_of_weakExclusion_allPreempted
      reward hWE hpreempted hM hε hreward
  · push Not at hpreempted
    obtain ⟨owner, hunpreempted⟩ := hpreempted
    apply exists_finiteWord_debtSum_le_of_nonnegative_unpreemptedOwner
      reward owner hM hε hreward hsingleton
    intro player hplayer
    linarith [hunpreempted player]

/-- The finite-word selector feeds the standard all-errors compactness
consumer and yields one fixed uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_weakExclusion_nonnegativeSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  obtain ⟨roots, hdebt⟩ :=
    exists_finiteWord_debtSum_le_of_weakExclusion_nonnegativeSingleton
      reward hWE hsingleton hε
  refine ⟨quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward), ?_⟩
  exact isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le reward _ hdebt

end GameTheory
