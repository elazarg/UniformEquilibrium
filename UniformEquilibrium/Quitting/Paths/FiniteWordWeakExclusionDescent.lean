import UniformEquilibrium.Quitting.Paths.FiniteWordWeakExclusionRates
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Finite weak-exclusion descent and uniform-payoff consumption -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Repeated exact cap-threshold renewal terminates at a literal finite word of any
prescribed positive total-debt accuracy. The selected words are shared with the
quantitative phase and date bounds. -/
theorem exists_finiteWord_debtSum_le_of_weakExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε := by
  obtain ⟨phase, _, hdebt⟩ :=
    exists_quittingWeakExclusionExactWordDebt_le_of_phase_bound
      reward hWE preemption M hM hreward hε
  exact ⟨quittingWeakExclusionExactWords
    reward hWE preemption M hM hreward phase, hdebt⟩

/-- General all-preempted form: the common finite preemption floor is
constructed internally rather than supplied as input. -/
theorem exists_finiteWord_debtSum_le_of_weakExclusion_allPreempted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (hpreempted : ∀ owner, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε := by
  obtain ⟨owner, howner⟩ := hWE []
  letI : Nonempty ι := ⟨owner⟩
  obtain ⟨preemption⟩ :=
    nonempty_singletonColumnBlockerCertificate_of_all_strictPreempted
      reward hpreempted
  exact exists_finiteWord_debtSum_le_of_weakExclusion
    reward hWE preemption hM hε hreward

/-- The produced literal finite words at every accuracy feed the standard
all-errors selector and therefore yield one fixed uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_finiteWordWeakExclusion_allPreempted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (hpreempted : ∀ owner, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let M := quittingRewardBound reward + 1
  have hM : 0 < M := by
    dsimp only [M]
    linarith [quittingRewardBound_nonneg reward]
  have hreward : ∀ terminal player, |reward terminal player| ≤ M := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans (by
      dsimp only [M]
      linarith)
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  obtain ⟨roots, hdebt⟩ :=
    exists_finiteWord_debtSum_le_of_weakExclusion_allPreempted
      reward hWE hpreempted hM hε hreward
  refine ⟨quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward), ?_⟩
  exact isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le reward _ hdebt

end GameTheory
