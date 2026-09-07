import UniformEquilibrium.Quitting.Paths.FiniteWordWeakExclusionSelection
import UniformEquilibrium.Quitting.Terminal.FiniteMenuFullProfileApproximation
import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource

/-! # Finite-menu consequences of weak exclusion for a single pivot -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Weak exclusion for a canonical single-pivot singleton table produces actual finite
timing menus whose displayed-menu error and exceptional post-cutoff scalar are both
arbitrarily small.  The deadline can be required to exceed any prescribed lower bound. -/
theorem exists_singlePivot_finiteMenu_errors_lt_of_weakExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    {ε : ℝ} (hε : 0 < ε) (lowerDeadline : ℕ) :
    letI : Nonempty ι := ⟨pivot⟩
    ∃ deadline : ℕ, lowerDeadline ≤ deadline ∧
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
        quittingFiniteDeadlineMenuExploitability reward deadline mixed < ε ∧
        quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
            quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
            quittingTerminalPayoff reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot < ε := by
  letI : Nonempty ι := ⟨pivot⟩
  have hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player := by
    intro player
    rw [hcanonical player]
    split <;> norm_num
  obtain ⟨target, htarget⟩ :=
    exists_uniformEquilibriumPayoff_of_weakExclusion_nonnegativeSingleton
      reward hWE hsingleton
  obtain ⟨deadline, hdeadline, mixed, hexploit, _⟩ :=
    (isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation
      reward target).mp htarget ε hε lowerDeadline
  have hmax := singlePivot_fullExploitability_eq_max_menuExploitability_scalar
    reward pivot hcanonical deadline mixed
  refine ⟨deadline, hdeadline, mixed, ?_, ?_⟩
  · exact (le_max_left _ _).trans_lt (hmax ▸ hexploit)
  · exact (le_max_right _ _).trans_lt (hmax ▸ hexploit)

end GameTheory
