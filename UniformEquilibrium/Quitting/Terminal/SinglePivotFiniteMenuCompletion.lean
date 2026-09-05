import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Conditional completion of a canonical single-pivot finite-menu source -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A canonical finite-menu producer whose menu exploitability and exceptional
scalar are simultaneously arbitrarily small yields some fixed terminal uniform
payoff.  The producer is an explicit hypothesis; exact finite-menu Nash is not
required. -/
theorem exists_uniformEquilibriumPayoff_of_singlePivot_finiteMenu_scalar_source
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) :
    letI : Nonempty ι := ⟨pivot⟩
    (∀ ε : ℝ, 0 < ε →
      ∃ deadline : ℕ,
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
        quittingFiniteDeadlineMenuExploitability reward deadline mixed ≤ ε ∧
        quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
            quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
            quittingTerminalPayoff reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot ≤ ε) →
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  letI : Nonempty ι := ⟨pivot⟩
  intro hproducer
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  obtain ⟨deadline, mixed, hmenu, hscalar⟩ := hproducer ε hε
  let profile := quittingFiniteDeadlineTimingProfile reward deadline mixed
  refine ⟨profile, ?_⟩
  apply isεAsymptoticNash_of_quittingTerminalExploitability_le
  rw [singlePivot_fullExploitability_eq_max_menuExploitability_scalar
    reward pivot hcanonical deadline mixed]
  exact max_le hmenu hscalar

end GameTheory
