import MathUE.Probability.PhaseOccupationDuality

/-!
# Finite phase-occupation duality

Reader-facing statement of semantic strong duality for finite periodic
occupation flows. The canonical proof remains in
`MathUE.Probability.PhaseOccupationDuality`.
-/

noncomputable section

namespace Theorems.PhaseOccupationDuality

open Math.Probability Math.Probability.PhaseOccupationDuality

variable {S A K : Type*} [Fintype S] [Fintype A] {P : ℕ} [NeZero P]

/-- Every nonempty finite phase-occupation problem has a primal optimum and a
matching bias certificate, each universally optimal in its semantic class. -/
theorem exists_optimal_occupation_and_bias
    (kernel : K → S → A → PMF S) (reward : K → S → A → ℝ)
    (word : Phase P → K)
    (hfeasible : ∃ occupation : PhaseOccupation P S A,
      IsPhaseOccupation kernel word occupation) :
    ∃ occupation potential g,
      IsPhaseOccupation kernel word occupation ∧
      HasPhaseBias kernel reward word potential g ∧
      phaseAverageReward reward word occupation = g ∧
      (∀ other, IsPhaseOccupation kernel word other →
        phaseAverageReward reward word other ≤
          phaseAverageReward reward word occupation) ∧
      (∀ potential' g', HasPhaseBias kernel reward word potential' g' →
        g ≤ g') := by
  exact exists_optimal_phaseOccupation_and_phaseBias_of_feasible
    kernel reward word hfeasible

end Theorems.PhaseOccupationDuality
