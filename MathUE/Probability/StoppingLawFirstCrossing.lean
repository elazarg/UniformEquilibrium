import MathUE.Probability.QuantileClock
import MathUE.Probability.StoppingLawQuantile

/-! # Actual first crossings of complete stopping laws

The quantile date is the existing first-crossing API. Neither finite support
nor positive mass at a preselected date is assumed; date zero is included.
-/

noncomputable section

namespace Math.Probability

open DiscreteHazard.StoppingLaw

theorem stoppingLawCumulativeFiniteMass_eq_one_sub_survival
    (law : PMF (Option ℕ)) (cutoff : ℕ) :
    stoppingLawCumulativeFiniteMass law cutoff = 1 - survival law (cutoff + 1) := by
  rw [stoppingLawCumulativeFiniteMass_eq_sum]
  simp only [survival, finiteMass]
  ring

/-- Small Never mass supplies the actual first inclusive crossing, its strict
pre-date survival bound, and its inclusive tail bound. -/
theorem exists_stoppingLawFirstCrossing_bounds
    (law : PMF (Option ℕ)) {threshold : ℝ}
    (hnone : (law none).toReal < threshold) (hthreshold : threshold < 1) :
    ∃ cutoff,
      stoppingLawFirstCrossing? law (1 - threshold) = some cutoff ∧
      1 - threshold ≤ stoppingLawCumulativeFiniteMass law cutoff ∧
      threshold < survival law cutoff ∧ survival law (cutoff + 1) ≤ threshold := by
  obtain ⟨witness, hwitness⟩ := exists_survival_succ_le_of_none_lt law hnone
  have hcross : ∃ cutoff, 1 - threshold ≤
      stoppingLawCumulativeFiniteMass law cutoff := by
    refine ⟨witness, ?_⟩
    rw [stoppingLawCumulativeFiniteMass_eq_one_sub_survival]
    linarith
  let cutoff := Nat.find hcross
  have hfirst : stoppingLawFirstCrossing? law (1 - threshold) = some cutoff :=
    (stoppingLawFirstCrossing?_eq_some_iff law (1 - threshold) cutoff).2
      ⟨hcross, rfl⟩
  have hspec := stoppingLawFirstCrossing?_spec law (1 - threshold) hfirst
  refine ⟨cutoff, hfirst, hspec.1, ?_, ?_⟩
  · cases hcutoff : cutoff with
    | zero =>
        rw [survival_zero]
        exact hthreshold
    | succ previous =>
        have hprevious := hspec.2 previous (by omega)
        rw [stoppingLawCumulativeFiniteMass_eq_one_sub_survival] at hprevious
        linarith
  · rw [stoppingLawCumulativeFiniteMass_eq_one_sub_survival] at hspec
    linarith [hspec.1]

end Math.Probability
