import MathUE.ProbabilityMassFunction.LateFiniteStoppingLawCensor
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability

/-! # Payoff and cap stability under late-finite stopping-law censoring -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

export _root_.Math.Probability
  (censorLateFiniteStoppingLaws exists_horizon_sum_stoppingLawLateFiniteMass_lt)

/-- Prescribed payoff is stable under coordinatewise late-finite censoring. -/
theorem abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (horizon : ℕ) (who : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingStoppingLawExpectedPayoff reward
          (censorLateFiniteStoppingLaws laws horizon) who -
        quittingStoppingLawExpectedPayoff reward laws who| ≤
      2 * bound * ∑ player, stoppingLawLateFiniteMass (laws player) horizon := by
  have hbound : 0 ≤ bound := by
    simpa using (abs_nonneg (reward ⟨{who}, Finset.singleton_nonempty who⟩ who)).trans
      (hreward ⟨{who}, Finset.singleton_nonempty who⟩ who)
  have h := abs_quittingStoppingLawExpectedPayoff_sub_le_terminalOutcomeDistance
    reward (censorLateFiniteStoppingLaws laws horizon) laws who hreward
  have hdist := quittingTerminalOutcomeOperationalDistance_le_sum
    (censorLateFiniteStoppingLaws laws horizon) laws
  calc
    _ ≤ bound * quittingTerminalOutcomeOperationalDistance
        (censorLateFiniteStoppingLaws laws horizon) laws := h
    _ ≤ bound * ∑ player,
        pmfOperationalDistance
          (censorLateFiniteStoppingLaws laws horizon player) (laws player) := by
      exact mul_le_mul_of_nonneg_left hdist hbound
    _ ≤ 2 * bound * ∑ player,
        stoppingLawLateFiniteMass (laws player) horizon := by
      unfold pmfOperationalDistance censorLateFiniteStoppingLaws
      rw [Finset.mul_sum]
      calc
        ∑ i, bound * (2 * pmfGeneralTV
              (censorLateFiniteStoppingLaw (laws i) horizon) (laws i)) ≤
            ∑ i, bound * (2 * stoppingLawLateFiniteMass (laws i) horizon) := by
          apply Finset.sum_le_sum
          intro player _
          gcongr
          rw [pmfGeneralTV_symm]
          exact pmfGeneralTV_censorLateFiniteStoppingLaw_le (laws player) horizon
        _ = 2 * bound * ∑ player,
            stoppingLawLateFiniteMass (laws player) horizon := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro player _
          ring

/-- The unrestricted replacement cap is stable under late-finite censoring. -/
theorem abs_replacementCap_censorLateFiniteStoppingLaws_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (horizon : ℕ) (who : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingStoppingLawReplacementPayoffCap reward
          (censorLateFiniteStoppingLaws laws horizon) who -
        quittingStoppingLawReplacementPayoffCap reward laws who| ≤
      2 * bound * ∑ player ∈ Finset.univ.erase who,
        stoppingLawLateFiniteMass (laws player) horizon := by
  have hbound : 0 ≤ bound := by
    simpa using (abs_nonneg (reward ⟨{who}, Finset.singleton_nonempty who⟩ who)).trans
      (hreward ⟨{who}, Finset.singleton_nonempty who⟩ who)
  have h := abs_quittingStoppingLawReplacementPayoffCap_sub_le_opponents
    reward (censorLateFiniteStoppingLaws laws horizon) laws who hreward
  calc
    _ ≤ bound * ∑ other ∈ Finset.univ.erase who,
        pmfOperationalDistance
          (censorLateFiniteStoppingLaws laws horizon other) (laws other) := h
    _ ≤ 2 * bound * ∑ other ∈ Finset.univ.erase who,
        stoppingLawLateFiniteMass (laws other) horizon := by
      unfold pmfOperationalDistance censorLateFiniteStoppingLaws
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro player _
      calc
        bound * (2 * pmfGeneralTV
            (censorLateFiniteStoppingLaw (laws player) horizon) (laws player)) ≤
            bound * (2 * stoppingLawLateFiniteMass (laws player) horizon) := by
          gcongr
          rw [pmfGeneralTV_symm]
          exact pmfGeneralTV_censorLateFiniteStoppingLaw_le (laws player) horizon
        _ = (2 * bound) * stoppingLawLateFiniteMass (laws player) horizon := by ring

/-- Censoring a fixed independent stopping-law profile increases literal
terminal exploitability by at most four reward bounds times its late mass. -/
theorem quittingTerminalExploitability_censored_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (horizon : ℕ) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward
          (censorLateFiniteStoppingLaws laws horizon)) ≤
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward laws) +
        4 * bound * ∑ player, stoppingLawLateFiniteMass (laws player) horizon := by
  rw [quittingTerminalExploitability_eq_max_debt,
    quittingTerminalExploitability_eq_max_debt]
  apply QuittingBoundaryHolonomy.finitePlayerMax_le
  intro who
  have hcap := abs_replacementCap_censorLateFiniteStoppingLaws_sub_le
    reward laws horizon who hreward
  have hpay := abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le
    reward laws horizon who hreward
  unfold quittingTerminalDeviationDebt
  rw [← quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile,
    quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  have hmax := QuittingBoundaryHolonomy.le_finitePlayerMax
    (fun player : ι => quittingTerminalDeviationDebt reward
      (quittingStoppingLawProfile reward laws) player) who
  unfold quittingTerminalDeviationDebt at hmax
  rw [← quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile,
    quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff] at hmax
  have herase : ∑ player ∈ Finset.univ.erase who,
      stoppingLawLateFiniteMass (laws player) horizon ≤
        ∑ player, stoppingLawLateFiniteMass (laws player) horizon := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => pmfFiniteComplementMass_nonneg _ _)
  have hbound : 0 ≤ bound := by
    simpa using (abs_nonneg (reward ⟨{who}, Finset.singleton_nonempty who⟩ who)).trans
      (hreward ⟨{who}, Finset.singleton_nonempty who⟩ who)
  have heraseScaled : 2 * bound *
        (∑ player ∈ Finset.univ.erase who,
          stoppingLawLateFiniteMass (laws player) horizon) ≤
      2 * bound * ∑ player, stoppingLawLateFiniteMass (laws player) horizon := by
    gcongr
  rw [abs_le] at hcap hpay
  linarith

end GameTheory
