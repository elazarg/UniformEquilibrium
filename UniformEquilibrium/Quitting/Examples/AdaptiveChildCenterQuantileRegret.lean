import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterQuantilePayoffs

/-! # Actual endpoint regrets and the anchor-mass lower bound -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open _root_.Math.Probability.DiscreteHazard.StoppingLaw

/-- Approximate parent Nash and the distinct prescribed/deviation estimates
give both finite endpoint debts, with the packet's 24-accuracy constant. -/
theorem actual_endpoint_regret_estimate
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3,
      0 < survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff)
    {error accuracy : ℝ} (herror : quittingTerminalExploitability reward parent ≤ error)
    (hbefore : ∀ active : Fin 3,
      1 - survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff ≤ accuracy)
    (htail : survival (quittingBehaviorStoppingLaws reward parent 3) (cutoff + 1) ≤ accuracy)
    (active : Fin 3) (quit : Bool) :
    finiteMass (quittingBehaviorStoppingLaws reward parent 3) cutoff *
        (activeEndpointPayoff (conditionalProbabilities
            (quittingBehaviorStoppingLaws reward parent) cutoff) active quit -
          activePayoff (conditionalProbabilities
            (quittingBehaviorStoppingLaws reward parent) cutoff) active) ≤
      error + 24 * accuracy := by
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le parent herror
  have hdeviation := hnash active.castSucc
    (quittingStoppingLawBehaviorStrategy reward active.castSucc (endpointLaw cutoff quit))
  have hprescribed := abs_le.mp
    (actual_prescribed_payoff_estimate parent cutoff hpositive hbefore htail active)
  have hendpoint := abs_le.mp
    (actual_endpoint_payoff_estimate parent cutoff hpositive hbefore htail active quit)
  nlinarith [hprescribed.1, hprescribed.2, hendpoint.1, hendpoint.2]

theorem one_sub_error_le_zero_payoff
    (parent : (quittingGame reward).BehaviorProfile) {error : ℝ}
    (herror : quittingTerminalExploitability reward parent ≤ error) :
    1 - error ≤ quittingTerminalPayoff reward parent 0 := by
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le parent herror
  have hreply := hnash 0
    (quittingStoppingLawBehaviorStrategy reward 0 (PMF.pure (some 0)))
  rw [zero_quitNow_payoff] at hreply
  linarith

theorem activePayoff_zero_le_two (q : Fin 3 → ℝ)
    (hbounds : ∀ active, 0 ≤ q active ∧ q active ≤ 1) : activePayoff q 0 ≤ 2 := by
  have hproduct := mul_le_mul_of_nonneg_left (hbounds 2).2
    (sub_nonneg.mpr (hbounds 0).2)
  simp only [activePayoff, Matrix.cons_val_zero]
  nlinarith [(hbounds 0).1]

theorem zero_payoff_le_two_anchor_mass_add
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3,
      0 < survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff ≤ accuracy)
    (htail : survival (quittingBehaviorStoppingLaws reward parent 3) (cutoff + 1) ≤ accuracy) :
    quittingTerminalPayoff reward parent 0 ≤
      2 * finiteMass (quittingBehaviorStoppingLaws reward parent 3) cutoff + 14 * accuracy := by
  have hestimate := actual_prescribed_payoff_estimate parent cutoff hpositive hbefore htail 0
  change |quittingTerminalPayoff reward parent 0 -
    finiteMass (quittingBehaviorStoppingLaws reward parent 3) cutoff *
      activePayoff (conditionalProbabilities
        (quittingBehaviorStoppingLaws reward parent) cutoff) 0| ≤ 14 * accuracy at hestimate
  have hprescribed := abs_le.mp hestimate
  have hbound := activePayoff_zero_le_two
    (conditionalProbabilities (quittingBehaviorStoppingLaws reward parent) cutoff)
    (conditionalProbabilities_bounds _ cutoff hpositive)
  have hscaled := mul_le_mul_of_nonneg_left hbound
    (finiteMass_nonneg (quittingBehaviorStoppingLaws reward parent 3) cutoff)
  nlinarith [hprescribed.2]

end GameTheory.AdaptiveChildCenter
