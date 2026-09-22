import UniformEquilibrium.Quitting.Stationary.DiscountedClippedDegree
import UniformEquilibrium.Quitting.Classification.AuxiliaryDiscountedQuantitativeLocalization

/-!
# The full singleton-degree criterion for the original finite-player game

Given full R0, absence of an original-game uniform-equilibrium payoff supplies
uniform localization of every fixed point of the actual auxiliary clipped map.
The degree comparison then gives one. The auxiliary terminal shift preserves
the singleton matrix literally; no auxiliary no-equilibrium hypothesis or
strategic equivalence under the shift is asserted. Dimension zero uses the
canonical degree normalization directly.
-/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming QuittingLCPClassification

/-- Under full R0, original-game noUE forces degree one through the actual
canonical auxiliary discounted source. -/
theorem singleton_r0Degree_eq_one_of_no_uniformPayoff {n : ℕ}
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward))
    (hno : ¬ ∃ payoff : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    r0Degree (quittingSingletonMatrix reward) hR0 = 1 := by
  cases n with
  | zero => exact r0Degree_fin_zero (quittingSingletonMatrix reward) hR0
  | succ n =>
    have hmatrix :
        (quittingSingletonMatrix (quittingAuxiliaryReward reward) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = quittingSingletonMatrix reward := by
      change quittingSingletonMatrix
        (fun coalition player => reward coalition player - quittingAuxiliaryLive reward player) = _
      exact quittingSingletonMatrix_sub_payoff reward (quittingAuxiliaryLive reward)
    have hauxR0 : IsR0Matrix (quittingSingletonMatrix (quittingAuxiliaryReward reward)) :=
      hmatrix.symm ▸ hR0
    have hauxDegree : r0Degree (quittingSingletonMatrix (quittingAuxiliaryReward reward))
        hauxR0 = 1 := by
      apply r0Degree_quittingSingletonMatrix_eq_one_of_discounted_fixedPoint_localization
      obtain ⟨radius, hradius, threshold, hthreshold, hlocal⟩ :=
        auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformEquilibriumPayoff
          reward hno hauxR0
      refine ⟨radius, hradius, min threshold 1, lt_min hthreshold zero_lt_one, ?_⟩
      intro discount hdiscount hsmall hazard hfixed
      have hzero : ∀ who, 0 ≤ hazard who := by
        intro who
        rw [← congrFun hfixed who]
        exact le_min (by norm_num) (le_max_left _ _)
      have hone : ∀ who, hazard who ≤ 1 := by
        intro who
        rw [← congrFun hfixed who]
        exact min_le_left _ _
      exact (hlocal discount hdiscount hsmall hazard hzero hone hfixed).2
    simpa only [hmatrix] using hauxDegree

/-- Any full R0 singleton matrix of degree different from one forces a uniform
equilibrium payoff in the original finite-player quitting game. -/
theorem exists_uniformEquilibriumPayoff_of_r0Degree_ne_one {n : ℕ}
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward))
    (hdegree : r0Degree (quittingSingletonMatrix reward) hR0 ≠ 1) :
    ∃ payoff : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  exact hdegree (singleton_r0Degree_eq_one_of_no_uniformPayoff reward hR0 hno)

end GameTheory
