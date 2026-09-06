import UniformEquilibrium.Quitting.Examples.ThreeOwnerRobustCycle
import UniformEquilibrium.Quitting.Projective.PolynomialForwardCertificateCharacterization

/-! # Uniform-payoff consequence for the literal three-owner robust cycle -/

noncomputable section

namespace GameTheory.ThreeOwnerRobustCycle

/-- The literal normal stress table has a uniform-equilibrium payoff.  If it
did not, the polynomial characterization would construct one potential on
all robust edges in the box of radius `3 + 2`; the exact charged three-cycle
rules out that very potential. -/
theorem exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hcharacterization :=
    quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential
      reward 3 reward_abs_le_three isNormal
        (by refine ⟨0, ?_⟩
            rw [singletonSelfReward]
            norm_num [Matrix.cons_val_zero])
  obtain ⟨-, tolerance, htolerance, -, expression, hpotential⟩ :=
    hcharacterization.mp hno
  apply no_potential (tolerance : ℝ) (3 + 2)
    (by exact_mod_cast htolerance.le) (by norm_num)
  exact ⟨fun state =>
    Math.Interval.RationalPolynomial.evalReal state.1 expression, hpotential⟩

end GameTheory.ThreeOwnerRobustCycle
