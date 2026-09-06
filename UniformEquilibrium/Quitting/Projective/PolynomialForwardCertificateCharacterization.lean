import UniformEquilibrium.Quitting.Projective.RobustChargedRelationPolynomialSeparator
import UniformEquilibrium.Quitting.Projective.RobustCapacityFromPacketFailure
import UniformEquilibrium.Quitting.Projective.PolynomialForwardCertificateConsumer

/-! # Rational polynomial characterization of the fixed-box normal quitting-game obstruction

The polynomial is constructed from finite outer capacity under failure of uniform-payoff
existence. No polynomial producer or smooth separator is an extra premise.
-/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

/-- Under normality and a positive singleton, failure of uniform-payoff existence is exactly
failure of the finite sure-root alternative together with one rational polynomial
certificate on every robust edge at a positive rational tolerance at most `1/4`,
in the fixed box `rewardBound + 2`. -/
theorem quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who) :
    (¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ¬ HasQuittingPunishmentVectorNashRootWithSureQuitter reward ∧
        ∃ tolerance : ℚ, 0 < tolerance ∧ tolerance ≤ 1 / 4 ∧
          ∃ expression : RationalPolynomial 4,
            (quittingFloorFreeRobustChargedRelation reward (tolerance : ℝ)
              (rewardBound + 2)).IsPotential (fun state ↦ evalReal state.1 expression) := by
  constructor
  · intro hnoUniform
    have hbound : 0 < rewardBound := by
      obtain ⟨who, hsingleton⟩ := hpositive
      exact hsingleton.trans_le ((le_abs_self _).trans (hreward _ who))
    have hnoSureRoot : ¬ HasQuittingPunishmentVectorNashRootWithSureQuitter reward := by
      intro hsureRoot
      exact hnoUniform
        ((quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot
          reward rewardBound hreward hnormal hpositive).2 (Or.inr hsureRoot))
    obtain ⟨epsilon, hepsilon, hepsilonMax, hbudget⟩ :=
      exists_positiveRationalTolerance_hasFiniteRobustBudget_of_noUniformPayoff
        reward rewardBound hbound hreward hnormal hnoUniform
    have hbudget' :
        (quittingFloorFreeRobustChargedRelation reward (epsilon : ℝ)
          ((rewardBound + 2) + 1)).HasFiniteBudget := by
      rw [show rewardBound + 2 + 1 = rewardBound + 3 by ring]
      exact hbudget
    obtain ⟨expression, hexpression⟩ :=
      exists_quittingRobustChargedRelation_rationalPotential_of_finiteBudget reward rewardBound
        (epsilon : ℝ) (rewardBound + 2) hreward hepsilon hepsilonMax hbudget'
    refine ⟨hnoSureRoot, epsilon / 4, div_pos (by exact_mod_cast hepsilon) (by norm_num),
      ?_, expression, ?_⟩
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hepsilonMax) (by norm_num)
    · rw [Rat.cast_div, Rat.cast_ofNat]
      exact hexpression
  · rintro ⟨hnoSureRoot, tolerance, htolerance, _htoleranceMax, expression, hpotential⟩
    exact quittingGame_not_exists_uniformEquilibriumPayoff_of_noSureRoot_of_rationalPotential
      reward rewardBound hreward hnormal hpositive hnoSureRoot (tolerance : ℝ)
      (by exact_mod_cast htolerance) expression hpotential

end GameTheory
