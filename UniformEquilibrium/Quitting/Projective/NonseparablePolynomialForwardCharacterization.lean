import UniformEquilibrium.Quitting.Projective.NonquasiconvexPolynomialForwardCharacterization
import UniformEquilibrium.Quitting.Projective.SingletonBoxRepresentationExclusions
import UniformEquilibrium.Quitting.Projective.FinFourAmbientQSimplex

/-! # The same source-produced polynomial is not additive or a regular scalar composition

The nonquasiconvex polynomial characterization's selected tolerance, actual
table, polynomial and robust box are retained. Actual Q is produced from the
same bare no-UE input.
No second polynomial, favorable simplex, or outer monotonicity is supplied.
-/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

/-- Exact refinement of the original Fin4 polynomial obstruction equivalence:
one identical expression is nonquasiconvex, not additive, and not a regular
possibly nonmonotone scalar composition on the actual closed singleton box. -/
theorem quittingGame_noUniformPayoff_iff_noSureRoot_and_nonseparable_rationalPotential
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
              (rewardBound + 2)).IsPotential (fun state => evalReal state.1 expression) ∧
            ¬ QuasiconvexOn ℝ (quittingSingletonBox reward rewardBound)
              (fun point => evalReal point expression) ∧
            ¬ IsQuittingSingletonBoxAdditive reward rewardBound
              (fun point => evalReal point expression) ∧
            ¬ IsQuittingSingletonBoxRegularScalarComposition reward rewardBound
              (fun point => evalReal point expression) := by
  constructor
  · intro hnoUniform
    obtain ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression,
        hpotential, hnotQuasiconvex⟩ :=
      (quittingGame_noUniformPayoff_iff_noSureRoot_and_nonquasiconvex_rationalPotential
        reward rewardBound hreward hnormal hpositive).mp hnoUniform
    have hQ := isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff
      reward hnoUniform
    have hregular := contDiff_evalReal expression 1
    have hdifferentiable : ∀ point ∈ quittingSingletonBox reward rewardBound,
        DifferentiableAt ℝ (fun input => evalReal input expression) point :=
      fun point _ => hregular.differentiable_one point
    have hexact := isQuittingFullExactRootPotential_add_one_of_robust_add_two reward
      (by exact_mod_cast htolerance.le) hreward (fun point => evalReal point expression) hpotential
    have hface := hexact.singletonBox_positive_face_drift hreward hdifferentiable
    refine ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression,
      hpotential, hnotQuasiconvex, ?_, ?_⟩
    · exact not_singletonBox_additive_of_standardQ_positive_face_drift reward hreward hQ
        (fun point => evalReal point expression) hdifferentiable hface
    · exact not_singletonBox_scalarComposition_of_standardQ_positive_face_drift reward hreward hQ
        (fun point => evalReal point expression) hdifferentiable hface
  · rintro ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression,
      hpotential, _, _, _⟩
    exact (quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential
      reward rewardBound hreward hnormal hpositive).mpr
        ⟨hnoSureRoot, tolerance, htolerance, htoleranceMax, expression, hpotential⟩

end GameTheory
