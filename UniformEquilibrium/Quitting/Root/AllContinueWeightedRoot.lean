import UniformEquilibrium.Quitting.Root.VectorTranslation
import UniformEquilibrium.Quitting.Root.NashDefect
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction

/-! # Absorption-relative bounds and translations at the all-Continue root -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {player : Type} [Fintype player] [DecidableEq player]

omit [DecidableEq player] in
@[simp] theorem quittingRootAbsorptionMass_allContinue_eq_zero :
    quittingRootAbsorptionMass
      (quittingAllContinueRoot : player → PMF Bool) = 0 := by
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_allContinueRoot]
  norm_num

theorem quittingRootCoordinateNashDefect_allContinue_eq_posPart
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (value : Payoff player) (who : player) :
    quittingRootCoordinateNashDefect reward value
        (quittingAllContinueRoot : player → PMF Bool) who =
      max (reward (quittingSingletonTerminal who) who - value who) 0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    quittingRootEndpointDifference_allContinueRoot]
  simp [quittingAllContinueRoot]

omit [DecidableEq player] in
/-- An absorption-weighted Bellman row at the all-Continue root has identical
endpoints, independently of its tolerance. -/
theorem eq_of_allContinue_absorptionWeightedBellman
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (source target : Payoff player) (tolerance : ℝ)
    (hbellman : ∀ who,
      |target who - quittingRootSuccessorPayoff reward source
        (quittingAllContinueRoot : player → PMF Bool) who| ≤
          tolerance * quittingRootAbsorptionMass
            (quittingAllContinueRoot : player → PMF Bool)) :
    target = source := by
  funext who
  have hrow := hbellman who
  rw [quittingRootSuccessorPayoff_allContinueRoot_eq,
    quittingRootAbsorptionMass_allContinue_eq_zero, mul_zero] at hrow
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hrow (abs_nonneg _)))

/-- A negative common shift that crosses one singleton payoff creates
strictly positive ordinary Nash defect while the row charge remains zero. -/
theorem allContinue_negativeVectorTranslate_obstruction
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (value shift : Payoff player) (who : player)
    (hcross : quittingPayoffVectorTranslate value shift who <
      reward (quittingSingletonTerminal who) who) :
    quittingRootAbsorptionMass
        (quittingAllContinueRoot : player → PMF Bool) = 0 ∧
      0 < quittingRootCoordinateNashDefect reward
        (quittingPayoffVectorTranslate value shift)
          (quittingAllContinueRoot : player → PMF Bool) who := by
  rw [quittingRootCoordinateNashDefect_allContinue_eq_posPart]
  exact ⟨quittingRootAbsorptionMass_allContinue_eq_zero,
    lt_max_of_lt_left (sub_pos.mpr hcross)⟩

end GameTheory
