import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity

/-! # Exact and marked-player survival for a constant product-root word -/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A repeated root has the expected power-law joint survival. -/
theorem quittingJointSurvivalWeight_const
    (root : ι → PMF Bool) (fuel : ℕ) :
    quittingJointSurvivalWeight (fun _ => root) 0 fuel =
      quittingStationaryContinueMass root ^ fuel := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simp

omit [DecidableEq ι] in
/-- One marked marginal bounds the joint survival of a repeated root. -/
theorem quittingJointSurvivalWeight_const_le_pow_continue
    (root : ι → PMF Bool) (marked : ι) (fuel : ℕ) :
    quittingJointSurvivalWeight (fun _ => root) 0 fuel ≤
      (root marked false).toReal ^ fuel := by
  rw [quittingJointSurvivalWeight_const]
  exact pow_le_pow_left₀ (quittingStationaryContinueMass_nonneg root)
    (quittingStationaryContinueMass_le_ownContinueProbability root marked) fuel

/-- If `marked` is one of `who`'s opponents, its Continue probability bounds
the whole repeated-prefix opponent-survival clock. -/
theorem quittingOpponentSurvivalWeight_const_le_pow_continue
    (root : ι → PMF Bool) (who marked : ι) (hne : marked ≠ who) (fuel : ℕ) :
    quittingOpponentSurvivalWeight (fun _ => root) who 0 fuel ≤
      (root marked false).toReal ^ fuel := by
  unfold quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
  have hprod :
      (∏ _offset ∈ Finset.range fuel,
          quittingStationaryContinueMass
            (Function.update root who (PMF.pure false))) ≤
        ∏ _offset ∈ Finset.range fuel, (root marked false).toReal := by
    apply Finset.prod_le_prod₀
    · intro offset _
      exact quittingStationaryContinueMass_nonneg
        (Function.update root who (PMF.pure false))
    · intro offset _
      have hmass := quittingStationaryContinueMass_le_ownContinueProbability
        (Function.update root who (PMF.pure false)) marked
      rw [Function.update_of_ne hne] at hmass
      exact hmass
  simpa using hprod

end GameTheory
