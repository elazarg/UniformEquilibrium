import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Stationary.OneSidedWeakUnitProducer
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakHalfResidual

/-! # The two finite raw upper-guard classes do not subsume one another -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingFinFourEndpointRows Math.Finset

/-- No relabeling of the selected ordered pair makes the half-ceiling table
pass the matrix-free sixteen weak comparisons. -/
theorem halfCeiling_not_oneSidedWeakRawGuards
    (owner passive : Fin 4) (hdistinct : owner ≠ passive) :
    ¬ QuittingOneSidedWeakUnitRawGuards halfCeilingReward owner passive := by
  fin_cases owner <;> fin_cases passive <;> try exact (hdistinct rfl).elim
  all_goals
    intro hraw
    solve
    | (have h := hraw.lower ∅ {0} (Finset.empty_subset _) (by decide) (by simp)
       norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode] at h)
    | (have h := hraw.lower ∅ {1} (Finset.empty_subset _) (by decide) (by simp)
       norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode] at h)
    | (have h := hraw.lower ∅ {2} (Finset.empty_subset _) (by decide) (by simp)
       norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode] at h)
    | (have h := hraw.lower ∅ {3} (Finset.empty_subset _) (by decide) (by simp)
       norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode] at h)
    | (have h := hraw.lower ∅ {0, 1} (Finset.empty_subset _) (by decide) (by simp)
       norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode] at h)
    | (have h := hraw.upper ∅ (Finset.empty_subset _)
       norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode] at h)

theorem unitCeiling_halfFirstSureOutsidersResidual :
    quittingHalfFirstResidual unitCeilingReward 1 1 = 1 / 2 := by
  have hmass : continueMassExcl (halfFirstRow 1 1) 0 = 0 :=
    quittingCrossed_continueMassExcl_partner_one (halfFirstRow 1 1) 0 2
      (by decide) (by norm_num [halfFirstRow])
  rw [quittingHalfFirstResidual, quittingDiscountedDisplacement, hmass,
    sigmaValue_eq_pureQuitEndpointRowSum, excludedValue_eq_excludedEndpointRowSum]
  simp only [pureQuitEndpointRowSum, excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
    halfFirstRow]
  norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

/-- A positive corner is already a positive final Bernstein coefficient;
the unit table therefore fails even the weak half-ceiling upper test. -/
theorem unitCeiling_not_weakHalfBernsteinUpper :
    ¬ QuittingHalfWeakBernsteinUpper unitCeilingReward := by
  intro hupper
  have hcorner := hupper.first 2 2
  norm_num [Math.quadraticTensorBernsteinCoefficient, Math.quadraticBernsteinCoefficient,
    unitCeiling_halfFirstSureOutsidersResidual] at hcorner

end GameTheory.GuardedCrossedResponseExamples
