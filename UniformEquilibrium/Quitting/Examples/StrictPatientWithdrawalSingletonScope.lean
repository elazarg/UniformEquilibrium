import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalTable
import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseInverseNeighborhood
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawMatrix
import MathUE.LinearProgramming.R0AmbientDegree

/-! # Literal positive singleton degree of the strict patient class

The center shares the existing printed matrix and inverse. The same quantitative
resolvent theorem handles every raw coordinate within the exact radius 1/100.
Degree one is a matrix invariant, not by itself an equilibrium producer.
-/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

open GuardedCrossedResponseExamples QuittingLCPClassification Math.LinearProgramming
open Math.Topology
open scoped Matrix.Norms.Operator

theorem singletonMatrix_eq : quittingSingletonMatrix reward = sourceSingletonMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num +decide [quittingSingletonMatrix, reward, coalitionCode, sourceSingletonMatrix]

theorem singletonMatrix_det : (quittingSingletonMatrix reward).det = 45 := by
  rw [singletonMatrix_eq, sourceSingletonMatrix_det]

theorem singletonMatrix_inverse :
    (quittingSingletonMatrix reward)⁻¹ = sourceSingletonInverse := by
  rw [singletonMatrix_eq, sourceSingletonMatrix_inverse]

theorem singletonDegree_one :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix reward),
      r0Degree (quittingSingletonMatrix reward) hR0 = 1 := by
  apply quittingSingletonMatrix_r0_degree_one_of_positiveInverse
  · rw [singletonMatrix_det]
    norm_num
  · rw [singletonMatrix_eq]
    exact sourceSingletonMatrix_inverse_pos

theorem inverse_neighborhood_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error) :
    0 < (quittingSingletonMatrix other).det ∧
      (∀ row column, 0 < (quittingSingletonMatrix other)⁻¹ row column) ∧
      ‖(quittingSingletonMatrix other)⁻¹ - sourceSingletonMatrix⁻¹‖ ≤
        6 * error / (1 - 6 * error) :=
  sourceSingletonMatrix_neighborhood reward other singletonMatrix_eq error herror hclose

/-- The packet's strict inverse-distance bound at the full raw radius 1/100. -/
theorem inverse_change_lt_three_div_fortySeven_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error) :
    ‖(quittingSingletonMatrix other)⁻¹ - sourceSingletonMatrix⁻¹‖ < 3 / 47 := by
  have hbound :=
    (inverse_neighborhood_of_coordinate_error other error herror hclose).2.2
  refine hbound.trans_lt ?_
  apply (div_lt_iff₀ (by linarith : 0 < 1 - 6 * error)).mpr
  linarith

theorem singletonDegree_one_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error) :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix other),
      r0Degree (quittingSingletonMatrix other) hR0 = 1 := by
  obtain ⟨hdet, hinverse, _⟩ := inverse_neighborhood_of_coordinate_error other error herror hclose
  exact quittingSingletonMatrix_r0_degree_one_of_positiveInverse other hdet hinverse

/-- The literal minimum field has intrinsic degree one on every bounded open
neighborhood of the origin, without root-finiteness or regularity assumptions. -/
theorem ambientDegree_one_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error) :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix other),
      ∀ (region : Set (Fin 4 → ℝ)) (hopen : IsOpen region)
        (hbounded : Bornology.IsBounded region) (horigin : 0 ∈ region),
        ambientDegree (lcpMinMap (quittingSingletonMatrix other) 0) region 0 hopen hbounded
          (continuous_lcpMinMap (quittingSingletonMatrix other) 0).continuousOn
          (lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix
            (quittingSingletonMatrix other) hR0 region hopen horigin) = 1 := by
  obtain ⟨hR0, hdegree⟩ := singletonDegree_one_of_coordinate_error other error herror hclose
  refine ⟨hR0, ?_⟩
  intro region hopen hbounded horigin
  exact (ambientDegree_lcpMinMap_zero_eq_r0Degree
    (quittingSingletonMatrix other) hR0 region hopen hbounded horigin).trans hdegree

end GameTheory.StrictPatientWithdrawal
