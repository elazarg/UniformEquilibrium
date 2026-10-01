import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalSingletonScope
import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalResponseScope
import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalNeighborhood

/-! # One literal full reward ball has patient UE, degree one, and no response quotient

The full-table distance is the ordinary nested Pi sup metric, not a matrix
operator norm. The UE target is produced by the strict patient reward rows;
degree one and partition separation are additional independently derived properties.
-/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

open QuittingLCPClassification Math.LinearProgramming Math.Topology

private theorem coordinate_error_le_dist
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |other terminal who - reward terminal who| ≤ dist other reward := by
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist (other terminal) (reward terminal) who).trans
      (dist_le_pi_dist other reward terminal)

theorem singletonDegree_one_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix other),
      r0Degree (quittingSingletonMatrix other) hR0 = 1 :=
  singletonDegree_one_of_coordinate_error other (dist other reward) hclose
    (coordinate_error_le_dist other)

theorem ambientDegree_one_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix other),
      ∀ (region : Set (Fin 4 → ℝ)) (hopen : IsOpen region)
        (hbounded : Bornology.IsBounded region) (horigin : 0 ∈ region),
        ambientDegree (lcpMinMap (quittingSingletonMatrix other) 0) region 0 hopen hbounded
          (continuous_lcpMinMap (quittingSingletonMatrix other) 0).continuousOn
          (lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix
            (quittingSingletonMatrix other) hR0 region hopen horigin) = 1 :=
  ambientDegree_one_of_coordinate_error other (dist other reward) hclose
    (coordinate_error_le_dist other)

/-- All three claims concern the same full reward table and the same exact radius. -/
theorem degree_response_and_uniformPayoff_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) :
    (∃ hR0 : IsR0Matrix (quittingSingletonMatrix other),
      r0Degree (quittingSingletonMatrix other) hR0 = 1) ∧
    (∀ (k : ℕ) (block : Fin 4 → Fin k),
      QuittingResponseInvariantOnUnitCube other block → Function.Injective block) ∧
    ∃ payoff : Payoff (Fin 4), (quittingGame other).IsUniformEquilibriumPayoff none payoff := by
  exact ⟨singletonDegree_one_of_dist_lt other hclose,
    fun _ block hresponse => block_injective_of_dist_lt_responseInvariant
      other hclose block hresponse,
    exists_uniformPayoff_of_dist_lt other hclose⟩

end GameTheory.StrictPatientWithdrawal
