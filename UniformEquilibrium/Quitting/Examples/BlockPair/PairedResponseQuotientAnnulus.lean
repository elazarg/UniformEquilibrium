import UniformEquilibrium.Quitting.Examples.BlockPair.PairedResponseQuotientMatrix
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientAmbientDegree

/-!
# Paired quotient: unique offset-minus-one root and entire-fiber degree two

The root calculation delegates to the generic nonnegative-inverse theorem.
The intrinsic degree retains the whole nonzero fixed fiber of the actual
raw-table quotient field. No isolated roots, regularity, or root count is assumed.
Only the literal singleton matrix is needed for these two topological conclusions;
centered paired rows are required separately for original-player strategic decoding.
-/

noncomputable section

namespace GameTheory
namespace PairedResponseQuotient

open Set Math.Topology Math.LinearProgramming QuittingLCPClassification
open FourPlayerPairedSingleton

/-- The printed inverse has all three row sums exactly one. -/
theorem inverse_mulVec_one_eq_one : matrix⁻¹.mulVec (1 : Fin 3 → ℝ) = 1 := by
  ext row
  rw [inverse_eq]
  fin_cases row <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The unique LCP root at offset minus one is the literal all-ones vector. -/
theorem isStandardLCPSolution_neg_one_iff (root : Fin 3 → ℝ) :
    IsStandardLCPSolution matrix (-1) root ↔ root = 1 := by
  rw [isStandardLCPSolution_neg_one_iff_of_nonnegative_inverse matrix det_neg.ne
    (fun row column => (inverse_pos row column).le) root, inverse_mulVec_one_eq_one]

/-- Every reward completion of the literal singleton matrix has an actual annulus
containing exactly the entire nonzero quotient fixed fiber and ambient degree two. -/
theorem exists_omegaAnnulus_ambientDegree_eq_two_of_pairedSingletonMatrix
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hmatrix : quittingSingletonMatrix reward = pairedSingletonMatrix) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 / 2 ∧
      (∀ point : Fin 3 → ℝ, ‖point‖ ≤ radius →
        quittingQuotientStationaryClippedMap reward block representative point = point →
          point = 0) ∧
      ∃ hfrontier : ∀ point ∈ frontier (quittingQuotientOmegaAnnulus (k := 3) radius),
          quittingQuotientFixedPointField reward block representative point ≠ 0,
        ({point | quittingQuotientFixedPointField reward block representative point = 0} ∩
          quittingQuotientOmegaAnnulus radius) =
            quittingQuotientNonzeroFixedPointSet reward block representative ∧
        ambientDegree (quittingQuotientFixedPointField reward block representative)
          (quittingQuotientOmegaAnnulus radius) 0
          (isOpen_quittingQuotientOmegaAnnulus radius)
          (isBounded_quittingQuotientOmegaAnnulus radius)
          (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
          hfrontier = 2 := by
  have hquotient := quotientMatrix_eq_of_pairedSingletonMatrix reward hmatrix
  have hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative) := by
    rw [hquotient]
    exact isR0
  have hdegree :
      r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 = -1 := by
    simpa only [hquotient] using degree_eq_neg_one
  obtain ⟨radius, hradius, hsmall, hisolation, hfrontier, hfiber, hactualDegree⟩ :=
    exists_quittingQuotientOmegaAnnulus_ambientDegree_eq_one_sub_r0Degree
      reward block representative block_representative hR0
  refine ⟨radius, hradius, hsmall, hisolation, hfrontier, hfiber, ?_⟩
  rw [hdegree] at hactualDegree
  norm_num at hactualDegree
  exact hactualDegree

end PairedResponseQuotient
end GameTheory
