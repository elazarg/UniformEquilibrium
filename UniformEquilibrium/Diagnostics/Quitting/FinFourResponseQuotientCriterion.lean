import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientHomogeneous
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientNormalCompletion
import UniformEquilibrium.Diagnostics.Quitting.FinFourAuxiliaryDiscountedLocalization
import MathUE.LinearProgramming.NonnegativeInverseDegree

/-!
# Original Fin4 no-UE restrictions on every response-invariant quotient

The same original-game contrary hypothesis supplies full singleton R0. The
actual block lift transfers it to the quotient; the existing quotient root
producer then forces quotient degree one. Thus a negative determinant and
entrywise nonnegative inverse suffice for UE without an input R0 certificate.
Zero inverse entries are allowed. No finite or regular zero fiber is assumed.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming

/-- Original Fin4 no-UE forces R0 for every actual response-invariant quotient. -/
theorem finFour_isR0Matrix_quittingResponseQuotientMatrix_of_no_uniformPayoff
    {k : ℕ} (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (block : Fin 4 → Fin k) (representative : Fin k → Fin 4)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    IsR0Matrix (quittingResponseQuotientMatrix reward block representative) :=
  isR0Matrix_quittingResponseQuotientMatrix_of_singleton
    reward block representative hrepresentative hresponse
    (finFour_isR0Matrix_quittingSingletonMatrix_of_no_uniformPayoff reward hno)

/-- The quotient's R0 proof and degree-one conclusion are both produced from
the same original-game no-UE assumption, not supplied as matrix certificates. -/
theorem finFour_responseQuotient_r0Degree_eq_one_of_no_uniformPayoff
    {k : ℕ} (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (block : Fin 4 → Fin k) (representative : Fin k → Fin 4)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative),
      r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 = 1 := by
  have hR0 := finFour_isR0Matrix_quittingResponseQuotientMatrix_of_no_uniformPayoff
    reward block representative hrepresentative hresponse hno
  refine ⟨hR0, ?_⟩
  by_contra hdegree
  exact hno (exists_uniformEquilibriumPayoff_finFour_of_responseInvariant_degree_ne_one
    reward block representative hrepresentative hresponse hR0 hdegree)

/-- A raw response-invariant quotient with negative determinant and
nonnegative inverse produces original Fin4 UE. R0 is not an input, and the
inverse may have zero entries. -/
theorem finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse
    {k : ℕ} (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (block : Fin 4 → Fin k) (representative : Fin k → Fin 4)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hdet : (quittingResponseQuotientMatrix reward block representative).det < 0)
    (hinverse : ∀ row column,
      0 ≤ (quittingResponseQuotientMatrix reward block representative)⁻¹ row column) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  obtain ⟨hR0, hdegree⟩ :=
    finFour_responseQuotient_r0Degree_eq_one_of_no_uniformPayoff
      reward block representative hrepresentative hresponse hno
  have hnegative :
      r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 = -1 := by
    rw [r0Degree_eq_sign_det_of_nonnegative_inverse
      (quittingResponseQuotientMatrix reward block representative) hR0 hdet.ne hinverse,
      sign_neg hdet]
    rfl
  have hfalse : (-1 : ℤ) = 1 := hnegative.symm.trans hdegree
  norm_num at hfalse

end GameTheory
