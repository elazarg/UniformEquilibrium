import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient
import MathUE.LinearProgramming.LocalAffine

/-!
# Homogeneous complementarity through the actual response quotient

The block lift repeats original-player hazards; it does not construct a
smaller quitting game. The actual singleton-matrix intertwining identity
transports homogeneous residuals and complementarity. Representatives make
the lift injective, so full singleton R0 implies quotient R0.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- Representatives recover every coordinate of the actual block lift. -/
theorem quittingBlockLift_injective
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate) :
    Function.Injective (quittingBlockLift block) := by
  intro first second hequal
  funext coordinate
  have hcoordinate := congrFun hequal (representative coordinate)
  simpa only [quittingBlockLift, hrepresentative] using hcoordinate

/-- The homogeneous residual is the lift of the actual quotient residual. -/
theorem lcpResidual_quittingBlockLift_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (point : Fin k → ℝ) :
    lcpResidual (quittingSingletonMatrix reward) 0 (quittingBlockLift block point) =
      quittingBlockLift block
        (lcpResidual (quittingResponseQuotientMatrix reward block representative) 0 point) := by
  simp only [lcpResidual_eq_add_mulVec, zero_add]
  exact quittingSingletonMatrix_mulVec_blockLift_eq_quotient
    reward block representative hrepresentative hresponse point

/-- Every actual homogeneous quotient solution lifts to a full singleton
solution, including boundary vectors and vectors outside the strategy cube. -/
theorem isStandardLCPSolution_quittingBlockLift_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (point : Fin k → ℝ)
    (hpoint : IsStandardLCPSolution
      (quittingResponseQuotientMatrix reward block representative) 0 point) :
    IsStandardLCPSolution (quittingSingletonMatrix reward) 0
      (quittingBlockLift block point) := by
  refine ⟨fun who => hpoint.weight_nonneg (block who), ?_, ?_⟩
  · intro who
    rw [lcpResidual_quittingBlockLift_zero
      reward block representative hrepresentative hresponse point]
    exact hpoint.residual_nonneg (block who)
  · intro who
    rw [lcpResidual_quittingBlockLift_zero
      reward block representative hrepresentative hresponse point]
    exact hpoint.complementary (block who)

/-- R0 descends from the full original singleton matrix to every actual
response-invariant quotient with nonempty blocks. -/
theorem isR0Matrix_quittingResponseQuotientMatrix_of_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward)) :
    IsR0Matrix (quittingResponseQuotientMatrix reward block representative) := by
  intro point hpoint coordinate
  have hzero := hR0 (quittingBlockLift block point)
    (isStandardLCPSolution_quittingBlockLift_zero
      reward block representative hrepresentative hresponse point hpoint)
    (representative coordinate)
  simpa only [quittingBlockLift, hrepresentative] using hzero

end GameTheory
