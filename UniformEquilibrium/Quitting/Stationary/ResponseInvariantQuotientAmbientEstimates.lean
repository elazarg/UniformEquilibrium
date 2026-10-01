import UniformEquilibrium.Quitting.Stationary.DiscountedAmbientQuadraticRemainder
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient

/-! # Signed ambient quadratic remainder for the actual response quotient

The original-game estimate is restricted by coordinate repetition and recipient
projection. Hazards may have either sign; no positive-cube premise is imposed.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The packet's quotient remainder on a whole signed ambient neighborhood. -/
theorem exists_quittingQuotientResponse_ambient_quadratic_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block) :
    ∃ constant > 0, ∃ radius > 0, ∀ point : Fin k → ℝ, ‖point‖ < radius →
      ‖quittingQuotientResponse reward block representative point +
        (quittingResponseQuotientMatrix reward block representative).mulVec point‖ ≤
          constant * ‖point‖ ^ 2 := by
  obtain ⟨constant, hconstant, radius, hradius, hbound⟩ :=
    exists_ambient_quittingDisplacement_singleton_bound reward
  refine ⟨constant, hconstant, radius, hradius, fun point hpoint => ?_⟩
  have hlift : ‖quittingBlockLift block point‖ ≤ ‖point‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg point)).mpr
    intro who
    exact norm_le_pi_norm point (block who)
  have hintertwine := quittingSingletonMatrix_mulVec_blockLift_eq_quotient
    reward block representative hrepresentative hresponse point
  have hproject :
      ‖quittingQuotientResponse reward block representative point +
        (quittingResponseQuotientMatrix reward block representative).mulVec point‖ ≤
      ‖quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) +
        (quittingSingletonMatrix reward).mulVec (quittingBlockLift block point)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro coordinate
    have hlinear := congrFun hintertwine (representative coordinate)
    change (quittingSingletonMatrix reward).mulVec (quittingBlockLift block point)
        (representative coordinate) =
      (quittingResponseQuotientMatrix reward block representative).mulVec point
        (block (representative coordinate)) at hlinear
    rw [hrepresentative] at hlinear
    change ‖quittingDiscountedDisplacement reward 0 (quittingBlockLift block point)
        (representative coordinate) +
      (quittingResponseQuotientMatrix reward block representative).mulVec point coordinate‖ ≤ _
    rw [← hlinear]
    exact norm_le_pi_norm
      (quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) +
        (quittingSingletonMatrix reward).mulVec (quittingBlockLift block point))
      (representative coordinate)
  calc
    _ ≤ ‖quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) +
        (quittingSingletonMatrix reward).mulVec (quittingBlockLift block point)‖ := hproject
    _ ≤ constant * ‖quittingBlockLift block point‖ ^ 2 :=
      hbound _ (hlift.trans_lt hpoint)
    _ ≤ constant * ‖point‖ ^ 2 := by gcongr

end GameTheory
