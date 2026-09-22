import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientLocalMin

/-! # Crossed stationary-response map with an auxiliary ceiling -/

noncomputable section

namespace GameTheory

open Set QuittingLCPClassification

variable {n : ℕ}

/-- The genuine row-permuted singleton matrix `PΓ`: payoff-recipient rows
are exchanged, while hazard columns and the original game are unchanged. -/
def quittingCrossedSingletonMatrix
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun row column => quittingSingletonMatrix reward
    ((Equiv.swap first second) row) column

/-- The crossed residual used only by the auxiliary fixed-point map. This is
neither a response-invariant quotient nor the ordinary unswapped Nash gain. -/
def quittingCrossedResponse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hazard : Fin n → ℝ) : Fin n → ℝ :=
  fun coordinate => quittingDiscountedDisplacement reward 0 hazard
    ((Equiv.swap first second) coordinate)

/-- Selected coordinates have auxiliary upper ceiling `height`; every other
coordinate retains unit ceiling. No original player action is restricted. -/
def quittingCrossedCeiling (first second : Fin n) (height : ℝ) : Fin n → ℝ :=
  fun coordinate => if coordinate = first ∨ coordinate = second then height else 1

/-- Literal crossed self-map on the entire ambient real hazard space. -/
def quittingCrossedClippedMap
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ)
    (hazard : Fin n → ℝ) : Fin n → ℝ :=
  fun coordinate => min (quittingCrossedCeiling first second height coordinate)
    (max 0 (hazard coordinate +
      quittingCrossedResponse reward first second hazard coordinate))

/-- The ambient fixed-point displacement, whose local minimum model is
`min(q,(PΓ)q)` at all-Continue. -/
def quittingCrossedFixedPointField
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ)
    (hazard : Fin n → ℝ) : Fin n → ℝ :=
  hazard - quittingCrossedClippedMap reward first second height hazard

theorem continuous_quittingCrossedResponse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) :
    Continuous (quittingCrossedResponse reward first second) := by
  apply continuous_pi
  intro coordinate
  exact (continuous_quittingDiscountedDisplacement reward
    ((Equiv.swap first second) coordinate)).comp
      (continuous_const.prodMk continuous_id)

theorem continuous_quittingCrossedClippedMap
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) :
    Continuous (quittingCrossedClippedMap reward first second height) := by
  apply continuous_pi
  intro coordinate
  exact continuous_const.min (continuous_const.max
    ((continuous_apply coordinate).add
      ((continuous_apply coordinate).comp
        (continuous_quittingCrossedResponse reward first second))))

theorem quittingCrossedResponse_zero
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) :
    quittingCrossedResponse reward first second 0 = 0 := by
  funext coordinate
  exact quittingDiscountedDisplacement_zero reward
    ((Equiv.swap first second) coordinate)

private theorem crossedResponse_eq_quotientResponse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) :
    quittingCrossedResponse reward first second =
      quittingQuotientResponse reward (fun coordinate => coordinate)
        (Equiv.swap first second) := by
  funext hazard coordinate
  rfl

private theorem crossedMatrix_eq_quotientMatrix
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) :
    quittingCrossedSingletonMatrix reward first second =
      quittingResponseQuotientMatrix reward (fun coordinate => coordinate)
        (Equiv.swap first second) := by
  ext row column
  simp [quittingCrossedSingletonMatrix, quittingResponseQuotientMatrix,
    quittingSingletonBlockRowSum]

/-- The ambient derivative of the crossed response is exactly `−PΓ`, with
no response-invariance premise. The quotient derivative theorem is reused
only for its polynomial chain rule, not for any quotient strategy semantics. -/
theorem quittingCrossedResponse_derivative_apply
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (point : Fin n → ℝ) :
    fderiv ℝ (quittingCrossedResponse reward first second) 0 point =
      -(quittingCrossedSingletonMatrix reward first second).mulVec point := by
  rw [crossedResponse_eq_quotientResponse]
  have hderiv := hasFDerivAt_quittingQuotientResponse_zero reward
    (fun coordinate => coordinate) (Equiv.swap first second)
  rw [hderiv.fderiv]
  rw [quittingQuotientResponse_derivative_apply]
  rw [crossedMatrix_eq_quotientMatrix]

end GameTheory
