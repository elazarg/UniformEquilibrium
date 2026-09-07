import Mathlib.Algebra.MvPolynomial.Eval
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumInwardViolation
import UniformEquilibrium.Quitting.Root.RewardTableCoordinates

/-! # Joint reward-hazard polynomials for product-low quitting premiums -/

noncomputable section

namespace GameTheory

variable {n : Nat}

/-- A hazard coordinate in the last block of the joint reward-hazard layout. -/
def quittingProductLowHazardCoordinate (player : Fin n) :
    Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) + n) :=
  Fin.natAdd (Fintype.card (QuittingRewardTableVariable (Fin n))) player

/-- A reward coordinate in the first block of the joint reward-hazard layout. -/
def quittingProductLowRewardCoordinate
    (terminal : {S : Finset (Fin n) // S.Nonempty}) (observer : Fin n) :
    Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) + n) :=
  Fin.castAdd n
    (Fintype.equivFin (QuittingRewardTableVariable (Fin n)) (terminal, observer))

/-- The singleton-relative Quit premium, jointly polynomial in the reward table
and hazard coordinates. -/
def quittingProductLowPremiumPolynomial (player : Fin n) :
    MvPolynomial
      (Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) + n)) ℝ :=
  ∑ coalition ∈ (Finset.univ.erase player).powerset,
    ((∏ other ∈ coalition,
        MvPolynomial.X (quittingProductLowHazardCoordinate other)) *
      ∏ other ∈ Finset.univ.erase player \ coalition,
        (1 - MvPolynomial.X (quittingProductLowHazardCoordinate other))) *
      (MvPolynomial.X (quittingProductLowRewardCoordinate
          ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player) -
        MvPolynomial.X (quittingProductLowRewardCoordinate
          (quittingSingletonTerminal player) player))

@[simp]
theorem eval_quittingProductLowPremiumPolynomial
    (table : Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ)
    (hazard : Fin n → ℝ) (player : Fin n) :
    MvPolynomial.eval (Fin.append table hazard)
        (quittingProductLowPremiumPolynomial player) =
      quittingHazardQuitPremium (quittingRewardTableFromCoordinates table)
        hazard player := by
  unfold quittingProductLowPremiumPolynomial quittingHazardQuitPremium
  simp only [map_sum, map_mul, map_prod, map_sub, MvPolynomial.eval_X, map_one,
    quittingProductLowHazardCoordinate, quittingProductLowRewardCoordinate,
    Fin.append_right, Fin.append_left, quittingRewardTableFromCoordinates]

end GameTheory
