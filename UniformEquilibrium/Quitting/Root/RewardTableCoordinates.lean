import UniformEquilibrium.ProofView.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-! # Finite coordinates for quitting-game reward tables -/

noncomputable section

namespace GameTheory

variable {n : Nat}

/-- One independent coordinate for every nonempty-coalition reward entry. -/
abbrev QuittingRewardTableVariable (ι : Type) :=
  {S : Finset ι // S.Nonempty} × ι

/-- Read each raw reward entry from its own coordinate, without restrictions on its value. -/
def quittingRewardTableFromCoordinates
    (table : Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ) :
    {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n) :=
  fun terminal observer => table
    (Fintype.equivFin (QuittingRewardTableVariable (Fin n)) (terminal, observer))

/-- Encode a real reward table in the same fixed coordinate layout. -/
def quittingRewardTableCoordinates
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n)) :
    Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ :=
  fun index => reward
    ((Fintype.equivFin (QuittingRewardTableVariable (Fin n))).symm index).1
    ((Fintype.equivFin (QuittingRewardTableVariable (Fin n))).symm index).2

/-- Decoding the coordinates of a reward table recovers that table. -/
theorem quittingRewardTableFromCoordinates_encode
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n)) :
    quittingRewardTableFromCoordinates (quittingRewardTableCoordinates reward) = reward := by
  funext terminal observer
  unfold quittingRewardTableFromCoordinates quittingRewardTableCoordinates
  rw [Equiv.symm_apply_apply]

/-- Encoding a decoded coordinate vector recovers every coordinate. -/
theorem quittingRewardTableCoordinates_decode
    (table : Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ) :
    quittingRewardTableCoordinates (quittingRewardTableFromCoordinates table) = table := by
  funext index
  unfold quittingRewardTableCoordinates quittingRewardTableFromCoordinates
  rw [Equiv.apply_symm_apply]

end GameTheory
