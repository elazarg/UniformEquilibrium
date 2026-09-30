import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-! # Binary-mask enumeration of nonempty four-coordinate subsets -/

noncomputable section

namespace Math.Finset

/-- Binary-mask enumeration of the fifteen nonempty coalitions. -/
def finFourCoalitionOfRow (row : (Fin 15)) : Finset (Fin 4) :=
  match row.val with
  | 0 => {0}
  | 1 => {1}
  | 2 => {0, 1}
  | 3 => {2}
  | 4 => {0, 2}
  | 5 => {1, 2}
  | 6 => {0, 1, 2}
  | 7 => {3}
  | 8 => {0, 3}
  | 9 => {1, 3}
  | 10 => {0, 1, 3}
  | 11 => {2, 3}
  | 12 => {0, 2, 3}
  | 13 => {1, 2, 3}
  | _ => {0, 1, 2, 3}

theorem finFourCoalitionOfRow_nonempty (row : (Fin 15)) :
    (finFourCoalitionOfRow row).Nonempty := by
  fin_cases row <;> simp [finFourCoalitionOfRow]

/-- The row enumeration as an equivalence with nonempty coalitions. -/
def finFourCoalitionRowEquiv : (Fin 15) ≃
    {coalition : Finset (Fin 4) // coalition.Nonempty} :=
  Equiv.ofBijective (fun row ↦
    ⟨finFourCoalitionOfRow row, finFourCoalitionOfRow_nonempty row⟩) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · decide
    · change 15 = Fintype.card {coalition : Finset (Fin 4) // coalition.Nonempty}
      decide

end Math.Finset
