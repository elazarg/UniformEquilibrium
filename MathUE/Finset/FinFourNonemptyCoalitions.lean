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

/-- The first fourteen canonical rows exhaust all nonempty proper coalitions. -/
theorem finFour_properNonemptyCoalition_row
    (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hproper : coalition ≠ Finset.univ) :
    ∃ row : Fin 14, finFourCoalitionOfRow row.castSucc = coalition := by
  obtain ⟨row, hrow⟩ := finFourCoalitionRowEquiv.surjective ⟨coalition, hnonempty⟩
  have heq : finFourCoalitionOfRow row = coalition := congrArg Subtype.val hrow
  have hlt : row.val < 14 := by
    by_contra hnot
    have hlast : row = 14 := Fin.ext (by omega)
    subst row
    apply hproper
    rw [← heq]
    decide
  refine ⟨⟨row.val, hlt⟩, ?_⟩
  exact heq

theorem finFour_nonempty_proper_iff_row
    (coalition : Finset (Fin 4)) :
    coalition.Nonempty ∧ coalition ≠ Finset.univ ↔
      ∃ row : Fin 14, finFourCoalitionOfRow row.castSucc = coalition := by
  constructor
  · rintro ⟨hnonempty, hproper⟩
    exact finFour_properNonemptyCoalition_row coalition hnonempty hproper
  · rintro ⟨row, rfl⟩
    refine ⟨finFourCoalitionOfRow_nonempty _, ?_⟩
    fin_cases row <;> decide

end Math.Finset
