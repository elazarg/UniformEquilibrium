import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Real.Basic

/-! # Supremum identities for finite date-or-Never menus -/

namespace Math

/-- Splitting the finite date-or-Never menu at date zero. The remaining
finite dates are reindexed by `Fin.succ`; Never is retained literally. -/
theorem sup'_option_fin_succ_eq_max
    (deadline : ℕ) (value : Option (Fin (deadline + 1)) → ℝ) :
    Finset.univ.sup' (Finset.univ_nonempty :
        (Finset.univ : Finset (Option (Fin (deadline + 1)))).Nonempty) value =
      max (value (some 0))
        (Finset.univ.sup' (Finset.univ_nonempty :
          (Finset.univ : Finset (Option (Fin deadline))).Nonempty)
          (fun action => value (action.map Fin.succ))) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro action _
    cases action with
    | none =>
        apply le_max_of_le_right
        simpa using Finset.le_sup'
          (fun action : Option (Fin deadline) => value (action.map Fin.succ))
          (Finset.mem_univ (none : Option (Fin deadline)))
    | some time =>
        refine Fin.cases ?_ (fun earlier => ?_) time
        · exact le_max_left _ _
        · apply le_max_of_le_right
          simpa using Finset.le_sup'
            (fun action : Option (Fin deadline) => value (action.map Fin.succ))
            (Finset.mem_univ (some earlier))
  · apply max_le
    · apply Finset.le_sup'
      exact Finset.mem_univ (some (0 : Fin (deadline + 1)))
    · apply Finset.sup'_le
      intro action _
      apply Finset.le_sup'
      exact Finset.mem_univ (action.map Fin.succ)

theorem sup'_affine_of_nonneg
    {α : Type} [Fintype α] [Nonempty α] (value : α → ℝ)
    (offset scale : ℝ) (hscale : 0 ≤ scale) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun action => offset + scale * value action) =
      offset + scale * Finset.univ.sup' Finset.univ_nonempty value := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro action _
    simpa [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left
        (Finset.le_sup' value (Finset.mem_univ action)) hscale) offset
  · obtain ⟨action, _, haction⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset α)) Finset.univ_nonempty value
    rw [haction]
    exact Finset.le_sup' (fun candidate : α => offset + scale * value candidate)
      (Finset.mem_univ action)

end Math
