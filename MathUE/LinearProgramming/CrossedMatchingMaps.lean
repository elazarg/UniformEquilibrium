import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! # The three literal perfect matchings on four labels -/

namespace Math.CrossedMatching

def favorite : Fin 4 → Fin 4 := ![1, 0, 3, 2]

def scheduled : Fin 4 → Fin 4 := ![2, 3, 0, 1]

def other : Fin 4 → Fin 4 := ![3, 2, 1, 0]

theorem favorite_involutive : Function.Involutive favorite := by
  intro i
  fin_cases i <;> rfl

theorem scheduled_involutive : Function.Involutive scheduled := by
  intro i
  fin_cases i <;> rfl

theorem other_eq_favorite_scheduled (i : Fin 4) : other i = favorite (scheduled i) := by
  fin_cases i <;> rfl

def favoriteEquiv : Fin 4 ≃ Fin 4 :=
  ⟨favorite, favorite, favorite_involutive, favorite_involutive⟩

theorem other_scheduled_eq_favorite (i : Fin 4) : other (scheduled i) = favorite i := by
  fin_cases i <;> rfl

end Math.CrossedMatching
