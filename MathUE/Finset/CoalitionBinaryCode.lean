import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.FinCases

/-! # The canonical binary code of a finite indexed coalition -/

namespace Math.FiniteCoalition

open scoped BigOperators

def binaryCode {players : ℕ} (coalition : Finset (Fin players)) : ℕ :=
  ∑ player ∈ coalition, 2 ^ player.val

theorem binaryCode_injective {players : ℕ} :
    Function.Injective (@binaryCode players) := by
  intro left right hequal
  have himage : left.image Fin.val = right.image Fin.val := by
    apply Finset.geomSum_injective (n := 2) (by omega)
    change (∑ i ∈ left.image Fin.val, 2 ^ i) =
      ∑ i ∈ right.image Fin.val, 2 ^ i
    rw [Finset.sum_image (fun _ _ _ _ hequal => Fin.ext hequal),
      Finset.sum_image (fun _ _ _ _ hequal => Fin.ext hequal)]
    exact hequal
  exact Finset.image_injective Fin.val_injective himage

theorem binaryCode_finFour (coalition : Finset (Fin 4)) :
    binaryCode coalition =
      (if 0 ∈ coalition then 1 else 0) + (if 1 ∈ coalition then 2 else 0) +
        (if 2 ∈ coalition then 4 else 0) + (if 3 ∈ coalition then 8 else 0) := by
  fin_cases coalition <;> decide

end Math.FiniteCoalition
