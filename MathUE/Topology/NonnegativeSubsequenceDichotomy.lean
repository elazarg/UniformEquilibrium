import Mathlib.Topology.Instances.ENNReal.Lemmas
import MathUE.CurveSelection.UltrafilterSubsequence

/-!
# Positive-floor or vanishing subsequences

A nonnegative real sequence either has a strict subsequence bounded below by
one positive constant, or the original sequence tends to zero.  The latter
arm is returned with the identity strict selector so downstream refinements
can use one uniform data-bearing interface.
-/

namespace Math

open Filter
open scoped Topology

/-- A data-bearing strict-subsequence split for a nonnegative real sequence. -/
inductive NonnegativeSubsequenceAlternative
    (sequence : ℕ → ℝ) : Type
  | positiveFloor
      (select : ℕ → ℕ)
      (select_strictMono : StrictMono select)
      (floor : ℝ)
      (floor_pos : 0 < floor)
      (floor_le : ∀ rank, floor ≤ sequence (select rank))
  | vanishing
      (select : ℕ → ℕ)
      (select_strictMono : StrictMono select)
      (tendsto_zero : Tendsto (sequence ∘ select) atTop (nhds 0))

/-- Every nonnegative real sequence has a positive-floor strict subsequence
or a strict subsequence tending to zero. -/
theorem nonempty_nonnegativeSubsequenceAlternative
    (sequence : ℕ → ℝ) (hnonneg : ∀ rank, 0 ≤ sequence rank) :
    Nonempty (NonnegativeSubsequenceAlternative sequence) := by
  by_cases hfloor : ∃ floor, 0 < floor ∧ ∃ᶠ rank in atTop, floor ≤ sequence rank
  · obtain ⟨floor, hfloorPos, hfrequent⟩ := hfloor
    obtain ⟨select, hselect, hselected⟩ :=
      extraction_of_frequently_atTop hfrequent
    exact ⟨.positiveFloor select hselect floor hfloorPos hselected⟩
  · have htendsto : Tendsto sequence atTop (nhds 0) := by
      apply tendsto_order.2
      constructor
      · intro lower hlower
        exact Filter.Eventually.of_forall fun rank ↦
          hlower.trans_le (hnonneg rank)
      · intro upper hupper
        have hnotFrequently : ¬∃ᶠ rank in atTop, upper ≤ sequence rank := by
          intro hfrequent
          exact hfloor ⟨upper, hupper, hfrequent⟩
        exact (not_frequently.mp hnotFrequently).mono fun rank hnot ↦
          lt_of_not_ge hnot
    exact ⟨.vanishing id strictMono_id (by simpa using htendsto)⟩

end Math
