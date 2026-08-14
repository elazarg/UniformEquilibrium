import MathUE.CyclicExposure

/-!
# Sharp cyclic exposure

Reader-facing statements of the sharp exposure bound and its unique optimizer.
The canonical proofs remain in `MathUE.CyclicExposure`.
-/

namespace Theorems.CyclicExposure

open Math.CyclicExposure

/-- Every finite nonempty permutation system and every row in the unit cube
has a directed exposure of at most one quarter. -/
theorem exists_exposure_le_quarter
    {ι : Type} (C : Neighbours ι) [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ i, C.exposure x i ≤ (1 / 4 : ℝ) := by
  exact C.exists_exposure_le_quarter x hunit

/-- Every directed exposure is at least one quarter exactly for the constant
fair row. -/
theorem all_exposures_ge_quarter_iff_fair
    {ι : Type} (C : Neighbours ι) [Finite ι] [Nonempty ι]
    (x : ι → ℝ) (hunit : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (∀ i, (1 / 4 : ℝ) ≤ C.exposure x i) ↔
      x = fun _ => (1 / 2 : ℝ) := by
  exact C.forall_quarter_le_exposure_iff_eq_fair x hunit

end Theorems.CyclicExposure
