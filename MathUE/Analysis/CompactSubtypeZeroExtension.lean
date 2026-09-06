import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Integrability of a bounded Borel function extended by zero from a compact real domain -/

noncomputable section

namespace Math

open Set MeasureTheory Filter

variable {coordinate : Type} [Fintype coordinate]

/-- Extending a bounded Borel function by zero from a compact domain gives an integrable
ambient function. Empty domains and dimension zero require no separate hypotheses. -/
theorem integrable_extend_subtype_zero_of_isCompact
    (domain : Set (coordinate → ℝ)) (hcompact : IsCompact domain)
    (function : domain → ℝ) (hmeasurable : Measurable function)
    (bound : ℝ) (hbound : ∀ point, ‖function point‖ ≤ bound) :
    Integrable (Function.extend Subtype.val function (fun _ ↦ 0)) := by
  let extension := Function.extend Subtype.val function (fun _ : coordinate → ℝ ↦ 0)
  have hextension : Measurable extension :=
    (MeasurableEmbedding.subtype_coe hcompact.isClosed.measurableSet).measurable_extend
      hmeasurable measurable_const
  have hoff (point : coordinate → ℝ) (hpoint : point ∉ domain) : extension point = 0 := by
    apply Function.extend_apply'
    rintro ⟨inside, hinside⟩
    exact hpoint (hinside ▸ inside.2)
  have hbounded : ∀ point, ‖extension point‖ ≤ max 0 bound := by
    intro point
    by_cases hpoint : point ∈ domain
    · have hvalue : extension point = function ⟨point, hpoint⟩ :=
        Subtype.val_injective.extend_apply function (fun _ ↦ 0) ⟨point, hpoint⟩
      rw [hvalue]
      exact (hbound _).trans (le_max_right _ _)
    · rw [hoff point hpoint, norm_zero]
      exact le_max_left _ _
  have hon : IntegrableOn extension domain :=
    Measure.integrableOn_of_bounded hcompact.measure_lt_top.ne
      hextension.aestronglyMeasurable (Eventually.of_forall hbounded)
  exact hon.integrable_of_forall_notMem_eq_zero hoff

end Math
