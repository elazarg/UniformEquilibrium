import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Algebra.Order.Field

/-! # Rational density in literal closed boxes, including degenerate faces -/

noncomputable section

namespace Math.Interval

open Set
open scoped Topology

variable {ι : Type*}

/-- Cast a rational boxed point into the identical real closed box. -/
def rationalClosedBoxCast (lower upper : ι → ℚ)
    (point : Icc lower upper) :
    Icc (fun who => (lower who : ℝ)) (fun who => (upper who : ℝ)) :=
  ⟨fun who => (point.1 who : ℝ),
    ⟨fun who => Rat.cast_le.mpr (point.2.1 who),
      fun who => Rat.cast_le.mpr (point.2.2 who)⟩⟩

/-- Clamping a dense rational product preserves closed faces exactly.
Zero-width coordinates are allowed, hence so are fixed rational face coordinates. -/
theorem denseRange_rationalClosedBoxCast (lower upper : ι → ℚ)
    (hwidth : lower ≤ upper) : DenseRange (rationalClosedBoxCast lower upper) := by
  let clip : (ι → ℝ) →
      Icc (fun who => (lower who : ℝ)) (fun who => (upper who : ℝ)) :=
    fun raw => ⟨fun who => max (lower who : ℝ) (min (upper who : ℝ) (raw who)),
      ⟨fun _ => le_max_left _ _, fun who =>
        max_le (Rat.cast_le.mpr (hwidth who)) (min_le_left _ _)⟩⟩
  have hclip : Continuous clip :=
    (continuous_pi fun who => continuous_const.max
      (continuous_const.min (continuous_apply who))).subtype_mk _
  have hsurjective : Function.Surjective clip := by
    intro point
    refine ⟨point.1, Subtype.ext ?_⟩
    funext who
    change max (lower who : ℝ) (min (upper who : ℝ) (point.1 who)) = point.1 who
    rw [min_eq_right (point.2.2 who), max_eq_right (point.2.1 who)]
  have hraw : DenseRange (fun point : ι → ℚ => fun who => (point who : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hdense := hsurjective.denseRange.comp hraw hclip
  apply Dense.mono (hd := hdense)
  rintro point ⟨raw, rfl⟩
  let selected : Icc lower upper :=
    ⟨fun who => max (lower who) (min (upper who) (raw who)),
      ⟨fun _ => le_max_left _ _, fun who => max_le (hwidth who) (min_le_left _ _)⟩⟩
  refine ⟨selected, Subtype.ext ?_⟩
  funext who
  simp only [rationalClosedBoxCast, selected, Function.comp_apply, clip,
    Rat.cast_max, Rat.cast_min]

end Math.Interval
