import MathUE.Topology.SeparatelyAffineCoveringEndpoint
import Mathlib.Analysis.Complex.CoveringMap

/-! # Closed logarithmic lifts of separately affine image loops

Translation by a point outside the image gives a literal map to the punctured
complex plane. The exponential covering and the compact-incidence endpoint
theorem produce a continuous logarithm with equal endpoints. This is not a
nullhomotopy in the original image, and no integer-valued index is assumed.
-/

noncomputable section

namespace Math.Topology.SeparatelyAffinePair

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {left : ContinuousMixer X} {right : ContinuousMixer Y}
  (field : SeparatelyAffinePair (E := ℂ) left right)

/-- The actual translated image, with the omitted point removed. -/
def puncturedImageMap (outside : ℂ) (houtside : outside ∉ Set.range field.value) :
    C(Set.range field.value, {z : ℂ // z ≠ 0}) where
  toFun point := ⟨point.val - outside, fun hzero =>
    houtside ((sub_eq_zero.mp hzero) ▸ point.property)⟩
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

/-- Every translated image loop has a continuous logarithm whose endpoints
both equal the canonical logarithm of its base point. No strategy lift is used. -/
theorem exists_closed_logarithmic_lift [CompactSpace X] [CompactSpace Y]
    (base : X × Y) (loop : Path (field.rangeMap base) (field.rangeMap base))
    (outside : ℂ) (houtside : outside ∉ Set.range field.value) :
    ∃ lifted : C(unitInterval, ℂ),
      (∀ time, Complex.exp (lifted time) = (loop time).val - outside) ∧
      lifted 0 = Complex.log (field.value base - outside) ∧
      lifted 1 = Complex.log (field.value base - outside) := by
  let imageMap := field.puncturedImageMap outside houtside
  let projection : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨z.exp, z.exp_ne_zero⟩
  have hnonzero : field.value base - outside ≠ 0 := by
    intro hzero
    exact houtside ⟨base, sub_eq_zero.mp hzero⟩
  have hlog : projection (Complex.log (field.value base - outside)) =
      imageMap (field.rangeMap base) := by
    apply Subtype.ext
    exact Complex.exp_log hnonzero
  let start : projection ⁻¹' {imageMap (field.rangeMap base)} :=
    ⟨Complex.log (field.value base - outside), hlog⟩
  let translated := (loop.map imageMap.continuous).toContinuousMap
  have hstart : translated 0 = projection start.val :=
    (congrArg imageMap loop.source).trans hlog.symm
  let lifted := Complex.isCoveringMap_exp.liftPath translated start.val hstart
  refine ⟨lifted, ?_, ?_, ?_⟩
  · intro time
    exact congrArg Subtype.val
      (congrFun (Complex.isCoveringMap_exp.liftPath_lifts translated start.val hstart) time)
  · exact Complex.isCoveringMap_exp.liftPath_zero translated start.val hstart
  · exact field.liftPath_imageLoop_apply_one base loop imageMap Complex.isCoveringMap_exp start

end Math.Topology.SeparatelyAffinePair
