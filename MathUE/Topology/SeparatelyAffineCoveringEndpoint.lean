import MathUE.Topology.SeparatelyAffineImageLoopFamily
import MathUE.Topology.CoveringImageIncidence

/-! # Covering lifts of loops in compact separately affine images close

The actual prefix-and-return family supplies continuity, equal-time homotopies,
and a constant initial slice. Compact incidence then makes its covering endpoint
constant. The final slice is homotopic to the original image loop, so the lift
of that loop returns to its starting point. No image loop is assumed to lift
to strategy space, and no planar simple-connectedness conclusion is asserted.
-/

noncomputable section

namespace Math.Topology.SeparatelyAffinePair

variable {X Y E Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace Z] [TopologicalSpace W]
  {left : ContinuousMixer X} {right : ContinuousMixer Y}
  (field : SeparatelyAffinePair (E := E) left right)

/-- The covering-family slice is the underlying continuous map of the
literal mapped prefix-and-return path. -/
theorem slice_mappedPrefixReturnFamily (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base))
    (imageMap : C(Set.range field.value, Z)) (point : field.LoopIncidence base loop) :
    CoveringLoopFamily.slice (imageMap.comp (field.prefixReturnFamily base loop)) point =
      ((field.prefixReturnLoop base loop point).map imageMap.continuous).toContinuousMap := rfl

/-- This explicit bridge uses the actual equal-time path homotopy, rather
than requiring a separate homotopy callback for the covering construction. -/
theorem mappedPrefixReturnFamily_same_time (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base))
    (imageMap : C(Set.range field.value, Z))
    (first last : field.LoopIncidence base loop) (htime : first.val.1 = last.val.1) :
    (CoveringLoopFamily.slice
      (imageMap.comp (field.prefixReturnFamily base loop)) first).HomotopicRel
        (CoveringLoopFamily.slice (imageMap.comp (field.prefixReturnFamily base loop)) last)
        {0, 1} := by
  rw [field.slice_mappedPrefixReturnFamily, field.slice_mappedPrefixReturnFamily]
  exact (field.prefixReturnLoop_homotopic_of_same_time base loop first last htime).map imageMap

/-- Every covering lift of a continuously mapped image loop closes. The
compact strategy spaces may have nontrivial fibers and need no chosen section. -/
theorem liftPath_imageLoop_apply_one [CompactSpace X] [CompactSpace Y] [T2Space E]
    (base : X × Y) (loop : Path (field.rangeMap base) (field.rangeMap base))
    (imageMap : C(Set.range field.value, Z))
    {projection : W → Z} (cover : IsCoveringMap projection)
    (start : projection ⁻¹' {imageMap (field.rangeMap base)}) :
    cover.liftPath (loop.map imageMap.continuous).toContinuousMap start.val
      ((congrArg imageMap loop.source).trans
        (show projection start.val = imageMap (field.rangeMap base) from start.property).symm)
      1 = start.val := by
  let family := imageMap.comp (field.prefixReturnFamily base loop)
  have hzero : ∀ point : field.LoopIncidence base loop,
      family (0, point) = imageMap (field.rangeMap base) := by
    intro point
    exact congrArg imageMap (field.prefixReturnFamily_zero base loop point)
  have hone : ∀ point : field.LoopIncidence base loop,
      family (1, point) = imageMap (field.rangeMap base) := by
    intro point
    exact congrArg imageMap (field.prefixReturnFamily_one base loop point)
  have himage : ∀ time, loop time ∈ Set.range field.rangeMap := by
    intro time
    obtain ⟨point, hpoint⟩ := (loop time).property
    exact ⟨point, Subtype.ext hpoint⟩
  have hconstant : CoveringLoopFamily.slice family (field.initialIncidence base loop) =
      .const unitInterval (imageMap (field.rangeMap base)) := by
    rw [field.slice_mappedPrefixReturnFamily, field.prefixReturnLoop_initial]
    rfl
  have hendpoint := coveringEndpoint_eq_start_of_compact_incidence
    (fun time => loop time) field.rangeMap loop.continuous field.rangeMap.continuous himage
    cover (imageMap (field.rangeMap base)) start family hzero hone
    (field.mappedPrefixReturnFamily_same_time base loop imageMap)
    (field.initialIncidence base loop) hconstant (field.finalIncidence base loop)
  have hactual := congrArg Subtype.val hendpoint
  rw [CoveringLoopFamily.endpoint_val] at hactual
  have hfinal : (CoveringLoopFamily.slice family (field.finalIncidence base loop)).HomotopicRel
      (loop.map imageMap.continuous).toContinuousMap {0, 1} := by
    rw [field.slice_mappedPrefixReturnFamily]
    exact (field.prefixReturnLoop_final_homotopic base loop).map imageMap
  have hstart : projection start.val = imageMap (field.rangeMap base) := start.property
  have hsame := cover.liftPath_apply_one_eq_of_homotopicRel hfinal start.val
    ((hzero (field.finalIncidence base loop)).trans hstart.symm)
    ((congrArg imageMap loop.source).trans hstart.symm)
  exact hsame.symm.trans hactual

end Math.Topology.SeparatelyAffinePair
