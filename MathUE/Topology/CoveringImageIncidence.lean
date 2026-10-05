import MathUE.Topology.CoveringLoopFamilyEndpoint
import MathUE.Topology.QuotientFiberCollision

/-! # Covering endpoints on a compact image incidence space

The observable is the actual endpoint of a lifted loop family. If slices over
the same parameter are endpoint-fixed homotopic, compact incidence and
preconnectedness force all these endpoints to agree. No index oracle or
lifting of arbitrary image paths to the strategy space is assumed.
-/

noncomputable section

namespace Math.Topology

variable {T S V E X : Type*}
  [TopologicalSpace T] [CompactSpace T] [T2Space T] [PreconnectedSpace T]
  [TopologicalSpace S] [CompactSpace S] [TopologicalSpace V] [T2Space V]
  [TopologicalSpace E] [TopologicalSpace X] {projection : E → X}

/-- The actual lifted endpoint is constant across compact image incidences
when equal-parameter loops are homotopic relative to their endpoints. -/
theorem coveringEndpoint_eq_of_compact_incidence
    (curve : T → V) (field : S → V)
    (hcurve : Continuous curve) (hfield : Continuous field)
    (himage : ∀ parameter, curve parameter ∈ Set.range field)
    (cover : IsCoveringMap projection) (base : X) (start : projection ⁻¹' {base})
    (family : C(unitInterval × ImageIncidence curve field, X))
    (hzero : ∀ point, family (0, point) = base)
    (hone : ∀ point, family (1, point) = base)
    (hfiber : ∀ left right : ImageIncidence curve field, left.val.1 = right.val.1 →
      (CoveringLoopFamily.slice family left).HomotopicRel
        (CoveringLoopFamily.slice family right) {0, 1})
    (first last : ImageIncidence curve field) :
    CoveringLoopFamily.endpoint cover base start family hzero hone first =
      CoveringLoopFamily.endpoint cover base start family hzero hone last := by
  by_contra hne
  obtain ⟨left, right, hparameter, hdifferent⟩ :=
    exists_same_parameter_ne_of_compact_incidence curve field hcurve hfield himage
      (CoveringLoopFamily.endpoint cover base start family hzero hone)
      (CoveringLoopFamily.endpoint_isLocallyConstant cover base start family hzero hone)
      first last hne
  exact hdifferent (CoveringLoopFamily.endpoint_eq_of_homotopicRel
    cover base start family hzero hone left right (hfiber left right hparameter))

/-- One constant slice normalizes every actual lifted endpoint to the chosen start. -/
theorem coveringEndpoint_eq_start_of_compact_incidence
    (curve : T → V) (field : S → V)
    (hcurve : Continuous curve) (hfield : Continuous field)
    (himage : ∀ parameter, curve parameter ∈ Set.range field)
    (cover : IsCoveringMap projection) (base : X) (start : projection ⁻¹' {base})
    (family : C(unitInterval × ImageIncidence curve field, X))
    (hzero : ∀ point, family (0, point) = base)
    (hone : ∀ point, family (1, point) = base)
    (hfiber : ∀ left right : ImageIncidence curve field, left.val.1 = right.val.1 →
      (CoveringLoopFamily.slice family left).HomotopicRel
        (CoveringLoopFamily.slice family right) {0, 1})
    (origin : ImageIncidence curve field)
    (hconstant : CoveringLoopFamily.slice family origin = .const unitInterval base)
    (point : ImageIncidence curve field) :
    CoveringLoopFamily.endpoint cover base start family hzero hone point = start := by
  exact (coveringEndpoint_eq_of_compact_incidence curve field hcurve hfield himage
    cover base start family hzero hone hfiber point origin).trans
      (CoveringLoopFamily.endpoint_eq_start_of_constant
        cover base start family hzero hone origin hconstant)

end Math.Topology
