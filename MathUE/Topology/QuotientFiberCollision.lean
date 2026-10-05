import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Separation.Hausdorff

/-! # Locally constant values collide on a quotient fiber

A locally constant function on a quotient's source either varies on one fiber
or descends to a locally constant function on the target. A preconnected target
therefore forces a fiber collision whenever two source values differ.
The compact-incidence specialization needs neither a continuous selector nor
connected strategy fibers, and constructs no planar index.
-/

noncomputable section

namespace Math.Topology

variable {X T S V J : Type*}

/-- Distinct locally constant values over a preconnected quotient must already
occur over a single target point. The value type carries no topology. -/
theorem exists_same_fiber_ne_of_isQuotientMap
    [TopologicalSpace X] [TopologicalSpace T] [PreconnectedSpace T]
    (projection : X → T) (hquotient : _root_.Topology.IsQuotientMap projection)
    (value : X → J) (hvalue : IsLocallyConstant value)
    (first last : X) (hne : value first ≠ value last) :
    ∃ left right : X, projection left = projection right ∧ value left ≠ value right := by
  classical
  by_contra hnone
  have hfiber : ∀ left right : X, projection left = projection right →
      value left = value right := by
    intro left right heq
    by_contra hne
    exact hnone ⟨left, right, heq, hne⟩
  let sectionMap : T → X := fun target => (hquotient.surjective target).choose
  have hsection : ∀ target, projection (sectionMap target) = target :=
    fun target => (hquotient.surjective target).choose_spec
  let descended : T → J := fun target => value (sectionMap target)
  have hdescended : ∀ point, descended (projection point) = value point := by
    intro point
    exact hfiber (sectionMap (projection point)) point (hsection (projection point))
  have hlocallyConstant : IsLocallyConstant descended := by
    intro subset
    apply hquotient.isCoinducing.isOpen_preimage.mp
    have heq : projection ⁻¹' (descended ⁻¹' subset) = value ⁻¹' subset := by
      ext point
      change descended (projection point) ∈ subset ↔ value point ∈ subset
      rw [hdescended]
    rw [heq]
    exact hvalue subset
  exact hne (by
    rw [← hdescended first, ← hdescended last]
    exact hlocallyConstant.apply_eq_of_preconnectedSpace (projection first) (projection last))

/-- Continuous compact-to-Hausdorff surjections provide the required quotient map. -/
theorem exists_same_fiber_ne_of_compact_surjection
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace T] [T2Space T] [PreconnectedSpace T]
    (projection : X → T) (hcontinuous : Continuous projection)
    (hsurjective : Function.Surjective projection)
    (value : X → J) (hvalue : IsLocallyConstant value)
    (first last : X) (hne : value first ≠ value last) :
    ∃ left right : X, projection left = projection right ∧ value left ≠ value right :=
  exists_same_fiber_ne_of_isQuotientMap projection
    (_root_.Topology.IsQuotientMap.of_surjective_continuous hsurjective hcontinuous)
    value hvalue first last hne

/-- Parameters paired with strategies realizing the corresponding image point. -/
abbrev ImageIncidence (curve : T → V) (field : S → V) :=
  {point : T × S // curve point.1 = field point.2}

/-- A continuous image curve and compact strategy carrier give a quotient
projection of their actual incidence space onto the parameter space. -/
theorem isQuotientMap_incidence_projection
    [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TopologicalSpace S] [CompactSpace S] [TopologicalSpace V] [T2Space V]
    (curve : T → V) (field : S → V)
    (hcurve : Continuous curve) (hfield : Continuous field)
    (himage : ∀ parameter, curve parameter ∈ Set.range field) :
    _root_.Topology.IsQuotientMap
      (fun point : ImageIncidence curve field => point.val.1) := by
  have hclosed : IsClosed {point : T × S | curve point.1 = field point.2} :=
    isClosed_eq (hcurve.comp continuous_fst) (hfield.comp continuous_snd)
  let : CompactSpace (ImageIncidence curve field) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  apply _root_.Topology.IsQuotientMap.of_surjective_continuous
  · intro parameter
    obtain ⟨strategy, hstrategy⟩ := himage parameter
    exact ⟨⟨(parameter, strategy), hstrategy.symm⟩, rfl⟩
  · exact continuous_fst.comp continuous_subtype_val

/-- The compact-incidence collision used by the printed fiber argument.
The locally constant observable remains arbitrary; no index is supplied here. -/
theorem exists_same_parameter_ne_of_compact_incidence
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [PreconnectedSpace T]
    [TopologicalSpace S] [CompactSpace S] [TopologicalSpace V] [T2Space V]
    (curve : T → V) (field : S → V)
    (hcurve : Continuous curve) (hfield : Continuous field)
    (himage : ∀ parameter, curve parameter ∈ Set.range field)
    (value : ImageIncidence curve field → J) (hvalue : IsLocallyConstant value)
    (first last : ImageIncidence curve field) (hne : value first ≠ value last) :
    ∃ left right : ImageIncidence curve field,
      left.val.1 = right.val.1 ∧ value left ≠ value right :=
  exists_same_fiber_ne_of_isQuotientMap (fun point => point.val.1)
    (isQuotientMap_incidence_projection curve field hcurve hfield himage)
    value hvalue first last hne

end Math.Topology
