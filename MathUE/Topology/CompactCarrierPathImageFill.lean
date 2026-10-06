import MathUE.Topology.SelectedComponentFillLocallyPathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Separation.Hausdorff

/-! # Canonical filling of an interval image inside a compact carrier

The seeds are computed from complement components contained in the carrier.
The resulting closed, compact, path-connected and locally path-connected set
contains the original interval image and stays inside the carrier. This is the
actual loop-image filling used before the planar disk-model argument; neither
a Peano set nor a disk model is supplied as an input. Endpoint equality is not
needed for this prerequisite. No planar nullhomotopy conclusion is asserted.
-/

noncomputable section

namespace Math.Topology

open Set _root_.Topology

variable {X : Type*} [TopologicalSpace X]

/-- Adjoin exactly the complement path components contained in the carrier. -/
def carrierPathImageFill (path : C(unitInterval, X)) (carrier : Set X) : Set X :=
  selectedComponentFill (Set.range path)
    {seed | pathComponentIn (Set.range path)ᶜ seed ⊆ carrier}

theorem range_subset_carrierPathImageFill (path : C(unitInterval, X)) (carrier : Set X) :
    Set.range path ⊆ carrierPathImageFill path carrier :=
  source_subset_selectedComponentFill _ _

theorem carrierPathImageFill_subset (path : C(unitInterval, X)) {carrier : Set X}
    (hpath : Set.range path ⊆ carrier) : carrierPathImageFill path carrier ⊆ carrier := by
  intro point hpoint
  rcases hpoint with hsource | ⟨seed, hseed, hcomponent⟩
  · exact hpath hsource
  · exact hseed hcomponent

/-- A continuous interval image is locally path connected by the compact
quotient theorem; no choice of a continuous section is involved. -/
theorem locallyPathConnectedSpace_interval_image [T2Space X]
    (path : C(unitInterval, X)) : LocallyPathConnectedSpace (Set.range path) := by
  let : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let restricted : unitInterval → Set.range path := fun time => ⟨path time, ⟨time, rfl⟩⟩
  have hcontinuous : Continuous restricted := path.continuous.subtype_mk _
  have hsurjective : Function.Surjective restricted := by
    rintro ⟨point, time, htime⟩
    exact ⟨time, Subtype.ext htime⟩
  have hquotient := IsQuotientMap.of_surjective_continuous hsurjective hcontinuous
  exact hquotient.locallyPathConnectedSpace

theorem isClosed_carrierPathImageFill [T2Space X] [LocallyPathConnectedSpace X]
    (path : C(unitInterval, X)) (carrier : Set X) :
    IsClosed (carrierPathImageFill path carrier) :=
  isClosed_selectedComponentFill (isCompact_range path.continuous).isClosed _

/-- Compactness comes from the closed filling's inclusion in the compact
carrier, not from compactness of the ambient space. -/
theorem isCompact_carrierPathImageFill [T2Space X] [LocallyPathConnectedSpace X]
    (path : C(unitInterval, X)) {carrier : Set X} (hcarrier : IsCompact carrier)
    (hpath : Set.range path ⊆ carrier) : IsCompact (carrierPathImageFill path carrier) :=
  hcarrier.of_isClosed_subset (isClosed_carrierPathImageFill path carrier)
    (carrierPathImageFill_subset path hpath)

theorem isPathConnected_carrierPathImageFill [T2Space X] [PathConnectedSpace X]
    (path : C(unitInterval, X)) (carrier : Set X) :
    IsPathConnected (carrierPathImageFill path carrier) := by
  let : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  exact isPathConnected_selectedComponentFill (isCompact_range path.continuous).isClosed
    (isPathConnected_range path.continuous) _

theorem locallyPathConnectedSpace_carrierPathImageFill
    [T2Space X] [LocallyPathConnectedSpace X]
    (path : C(unitInterval, X)) (carrier : Set X) :
    LocallyPathConnectedSpace (carrierPathImageFill path carrier) := by
  let := locallyPathConnectedSpace_interval_image path
  exact locallyPathConnectedSpace_selectedComponentFill
    (isCompact_range path.continuous).isClosed _

/-- The canonical compact, path-connected, locally path-connected interval-image filling.
No local connectivity of the containing carrier is assumed. -/
theorem carrierPathImageFill_spec [T2Space X] [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] (path : C(unitInterval, X)) {carrier : Set X}
    (hcarrier : IsCompact carrier) (hpath : Set.range path ⊆ carrier) :
    Set.range path ⊆ carrierPathImageFill path carrier ∧
      carrierPathImageFill path carrier ⊆ carrier ∧
      IsCompact (carrierPathImageFill path carrier) ∧
      IsPathConnected (carrierPathImageFill path carrier) ∧
      LocallyPathConnectedSpace (carrierPathImageFill path carrier) :=
  ⟨range_subset_carrierPathImageFill path carrier, carrierPathImageFill_subset path hpath,
    isCompact_carrierPathImageFill path hcarrier hpath,
    isPathConnected_carrierPathImageFill path carrier,
    locallyPathConnectedSpace_carrierPathImageFill path carrier⟩

end Math.Topology
