import MathUE.Topology.PathFirstClosedSetHit
import Mathlib.Topology.Connected.LocallyPathConnected

/-! # Closedness and path connectivity of selected component fillings

Adjoin an arbitrary family of complement path components to a closed set.
Closedness uses openness of complement components in a locally path-connected
ambient space. Actual paths into the original set are clipped at their first
closed-set hit. The ambient space can be the subtype of a larger Peano continuum.
No finite-family restriction is used. Local path connectivity of the filled
set, the remaining part of Fischer--Zastrow Lemma 12, is not asserted here.
-/

noncomputable section

namespace Math.Topology

open Set

variable {X : Type*} [TopologicalSpace X]

/-- Seeds select entire complement components; seeds inside the source set
contribute nothing, so the selecting family requires no side condition. -/
def selectedComponentFill (source seeds : Set X) : Set X :=
  source ∪ {point | ∃ seed ∈ seeds, point ∈ pathComponentIn sourceᶜ seed}

theorem source_subset_selectedComponentFill (source seeds : Set X) :
    source ⊆ selectedComponentFill source seeds := fun _ hpoint => Or.inl hpoint

/-- Membership is saturated along paths in the complement. -/
theorem mem_selectedComponentFill_of_joinedIn {source seeds : Set X} {first last : X}
    (hfirst : first ∈ selectedComponentFill source seeds)
    (hjoined : JoinedIn sourceᶜ first last) :
    last ∈ selectedComponentFill source seeds := by
  rcases hfirst with hsource | ⟨seed, hseed, hpath⟩
  · exact (hjoined.source_mem hsource).elim
  · exact Or.inr ⟨seed, hseed, hpath.trans hjoined⟩

/-- Unselected components give open neighborhoods in the complement of the fill. -/
theorem isClosed_selectedComponentFill [LocallyPathConnectedSpace X]
    {source : Set X} (hsource : IsClosed source) (seeds : Set X) :
    IsClosed (selectedComponentFill source seeds) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro point hpoint
  have houtside : point ∈ sourceᶜ := fun hmem => hpoint (Or.inl hmem)
  have hsubset : pathComponentIn sourceᶜ point ⊆
      (selectedComponentFill source seeds)ᶜ := by
    intro other hother hselected
    exact hpoint (mem_selectedComponentFill_of_joinedIn hselected hother.symm)
  exact Filter.mem_of_superset
    ((hsource.isOpen_compl.pathComponentIn point).mem_nhds
      (mem_pathComponentIn_self houtside)) hsubset

theorem isCompact_selectedComponentFill [CompactSpace X] [LocallyPathConnectedSpace X]
    {source : Set X} (hsource : IsClosed source) (seeds : Set X) :
    IsCompact (selectedComponentFill source seeds) :=
  (isClosed_selectedComponentFill hsource seeds).isCompact

/-- In a path-connected ambient space, every point of the fill has an actual
path inside the fill to a prescribed source point. Local connectivity is not
needed for this path construction. -/
theorem joinedIn_selectedComponentFill_to_source [PathConnectedSpace X]
    {source seeds : Set X} (hclosed : IsClosed source) (hsource : IsPathConnected source)
    {point anchor : X} (hpoint : point ∈ selectedComponentFill source seeds)
    (hanchor : anchor ∈ source) :
    JoinedIn (selectedComponentFill source seeds) point anchor := by
  let path := PathConnectedSpace.somePath point anchor
  obtain ⟨time, htime, _hbefore, clipped, hrange⟩ :=
    exists_path_to_first_closedSet_hit path hclosed hanchor
  have hclipped : JoinedIn (selectedComponentFill source seeds) point (path time) := by
    refine ⟨clipped, ?_⟩
    intro parameter
    rcases (hrange ⟨parameter, rfl⟩).2 with hmem | hcomponent
    · exact Or.inl hmem
    · exact mem_selectedComponentFill_of_joinedIn hpoint hcomponent
  exact hclipped.trans ((hsource.joinedIn (path time) htime anchor hanchor).mono
    (source_subset_selectedComponentFill source seeds))

/-- The first two conclusions of the selected-filling argument: any family
of complement components preserves path connectivity of a nonempty source. -/
theorem isPathConnected_selectedComponentFill [PathConnectedSpace X]
    {source : Set X} (hclosed : IsClosed source) (hsource : IsPathConnected source)
    (seeds : Set X) : IsPathConnected (selectedComponentFill source seeds) := by
  obtain ⟨anchor, hanchor⟩ := hsource.nonempty
  refine ⟨anchor, Or.inl hanchor, ?_⟩
  intro point hpoint
  exact (joinedIn_selectedComponentFill_to_source hclosed hsource hpoint hanchor).symm

end Math.Topology
