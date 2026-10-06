import MathUE.Topology.SelectedComponentFill

/-! # Local path connectivity of selected component fillings

The neighborhood-path proof of Fischer--Zastrow Lemma 12 uses a first-hit
clipping inside a small ambient neighborhood, followed by a small source path.
Only local path connectivity of the ambient space and of the closed source is
needed. Global connectedness, compactness, metrics, and finite component families
are not assumed. This does not assert the subsequent planar disk-model theorem.
-/

noncomputable section

namespace Math.Topology

open Set Filter _root_.Topology

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]

/-- An ambient neighborhood whose selected-fill points connect to the base
point inside any prescribed open neighborhood intersected with the fill. -/
theorem exists_open_joinedIn_selectedComponentFill
    {source : Set X} (hclosed : IsClosed source) [LocallyPathConnectedSpace source]
    (seeds : Set X) {point : X} (hpoint : point ∈ selectedComponentFill source seeds)
    {outer : Set X} (houter : IsOpen outer) (hpointOuter : point ∈ outer) :
    ∃ inner : Set X, IsOpen inner ∧ point ∈ inner ∧ inner ⊆ outer ∧
      ∀ other ∈ inner, other ∈ selectedComponentFill source seeds →
        JoinedIn (selectedComponentFill source seeds ∩ outer) point other := by
  by_cases hsource : point ∈ source
  · let sourcePoint : source := ⟨point, hsource⟩
    let sourceOuter : Set source := Subtype.val ⁻¹' outer
    have hsourceOuter : IsOpen sourceOuter := houter.preimage continuous_subtype_val
    have hsourcePoint : sourcePoint ∈ sourceOuter := hpointOuter
    have hcomponentOpen := hsourceOuter.pathComponentIn sourcePoint
    obtain ⟨ambient, hambient, heq⟩ := isOpen_induced_iff.mp hcomponentOpen
    have hpointAmbient : point ∈ ambient := by
      have hmem := mem_pathComponentIn_self hsourcePoint
      rw [← heq] at hmem
      exact hmem
    let inner := pathComponentIn (ambient ∩ outer) point
    have hpointInner : point ∈ inner := mem_pathComponentIn_self
      ⟨hpointAmbient, hpointOuter⟩
    refine ⟨inner, (hambient.inter houter).pathComponentIn point, hpointInner,
      pathComponentIn_subset.trans inter_subset_right, ?_⟩
    intro other hother hotherFill
    have hpath : JoinedIn (ambient ∩ outer) other point := hother.symm
    obtain ⟨time, htime, _hbefore, clipped, hrange⟩ :=
      exists_path_to_first_closedSet_hit hpath.somePath hclosed hsource
    have hhitAmbient : hpath.somePath time ∈ ambient := (hpath.somePath_mem time).1
    have hsourceJoin : JoinedIn sourceOuter sourcePoint
        ⟨hpath.somePath time, htime⟩ := by
      change (⟨hpath.somePath time, htime⟩ : source) ∈
        pathComponentIn sourceOuter sourcePoint
      rw [← heq]
      exact hhitAmbient
    have hsourceMapped : JoinedIn (selectedComponentFill source seeds ∩ outer)
        point (hpath.somePath time) := by
      apply (hsourceJoin.map continuous_subtype_val.continuousOn).mono
      rintro target ⟨preimage, hpreimage, rfl⟩
      exact ⟨Or.inl preimage.property, hpreimage⟩
    have hclipped : JoinedIn (selectedComponentFill source seeds ∩ outer)
        other (hpath.somePath time) := by
      refine ⟨clipped, ?_⟩
      intro parameter
      obtain ⟨hinrange, hwhere⟩ := hrange ⟨parameter, rfl⟩
      have houterPoint : clipped parameter ∈ outer := by
        obtain ⟨original, horiginal⟩ := hinrange
        exact horiginal ▸ (hpath.somePath_mem original).2
      refine ⟨?_, houterPoint⟩
      rcases hwhere with hinSource | hinComponent
      · exact Or.inl hinSource
      · exact mem_selectedComponentFill_of_joinedIn hotherFill hinComponent
    exact hsourceMapped.trans hclipped.symm
  · let inner := pathComponentIn (sourceᶜ ∩ outer) point
    have hpointInner : point ∈ inner := mem_pathComponentIn_self ⟨hsource, hpointOuter⟩
    have hsubset : inner ⊆ selectedComponentFill source seeds ∩ outer := by
      intro other hother
      exact ⟨mem_selectedComponentFill_of_joinedIn hpoint
        (hother.mono inter_subset_left), hother.target_mem.2⟩
    refine ⟨inner, (hclosed.isOpen_compl.inter houter).pathComponentIn point,
      hpointInner, hsubset.trans inter_subset_right, ?_⟩
    intro other hother _hotherFill
    exact ((isPathConnected_pathComponentIn
      (show point ∈ sourceᶜ ∩ outer from ⟨hsource, hpointOuter⟩)).joinedIn
      point hpointInner other hother).mono hsubset

/-- Arbitrary selected complement components preserve local path connectivity
of a closed, locally path-connected source in a locally path-connected ambient space. -/
theorem locallyPathConnectedSpace_selectedComponentFill
    {source : Set X} (hclosed : IsClosed source) [LocallyPathConnectedSpace source]
    (seeds : Set X) : LocallyPathConnectedSpace (selectedComponentFill source seeds) := by
  apply locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr
  intro point outer houter hpointOuter
  obtain ⟨ambient, hambient, rfl⟩ := isOpen_induced_iff.mp houter
  obtain ⟨inner, hinner, hpointInner, _hsubset, hjoin⟩ :=
    exists_open_joinedIn_selectedComponentFill hclosed seeds point.property hambient hpointOuter
  apply (mem_nhds_subtype _ point _).mpr
  refine ⟨inner, hinner.mem_nhds hpointInner, ?_⟩
  intro other hother
  have hjoined := hjoin other.val hother other.property
  let path : Path point other :=
    { toFun := fun time => ⟨hjoined.somePath time, (hjoined.somePath_mem time).1⟩
      continuous_toFun := hjoined.somePath.continuous.subtype_mk _
      source' := Subtype.ext hjoined.somePath.source
      target' := Subtype.ext hjoined.somePath.target }
  refine ⟨path, ?_⟩
  intro time
  exact (hjoined.somePath_mem time).2

end Math.Topology
