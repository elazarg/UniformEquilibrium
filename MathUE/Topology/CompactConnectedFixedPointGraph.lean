import MathUE.Topology.ConnectedFixedPointContinuation
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Fixed-point continuation over a compact connected parameter set

The family is defined on the whole locally path-connected metric parameter space.
The selected compact set need not be path connected. Component separation, closed
projection along the compact state space, and the existing interval continuation
theorem produce actual fixed points in one connected component over the original set.
-/

namespace Math

open Set

private theorem exists_path_in_open_of_preconnected
    {X : Type*} [MetricSpace X] [LocallyPathConnectedSpace X]
    {D V : Set X} (hD : IsPreconnected D) (hV : IsOpen V) (hDV : D ⊆ V)
    {x y : X} (hx : x ∈ D) (hy : y ∈ D) :
    ∃ path : Path x y, ∀ time, path time ∈ V := by
  let : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
  have hpre : IsPreconnected (Subtype.val ⁻¹' D : Set V) :=
    hD.preimage_of_isOpenMap Subtype.val_injective hV.isOpenMap_subtype_val
      (fun point hpoint => ⟨⟨point, hDV hpoint⟩, rfl⟩)
  have hjoined : Joined (⟨x, hDV hx⟩ : V) ⟨y, hDV hy⟩ := by
    change (⟨y, hDV hy⟩ : V) ∈ pathComponent (⟨x, hDV hx⟩ : V)
    rw [pathComponent_eq_connectedComponent]
    exact hpre.subset_connectedComponent hx hy
  refine ⟨hjoined.somePath.map continuous_subtype_val, ?_⟩
  intro time
  exact (hjoined.somePath time).property

/-- A globally continuous family on a nonempty compact convex state space has
fixed points in one compact connected graph subset above any two points of an
arbitrary compact preconnected parameter set. No path in that set is required. -/
theorem exists_compact_connected_fixedPoint_graph_over_connected_set
    {X E : Type*} [MetricSpace X] [LocallyPathConnectedSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hconvex : Convex ℝ K) (hcompact : IsCompact K)
    (hne : K.Nonempty) (f : C(X × K, K))
    (D : Set X) (hDcompact : IsCompact D) (hD : IsPreconnected D)
    (x : X) (hx : x ∈ D) (y : X) (hy : y ∈ D) :
    ∃ component : Set (X × K),
      IsCompact component ∧ IsConnected component ∧
      (∀ point ∈ component, point.1 ∈ D ∧ f point = point.2) ∧
      (∃ state, (x, state) ∈ component) ∧
      (∃ state, (y, state) ∈ component) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let P := X × K
  let graph : Set P := {point | point.1 ∈ D ∧ f point = point.2}
  have hfixed : IsClosed {point : P | f point = point.2} :=
    isClosed_eq f.continuous continuous_snd
  have hgraphClosed : IsClosed graph :=
    (hDcompact.isClosed.preimage continuous_fst).inter hfixed
  have hgraphCompact : IsCompact graph :=
    (hDcompact.prod (isCompact_univ : IsCompact (univ : Set K))).of_isClosed_subset
      hgraphClosed (fun point hpoint => ⟨hpoint.1, mem_univ _⟩)
  let : CompactSpace graph := isCompact_iff_compactSpace.mp hgraphCompact
  let A : Set graph := {point | point.val.1 = x}
  let B : Set graph := {point | point.val.1 = y}
  have hA : IsClosed A :=
    isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hB : IsClosed B :=
    isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hspanning : ∃ a : graph, a ∈ A ∧
      ∃ b : graph, b ∈ B ∧ b ∈ connectedComponent a := by
    by_contra hnone
    obtain ⟨U, hU, hAU, hUB⟩ :=
      exists_isClopen_separator_of_no_common_component hA hB
        (fun a ha b hb hab => hnone ⟨a, ha, b, hb, hab⟩)
    let firstPiece : Set P := Subtype.val '' U
    let secondPiece : Set P := Subtype.val '' Uᶜ
    have hfirstClosed : IsClosed firstPiece :=
      (hU.isClosed.isCompact.image continuous_subtype_val).isClosed
    have hsecondClosed : IsClosed secondPiece :=
      (hU.compl.isClosed.isCompact.image continuous_subtype_val).isClosed
    have hpiecesDisjoint : Disjoint firstPiece secondPiece := by
      apply disjoint_left.mpr
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
      have hequal : b = a := Subtype.ext hba
      subst b
      exact hb ha
    obtain ⟨V₀, V₁, hV₀, hV₁, hfirstV₀, hsecondV₁, hdisjoint⟩ :=
      normal_separation hfirstClosed hsecondClosed hpiecesDisjoint
    let bad : Set P := {point | f point = point.2} ∩ (V₀ ∪ V₁)ᶜ
    have hbad : IsClosed bad := hfixed.inter (hV₀.union hV₁).isClosed_compl
    let V : Set X := (Prod.fst '' bad)ᶜ
    have hV : IsOpen V :=
      (isClosedMap_fst_of_compactSpace bad hbad).isOpen_compl
    have hDV : D ⊆ V := by
      intro parameter hparameter hbadParameter
      obtain ⟨point, hpoint, hequal⟩ := hbadParameter
      let z : graph := ⟨point, ⟨by simpa only [hequal] using hparameter, hpoint.1⟩⟩
      by_cases hz : z ∈ U
      · exact hpoint.2 (Or.inl (hfirstV₀ ⟨z, hz, rfl⟩))
      · exact hpoint.2 (Or.inr (hsecondV₁ ⟨z, hz, rfl⟩))
    have hcovered (point : P) (hparameter : point.1 ∈ V)
        (hpoint : f point = point.2) : point ∈ V₀ ∪ V₁ := by
      by_contra houtside
      exact hparameter ⟨point, ⟨hpoint, houtside⟩, rfl⟩
    obtain ⟨path, hpath⟩ := exists_path_in_open_of_preconnected hD hV hDV hx hy
    let family : C(unitInterval × K, K) :=
      ⟨fun point => f (path point.1, point.2),
        f.continuous.comp ((path.continuous.comp continuous_fst).prodMk continuous_snd)⟩
    obtain ⟨C, _hCcompact, hCconnected, hCfixed, hzero, hone⟩ :=
      exists_compact_connected_fixedPoint_continuation hconvex hcompact hne family
    let decode := fun point : unitInterval × K => (path point.1, point.2)
    have hdecode : Continuous decode :=
      (path.continuous.comp continuous_fst).prodMk continuous_snd
    have himageConnected : IsConnected (decode '' C) :=
      hCconnected.image decode hdecode.continuousOn
    have himageCovered : decode '' C ⊆ V₀ ∪ V₁ := by
      rintro _ ⟨point, hpoint, rfl⟩
      exact hcovered (decode point) (hpath point.1) (hCfixed point hpoint)
    obtain ⟨state₀, hstate₀⟩ := hzero
    obtain ⟨state₁, hstate₁⟩ := hone
    have hzeroFixed : f (x, state₀) = state₀ := by
      have hequal := hCfixed (0, state₀) hstate₀
      change f (path 0, state₀) = state₀ at hequal
      simpa only [Path.source] using hequal
    have honeFixed : f (y, state₁) = state₁ := by
      have hequal := hCfixed (1, state₁) hstate₁
      change f (path 1, state₁) = state₁ at hequal
      simpa only [Path.target] using hequal
    let zeroPoint : graph := ⟨(x, state₀), hx, hzeroFixed⟩
    let onePoint : graph := ⟨(y, state₁), hy, honeFixed⟩
    have hzeroV₀ : (x, state₀) ∈ V₀ :=
      hfirstV₀ ⟨zeroPoint, hAU rfl, rfl⟩
    have honeV₁ : (y, state₁) ∈ V₁ :=
      hsecondV₁ ⟨onePoint, fun hmem => disjoint_left.mp hUB hmem rfl, rfl⟩
    have hzeroImage : (x, state₀) ∈ decode '' C := by
      refine ⟨(0, state₀), hstate₀, ?_⟩
      simp only [decode, Path.source]
    have honeImage : (y, state₁) ∈ decode '' C := by
      refine ⟨(1, state₁), hstate₁, ?_⟩
      simp only [decode, Path.target]
    have himageV₀ : decode '' C ⊆ V₀ :=
      himageConnected.isPreconnected.subset_left_of_subset_union
        hV₀ hV₁ hdisjoint himageCovered ⟨(x, state₀), hzeroImage, hzeroV₀⟩
    exact disjoint_left.mp hdisjoint (himageV₀ honeImage) honeV₁
  obtain ⟨a, ha, b, hb, hab⟩ := hspanning
  refine ⟨Subtype.val '' connectedComponent a,
    isClosed_connectedComponent.isCompact.image continuous_subtype_val,
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn, ?_, ?_, ?_⟩
  · rintro point ⟨source, _, rfl⟩
    exact source.property
  · exact ⟨a.val.2, ⟨a, mem_connectedComponent, Prod.ext ha rfl⟩⟩
  · exact ⟨b.val.2, ⟨b, hab, Prod.ext hb rfl⟩⟩

end Math
