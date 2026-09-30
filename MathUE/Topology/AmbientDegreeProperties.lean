import MathUE.Topology.AmbientDegree
import MathUE.Topology.BoxComplementaritySelfMapNormalization

/-!
# Ambient degree extensionality, excision, additivity, and normalization

All comparisons compute with one source extension and one enclosing chart.
Subregions need only be contained in the source region, not have their closures
contained in its interior. Admissibility of excised regions is derived from
retention of all target-valued points. Disjoint open subregions covering those
points give additivity without a finite or regular fiber assumption.

Identity normalization on every bounded open region containing its target
delegates to the actual constant rectangle self-map and its counted degree.
-/

noncomputable section

namespace Math.Topology

open Set

variable {n : ℕ}

/-- Agreement on the source closure transfers its frontier avoidance. -/
theorem frontier_avoids_of_eqOn_closure
    (first second : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hEqual : EqOn first second (closure region))
    (hfrontier : ∀ point ∈ frontier region, first point ≠ target) :
    ∀ point ∈ frontier region, second point ≠ target := by
  intro point hpoint
  rw [← hEqual (frontier_subset_closure hpoint)]
  exact hfrontier point hpoint

/-- The actual source field may be replaced by one agreeing on its closure.
Continuity and frontier avoidance of the replacement are derived. -/
theorem ambientDegree_congr
    (first second : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region) (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn first (closure region))
    (hfrontier : ∀ point ∈ frontier region, first point ≠ target)
    (hEqual : EqOn first second (closure region)) :
    ambientDegree first region target hopen hbounded hfield hfrontier =
      ambientDegree second region target hopen hbounded (hfield.congr hEqual.symm)
        (frontier_avoids_of_eqOn_closure first second region target hEqual hfrontier) := by
  obtain ⟨lower, upper, hwidth, hclosure, extension, hextension⟩ :=
    exists_rectangular_continuousExtension_of_isBounded region hbounded first hfield
  have hsecondEqual : EqOn extension second (closure region) :=
    fun _ hpoint => (hextension hpoint).trans (hEqual hpoint)
  exact (ambientDegree_eq_of_extension first region target hopen hbounded hfield hfrontier
    lower upper hwidth hclosure extension extension.continuous.continuousOn hextension).trans
      (ambientDegree_eq_of_extension second region target hopen hbounded
        (hfield.congr hEqual.symm)
        (frontier_avoids_of_eqOn_closure first second region target hEqual hfrontier)
        lower upper hwidth hclosure extension extension.continuous.continuousOn
        hsecondEqual).symm

private theorem extension_subregion_isolating
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (region part : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hopen : IsOpen part) (hsubset : part ⊆ region)
    (hfrontier : ∀ point ∈ frontier part, field point ≠ target)
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (extension : (Fin n → ℝ) → Fin n → ℝ)
    (hExtension : ContinuousOn extension (Icc lower upper))
    (hEqual : EqOn extension field (closure region)) :
    (Math.BoxComplementarityProblem.ofAmbientMap lower upper hwidth
      (fun point => extension point - target) (hExtension.sub continuousOn_const)).IsIsolating
      (rectangularCubePoint lower upper ⁻¹' part) :=
  isIsolating_ambientExtension field part target hopen hfrontier lower upper hwidth
    (fun _ hpoint => hclosure (closure_mono hsubset hpoint)) extension hExtension
    (fun _ hpoint => hEqual (closure_mono hsubset hpoint))

private theorem ambientDegree_eq_extension_subregion
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (region part : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hbounded : Bornology.IsBounded region) (hfield : ContinuousOn field (closure region))
    (hopen : IsOpen part) (hsubset : part ⊆ region)
    (hfrontier : ∀ point ∈ frontier part, field point ≠ target)
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (extension : (Fin n → ℝ) → Fin n → ℝ)
    (hExtension : ContinuousOn extension (Icc lower upper))
    (hEqual : EqOn extension field (closure region)) :
    ambientDegree field part target hopen (hbounded.subset hsubset)
      (hfield.mono (closure_mono hsubset)) hfrontier =
      (Math.BoxComplementarityProblem.ofAmbientMap lower upper hwidth
        (fun point => extension point - target) (hExtension.sub continuousOn_const)).localDegree
        (rectangularCubePoint lower upper ⁻¹' part)
        (extension_subregion_isolating field region part target hopen hsubset hfrontier
          lower upper hwidth hclosure extension hExtension hEqual) :=
  ambientDegree_eq_of_extension field part target hopen (hbounded.subset hsubset)
    (hfield.mono (closure_mono hsubset)) hfrontier lower upper hwidth
    (fun _ hpoint => hclosure (closure_mono hsubset hpoint)) extension hExtension
    (fun _ hpoint => hEqual (closure_mono hsubset hpoint))

private theorem solutionsIn_extension_subregion_eq
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (region part : Set (Fin n → ℝ)) (target : Fin n → ℝ) (hsubset : part ⊆ region)
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (extension : (Fin n → ℝ) → Fin n → ℝ)
    (hExtension : ContinuousOn extension (Icc lower upper))
    (hEqual : EqOn extension field (closure region)) :
    (Math.BoxComplementarityProblem.ofAmbientMap lower upper hwidth
      (fun point => extension point - target) (hExtension.sub continuousOn_const)).solutionsIn
      (rectangularCubePoint lower upper ⁻¹' part) =
      rectangularCubePoint lower upper ⁻¹' ({point | field point = target} ∩ part) := by
  rw [Math.BoxComplementarityProblem.solutionsIn_ofAmbientMap_preimage_eq
    lower upper hwidth (fun point => extension point - target)
    (hExtension.sub continuousOn_const) part
    (fun _ hpoint => hclosure (subset_closure (hsubset hpoint.1)))]
  ext point
  change (extension (rectangularCubePoint lower upper point) - target = 0 ∧
      rectangularCubePoint lower upper point ∈ part) ↔
    (field (rectangularCubePoint lower upper point) = target ∧
      rectangularCubePoint lower upper point ∈ part)
  by_cases hpoint : rectangularCubePoint lower upper point ∈ part
  · rw [hEqual (subset_closure (hsubset hpoint)), sub_eq_zero]
  · simp only [hpoint, and_false]

/-- An open subregion retaining every source root automatically avoids the
target on its own frontier; its closure need not stay inside the source. -/
theorem frontier_avoids_of_targetFiber_retained
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (region part : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hopen : IsOpen part) (hsubset : part ⊆ region)
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (hretain : ∀ point ∈ region, field point = target → point ∈ part) :
    ∀ point ∈ frontier part, field point ≠ target := by
  intro point hpoint htarget
  have hsource : point ∈ closure region :=
    closure_mono hsubset (frontier_subset_closure hpoint)
  rw [closure_eq_self_union_frontier] at hsource
  rcases hsource with hsource | hsource
  · have hpart := hretain point hsource htarget
    have hinterior : point ∈ interior part := by
      rwa [hopen.interior_eq]
    exact (mem_interior_iff_notMem_frontier hpart).mp hinterior hpoint
  · exact hfrontier point hsource htarget

/-- Excision retains every target-valued point, without finite-root or
regularity assumptions and without requiring closure containment in the source. -/
theorem ambientDegree_excision
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (region part : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hopen : IsOpen region) (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region))
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (hpartOpen : IsOpen part) (hsubset : part ⊆ region)
    (hretain : ∀ point ∈ region, field point = target → point ∈ part) :
    ambientDegree field region target hopen hbounded hfield hfrontier =
      ambientDegree field part target hpartOpen (hbounded.subset hsubset)
        (hfield.mono (closure_mono hsubset))
        (frontier_avoids_of_targetFiber_retained field region part target hpartOpen
          hsubset hfrontier hretain) := by
  obtain ⟨lower, upper, hwidth, hclosure, extension, hEqual⟩ :=
    exists_rectangular_continuousExtension_of_isBounded region hbounded field hfield
  let problem := Math.BoxComplementarityProblem.ofAmbientMap lower upper hwidth
    (fun point => extension point - target)
    (extension.continuous.continuousOn.sub continuousOn_const)
  let cubeRegion := rectangularCubePoint lower upper ⁻¹' region
  let cubePart := rectangularCubePoint lower upper ⁻¹' part
  have hpartFrontier := frontier_avoids_of_targetFiber_retained field region part target
    hpartOpen hsubset hfrontier hretain
  have hregionIso : problem.IsIsolating cubeRegion :=
    extension_subregion_isolating field region region target hopen (Subset.rfl) hfrontier
      lower upper hwidth hclosure extension extension.continuous.continuousOn hEqual
  have hpartIso : problem.IsIsolating cubePart :=
    extension_subregion_isolating field region part target hpartOpen hsubset hpartFrontier
      lower upper hwidth hclosure extension extension.continuous.continuousOn hEqual
  have hsolutions : problem.solutionsIn cubeRegion = problem.solutionsIn cubePart := by
    rw [solutionsIn_extension_subregion_eq field region region target (Subset.rfl)
      lower upper hwidth hclosure extension extension.continuous.continuousOn hEqual,
      solutionsIn_extension_subregion_eq field region part target hsubset
        lower upper hwidth hclosure extension extension.continuous.continuousOn hEqual]
    apply congrArg (fun selected : Set (Fin n → ℝ) =>
      rectangularCubePoint lower upper ⁻¹' selected)
    ext point
    constructor
    · rintro ⟨htarget, hpoint⟩
      exact ⟨htarget, hretain point hpoint htarget⟩
    · rintro ⟨htarget, hpoint⟩
      exact ⟨htarget, hsubset hpoint⟩
  exact (ambientDegree_eq_extension_subregion field region region target hbounded hfield
    hopen (Subset.rfl) hfrontier lower upper hwidth hclosure extension
    extension.continuous.continuousOn hEqual).trans
      ((problem.localDegree_eq_of_solutionsIn_eq cubeRegion cubePart hregionIso hpartIso
        hsolutions).trans
        (ambientDegree_eq_extension_subregion field region part target hbounded hfield
          hpartOpen hsubset hpartFrontier lower upper hwidth hclosure extension
          extension.continuous.continuousOn hEqual).symm)

/-- Each open member of a disjoint decomposition is admissible whenever the
decomposition covers every source root. -/
theorem frontier_avoids_of_disjoint_rootCover
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (region first second : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hfirstOpen : IsOpen first) (hsecondOpen : IsOpen second)
    (hfirstSubset : first ⊆ region) (hdisjoint : Disjoint first second)
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (hretain : ∀ point ∈ region, field point = target → point ∈ first ∪ second) :
    ∀ point ∈ frontier first, field point ≠ target := by
  intro point hpoint htarget
  have hsource : point ∈ closure region :=
    closure_mono hfirstSubset (frontier_subset_closure hpoint)
  rw [closure_eq_self_union_frontier] at hsource
  rcases hsource with hsource | hsource
  · rcases hretain point hsource htarget with hfirst | hsecond
    · have hinterior : point ∈ interior first := by
        rwa [hfirstOpen.interior_eq]
      exact (mem_interior_iff_notMem_frontier hfirst).mp hinterior hpoint
    · exact (Set.disjoint_left.mp (hdisjoint.closure_left hsecondOpen))
        (frontier_subset_closure hpoint) hsecond
  · exact hfrontier point hsource htarget

/-- Additivity on two disjoint open subregions covering all source roots.
Subregion admissibility is derived; empty pieces and nonregular fibers are allowed. -/
theorem ambientDegree_additive
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (region first second : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hopen : IsOpen region) (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region))
    (hfrontier : ∀ point ∈ frontier region, field point ≠ target)
    (hfirstOpen : IsOpen first) (hsecondOpen : IsOpen second)
    (hfirstSubset : first ⊆ region) (hsecondSubset : second ⊆ region)
    (hdisjoint : Disjoint first second)
    (hretain : ∀ point ∈ region, field point = target → point ∈ first ∪ second) :
    let hfirstFrontier := frontier_avoids_of_disjoint_rootCover field region first second
      target hfirstOpen hsecondOpen hfirstSubset hdisjoint hfrontier hretain
    let hsecondFrontier := frontier_avoids_of_disjoint_rootCover field region second first
      target hsecondOpen hfirstOpen hsecondSubset hdisjoint.symm hfrontier
      (fun point hpoint htarget => (hretain point hpoint htarget).symm)
    ambientDegree field region target hopen hbounded hfield hfrontier =
      ambientDegree field first target hfirstOpen (hbounded.subset hfirstSubset)
        (hfield.mono (closure_mono hfirstSubset)) hfirstFrontier +
      ambientDegree field second target hsecondOpen (hbounded.subset hsecondSubset)
        (hfield.mono (closure_mono hsecondSubset)) hsecondFrontier := by
  dsimp only
  obtain ⟨lower, upper, hwidth, hclosure, extension, hEqual⟩ :=
    exists_rectangular_continuousExtension_of_isBounded region hbounded field hfield
  let problem := Math.BoxComplementarityProblem.ofAmbientMap lower upper hwidth
    (fun point => extension point - target)
    (extension.continuous.continuousOn.sub continuousOn_const)
  let cubeRegion := rectangularCubePoint lower upper ⁻¹' region
  let cubeFirst := rectangularCubePoint lower upper ⁻¹' first
  let cubeSecond := rectangularCubePoint lower upper ⁻¹' second
  have hfirstFrontier := frontier_avoids_of_disjoint_rootCover field region first second
    target hfirstOpen hsecondOpen hfirstSubset hdisjoint hfrontier hretain
  have hsecondFrontier := frontier_avoids_of_disjoint_rootCover field region second first
    target hsecondOpen hfirstOpen hsecondSubset hdisjoint.symm hfrontier
    (fun point hpoint htarget => (hretain point hpoint htarget).symm)
  have hregionIso : problem.IsIsolating cubeRegion :=
    extension_subregion_isolating field region region target hopen (Subset.rfl) hfrontier
      lower upper hwidth hclosure extension extension.continuous.continuousOn hEqual
  have hfirstIso : problem.IsIsolating cubeFirst :=
    extension_subregion_isolating field region first target hfirstOpen hfirstSubset hfirstFrontier
      lower upper hwidth hclosure extension extension.continuous.continuousOn hEqual
  have hsecondIso : problem.IsIsolating cubeSecond :=
    extension_subregion_isolating field region second target hsecondOpen hsecondSubset
      hsecondFrontier lower upper hwidth hclosure extension
      extension.continuous.continuousOn hEqual
  have hunionSubset : first ∪ second ⊆ region := union_subset hfirstSubset hsecondSubset
  have hsolutions :
      problem.solutionsIn cubeRegion = problem.solutionsIn (cubeFirst ∪ cubeSecond) := by
    change problem.solutionsIn (rectangularCubePoint lower upper ⁻¹' region) =
      problem.solutionsIn
        (rectangularCubePoint lower upper ⁻¹' first ∪
          rectangularCubePoint lower upper ⁻¹' second)
    rw [← preimage_union,
      solutionsIn_extension_subregion_eq field region region target (Subset.rfl)
        lower upper hwidth hclosure extension extension.continuous.continuousOn hEqual,
      solutionsIn_extension_subregion_eq field region (first ∪ second) target hunionSubset
        lower upper hwidth hclosure extension extension.continuous.continuousOn hEqual]
    apply congrArg (fun selected : Set (Fin n → ℝ) =>
      rectangularCubePoint lower upper ⁻¹' selected)
    ext point
    constructor
    · rintro ⟨htarget, hpoint⟩
      exact ⟨htarget, hretain point hpoint htarget⟩
    · rintro ⟨htarget, hpoint⟩
      exact ⟨htarget, hunionSubset hpoint⟩
  calc
    _ = problem.localDegree cubeRegion hregionIso :=
      ambientDegree_eq_extension_subregion field region region target hbounded hfield
        hopen (Subset.rfl) hfrontier lower upper hwidth hclosure extension
        extension.continuous.continuousOn hEqual
    _ = problem.localDegree (cubeFirst ∪ cubeSecond)
        (problem.isIsolating_union cubeFirst cubeSecond hfirstIso hsecondIso) :=
      problem.localDegree_eq_of_solutionsIn_eq cubeRegion (cubeFirst ∪ cubeSecond)
        hregionIso (problem.isIsolating_union cubeFirst cubeSecond hfirstIso hsecondIso)
        hsolutions
    _ = problem.localDegree cubeFirst hfirstIso + problem.localDegree cubeSecond hsecondIso :=
      problem.localDegree_union_of_disjoint cubeFirst cubeSecond hfirstIso hsecondIso
        (hdisjoint.preimage (rectangularCubePoint lower upper))
    _ = _ := congrArg₂ (· + ·)
      (ambientDegree_eq_extension_subregion field region first target hbounded hfield
        hfirstOpen hfirstSubset hfirstFrontier lower upper hwidth hclosure extension
        extension.continuous.continuousOn hEqual).symm
      (ambientDegree_eq_extension_subregion field region second target hbounded hfield
        hsecondOpen hsecondSubset hsecondFrontier lower upper hwidth hclosure extension
        extension.continuous.continuousOn hEqual).symm

/-- The identity misses an interior target on the source frontier. -/
theorem identity_ne_target_on_frontier
    (region : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hopen : IsOpen region) (htarget : target ∈ region) :
    ∀ point ∈ frontier region, (id point : Fin n → ℝ) ≠ target := by
  intro point hpoint hequal
  change point = target at hequal
  subst point
  have hinterior : target ∈ interior region := by
    rwa [hopen.interior_eq]
  exact (mem_interior_iff_notMem_frontier htarget).mp hinterior hpoint

/-- Full positive identity normalization on every bounded open source
containing its target. No dimension, regularity, or root-count restriction. -/
theorem ambientDegree_id_eq_one
    (region : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hopen : IsOpen region) (hbounded : Bornology.IsBounded region)
    (htarget : target ∈ region) :
    ambientDegree id region target hopen hbounded continuous_id.continuousOn
      (identity_ne_target_on_frontier region target hopen htarget) = 1 := by
  obtain ⟨lower, upper, hwidth, hclosure, _⟩ :=
    exists_rectangular_continuousExtension_of_isBounded region hbounded id
      continuous_id.continuousOn
  have htargetBox : target ∈ Icc lower upper :=
    ⟨fun who => (hclosure (subset_closure htarget) who).1.le,
      fun who => (hclosure (subset_closure htarget) who).2.le⟩
  have hself : MapsTo (fun _ : Fin n → ℝ => target) (Icc lower upper) (Icc lower upper) :=
    fun _ _ => htargetBox
  have hfixed : ∀ point ∈ Icc lower upper,
      point = (fun _ : Fin n → ℝ => target) point → point ∈ region :=
    fun _ _ hequal => hequal.symm ▸ htarget
  rw [ambientDegree_eq_of_extension id region target hopen hbounded
    continuous_id.continuousOn (identity_ne_target_on_frontier region target hopen htarget)
    lower upper hwidth hclosure id continuous_id.continuousOn (fun _ _ => rfl)]
  exact Math.BoxComplementarityProblem.localDegree_of_selfMap_preimage_eq_one
    lower upper hwidth (fun _ => target) continuousOn_const hself region hopen hfixed

end Math.Topology
