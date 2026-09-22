import MathUE.Topology.BoxComplementarityAmbientMapAdapter
import MathUE.Topology.BoxComplementarityMeshOneNormalization
import MathUE.Topology.BoxComplementaritySolutionExcision

/-!
# Normalization for a self-map in a rectangular chart

For a continuous self-map of a closed rectangle, the actual complementarity
problem for `point - map point` has precisely the pulled-back fixed points as
solutions, including boundary fixed points. Any open ambient
region containing these fixed points therefore has local degree one, by
same-problem excision and whole-cube normalization. The map's entire image need
not lie in that region. Strict inwardness additionally excludes all boundary
solutions. No chart-independence assertion is used.
-/

noncomputable section

namespace Math.BoxComplementarityProblem

open Set Math.Topology

variable {ι : Type*} [Fintype ι]
variable (lower upper : ι → ℝ) (hwidth : ∀ who, lower who < upper who)
  (map : (ι → ℝ) → ι → ℝ) (hmap : ContinuousOn map (Icc lower upper))

/-- For a rectangle self-map, all actual box solutions are fixed points,
including possible boundary solutions. -/
theorem isSolution_of_selfMap_iff
    (hself : MapsTo map (Icc lower upper) (Icc lower upper)) (point : UnitCube ι) :
    (ofAmbientMap lower upper hwidth (fun point => point - map point)
      (continuousOn_id.sub hmap)).IsSolution point ↔
        rectangularCubePoint lower upper point =
          map (rectangularCubePoint lower upper point) := by
  constructor
  · intro hsolution
    have hin := hself (rectangularCubePoint_mem_Icc hwidth point)
    funext who
    have hlower := hin.1 who
    have hupper := hin.2 who
    have hbounds := (point who).property
    by_cases hzero : (point who : ℝ) = 0
    · have hgain := (hsolution who).1 hzero
      change -(rectangularCubePoint lower upper point who -
        map (rectangularCubePoint lower upper point) who) ≤ 0 at hgain
      have hchart : rectangularCubePoint lower upper point who = lower who := by
        simp [rectangularCubePoint, rectangularPoint, hzero]
      rw [hchart] at hgain ⊢
      linarith
    · by_cases hone : (point who : ℝ) = 1
      · have hgain := (hsolution who).2.1 hone
        change 0 ≤ -(rectangularCubePoint lower upper point who -
          map (rectangularCubePoint lower upper point) who) at hgain
        have hchart : rectangularCubePoint lower upper point who = upper who := by
          simp [rectangularCubePoint, rectangularPoint, hone]
        rw [hchart] at hgain ⊢
        linarith
      · have hgain := (hsolution who).2.2
          (lt_of_le_of_ne hbounds.1 (Ne.symm hzero)) (lt_of_le_of_ne hbounds.2 hone)
        change -(rectangularCubePoint lower upper point who -
          map (rectangularCubePoint lower upper point) who) = 0 at hgain
        linarith
  · intro hfixed
    apply isSolution_of_gain_eq_zero
    change -(rectangularCubePoint lower upper point -
      map (rectangularCubePoint lower upper point)) = 0
    exact neg_eq_zero.mpr (sub_eq_zero.mpr hfixed)

/-- Strict inwardness excludes every cube-boundary solution of the actual
pulled-back fixed-point field. This includes the empty coordinate type. -/
theorem coordinateInterior_of_isSolution_of_inwardMap
    (hinward : ∀ point ∈ Icc lower upper,
      ∀ who, lower who < map point who ∧ map point who < upper who)
    (point : UnitCube ι)
    (hsolution : (ofAmbientMap lower upper hwidth (fun point => point - map point)
      (continuousOn_id.sub hmap)).IsSolution point) :
    ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
  have hmaps : MapsTo map (Icc lower upper) (Icc lower upper) := by
    intro source hsource
    exact ⟨fun who => (hinward source hsource who).1.le,
      fun who => (hinward source hsource who).2.le⟩
  have hfixed := (isSolution_of_selfMap_iff lower upper hwidth map hmap hmaps point).mp
    hsolution
  apply (rectangularCubePoint_coordinateInterior_iff hwidth point).mp
  intro who
  rw [hfixed]
  exact hinward _ (rectangularCubePoint_mem_Icc hwidth point) who

/-- An open region containing the ambient fixed points is automatically
isolating; no separate source isolation or whole-image containment is assumed. -/
theorem isIsolating_of_selfMap_preimage
    (hself : MapsTo map (Icc lower upper) (Icc lower upper)) (region : Set (ι → ℝ))
    (hopen : IsOpen region)
    (hfixed : ∀ point ∈ Icc lower upper, point = map point → point ∈ region) :
    (ofAmbientMap lower upper hwidth (fun point => point - map point)
      (continuousOn_id.sub hmap)).IsIsolating
        (rectangularCubePoint lower upper ⁻¹' region) := by
  have hopenPreimage := hopen.preimage (continuous_rectangularCubePoint lower upper)
  refine ⟨hopenPreimage, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hmem : point ∈ rectangularCubePoint lower upper ⁻¹' region :=
    hfixed _ (rectangularCubePoint_mem_Icc hwidth point)
      ((isSolution_of_selfMap_iff lower upper hwidth map hmap hself point).mp hsolution)
  have hinterior : point ∈ interior (rectangularCubePoint lower upper ⁻¹' region) := by
    rwa [hopenPreimage.interior_eq]
  exact (mem_interior_iff_notMem_frontier hmem).mp hinterior hfrontier

variable {n : ℕ}

/-- The actual degree of `point - map point` is one on any open region
containing its fixed points. The conclusion includes dimension zero. -/
theorem localDegree_of_selfMap_preimage_eq_one
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (map : (Fin n → ℝ) → Fin n → ℝ) (hmap : ContinuousOn map (Icc lower upper))
    (hself : MapsTo map (Icc lower upper) (Icc lower upper))
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hfixed : ∀ point ∈ Icc lower upper, point = map point → point ∈ region) :
    (ofAmbientMap lower upper hwidth (fun point => point - map point)
      (continuousOn_id.sub hmap)).localDegree
        (rectangularCubePoint lower upper ⁻¹' region)
        (isIsolating_of_selfMap_preimage lower upper hwidth map hmap hself
          region hopen hfixed) = 1 := by
  let problem := ofAmbientMap lower upper hwidth (fun point => point - map point)
    (continuousOn_id.sub hmap)
  have hequal : problem.solutionsIn (rectangularCubePoint lower upper ⁻¹' region) =
      problem.solutionsIn univ := by
    ext point
    change (problem.IsSolution point ∧ rectangularCubePoint lower upper point ∈ region) ↔
      (problem.IsSolution point ∧ point ∈ (univ : Set (UnitCube (Fin n))))
    constructor
    · exact fun hpoint => ⟨hpoint.1, mem_univ _⟩
    · intro hpoint
      exact ⟨hpoint.1, hfixed _ (rectangularCubePoint_mem_Icc hwidth point)
        ((isSolution_of_selfMap_iff lower upper hwidth map hmap hself point).mp hpoint.1)⟩
  exact (problem.localDegree_eq_of_solutionsIn_eq _ _
    (isIsolating_of_selfMap_preimage lower upper hwidth map hmap hself
      region hopen hfixed) (by simp [IsIsolating]) hequal).trans
        problem.localDegree_univ_eq_one

end Math.BoxComplementarityProblem
