import Research.Topology.BoxComplementaritySignedLocalCount
import Research.Topology.KuhnPrismBoundaryCollar

/-!
# Local signed endpoint equality on the same sufficiently fine mesh

The actual continuous family, common isolating region, mixed-time prism,
parent base selections, and old endpoint anchors are retained throughout.
Uniform collar clearance supplies all selection compatibility hypotheses.
This theorem does not compare different mesh resolutions.
-/

noncomputable section

namespace Math

open Classical Filter Set Topology

variable {n : ℕ}

/-- A cleared actual family-prism collar transports the old local anchor count at that mesh. -/
theorem boxComplementarityLocalSignedCount_sampled_endpoints_eq_of_cleared
    (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) (region : Set (UnitCube (Fin n))) (hopen : IsOpen region)
    (radius : ℝ) (hmesh : 1 / (p : ℝ) ≤ radius)
    (hcleared : ¬HasFamilyPrismFaceVertexIn family
      (Metric.cthickening radius (frontier region)) p) :
    boxComplementarityLocalSignedCount (family (boxComplementarityGridParameter p 0)) p hp region =
      boxComplementarityLocalSignedCount
        (family (boxComplementarityGridParameter p (Fin.last p))) p hp region := by
  let sampled := fun index => family (boxComplementarityGridParameter p index)
  have hagrees (parameter : Fin (p + 1))
      (endpoint : KuhnEndpointLabeledSimplex (sampled parameter) p hp)
      (first second : Fin (n + 1)) :
      boxComplementarityGridPoint p (endpoint.1 first) ∈ region ↔
        boxComplementarityGridPoint p (endpoint.1 second) ∈ region := by
    let equivalence := boxComplementarityDiscretePrismParameterEndEquiv p hp sampled parameter
    let face := equivalence.symm endpoint
    have hfirst := congrFun (congrArg Subtype.val (equivalence.apply_symm_apply endpoint)) first
    have hsecond := congrFun (congrArg Subtype.val (equivalence.apply_symm_apply endpoint)) second
    change Fin.init (face.1.1 first) = endpoint.1 first at hfirst
    change Fin.init (face.1.1 second) = endpoint.1 second at hsecond
    have h := familyPrismFace_vertices_mem_iff_of_cleared family region hopen radius hmesh
      hcleared face.1 first second
    change boxComplementarityGridPoint p (Fin.init (face.1.1 first)) ∈ region ↔
      boxComplementarityGridPoint p (Fin.init (face.1.1 second)) ∈ region at h
    rwa [hfirst, hsecond] at h
  change boxComplementarityLocalSignedCount (sampled 0) p hp region =
    boxComplementarityLocalSignedCount (sampled (Fin.last p)) p hp region
  rw [boxComplementarityLocalSignedCount_eq_endpoint_base_sum _ p hp region (hagrees 0),
    boxComplementarityLocalSignedCount_eq_endpoint_base_sum _ p hp region (hagrees (Fin.last p))]
  have htransport := boxComplementarityDiscretePrism_endpointWeightedSum_eq p hp sampled
    (fun point => if point ∈ region then (1 : ℤ) else 0) (by
      intro cell face hincident
      have h := familyPrismFace_parent_base_mem_iff_vertex_of_cleared family region hopen
        radius hmesh hcleared face cell hincident 0
      exact if_congr h rfl rfl)
  convert htransport using 1 <;> apply Finset.sum_congr rfl <;> intro endpoint _ <;>
    simp only [ite_mul, one_mul, zero_mul] <;> congr 1

/-- The original continuous family's local signed counts agree at its actual endpoints
at every common sufficiently fine positive resolution. Cross-resolution independence is separate. -/
theorem IsContinuousBoxComplementarityFamily.eventually_localSignedCount_endpoints_eq
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family)
    (region : Set (UnitCube (Fin n)))
    (hisolating : ∀ parameter, (family parameter).IsIsolating region) :
    ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
      boxComplementarityLocalSignedCount (family 0) p hp region =
        boxComplementarityLocalSignedCount (family 1) p hp region := by
  obtain ⟨radius, hradius, threshold, hcleared⟩ :=
    hcontinuous.exists_isolatingFrontierCollar_eventually_prismCleared region hisolating
  have hmeshZero : Tendsto (fun p : ℕ => 1 / (p : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨meshThreshold, hmesh⟩ :=
    eventually_atTop.1 (hmeshZero.eventually (eventually_lt_nhds hradius))
  refine ⟨max threshold meshThreshold, ?_⟩
  intro p hpFine hp
  have hzero : boxComplementarityGridParameter p 0 = 0 := by
    apply Subtype.ext
    simp only [boxComplementarityGridParameter, boxComplementarityGridPoint,
      Fin.val_zero, Nat.cast_zero, zero_div, Set.Icc.coe_zero]
  have hone : boxComplementarityGridParameter p (Fin.last p) = 1 := by
    apply Subtype.ext
    simp only [boxComplementarityGridParameter, boxComplementarityGridPoint,
      Fin.val_last, div_self (show (p : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne'), Set.Icc.coe_one]
  have h := boxComplementarityLocalSignedCount_sampled_endpoints_eq_of_cleared family p hp
    region (hisolating 0).1 radius (hmesh p ((le_max_right _ _).trans hpFine)).le
    (hcleared p ((le_max_left _ _).trans hpFine))
  simpa only [hzero, hone] using h

end Math
