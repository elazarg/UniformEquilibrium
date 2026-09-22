import MathUE.Topology.BoxComplementarityFrontierReplacement

/-!
# Frontier perturbations of actual complementarity degree

An isolating frontier has a uniform gain-perturbation tolerance, even when it
meets cube faces. Compactness separates its gain graph from the closed relation
of complementary point-value pairs. The literal straight-line family stays
inside this tolerance, so the existing homotopy theorem preserves degree.

On coordinate-interior frontiers, a separate quantitative criterion compares
the perturbation norm with the original gain norm. This criterion needs no
compactness choice and is suitable for explicitly rescaled domains. Neither
result assumes finite or regular roots, or imposes conditions away from the
frontier. Empty frontiers and dimension zero are included.
-/

noncomputable section

namespace Math.BoxComplementarityProblem

open Set

variable {n : ℕ}

/-- Interpolating toward a second gain does not enlarge its distance from the first. -/
theorem norm_gain_straightLine_sub_le
    (first second : BoxComplementarityProblem (Fin n))
    (parameter : Icc (0 : ℝ) 1) (point : UnitCube (Fin n)) :
    ‖(first.straightLine second parameter).gain point - first.gain point‖ ≤
      ‖second.gain point - first.gain point‖ := by
  have hequal : (first.straightLine second parameter).gain point - first.gain point =
      (parameter : ℝ) • (second.gain point - first.gain point) := by
    funext who
    dsimp [straightLine]
    ring
  rw [hequal, norm_smul, Real.norm_eq_abs, abs_of_nonneg parameter.property.1]
  exact mul_le_of_le_one_left (norm_nonneg _) parameter.property.2

/-- A compact isolating frontier supplies one gain tolerance valid for every
straight-line parameter. No coordinate-interiority hypothesis is needed. -/
theorem exists_pos_isIsolating_straightLine_of_norm_sub_lt
    (first : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hisolating : first.IsIsolating region) :
    ∃ tolerance : ℝ, 0 < tolerance ∧
      ∀ second : BoxComplementarityProblem (Fin n),
        (∀ point ∈ frontier region,
          ‖second.gain point - first.gain point‖ < tolerance) →
        ∀ parameter, (first.straightLine second parameter).IsIsolating region := by
  let complementary : Set (UnitCube (Fin n) × (Fin n → ℝ)) :=
    ⋂ who : Fin n,
      {pair | 0 ≤ (pair.1 who : ℝ) * pair.2 who} ∩
      {pair | (1 - (pair.1 who : ℝ)) * pair.2 who ≤ 0}
  have hclosed : IsClosed complementary := by
    apply isClosed_iInter
    intro who
    have hcoordinate : Continuous
        (fun pair : UnitCube (Fin n) × (Fin n → ℝ) => (pair.1 who : ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply who).comp continuous_fst)
    have hvalue : Continuous
        (fun pair : UnitCube (Fin n) × (Fin n → ℝ) => pair.2 who) :=
      (continuous_apply who).comp continuous_snd
    exact (isClosed_le continuous_const (hcoordinate.mul hvalue)).inter
      (isClosed_le ((continuous_const.sub hcoordinate).mul hvalue) continuous_const)
  let graph := (fun point => (point, first.gain point)) '' frontier region
  have hcompact : IsCompact graph :=
    (first.isCompact_frontier_and_disjoint_solutionSet region hisolating).1.image
      (continuous_id.prodMk (continuous_pi first.continuous_gain))
  have hsubset : graph ⊆ complementaryᶜ := by
    rintro pair ⟨point, hfrontier, rfl⟩ hpair
    have hsolution : first.IsSolution point :=
      (first.isSolution_iff_mul_gain point).mpr (by
        simpa only [complementary, mem_iInter, mem_inter_iff, mem_ofPred_eq] using hpair)
    have hbad : point ∈ first.solutionSet ∩ frontier region := ⟨hsolution, hfrontier⟩
    rw [hisolating.2] at hbad
    exact hbad
  obtain ⟨tolerance, hpositive, hclear⟩ :=
    hcompact.exists_cthickening_subset_open hclosed.isOpen_compl hsubset
  refine ⟨tolerance, hpositive, ?_⟩
  intro second hclose parameter
  refine ⟨hisolating.1, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hdistance : dist (point, (first.straightLine second parameter).gain point)
      (point, first.gain point) ≤ tolerance := by
    rw [dist_prod_same_left, dist_eq_norm]
    exact ((first.norm_gain_straightLine_sub_le second parameter point).trans_lt
      (hclose point hfrontier)).le
  have hnear : (point, (first.straightLine second parameter).gain point) ∈
      Metric.cthickening tolerance graph :=
    Metric.mem_cthickening_of_dist_le _ _ _ _ ⟨point, hfrontier, rfl⟩ hdistance
  apply hclear hnear
  simpa only [complementary, mem_iInter, mem_inter_iff, mem_ofPred_eq] using
    ((first.straightLine second parameter).isSolution_iff_mul_gain point).mp hsolution

/-- Small enough frontier perturbations derive endpoint isolation and preserve
the actual integer degree, including when the frontier meets cube faces. -/
theorem exists_pos_localDegree_eq_of_norm_sub_lt
    (first : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hisolating : first.IsIsolating region) :
    ∃ tolerance : ℝ, 0 < tolerance ∧
      ∀ second : BoxComplementarityProblem (Fin n),
        (∀ point ∈ frontier region,
          ‖second.gain point - first.gain point‖ < tolerance) →
        ∃ hsecond : second.IsIsolating region,
          first.localDegree region hisolating = second.localDegree region hsecond := by
  obtain ⟨tolerance, hpositive, hstable⟩ :=
    first.exists_pos_isIsolating_straightLine_of_norm_sub_lt region hisolating
  refine ⟨tolerance, hpositive, ?_⟩
  intro second hclose
  have hfamily := hstable second hclose
  have hsecond : second.IsIsolating region := by
    simpa only [straightLine_one] using hfamily 1
  refine ⟨hsecond, ?_⟩
  simpa only [straightLine_zero, straightLine_one] using
    (first.isContinuous_straightLine second).localDegree_endpoints_eq region hfamily

/-- On a coordinate-interior frontier, a perturbation smaller than the original
gain cannot create a straight-line solution. Only the frontier needs to be interior;
even the first endpoint's isolation follows from the displayed strict inequality. -/
theorem isIsolating_straightLine_of_norm_sub_lt_norm
    (first second : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region)
    (hinterior : ∀ point ∈ frontier region,
      ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1)
    (hclose : ∀ point ∈ frontier region,
      ‖second.gain point - first.gain point‖ < ‖first.gain point‖)
    (parameter : Icc (0 : ℝ) 1) :
    (first.straightLine second parameter).IsIsolating region := by
  refine ⟨hopen, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hzero := (isSolution_iff_gain_eq_zero_of_coordinateInterior
    (first.straightLine second parameter) point (hinterior point hfrontier)).mp hsolution
  have hsmall := (first.norm_gain_straightLine_sub_le second parameter point).trans_lt
    (hclose point hfrontier)
  rw [hzero, zero_sub, norm_neg] at hsmall
  exact (lt_irrefl _) hsmall

/-- The explicit relative-norm criterion derives both endpoint isolations and
identifies their degrees. No regularity or finiteness of the roots is assumed. -/
theorem localDegree_eq_of_norm_sub_lt_norm
    (first second : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region)
    (hinterior : ∀ point ∈ frontier region,
      ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1)
    (hclose : ∀ point ∈ frontier region,
      ‖second.gain point - first.gain point‖ < ‖first.gain point‖) :
    ∃ hfirst : first.IsIsolating region, ∃ hsecond : second.IsIsolating region,
      first.localDegree region hfirst = second.localDegree region hsecond := by
  have hfamily := first.isIsolating_straightLine_of_norm_sub_lt_norm second
    region hopen hinterior hclose
  have hfirst : first.IsIsolating region := by
    simpa only [straightLine_zero] using hfamily 0
  have hsecond : second.IsIsolating region := by
    simpa only [straightLine_one] using hfamily 1
  refine ⟨hfirst, hsecond, ?_⟩
  simpa only [straightLine_zero, straightLine_one] using
    (first.isContinuous_straightLine second).localDegree_endpoints_eq region hfamily

end Math.BoxComplementarityProblem
