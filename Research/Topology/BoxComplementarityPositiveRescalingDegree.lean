import MathUE.Topology.BoxComplementarityAmbientMapAdapter
import Research.Topology.BoxComplementarityFrontierReplacement

/-!
# Positive rescaling of normalized complementarity degree

Positive scalar multiplication preserves the actual grid labels. The degree
corollary reuses the existing straight-line common-isolating homotopy theorem.
-/

noncomputable section

namespace Math

open Set

variable {n : ℕ}

/-- Positive gain scaling preserves the actual grid violation predicate. -/
theorem BoxComplementarityProblem.isGridViolation_scaleGain_iff
    (problem : BoxComplementarityProblem (Fin n)) {scalar : ℝ} (hscalar : 0 < scalar)
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) (who : Fin n) :
    (problem.scaleGain scalar).IsGridViolation p vertex who ↔
      problem.IsGridViolation p vertex who := by
  have hnegative (value : ℝ) : scalar * value < 0 ↔ value < 0 := by
    simpa only [mul_zero] using
      (mul_lt_mul_iff_right₀ hscalar : scalar * value < scalar * 0 ↔ value < 0)
  simp only [IsGridViolation, scaleGain, hnegative]

/-- Every literal reduced grid label is unchanged by positive gain scaling. -/
theorem boxComplementarityReducedLabel_scaleGain
    (problem : BoxComplementarityProblem (Fin n)) {scalar : ℝ} (hscalar : 0 < scalar)
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) :
    boxComplementarityReducedLabel (problem.scaleGain scalar) p vertex =
      boxComplementarityReducedLabel problem p vertex := by
  have hset : boxComplementarityGridViolationSet (problem.scaleGain scalar) p vertex =
      boxComplementarityGridViolationSet problem p vertex := by
    ext who
    simp only [boxComplementarityGridViolationSet, Finset.mem_filter,
      Finset.mem_univ, true_and, problem.isGridViolation_scaleGain_iff hscalar]
  simp only [boxComplementarityReducedLabel, hset]

/-- The straight interpolation to a rescaled gain has its displayed scalar coefficient. -/
theorem BoxComplementarityProblem.straightLine_scaleGain
    (problem : BoxComplementarityProblem (Fin n)) (scalar : ℝ)
    (parameter : Set.Icc (0 : ℝ) 1) :
    problem.straightLine (problem.scaleGain scalar) parameter =
      problem.scaleGain (1 - (parameter : ℝ) + (parameter : ℝ) * scalar) := by
  have hgain :
      (problem.straightLine (problem.scaleGain scalar) parameter).gain =
        (problem.scaleGain (1 - (parameter : ℝ) + (parameter : ℝ) * scalar)).gain := by
    funext point who
    dsimp [straightLine, scaleGain]
    ring
  exact BoxComplementarityProblem.ext hgain

/-- Positive gain rescaling preserves normalized degree on every isolating region. -/
theorem BoxComplementarityProblem.localDegree_scaleGain
    (problem : BoxComplementarityProblem (Fin n)) {scalar : ℝ} (hscalar : 0 < scalar)
    (region : Set (UnitCube (Fin n))) (hisolating : problem.IsIsolating region) :
    (problem.scaleGain scalar).localDegree region
        ((problem.isIsolating_scaleGain_iff hscalar region).mpr hisolating) =
      problem.localDegree region hisolating := by
  have hisolatingFamily (parameter : Set.Icc (0 : ℝ) 1) :
      (problem.straightLine (problem.scaleGain scalar) parameter).IsIsolating region := by
    rw [problem.straightLine_scaleGain]
    have hpositive : 0 < 1 - (parameter : ℝ) + (parameter : ℝ) * scalar := by
      by_cases hzero : (parameter : ℝ) = 0
      · simp [hzero]
      · have hparameter : 0 < (parameter : ℝ) :=
          lt_of_le_of_ne parameter.property.1 (Ne.symm hzero)
        exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr parameter.property.2)
          (mul_pos hparameter hscalar)
    exact (problem.isIsolating_scaleGain_iff hpositive region).mpr hisolating
  have hcontinuous := problem.isContinuous_straightLine (problem.scaleGain scalar)
  have hdegree := hcontinuous.localDegree_endpoints_eq region hisolatingFamily
  simpa only [straightLine_zero, straightLine_one] using hdegree.symm

open Topology in
/-- The actual normalized pullback degrees agree under positive ambient dilation,
inverse field scaling, and the displayed transformed chart and region. -/
theorem BoxComplementarityProblem.localDegree_ofAmbientMap_dilation
    (shift : Fin n → ℝ) {scalar : ℝ} (hscalar : 0 < scalar)
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (hfield : ContinuousOn field
      (Icc (positiveDilation shift scalar lower) (positiveDilation shift scalar upper)))
    (region : Set (Fin n → ℝ))
    (hisolating : (ofAmbientMap (positiveDilation shift scalar lower)
      (positiveDilation shift scalar upper) (positiveDilation_width shift hscalar hwidth)
      field hfield).IsIsolating
        (rectangularCubePoint (positiveDilation shift scalar lower)
          (positiveDilation shift scalar upper) ⁻¹' region)) :
    (ofAmbientMap lower upper hwidth (dilatedAmbientField shift scalar field)
      (continuousOn_dilatedAmbientField shift hscalar lower upper field hfield)).localDegree
        (rectangularCubePoint lower upper ⁻¹' (positiveDilation shift scalar ⁻¹' region))
        ((isIsolating_ofAmbientMap_dilation_iff shift hscalar lower upper hwidth field hfield
          region).mpr hisolating) =
      (ofAmbientMap (positiveDilation shift scalar lower) (positiveDilation shift scalar upper)
        (positiveDilation_width shift hscalar hwidth) field hfield).localDegree
        (rectangularCubePoint (positiveDilation shift scalar lower)
          (positiveDilation shift scalar upper) ⁻¹' region) hisolating := by
  simpa only [ofAmbientMap_dilatedAmbientField shift hscalar lower upper hwidth field hfield,
    ← rectangularCubePoint_preimage_positiveDilation] using
    localDegree_scaleGain _ (inv_pos.mpr hscalar) _ hisolating

end Math
