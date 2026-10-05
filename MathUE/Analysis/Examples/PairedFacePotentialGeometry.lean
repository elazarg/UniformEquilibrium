import MathUE.Analysis.Examples.PairedFacePotential
import MathUE.Analysis.CoordinateHessianEntries
import MathUE.Analysis.CoordinateAffineBoxMinimum
import MathUE.Interval.RationalPolynomialRegularity
import Mathlib.Analysis.Convex.Quasiconvex

/-! # The paired polynomial's canonical Hessian and minimizing vertices

The operator and minimizing vertices are derived from the polynomial.
Neither a spectral certificate nor a minimizer is supplied as input.
-/

noncomputable section

namespace Math.PairedFacePotential

open Set Math.Interval.RationalPolynomial
open scoped BigOperators Matrix

theorem translatedPotential_contDiff : ContDiff ℝ 2 translatedPotential := by
  have hfunction : translatedPotential = (fun input => evalReal input translatedExpression) :=
    funext fun input => (translatedExpression_eval input).symm
  rw [hfunction]
  exact contDiff_evalReal translatedExpression 2

/-- Equality of operators through the canonical coordinate equivalence. -/
theorem translated_coordinateHessian_conjugate (point : Fin 4 → ℝ) :
    (EuclideanSpace.equiv (Fin 4) ℝ).toLinearMap ∘ₗ
      (Math.coordinateHessian translatedPotential point).toLinearMap ∘ₗ
        (EuclideanSpace.equiv (Fin 4) ℝ).symm.toLinearMap = Matrix.toLin' hessianMatrix := by
  simpa only [translated_actual_hessian_entries] using
    Math.coordinateHessian_conjugate_eq_matrix translatedPotential point
      translatedPotential_contDiff

theorem translated_coordinateHessian_hasEigenvalue_iff (point : Fin 4 → ℝ) (value : ℝ) :
    Module.End.HasEigenvalue (Math.coordinateHessian translatedPotential point).toLinearMap value ↔
      value = 96 ∨ value = 32 ∨ value = -64 := by
  rw [Math.coordinateHessian_hasEigenvalue_iff_matrix translatedPotential point
    translatedPotential_contDiff]
  simp only [translated_actual_hessian_entries]
  exact hessian_hasEigenvalue_iff value

/-- Literal least eigenvalue of the actual canonical Riesz Hessian, at every point. -/
theorem translated_coordinateLeastHessianEigenvalue (point : Fin 4 → ℝ) :
    Math.coordinateLeastHessianEigenvalue translatedPotential point = -64 := by
  let equiv := EuclideanSpace.equiv (Fin 4) ℝ
  have hsmooth : ContDiffAt ℝ 2 (translatedPotential ∘ equiv) (equiv.symm point) :=
    (translatedPotential_contDiff.comp_continuousLinearMap
      (g := equiv.toContinuousLinearMap)).contDiffAt
  have heigenvalue : Module.End.HasEigenvalue
      (Math.coordinateHessian translatedPotential point).toLinearMap
      (Math.coordinateLeastHessianEigenvalue translatedPotential point) :=
    Math.leastHessianEigenvalue_hasEigenvalue (translatedPotential ∘ equiv)
      (equiv.symm point) hsmooth
  have hcases := (translated_coordinateHessian_hasEigenvalue_iff point _).mp heigenvalue
  have hnegative : Module.End.HasEigenvalue
      (Math.coordinateHessian translatedPotential point).toLinearMap (-64) :=
    (translated_coordinateHessian_hasEigenvalue_iff point (-64)).mpr (Or.inr (Or.inr rfl))
  have hupper : Math.coordinateLeastHessianEigenvalue translatedPotential point ≤ -64 :=
    Math.leastHessianEigenvalue_le_of_hasEigenvalue (translatedPotential ∘ equiv)
      (equiv.symm point) (-64) hnegative
  rcases hcases with h96 | h32 | hnegativeValue
  · linarith
  · linarith
  · exact hnegativeValue

theorem translated_coordinateMinimumHessianEigenvalue :
    Math.coordinateMinimumHessianEigenvalue translatedPotential (Icc (-3 : Fin 4 → ℝ) 3) =
      -64 := by
  have hzero : (0 : Fin 4 → ℝ) ∈ Icc (-3 : Fin 4 → ℝ) 3 := by
    constructor <;> intro who <;> norm_num
  let : Nonempty (Icc (-3 : Fin 4 → ℝ) 3) := ⟨⟨0, hzero⟩⟩
  simp [Math.coordinateMinimumHessianEigenvalue, translated_coordinateLeastHessianEigenvalue]

/-- Coordinate affinity retains all cross-coordinate terms of the literal expression. -/
theorem translatedPotential_coordinateAffine : Math.IsCoordinateAffine translatedPotential := by
  intro point coordinate
  refine ⟨translatedPotential (Function.update point coordinate 0),
    gradient (fun who => point who - 1 / 4) coordinate, ?_⟩
  intro value
  fin_cases coordinate <;>
    simp [translatedPotential, potential, expression, evalReal, gradient] <;> ring

/-- Singleton-face drift does not imply quasiconvexity, even above the singleton vector. -/
theorem translatedPotential_not_quasiconvexOn_singletonBox :
    ¬ QuasiconvexOn ℝ (Icc (fun _ : Fin 4 => (1 / 4 : ℝ)) 3) translatedPotential := by
  intro hquasiconvex
  have hleft : ![9 / 4, 1 / 4, 1 / 4, 1 / 4] ∈
      Icc (fun _ : Fin 4 => (1 / 4 : ℝ)) 3 := by
    constructor <;> intro coordinate <;> fin_cases coordinate <;> norm_num
  have hright : ![1 / 4, 9 / 4, 1 / 4, 1 / 4] ∈
      Icc (fun _ : Fin 4 => (1 / 4 : ℝ)) 3 := by
    constructor <;> intro coordinate <;> fin_cases coordinate <;> norm_num
  obtain ⟨_, hmax⟩ := quasiconvexOn_iff_le_max.mp hquasiconvex
  have hmiddle := hmax hleft hright
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [translatedPotential, potential, expression, evalReal,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hmiddle

/-- The compact box internally produces a minimizing vertex which is not the top vertex,
and thus has an actual lower-bound coordinate violating the full-root minimum restriction. -/
theorem exists_non_top_minimizing_vertex :
    ∃ vertex ∈ Icc (-3 : Fin 4 → ℝ) 3,
      (∀ coordinate, vertex coordinate = -3 ∨ vertex coordinate = 3) ∧
      IsMinOn translatedPotential (Icc (-3 : Fin 4 → ℝ) 3) vertex ∧
      vertex ≠ ![3, 3, 3, 3] ∧
      ∃ coordinate, vertex coordinate = -3 ∧ vertex coordinate < (1 / 4 : ℝ) := by
  have hnonempty : (Icc (-3 : Fin 4 → ℝ) 3).Nonempty := by
    refine ⟨0, ?_⟩
    constructor <;> intro coordinate <;> norm_num
  obtain ⟨minimum, hminimum, hmin⟩ :=
    (isCompact_Icc : IsCompact (Icc (-3 : Fin 4 → ℝ) 3)).exists_isMinOn hnonempty
      translatedPotential_contDiff.continuous.continuousOn
  obtain ⟨vertex, hvertex, hendpoints, hvertexMin⟩ :=
    translatedPotential_coordinateAffine.exists_vertex_minimum (-3) 3 minimum hminimum hmin
  have hnotTop : vertex ≠ ![3, 3, 3, 3] := by
    intro htop
    exact translatedPotential_top_not_minimum (by simpa [htop] using hvertexMin)
  have hlower : ∃ coordinate, vertex coordinate = -3 := by
    by_contra hnone
    push Not at hnone
    apply hnotTop
    ext coordinate
    rcases hendpoints coordinate with hbottom | htop
    · exact False.elim (hnone coordinate hbottom)
    · fin_cases coordinate <;> exact htop
  obtain ⟨coordinate, hcoordinate⟩ := hlower
  exact ⟨vertex, hvertex, hendpoints, hvertexMin, hnotTop,
    coordinate, hcoordinate, by rw [hcoordinate]; norm_num⟩

end Math.PairedFacePotential
