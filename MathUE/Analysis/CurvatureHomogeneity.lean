import MathUE.Analysis.CoordinateHessianExtrema
import Mathlib.Basic.Real.Pointwise

/-! # Positive scaling of actual Hessians and spectral extrema

These are homogeneity identities, not a new curvature or spectral argument.
Derivative scaling is canonical even at nondifferentiability points. Positive
scaling commutes with the actual real infima, including empty sets.
-/

noncomputable section

namespace Math

open Set

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem realHessian_const_mul (coefficient : ℝ) (potential : E → ℝ) (point : E) :
    realHessian (fun input => coefficient * potential input) point =
      coefficient • realHessian potential point := by
  have hfirst : fderiv ℝ (fun input => coefficient * potential input) =
      coefficient • fderiv ℝ potential :=
    fderiv_const_smul_field (𝕜 := ℝ) (f := potential) coefficient
  have hsecond := congrFun (fderiv_const_smul_field (𝕜 := ℝ)
    (f := fderiv ℝ potential) coefficient) point
  ext first
  apply ext_inner_right ℝ
  intro second
  simp only [smul_apply, inner_smul_left, RCLike.conj_to_real,
    realHessian_inner, hfirst, hsecond, Pi.smul_apply, smul_eq_mul]

theorem leastHessianEigenvalue_const_mul {coefficient : ℝ}
    (hcoefficient : 0 ≤ coefficient) (potential : E → ℝ) (point : E) :
    leastHessianEigenvalue (fun input => coefficient * potential input) point =
      coefficient * leastHessianEigenvalue potential point := by
  unfold leastHessianEigenvalue
  rw [realHessian_const_mul, Real.mul_iInf_of_nonneg hcoefficient]
  apply congrArg iInf
  funext direction
  simp only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, smul_apply,
    inner_smul_left, RCLike.conj_to_real, RCLike.re_to_real]
  ring

end Euclidean

section CoordinateSpectrum

variable {ι : Type*} [Fintype ι]

theorem coordinateLeastHessianEigenvalue_const_mul {coefficient : ℝ}
    (hcoefficient : 0 ≤ coefficient) (potential : (ι → ℝ) → ℝ) (point : ι → ℝ) :
    coordinateLeastHessianEigenvalue (fun input => coefficient * potential input) point =
      coefficient * coordinateLeastHessianEigenvalue potential point := by
  exact leastHessianEigenvalue_const_mul hcoefficient
    (potential ∘ EuclideanSpace.equiv ι ℝ) ((EuclideanSpace.equiv ι ℝ).symm point)

theorem coordinateMinimumHessianEigenvalue_const_mul {coefficient : ℝ}
    (hcoefficient : 0 ≤ coefficient) (potential : (ι → ℝ) → ℝ)
    (box : Set (ι → ℝ)) :
    coordinateMinimumHessianEigenvalue (fun input => coefficient * potential input) box =
      coefficient * coordinateMinimumHessianEigenvalue potential box := by
  unfold coordinateMinimumHessianEigenvalue
  simp_rw [coordinateLeastHessianEigenvalue_const_mul hcoefficient]
  exact (Real.mul_iInf_of_nonneg hcoefficient _).symm

end CoordinateSpectrum

end Math
