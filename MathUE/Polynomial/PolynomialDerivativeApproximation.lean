import MathUE.Polynomial.TensorBernsteinDerivativeConvergence
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! # Affine transport of simultaneous polynomial derivative approximation -/

noncomputable section

namespace Math

open Set
open scoped BigOperators

variable {dimension : ℕ}

/-- Substitution by a scalar affine map remains an actual multivariate polynomial. -/
def mvPolynomialAffineSubstitution (polynomial : MvPolynomial (Fin dimension) ℝ)
    (scale : ℝ) (shift : Fin dimension → ℝ) : MvPolynomial (Fin dimension) ℝ :=
  polynomial.eval₂ MvPolynomial.C
    (fun coordinate ↦ MvPolynomial.C scale * MvPolynomial.X coordinate +
      MvPolynomial.C (shift coordinate))

theorem eval_mvPolynomialAffineSubstitution (polynomial : MvPolynomial (Fin dimension) ℝ)
    (scale : ℝ) (shift point : Fin dimension → ℝ) :
    MvPolynomial.eval point (mvPolynomialAffineSubstitution polynomial scale shift) =
      MvPolynomial.eval (scale • point + shift) polynomial := by
  rw [mvPolynomialAffineSubstitution, ← MvPolynomial.eval_assoc]
  apply congrArg (fun input : Fin dimension → ℝ ↦ MvPolynomial.eval input polynomial)
  ext coordinate
  simp [Pi.smul_apply, smul_eq_mul]

theorem hasFDerivAt_scalarAffine (scale : ℝ) (shift point : Fin dimension → ℝ) :
    HasFDerivAt (fun input ↦ scale • input + shift)
      (scale • ContinuousLinearMap.id ℝ (Fin dimension → ℝ)) point :=
  ((hasFDerivAt_id point).const_smul scale).add_const shift

theorem fderiv_mvPolynomialAffineSubstitution
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (scale : ℝ) (shift point : Fin dimension → ℝ) :
    fderiv ℝ (fun input ↦
      MvPolynomial.eval input (mvPolynomialAffineSubstitution polynomial scale shift)) point =
      scale • fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial)
        (scale • point + shift) := by
  have hfunction : (fun input ↦
      MvPolynomial.eval input (mvPolynomialAffineSubstitution polynomial scale shift)) =
      (fun input ↦ MvPolynomial.eval (scale • input + shift) polynomial) := by
    funext input
    exact eval_mvPolynomialAffineSubstitution polynomial scale shift input
  rw [hfunction]
  have hchain := (((contDiff_eval_mvPolynomial polynomial 1).differentiable_one
    (scale • point + shift)).hasFDerivAt).comp point
      (hasFDerivAt_scalarAffine scale shift point)
  simpa [Function.comp_def] using! hchain.fderiv

/-- Affine transport needs actual differentiability only on the transported unit cube. -/
theorem exists_mvPolynomial_fderiv_close_on_affineUnitCube
    (function : (Fin dimension → ℝ) → ℝ)
    (derivative : (Fin dimension → ℝ) → ((Fin dimension → ℝ) →L[ℝ] ℝ))
    (scale : ℝ) (shift : Fin dimension → ℝ) (hscale : 0 < scale)
    (hderivative : ∀ point ∈ (fun input ↦ scale • input + shift) '' realUnitCube dimension,
      HasFDerivAt function (derivative point) point)
    (hcontinuous : ContinuousOn derivative
      ((fun input ↦ scale • input + shift) '' realUnitCube dimension))
    {error : ℝ} (herror : 0 < error) :
    ∃ polynomial : MvPolynomial (Fin dimension) ℝ,
      ∀ point ∈ (fun input ↦ scale • input + shift) '' realUnitCube dimension,
        ‖fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point - derivative point‖ <
          error := by
  let affine := fun input : Fin dimension → ℝ ↦ scale • input + shift
  let transformed := fun input ↦ function (affine input)
  let transformedDerivative := fun input ↦ scale • derivative (affine input)
  have htransformed : ∀ point ∈ realUnitCube dimension,
      HasFDerivAt transformed (transformedDerivative point) point := by
    intro point hpoint
    simpa [transformed, transformedDerivative, affine, Function.comp_def] using!
      (hderivative (affine point) ⟨point, hpoint, rfl⟩).comp point
        (hasFDerivAt_scalarAffine scale shift point)
  have htransformedContinuous : ContinuousOn transformedDerivative (realUnitCube dimension) :=
    (hcontinuous.comp ((continuous_id.const_smul scale).add continuous_const).continuousOn
      (fun point hpoint ↦ ⟨point, hpoint, rfl⟩)).const_smul scale
  obtain ⟨polynomial, hpolynomial⟩ := exists_mvPolynomial_fderiv_close_on_unitCube
    transformed transformedDerivative htransformed htransformedContinuous (mul_pos hscale herror)
  refine ⟨mvPolynomialAffineSubstitution polynomial scale⁻¹ (-scale⁻¹ • shift), ?_⟩
  rintro _ ⟨point, hpoint, rfl⟩
  have hinverse : scale⁻¹ • (scale • point + shift) + -scale⁻¹ • shift = point := by
    ext coordinate
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [fderiv_mvPolynomialAffineSubstitution, hinverse]
  have heq : scale⁻¹ • fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point -
      derivative (scale • point + shift) =
      scale⁻¹ • (fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point -
        transformedDerivative point) := by
    simp [smul_sub, transformedDerivative, affine, smul_smul, hscale.ne']
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
  calc
    _ < scale⁻¹ * (scale * error) :=
      mul_lt_mul_of_pos_left (hpolynomial point hpoint).2 (inv_pos.mpr hscale)
    _ = error := by field_simp

/-- Global C¹ functions admit simultaneous polynomial derivative approximation on any bounded
set. The set may be empty and need not be closed, and the dimension may be zero. -/
theorem exists_mvPolynomial_fderiv_close_on_bounded
    (function : (Fin dimension → ℝ) → ℝ) (hsmooth : ContDiff ℝ 1 function)
    (domain : Set (Fin dimension → ℝ)) (hbounded : Bornology.IsBounded domain)
    {error : ℝ} (herror : 0 < error) :
    ∃ polynomial : MvPolynomial (Fin dimension) ℝ, ∀ point ∈ domain,
      (∑ coordinate, |fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
        (Pi.single coordinate 1) - fderiv ℝ function point (Pi.single coordinate 1)|) < error ∧
      ‖fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point -
        fderiv ℝ function point‖ < error := by
  obtain ⟨radius, hradius, hbound⟩ := hbounded.exists_pos_norm_le
  have hscaled : 0 < error / (dimension + 1 : ℝ) := div_pos herror (by positivity)
  obtain ⟨polynomial, hpolynomial⟩ := exists_mvPolynomial_fderiv_close_on_affineUnitCube
    function (fderiv ℝ function) (2 * radius) (fun _ ↦ -radius) (by positivity)
    (fun point _ ↦ (hsmooth.differentiable_one point).hasFDerivAt)
    (hsmooth.continuous_fderiv (by norm_num)).continuousOn hscaled
  refine ⟨polynomial, ?_⟩
  intro point hpoint
  have hnorm := hbound point hpoint
  have hmember : point ∈
      (fun input : Fin dimension → ℝ ↦ (2 * radius) • input + (fun _ ↦ -radius)) ''
        realUnitCube dimension := by
    refine ⟨fun coordinate ↦ (point coordinate + radius) / (2 * radius), ?_, ?_⟩
    · intro coordinate
      have hcoordinate := (norm_le_pi_norm point coordinate).trans hnorm
      rw [Real.norm_eq_abs, abs_le] at hcoordinate
      exact ⟨div_nonneg (by linarith) (by positivity),
        (div_le_one (by positivity)).mpr (by linarith)⟩
    · ext coordinate
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have hsmall := hpolynomial point hmember
  let difference := fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point -
    fderiv ℝ function point
  have hsum : (∑ coordinate,
      |fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
        (Pi.single coordinate 1) - fderiv ℝ function point (Pi.single coordinate 1)|) ≤
      (dimension : ℝ) * ‖difference‖ := by
    calc
      _ ≤ ∑ _coordinate : Fin dimension, ‖difference‖ :=
        Finset.sum_le_sum fun coordinate _ ↦ by
          simpa only [dist_eq_norm] using abs_apply_single_sub_le_dist
            (fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point)
            (fderiv ℝ function point) coordinate
      _ = _ := by simp
  have hscaledSmall : (dimension + 1 : ℝ) * ‖difference‖ < error :=
    (mul_comm _ _).trans_lt ((lt_div_iff₀ (by positivity)).mp hsmall)
  constructor
  · exact hsum.trans_lt (by nlinarith [norm_nonneg difference])
  · change ‖difference‖ < error
    nlinarith [norm_nonneg difference, Nat.cast_nonneg (α := ℝ) dimension]

/-- Arbitrary real coordinate boxes, including reversed or degenerate intervals, require no
rationality or strict-width assumptions. -/
theorem exists_mvPolynomial_fderiv_close_on_box
    (function : (Fin dimension → ℝ) → ℝ) (hsmooth : ContDiff ℝ 1 function)
    (lower upper : Fin dimension → ℝ) {error : ℝ} (herror : 0 < error) :
    ∃ polynomial : MvPolynomial (Fin dimension) ℝ, ∀ point ∈ Icc lower upper,
      (∑ coordinate, |fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
        (Pi.single coordinate 1) - fderiv ℝ function point (Pi.single coordinate 1)|) < error ∧
      ‖fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point -
        fderiv ℝ function point‖ < error :=
  exists_mvPolynomial_fderiv_close_on_bounded function hsmooth (Icc lower upper)
    isCompact_Icc.isBounded herror

end Math
