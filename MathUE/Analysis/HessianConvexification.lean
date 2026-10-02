import MathUE.Analysis.LeastHessianEigenvalue
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Convexity from a local Hessian floor, only on the queried convex set -/

noncomputable section

namespace Math

open Set AffineMap
open scoped RealInnerProductSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Standard segment restriction of the scalar second-derivative convexity
criterion. Nonnegativity outside the closed queried set is not assumed. -/
theorem convexOn_of_secondFDeriv_nonneg
    (potential : E → ℝ) (box domain : Set E) (hconvex : Convex ℝ box)
    (hopen : IsOpen domain) (hbox : box ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hpositive : ∀ point ∈ box, ∀ direction,
      0 ≤ fderiv ℝ (fderiv ℝ potential) point direction direction) :
    ConvexOn ℝ box potential := by
  refine ⟨hconvex, ?_⟩
  intro first hfirst second hsecond left right hleft hright htotal
  let path : ℝ →ᵃ[ℝ] E := lineMap first second
  let direction := second - first
  have hpath : ∀ rate ∈ Icc (0 : ℝ) 1, path rate ∈ box := by
    intro rate hrate
    simpa only [path, lineMap_apply_module] using
      hconvex hfirst hsecond (sub_nonneg.mpr hrate.2) hrate.1 (by ring)
  have hdiff : ∀ rate ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ potential (path rate) := by
    intro rate hrate
    exact (hsmooth.differentiableOn (by norm_num) _
      (hbox (hpath rate hrate))).differentiableAt
      (hopen.mem_nhds (hbox (hpath rate hrate)))
  have hsecondDiff : ∀ rate ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fderiv ℝ potential) (path rate) := by
    intro rate hrate
    exact ((hsmooth.fderiv_of_isOpen hopen (by norm_num)).differentiableOn_one _
      (hbox (hpath rate hrate))).differentiableAt
      (hopen.mem_nhds (hbox (hpath rate hrate)))
  have hfirstDerivative : ∀ rate ∈ Icc (0 : ℝ) 1,
      HasDerivAt (potential ∘ path) (fderiv ℝ potential (path rate) direction) rate := by
    intro rate hrate
    exact (hdiff rate hrate).hasFDerivAt.comp_hasDerivAt rate hasDerivAt_lineMap
  have hsecondDerivative : ∀ rate ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun parameter => fderiv ℝ potential (path parameter) direction)
        (fderiv ℝ (fderiv ℝ potential) (path rate) direction direction) rate := by
    intro rate hrate
    have hpathDerivative : HasDerivAt path direction rate := hasDerivAt_lineMap
    have hderivative : HasDerivAt
        (fun parameter : ℝ => fderiv ℝ potential (path parameter))
        (fderiv ℝ (fderiv ℝ potential) (path rate) direction) rate := by
      simpa only [Function.comp_def] using
        (hsecondDiff rate hrate).hasFDerivAt.comp_hasDerivAt rate hpathDerivative
    have hconstant : HasDerivAt (fun _ : ℝ => direction) (0 : E) rate :=
      hasDerivAt_const rate direction
    simpa only [map_zero, add_zero] using! hderivative.clm_apply hconstant
  have hcontinuous : ContinuousOn (potential ∘ path) (Icc (0 : ℝ) 1) :=
    fun rate hrate => (hfirstDerivative rate hrate).continuousAt.continuousWithinAt
  have hsegment : ConvexOn ℝ (Icc (0 : ℝ) 1) (potential ∘ path) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hcontinuous
      (fun rate hrate => (hfirstDerivative rate (interior_subset hrate)).hasDerivWithinAt)
      (fun rate hrate => (hsecondDerivative rate (interior_subset hrate)).hasDerivWithinAt)
      (fun rate hrate => hpositive _ (hpath rate (interior_subset hrate)) direction)
  have hbound := hsegment.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hleft hright htotal
  have hleftEq : 1 - right = left := by linarith
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, Function.comp_apply,
    path, lineMap_apply_zero, lineMap_apply_one, lineMap_apply_module, hleftEq,
    sub_zero, sub_self, one_smul, zero_smul, add_zero] using hbound

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def shiftedQuadratic (center : E) (coefficient : ℝ) (point : E) : ℝ :=
  (coefficient / 2) * ‖point - center‖ ^ 2

theorem shiftedQuadratic_contDiff (center : E) (coefficient : ℝ) (order : WithTop ℕ∞) :
    ContDiff ℝ order (shiftedQuadratic center coefficient) := by
  have hshift : ContDiff ℝ order (fun input : E => input - center) :=
    (contDiff_id : ContDiff ℝ order (fun input : E => input)).sub contDiff_const
  exact contDiff_const.mul (hshift.norm_sq ℝ)

theorem shiftedQuadratic_hasFDerivAt (center : E) (coefficient : ℝ) (point : E) :
    HasFDerivAt (shiftedQuadratic center coefficient)
      (coefficient • innerSL ℝ (point - center)) point := by
  have hshift : HasFDerivAt (fun input : E => input - center)
      (ContinuousLinearMap.id ℝ E) point := hasFDerivAt_sub_const center
  have hnorm : HasFDerivAt (fun input : E => ‖input - center‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ (point - center)) point := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, two_smul] using
      (hasStrictFDerivAt_norm_sq (point - center)).hasFDerivAt.comp point hshift
  have hscalar : (coefficient / 2) * (2 : ℝ) = coefficient := by ring
  have hscaled := hnorm.const_smul (coefficient / 2)
  change HasFDerivAt (fun input : E => (coefficient / 2) * ‖input - center‖ ^ 2)
    ((coefficient / 2) • ((2 : ℝ) • innerSL ℝ (point - center))) point at hscaled
  rw [smul_smul, hscalar] at hscaled
  exact hscaled

theorem shiftedQuadratic_fderiv (center : E) (coefficient : ℝ) (point : E) :
    fderiv ℝ (shiftedQuadratic center coefficient) point =
      coefficient • innerSL ℝ (point - center) :=
  (shiftedQuadratic_hasFDerivAt center coefficient point).fderiv

theorem shiftedQuadratic_secondFDeriv (center : E) (coefficient : ℝ)
    (point direction : E) :
    fderiv ℝ (fderiv ℝ (shiftedQuadratic center coefficient)) point direction direction =
      coefficient * ‖direction‖ ^ 2 := by
  have hfirst : fderiv ℝ (shiftedQuadratic center coefficient) =
      fun input => coefficient • innerSL ℝ (input - center) :=
    funext (shiftedQuadratic_fderiv center coefficient)
  rw [hfirst]
  have hinner : HasFDerivAt (innerSL ℝ (E := E)) (innerSL ℝ (E := E))
      (point - center) := (innerSL ℝ (E := E)).hasFDerivAt
  have hshift : HasFDerivAt (fun input : E => input - center)
      (ContinuousLinearMap.id ℝ E) point := hasFDerivAt_sub_const center
  have hderivative := hinner.comp point hshift
  have hscaled : HasFDerivAt
      (fun input : E => coefficient • innerSL ℝ (input - center))
      (coefficient • (innerSL ℝ (E := E)).comp (ContinuousLinearMap.id ℝ E)) point := by
    simpa only [Function.comp_def, Pi.smul_apply] using! hderivative.const_smul coefficient
  rw [hscaled.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul,
    real_inner_self_eq_norm_sq]

/-- Convexification uses a Hessian floor only on box. In particular no
global convexity, global PSD, or supplied convexification certificate appears. -/
theorem convexOn_add_shiftedQuadratic_of_secondFDeriv_floor
    (potential : E → ℝ) (box domain : Set E) (center : E) (coefficient : ℝ)
    (hconvex : Convex ℝ box) (hopen : IsOpen domain) (hbox : box ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hfloor : ∀ point ∈ box, ∀ direction,
      -(coefficient * ‖direction‖ ^ 2) ≤
        fderiv ℝ (fderiv ℝ potential) point direction direction) :
    ConvexOn ℝ box (fun point => potential point + shiftedQuadratic center coefficient point) := by
  have hquadratic := shiftedQuadratic_contDiff center coefficient 2
  apply convexOn_of_secondFDeriv_nonneg _ box domain hconvex hopen hbox
    (hsmooth.add hquadratic.contDiffOn)
  intro point hpoint direction
  have hsum := congrArg (fun derivative => derivative ![direction, direction])
    (fun_iteratedFDeriv_add_apply (i := 2)
      (hsmooth.contDiffAt (hopen.mem_nhds (hbox hpoint))) hquadratic.contDiffAt)
  have hsecond : fderiv ℝ (fderiv ℝ
      (fun input => potential input + shiftedQuadratic center coefficient input)) point
        direction direction =
      fderiv ℝ (fderiv ℝ potential) point direction direction +
        coefficient * ‖direction‖ ^ 2 := by
    simpa only [add_apply, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, shiftedQuadratic_secondFDeriv] using hsum
  rw [hsecond]
  linarith [hfloor point hpoint direction]

end InnerProductSpace

end Math
