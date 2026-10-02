import MathUE.Analysis.PositiveFaceCurvatureBudget
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Literal finite-coordinate Euclidean Hessian extrema and convexification -/

noncomputable section

namespace Math

open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The actual Hessian in the standard Euclidean geometry on coordinates.
The function is transported by the canonical coordinate equivalence only. -/
def coordinateHessian (potential : (ι → ℝ) → ℝ) (point : ι → ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  realHessian (potential ∘ EuclideanSpace.equiv ι ℝ) ((EuclideanSpace.equiv ι ℝ).symm point)

def coordinateLeastHessianEigenvalue (potential : (ι → ℝ) → ℝ) (point : ι → ℝ) : ℝ :=
  leastHessianEigenvalue (potential ∘ EuclideanSpace.equiv ι ℝ)
    ((EuclideanSpace.equiv ι ℝ).symm point)

def coordinateMinimumHessianEigenvalue
    (potential : (ι → ℝ) → ℝ) (box : Set (ι → ℝ)) : ℝ :=
  ⨅ point : box, coordinateLeastHessianEigenvalue potential point

omit [DecidableEq ι] in
/-- Compactness produces the literal minimum of the actual least Hessian
eigenvalue over the original coordinate set, with its eigenvalue property. -/
theorem exists_coordinateMinimumHessianEigenvalue
    (potential : (ι → ℝ) → ℝ) (box domain : Set (ι → ℝ))
    (hcompact : IsCompact box) (hnonempty : box.Nonempty)
    (hopen : IsOpen domain) (hbox : box ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain) :
    ∃ point ∈ box,
      IsMinOn (coordinateLeastHessianEigenvalue potential) box point ∧
      coordinateMinimumHessianEigenvalue potential box =
        coordinateLeastHessianEigenvalue potential point ∧
      Module.End.HasEigenvalue (coordinateHessian potential point).toLinearMap
        (coordinateLeastHessianEigenvalue potential point) ∧
      ∀ other ∈ box, ∀ direction : EuclideanSpace ℝ ι,
        coordinateLeastHessianEigenvalue potential point * ‖direction‖ ^ 2 ≤
          fderiv ℝ (fderiv ℝ (potential ∘ EuclideanSpace.equiv ι ℝ))
            ((EuclideanSpace.equiv ι ℝ).symm other) direction direction := by
  let equiv := EuclideanSpace.equiv ι ℝ
  have hprecompact : IsCompact (equiv ⁻¹' box) :=
    equiv.toHomeomorph.isCompact_preimage.mpr hcompact
  have hprenonempty : (equiv ⁻¹' box).Nonempty := by
    obtain ⟨point, hpoint⟩ := hnonempty
    exact ⟨equiv.symm point, by simpa using hpoint⟩
  have hpreopen : IsOpen (equiv ⁻¹' domain) := hopen.preimage equiv.continuous
  have hpresmooth := hsmooth.comp_continuousLinearMap equiv.toContinuousLinearMap
  obtain ⟨point, hpoint, hmin, _, heigenvalue, hfloor⟩ :=
    exists_minimumHessianEigenvalue (potential ∘ equiv) (equiv ⁻¹' box)
      (equiv ⁻¹' domain) hprecompact hprenonempty hpreopen
      (fun _ hx => hbox hx) hpresmooth
  have hcoordinateMin : IsMinOn (coordinateLeastHessianEigenvalue potential) box
      (equiv point) := by
    intro other hother
    change coordinateLeastHessianEigenvalue potential (equiv point) ≤
      coordinateLeastHessianEigenvalue potential other
    have hcomparison := hmin (show equiv.symm other ∈ equiv ⁻¹' box by simpa using hother)
    change leastHessianEigenvalue (potential ∘ equiv) point ≤
      leastHessianEigenvalue (potential ∘ equiv) (equiv.symm other) at hcomparison
    simpa only [coordinateLeastHessianEigenvalue, equiv,
      ContinuousLinearEquiv.symm_apply_apply] using hcomparison
  refine ⟨equiv point, hpoint, hcoordinateMin,
    IsMinOn.iInf_eq hpoint hcoordinateMin, ?_, ?_⟩
  · simpa only [coordinateHessian, coordinateLeastHessianEigenvalue, equiv,
      ContinuousLinearEquiv.symm_apply_apply] using! heigenvalue
  · intro other hother direction
    simpa only [coordinateLeastHessianEigenvalue, equiv,
      ContinuousLinearEquiv.symm_apply_apply] using
      hfloor (equiv.symm other) (by simpa using hother) direction

omit [Nonempty ι] [DecidableEq ι] in
/-- A local Euclidean Hessian floor implies convexity of the literal
coordinate quadratic correction on box only, through the canonical equivalence. -/
theorem convexOn_add_coordinateShiftedQuadratic_of_hessian_floor
    (potential : (ι → ℝ) → ℝ) (box domain : Set (ι → ℝ))
    (lower : ι → ℝ) (coefficient : ℝ)
    (hconvex : Convex ℝ box) (hopen : IsOpen domain) (hbox : box ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hfloor : ∀ point ∈ box, ∀ direction : EuclideanSpace ℝ ι,
      -(coefficient * ‖direction‖ ^ 2) ≤
        fderiv ℝ (fderiv ℝ (potential ∘ EuclideanSpace.equiv ι ℝ))
          ((EuclideanSpace.equiv ι ℝ).symm point) direction direction) :
    ConvexOn ℝ box
      (fun point => potential point + coordinateShiftedQuadratic lower coefficient point) := by
  let equiv := EuclideanSpace.equiv ι ℝ
  have hpreconvex : Convex ℝ (equiv ⁻¹' box) := hconvex.linear_preimage equiv.toLinearMap
  have hpreopen : IsOpen (equiv ⁻¹' domain) := hopen.preimage equiv.continuous
  have hpresmooth := hsmooth.comp_continuousLinearMap equiv.toContinuousLinearMap
  have hpreFloor : ∀ point ∈ equiv ⁻¹' box, ∀ direction : EuclideanSpace ℝ ι,
      -(coefficient * ‖direction‖ ^ 2) ≤
        fderiv ℝ (fderiv ℝ (potential ∘ equiv)) point direction direction := by
    intro point hpoint direction
    simpa only [equiv, ContinuousLinearEquiv.symm_apply_apply] using
      hfloor (equiv point) hpoint direction
  have hcorrected := convexOn_add_shiftedQuadratic_of_secondFDeriv_floor
    (potential ∘ equiv) (equiv ⁻¹' box) (equiv ⁻¹' domain) (equiv.symm lower) coefficient
    hpreconvex hpreopen (fun _ hx => hbox hx) hpresmooth hpreFloor
  have hpulled := hcorrected.comp_linearMap equiv.symm.toLinearMap
  change ConvexOn ℝ (equiv.symm ⁻¹' (equiv ⁻¹' box))
    ((fun point => (potential ∘ equiv) point +
      shiftedQuadratic (equiv.symm lower) coefficient point) ∘ equiv.symm) at hpulled
  have hpreimage : equiv.symm ⁻¹' (equiv ⁻¹' box) = box := by ext point; simp
  rw [hpreimage] at hpulled
  simpa only [Function.comp_def, coordinateShiftedQuadratic, equiv,
    ContinuousLinearEquiv.apply_symm_apply] using hpulled

end Math
