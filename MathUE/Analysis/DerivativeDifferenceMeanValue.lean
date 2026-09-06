import Mathlib.Analysis.Calculus.MeanValue

/-! # Endpoint error from actual derivative error -/

namespace Math

variable {space codomain : Type*}
variable [NormedAddCommGroup space] [NormedSpace ℝ space]
variable [NormedAddCommGroup codomain] [NormedSpace ℝ codomain]

/-- A uniform derivative difference controls the difference of endpoint increments on a convex
set. The hypotheses concern actual derivatives, not an independently assigned gradient. -/
theorem norm_increment_sub_increment_le_of_hasFDerivWithinAt
    (first second : space → codomain)
    (firstDerivative secondDerivative : space → space →L[ℝ] codomain)
    (domain : Set space) (hconvex : Convex ℝ domain)
    (hfirst : ∀ point ∈ domain,
      HasFDerivWithinAt first (firstDerivative point) domain point)
    (hsecond : ∀ point ∈ domain,
      HasFDerivWithinAt second (secondDerivative point) domain point)
    (error : ℝ)
    (hclose : ∀ point ∈ domain, ‖firstDerivative point - secondDerivative point‖ ≤ error)
    {source target : space} (hsource : source ∈ domain) (htarget : target ∈ domain) :
    ‖(first source - second source) - (first target - second target)‖ ≤
      error * ‖source - target‖ :=
  hconvex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun point hpoint ↦ (hfirst point hpoint).sub (hsecond point hpoint)) hclose htarget hsource

/-- Whole-space actual derivatives give the same estimate even at boundary points of the set. -/
theorem norm_increment_sub_increment_le_of_fderiv_sub_le
    (first second : space → codomain) (domain : Set space) (hconvex : Convex ℝ domain)
    (hfirst : ∀ point ∈ domain, DifferentiableAt ℝ first point)
    (hsecond : ∀ point ∈ domain, DifferentiableAt ℝ second point)
    (error : ℝ)
    (hclose : ∀ point ∈ domain, ‖fderiv ℝ first point - fderiv ℝ second point‖ ≤ error)
    {source target : space} (hsource : source ∈ domain) (htarget : target ∈ domain) :
    ‖(first source - second source) - (first target - second target)‖ ≤
      error * ‖source - target‖ :=
  norm_increment_sub_increment_le_of_hasFDerivWithinAt first second
    (fderiv ℝ first) (fderiv ℝ second) domain hconvex
    (fun point hpoint ↦ (hfirst point hpoint).hasFDerivAt.hasFDerivWithinAt)
    (fun point hpoint ↦ (hsecond point hpoint).hasFDerivAt.hasFDerivWithinAt)
    error hclose hsource htarget

end Math
