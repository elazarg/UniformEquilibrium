import MathUE.Analysis.DerivativeDifferenceMeanValue
import MathUE.Interval.RationalPolynomialSmoothDerivativeApproximation

/-! # Rational polynomial drift from a smooth potential and charge-relative displacement -/

noncomputable section

namespace Math.Interval.RationalPolynomial

variable {dimension : ℕ} {edge : Type*}

/-- On a compact convex domain, a supplied actual C¹ drift potential can be replaced by one
rational polynomial whenever every edge displacement is bounded by a fixed multiple of charge.
Derivative approximation is constructed in the proof, uniformly for the entire edge family. -/
theorem exists_evalReal_charge_drift_of_contDiff
    (domain : Set (Fin dimension → ℝ)) (hcompact : IsCompact domain)
    (hconvex : Convex ℝ domain)
    (source target : edge → (Fin dimension → ℝ)) (charge : edge → ℝ)
    (hsource : ∀ step, source step ∈ domain) (htarget : ∀ step, target step ∈ domain)
    (displacementBound : ℝ) (hdisplacementBound : 0 < displacementBound)
    (hdisplacement : ∀ step, ‖source step - target step‖ ≤ displacementBound * charge step)
    (potential : (Fin dimension → ℝ) → ℝ) (hsmooth : ContDiff ℝ 1 potential)
    (hdrift : ∀ step, charge step ≤ potential (source step) - potential (target step)) :
    ∃ expression : RationalPolynomial dimension, ∀ step,
      charge step ≤ evalReal (source step) expression - evalReal (target step) expression := by
  obtain ⟨approximation, happroximation⟩ := exists_evalReal_fderiv_close_of_contDiff_on_compact
    potential hsmooth domain hcompact (show 0 < 1 / (2 * displacementBound) by positivity)
  refine ⟨.constant 2 * approximation, ?_⟩
  intro step
  have herror := Math.norm_increment_sub_increment_le_of_fderiv_sub_le
    (fun point ↦ evalReal point approximation) potential domain hconvex
    (fun point _ ↦ (hasFDerivAt_evalReal approximation point).differentiableAt)
    (fun point _ ↦ hsmooth.differentiable_one point) (1 / (2 * displacementBound))
    (fun point hpoint ↦ (happroximation point hpoint).2.le) (hsource step) (htarget step)
  have hrelative :
      |(evalReal (source step) approximation - potential (source step)) -
        (evalReal (target step) approximation - potential (target step))| ≤ charge step / 2 := by
    calc
      _ ≤ 1 / (2 * displacementBound) * ‖source step - target step‖ := herror
      _ ≤ 1 / (2 * displacementBound) * (displacementBound * charge step) :=
        mul_le_mul_of_nonneg_left (hdisplacement step) (by positivity)
      _ = charge step / 2 := by field_simp
  have hlower := (abs_le.mp hrelative).1
  have hsmoothDrift := hdrift step
  simp only [evalReal_mul, evalReal_constant, Rat.cast_ofNat]
  linarith

end Math.Interval.RationalPolynomial
