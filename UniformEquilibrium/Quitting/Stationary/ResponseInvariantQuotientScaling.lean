import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientLocalMin
import MathUE.LinearProgramming.R0Degree

/-!
# Signed ambient scaling of the stationary-response quotient

The literal quotient response has the raw block matrix as its derivative.
This gives uniform first-order control on fixed bounded signed coordinate
sets, without interpreting a block as a smaller quitting game.
-/

noncomputable section

namespace GameTheory

open Set Filter Math.LinearProgramming
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- Uniform signed scaling of the exact quotient response to its raw row-sum
matrix. No probability-cube restriction is imposed on the scaled points. -/
theorem quittingQuotientResponse_scaled_uniform_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    {domain : Set (Fin k → ℝ)} (hbounded : Bornology.IsBounded domain)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ δ > 0, ∀ scalar : ℝ, 0 < scalar → scalar ≤ δ →
      ∀ point ∈ domain,
        ‖(fun coordinate => -quittingQuotientResponse reward block representative
            (scalar • point) coordinate / scalar) -
          (quittingResponseQuotientMatrix reward block representative).mulVec point‖ <
          tolerance := by
  let response := quittingQuotientResponse reward block representative
  have hsource :=
    hasFDerivAt_quittingQuotientResponse_zero reward block representative
  let linear := fderiv ℝ response 0
  have hderiv : HasFDerivAt response linear 0 := by
    dsimp only [linear]
    rw [hsource.fderiv]
    exact hsource
  have hlinear (point : Fin k → ℝ) :
      linear point =
        -(quittingResponseQuotientMatrix reward block representative).mulVec point := by
    rw [show linear = _ from hsource.fderiv]
    exact quittingQuotientResponse_derivative_apply reward block representative point
  have hzero : response 0 = 0 :=
    quittingQuotientResponse_zero reward block representative
  obtain ⟨B, hB, hnorm⟩ := hbounded.exists_pos_norm_le
  have hB1 : 0 < 1 + B := by positivity
  have hsmall := hderiv.isLittleO.bound
    (show 0 < tolerance / (2 * (1 + B)) by positivity)
  simp only [hzero, sub_zero] at hsmall
  obtain ⟨radius, hradius, hlocal⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨radius / (2 * (1 + B)), by positivity, ?_⟩
  intro scalar hscalar hscalar_le point hpoint
  have hpointNorm : ‖scalar • point‖ ≤ scalar * (1 + B) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscalar]
    exact (mul_le_mul_of_nonneg_left (hnorm point hpoint) hscalar.le).trans
      (by nlinarith)
  have hnear : dist (scalar • point) 0 < radius := by
    rw [dist_zero_right]
    have := (le_div_iff₀ (show 0 < 2 * (1 + B) by positivity)).mp hscalar_le
    nlinarith
  have herror := hlocal hnear
  have herror' : ‖response (scalar • point) - linear (scalar • point)‖ ≤
      (tolerance / 2) * scalar := by
    calc
      _ ≤ (tolerance / (2 * (1 + B))) * ‖scalar • point‖ := herror
      _ ≤ (tolerance / (2 * (1 + B))) * (scalar * (1 + B)) :=
        mul_le_mul_of_nonneg_left hpointNorm (by positivity)
      _ = (tolerance / 2) * scalar := by field_simp [ne_of_gt hB1]
  have heq :
      (fun coordinate => -response (scalar • point) coordinate / scalar) -
        (quittingResponseQuotientMatrix reward block representative).mulVec point =
      (-scalar⁻¹) • (response (scalar • point) - linear (scalar • point)) := by
    rw [linear.map_smul, hlinear]
    funext coordinate
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    field_simp [ne_of_gt hscalar]
    ring
  rw [heq, norm_smul, norm_neg, norm_inv, Real.norm_eq_abs, abs_of_pos hscalar]
  calc
    scalar⁻¹ * ‖response (scalar • point) - linear (scalar • point)‖ ≤
        scalar⁻¹ * ((tolerance / 2) * scalar) :=
      mul_le_mul_of_nonneg_left herror' (inv_nonneg.mpr hscalar.le)
    _ = tolerance / 2 := by field_simp [ne_of_gt hscalar]
    _ < tolerance := by linarith

/-- The locally exact minimum field after positive input and output scaling. -/
def quittingQuotientMinFieldScaled
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (scalar : ℝ) (point : Fin k → ℝ) : Fin k → ℝ :=
  scalar⁻¹ • quittingQuotientMinField reward block representative (scalar • point)

/-- Uniformly on bounded signed sets, the scaled literal minimum field tends
to the homogeneous LCP minimum map of the raw quotient matrix. -/
theorem quittingQuotientMinFieldScaled_uniform_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    {domain : Set (Fin k → ℝ)} (hbounded : Bornology.IsBounded domain)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ δ > 0, ∀ scalar : ℝ, 0 < scalar → scalar ≤ δ →
      ∀ point ∈ domain,
        ‖quittingQuotientMinFieldScaled reward block representative scalar point -
          lcpMinMap (quittingResponseQuotientMatrix reward block representative)
            0 point‖ < tolerance := by
  obtain ⟨δ, hδ, hresponse⟩ := quittingQuotientResponse_scaled_uniform_bound
    reward block representative hbounded htolerance
  refine ⟨δ, hδ, ?_⟩
  intro scalar hscalar hsmall point hpoint
  have hbound := hresponse scalar hscalar hsmall point hpoint
  apply (pi_norm_lt_iff htolerance).mpr
  intro coordinate
  have hcoordinate := (pi_norm_lt_iff htolerance).mp hbound coordinate
  have hscaled :
      quittingQuotientMinFieldScaled reward block representative scalar point coordinate =
        min (point coordinate)
          (-quittingQuotientResponse reward block representative
            (scalar • point) coordinate / scalar) := by
    simp only [quittingQuotientMinFieldScaled, quittingQuotientMinField,
      Pi.smul_apply, smul_eq_mul]
    calc
      scalar⁻¹ * min (scalar * point coordinate)
          (-quittingQuotientResponse reward block representative
            (scalar • point) coordinate) =
          min (scalar * point coordinate)
            (-quittingQuotientResponse reward block representative
              (scalar • point) coordinate) / scalar := by
            simp [div_eq_mul_inv, mul_comm]
      _ = _ := by
        rw [← min_div_div_right hscalar.le]
        simp only [mul_div_cancel_left₀ _ hscalar.ne']
  simp only [Pi.sub_apply, Real.norm_eq_abs, lcpMinMap]
  rw [hscaled]
  change |min (point coordinate)
      (-quittingQuotientResponse reward block representative
        (scalar • point) coordinate / scalar) -
      min (point coordinate)
        (lcpResidual (quittingResponseQuotientMatrix reward block representative)
          0 point coordinate)| < tolerance
  have hmin := abs_min_sub_min_le_max (point coordinate)
    (-quittingQuotientResponse reward block representative
      (scalar • point) coordinate / scalar) (point coordinate)
    (lcpResidual (quittingResponseQuotientMatrix reward block representative)
      0 point coordinate)
  simp only [sub_self, abs_zero] at hmin
  rw [max_eq_right (abs_nonneg _)] at hmin
  have hresidual :
      lcpResidual (quittingResponseQuotientMatrix reward block representative)
        0 point coordinate =
      (quittingResponseQuotientMatrix reward block representative).mulVec point
        coordinate := by
    rw [lcpResidual_eq_add_mulVec]
    simp
  have hcoordinate' :
      |-quittingQuotientResponse reward block representative
        (scalar • point) coordinate / scalar -
        lcpResidual (quittingResponseQuotientMatrix reward block representative)
          0 point coordinate| < tolerance := by
    simpa only [hresidual, Pi.sub_apply, Real.norm_eq_abs] using hcoordinate
  exact hmin.trans_lt hcoordinate'

end GameTheory
