import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseFaces
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientScaling

/-! # The local minimum field of the crossed response -/

noncomputable section

namespace GameTheory

open Filter Set Math.LinearProgramming
open scoped Topology

variable {n : ℕ}

/-- The exact lower-clip field, retaining the crossed original-game residual. -/
def quittingCrossedMinField
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hazard : Fin n → ℝ) : Fin n → ℝ :=
  fun coordinate => min (hazard coordinate)
    (-quittingCrossedResponse reward first second hazard coordinate)

/-- Positive auxiliary ceilings are inactive near all-Continue, uniformly in
the finitely many coordinates. -/
theorem eventually_quittingCrossed_upperClip_inactive
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height) :
    ∀ᶠ hazard : Fin n → ℝ in 𝓝 0, ∀ coordinate,
      hazard coordinate + quittingCrossedResponse reward first second hazard coordinate <
        quittingCrossedCeiling first second height coordinate := by
  apply Filter.eventually_all.mpr
  intro coordinate
  have hcontinuous : Continuous (fun hazard : Fin n → ℝ =>
      hazard coordinate + quittingCrossedResponse reward first second hazard coordinate) :=
    (continuous_apply coordinate).add
      ((continuous_apply coordinate).comp
        (continuous_quittingCrossedResponse reward first second))
  have hceiling : 0 < quittingCrossedCeiling first second height coordinate := by
    unfold quittingCrossedCeiling
    split_ifs <;> positivity
  have hzero : (fun hazard : Fin n → ℝ =>
      hazard coordinate + quittingCrossedResponse reward first second hazard coordinate)
      0 = 0 := by
    simp [quittingCrossedResponse_zero reward first second]
  exact hcontinuous.continuousAt.eventually
    (isOpen_Iio.mem_nhds (by simpa only [hzero, Set.mem_Iio] using hceiling))

/-- With every upper clip inactive, the crossed fixed-point displacement is
literally `min(q,−PΔ(q))` on the signed ambient chart. -/
theorem quittingCrossedFixedPointField_eq_minField
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height)
    (hazard : Fin n → ℝ)
    (hupper : ∀ coordinate,
      hazard coordinate + quittingCrossedResponse reward first second hazard coordinate ≤
        quittingCrossedCeiling first second height coordinate) :
    quittingCrossedFixedPointField reward first second height hazard =
      quittingCrossedMinField reward first second hazard := by
  funext coordinate
  change hazard coordinate -
    min (quittingCrossedCeiling first second height coordinate)
      (max 0 (hazard coordinate +
        quittingCrossedResponse reward first second hazard coordinate)) =
    min (hazard coordinate)
      (-quittingCrossedResponse reward first second hazard coordinate)
  rw [min_eq_right (max_le (by
    have hceiling : 0 ≤ quittingCrossedCeiling first second height coordinate := by
      unfold quittingCrossedCeiling
      split_ifs <;> linarith
    exact hceiling) (hupper coordinate))]
  by_cases hnonneg : 0 ≤ hazard coordinate +
      quittingCrossedResponse reward first second hazard coordinate
  · rw [max_eq_right hnonneg, min_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge hnonneg), min_eq_left (by linarith)]
    simp

/-- The scaled crossed residual approaches the exact `PΓ` model uniformly
on any bounded signed set; quotient RI is not used. -/
theorem quittingCrossedResponse_scaled_uniform_bound
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n)
    {domain : Set (Fin n → ℝ)} (hbounded : Bornology.IsBounded domain)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ δ > 0, ∀ scalar : ℝ, 0 < scalar → scalar ≤ δ →
      ∀ point ∈ domain,
        ‖(fun coordinate => -quittingCrossedResponse reward first second
            (scalar • point) coordinate / scalar) -
          (quittingCrossedSingletonMatrix reward first second).mulVec point‖ <
          tolerance := by
  have hsource := quittingQuotientResponse_scaled_uniform_bound reward
    (fun coordinate : Fin n => coordinate) (Equiv.swap first second)
    hbounded htolerance
  have hresponse : quittingCrossedResponse reward first second =
      quittingQuotientResponse reward (fun coordinate => coordinate)
        (Equiv.swap first second) := by
    funext hazard coordinate
    rfl
  have hmatrix : quittingCrossedSingletonMatrix reward first second =
      quittingResponseQuotientMatrix reward (fun coordinate => coordinate)
        (Equiv.swap first second) := by
    ext row column
    simp [quittingCrossedSingletonMatrix, quittingResponseQuotientMatrix,
      quittingSingletonBlockRowSum]
  simpa only [hresponse, hmatrix] using hsource

/-- The positive scaling of the crossed minimum field. -/
def quittingCrossedMinFieldScaled
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (scalar : ℝ) (point : Fin n → ℝ) : Fin n → ℝ :=
  scalar⁻¹ • quittingCrossedMinField reward first second (scalar • point)

/-- Uniform approximation of the crossed minimum field by the `PΓ` LCP map. -/
theorem quittingCrossedMinFieldScaled_uniform_bound
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n)
    {domain : Set (Fin n → ℝ)} (hbounded : Bornology.IsBounded domain)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ δ > 0, ∀ scalar : ℝ, 0 < scalar → scalar ≤ δ →
      ∀ point ∈ domain,
        ‖quittingCrossedMinFieldScaled reward first second scalar point -
          lcpMinMap (quittingCrossedSingletonMatrix reward first second) 0 point‖ <
          tolerance := by
  have hsource := quittingQuotientMinFieldScaled_uniform_bound reward
    (fun coordinate : Fin n => coordinate) (Equiv.swap first second)
    hbounded htolerance
  have hmin : quittingCrossedMinField reward first second =
      quittingQuotientMinField reward (fun coordinate => coordinate)
        (Equiv.swap first second) := by
    funext hazard coordinate
    rfl
  have hmatrix : quittingCrossedSingletonMatrix reward first second =
      quittingResponseQuotientMatrix reward (fun coordinate => coordinate)
        (Equiv.swap first second) := by
    ext row column
    simp [quittingCrossedSingletonMatrix, quittingResponseQuotientMatrix,
      quittingSingletonBlockRowSum]
  simpa only [quittingCrossedMinFieldScaled, quittingQuotientMinFieldScaled,
    hmin, hmatrix] using hsource

end GameTheory
