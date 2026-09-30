import MathUE.Finset.BernoulliAffine
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawSums

/-! # Quitting sums are affine in each opponent hazard -/

noncomputable section

namespace GameTheory

open Math.Finset

variable {ι : Type*} [DecidableEq ι]

variable [Fintype ι]

/-- The existing pure-Quit sum is affine in each opponent hazard. -/
theorem quittingSigmaValue_update_affine
    (weight : Finset ι → ι → ℝ) (hazard : ι → ℝ)
    (recipient coordinate : ι) (hne : coordinate ≠ recipient) (rate : ℝ) :
    sigmaValue weight (Function.update hazard coordinate rate) recipient =
      (1 - rate) * sigmaValue weight (Function.update hazard coordinate 0) recipient +
        rate * sigmaValue weight (Function.update hazard coordinate 1) recipient := by
  unfold sigmaValue
  change (∑ subset ∈ (Finset.univ.erase recipient).powerset,
      bernoulliWeight (Function.update hazard coordinate rate)
        (Finset.univ.erase recipient) subset * weight (insert recipient subset) recipient) = _
  exact bernoulliSum_update_affine hazard (Finset.univ.erase recipient)
    coordinate (by simp [hne]) rate (fun subset => weight (insert recipient subset) recipient)

/-- The existing Continue sum is affine in each opponent hazard. -/
theorem quittingExcludedValue_update_affine
    (weight : Finset ι → ι → ℝ) (hazard : ι → ℝ)
    (recipient coordinate : ι) (hne : coordinate ≠ recipient) (rate : ℝ) :
    excludedValue weight (Function.update hazard coordinate rate) recipient =
      (1 - rate) * excludedValue weight (Function.update hazard coordinate 0) recipient +
        rate * excludedValue weight (Function.update hazard coordinate 1) recipient := by
  unfold excludedValue
  change (∑ subset ∈ (Finset.univ.erase recipient).powerset.erase ∅,
      bernoulliWeight (Function.update hazard coordinate rate)
        (Finset.univ.erase recipient) subset * weight subset recipient) = _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro subset _
  rw [bernoulliWeight_update_affine hazard
    (Finset.univ.erase recipient) subset coordinate (by simp [hne])
    rate]
  simp only [bernoulliWeight]
  ring_nf

end GameTheory
