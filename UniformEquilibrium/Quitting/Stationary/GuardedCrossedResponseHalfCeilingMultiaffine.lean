import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawSums

/-! # Affine dependence of finite Bernoulli coalition sums on one hazard -/

noncomputable section

namespace GameTheory

open Math.Finset

variable {ι : Type*} [DecidableEq ι]

/-- A single coalition mass is affine in any hazard coordinate in its carrier. -/
theorem quittingBernoulliWeight_update_affine
    (hazard : ι → ℝ) (carrier subset : Finset ι) (coordinate : ι)
    (hcoordinate : coordinate ∈ carrier) (rate : ℝ) :
    bernoulliWeight (Function.update hazard coordinate rate) carrier subset =
      (1 - rate) * bernoulliWeight (Function.update hazard coordinate 0) carrier subset +
        rate * bernoulliWeight (Function.update hazard coordinate 1) carrier subset := by
  by_cases hmem : coordinate ∈ subset
  · have hnotComp : coordinate ∉ carrier \ subset := by simp [hmem]
    have hrest (value : ℝ) :
        (∏ other ∈ subset.erase coordinate,
          Function.update hazard coordinate value other) =
          ∏ other ∈ subset.erase coordinate, hazard other := by
      apply Finset.prod_congr rfl
      intro other hother
      exact Function.update_of_ne (Finset.ne_of_mem_erase hother) value hazard
    have hcomp (value : ℝ) :
        (∏ other ∈ carrier \ subset,
          (1 - Function.update hazard coordinate value other)) =
          ∏ other ∈ carrier \ subset, (1 - hazard other) := by
      apply Finset.prod_congr rfl
      intro other hother
      have hne : other ≠ coordinate := by
        intro heq
        subst other
        exact hnotComp hother
      rw [Function.update_of_ne hne value hazard]
    have hformula (value : ℝ) :
        bernoulliWeight (Function.update hazard coordinate value) carrier subset =
          value * (∏ other ∈ subset.erase coordinate, hazard other) *
            (∏ other ∈ carrier \ subset, (1 - hazard other)) := by
      unfold bernoulliWeight
      rw [← Finset.mul_prod_erase subset _ hmem, hrest, hcomp]
      simp
    rw [hformula rate, hformula 0, hformula 1]
    ring
  · have hcompMem : coordinate ∈ carrier \ subset :=
      Finset.mem_sdiff.mpr ⟨hcoordinate, hmem⟩
    have hquit (value : ℝ) :
        (∏ other ∈ subset, Function.update hazard coordinate value other) =
          ∏ other ∈ subset, hazard other := by
      apply Finset.prod_congr rfl
      intro other hother
      have hne : other ≠ coordinate := by
        intro heq
        subst other
        exact hmem hother
      rw [Function.update_of_ne hne value hazard]
    have hrest (value : ℝ) :
        (∏ other ∈ (carrier \ subset).erase coordinate,
          (1 - Function.update hazard coordinate value other)) =
          ∏ other ∈ (carrier \ subset).erase coordinate, (1 - hazard other) := by
      apply Finset.prod_congr rfl
      intro other hother
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hother) value hazard]
    have hformula (value : ℝ) :
        bernoulliWeight (Function.update hazard coordinate value) carrier subset =
          (∏ other ∈ subset, hazard other) *
            ((1 - value) *
              (∏ other ∈ (carrier \ subset).erase coordinate, (1 - hazard other))) := by
      unfold bernoulliWeight
      rw [← Finset.mul_prod_erase (carrier \ subset) _ hcompMem, hquit, hrest]
      simp
    rw [hformula rate, hformula 0, hformula 1]
    ring

/-- An arbitrary finite reward-table coalition expectation is affine in one
independent Bernoulli coordinate. -/
theorem quittingBernoulliSum_update_affine
    (hazard : ι → ℝ) (carrier : Finset ι) (coordinate : ι)
    (hcoordinate : coordinate ∈ carrier) (rate : ℝ)
    (payoff : Finset ι → ℝ) :
    (∑ subset ∈ carrier.powerset,
      bernoulliWeight (Function.update hazard coordinate rate) carrier subset *
        payoff subset) =
      (1 - rate) * (∑ subset ∈ carrier.powerset,
        bernoulliWeight (Function.update hazard coordinate 0) carrier subset *
          payoff subset) +
      rate * (∑ subset ∈ carrier.powerset,
        bernoulliWeight (Function.update hazard coordinate 1) carrier subset *
          payoff subset) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro subset _
  rw [quittingBernoulliWeight_update_affine hazard carrier subset coordinate
    hcoordinate rate]
  ring

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
  exact quittingBernoulliSum_update_affine hazard (Finset.univ.erase recipient)
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
  rw [quittingBernoulliWeight_update_affine hazard
    (Finset.univ.erase recipient) subset coordinate (by simp [hne])
    rate]
  simp only [bernoulliWeight]
  ring_nf

end GameTheory
