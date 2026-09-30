import MathUE.Finset.PowersetBernoulliWeight

/-! # Affine dependence of finite Bernoulli coalition sums on one hazard -/

noncomputable section

namespace Math.Finset

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R]

/-- A single coalition mass is affine in any hazard coordinate in its carrier. -/
theorem bernoulliWeight_update_affine
    (hazard : ι → R) (carrier subset : Finset ι) (coordinate : ι)
    (hcoordinate : coordinate ∈ carrier) (rate : R) :
    bernoulliWeight (Function.update hazard coordinate rate) carrier subset =
      (1 - rate) * bernoulliWeight (Function.update hazard coordinate 0) carrier subset +
        rate * bernoulliWeight (Function.update hazard coordinate 1) carrier subset := by
  by_cases hmem : coordinate ∈ subset
  · have hnotComp : coordinate ∉ carrier \ subset := by simp [hmem]
    have hrest (value : R) :
        (∏ other ∈ subset.erase coordinate,
          Function.update hazard coordinate value other) =
          ∏ other ∈ subset.erase coordinate, hazard other := by
      apply Finset.prod_congr rfl
      intro other hother
      exact Function.update_of_ne (Finset.ne_of_mem_erase hother) value hazard
    have hcomp (value : R) :
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
    have hformula (value : R) :
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
    have hquit (value : R) :
        (∏ other ∈ subset, Function.update hazard coordinate value other) =
          ∏ other ∈ subset, hazard other := by
      apply Finset.prod_congr rfl
      intro other hother
      have hne : other ≠ coordinate := by
        intro heq
        subst other
        exact hmem hother
      rw [Function.update_of_ne hne value hazard]
    have hrest (value : R) :
        (∏ other ∈ (carrier \ subset).erase coordinate,
          (1 - Function.update hazard coordinate value other)) =
          ∏ other ∈ (carrier \ subset).erase coordinate, (1 - hazard other) := by
      apply Finset.prod_congr rfl
      intro other hother
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hother) value hazard]
    have hformula (value : R) :
        bernoulliWeight (Function.update hazard coordinate value) carrier subset =
          (∏ other ∈ subset, hazard other) *
            ((1 - value) *
              (∏ other ∈ (carrier \ subset).erase coordinate, (1 - hazard other))) := by
      unfold bernoulliWeight
      rw [← Finset.mul_prod_erase (carrier \ subset) _ hcompMem, hquit, hrest]
      simp
    rw [hformula rate, hformula 0, hformula 1]
    ring

/-- An arbitrary finite coefficient-weighted Bernoulli sum is affine in one
independent Bernoulli coordinate. -/
theorem bernoulliSum_update_affine
    (hazard : ι → R) (carrier : Finset ι) (coordinate : ι)
    (hcoordinate : coordinate ∈ carrier) (rate : R)
    (payoff : Finset ι → R) :
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
  rw [bernoulliWeight_update_affine hazard carrier subset coordinate
    hcoordinate rate]
  ring

end Math.Finset
