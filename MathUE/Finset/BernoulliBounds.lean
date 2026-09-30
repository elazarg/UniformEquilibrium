import MathUE.Finset.PowersetBernoulliWeight
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-! # Nonnegative Bernoulli weights and nonempty-coalition mass -/

namespace Math.Finset

variable {ι : Type*} [DecidableEq ι]

/-- Independent coalition weights are nonnegative on a bounded hazard carrier. -/
theorem bernoulliWeight_nonneg_of_bounds
    (hazard : ι → ℝ) (carrier subset : Finset ι) (hsubset : subset ⊆ carrier)
    (hbox : ∀ coordinate ∈ carrier, 0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1) :
    0 ≤ bernoulliWeight hazard carrier subset := by
  unfold bernoulliWeight
  exact mul_nonneg
    (Finset.prod_nonneg fun coordinate hcoordinate => (hbox coordinate (hsubset hcoordinate)).1)
    (Finset.prod_nonneg fun coordinate hcoordinate =>
      sub_nonneg.mpr (hbox coordinate (Finset.mem_sdiff.mp hcoordinate).1).2)

/-- Nonempty independent coalitions have exactly the complementary survival mass. -/
theorem sum_bernoulliWeight_erase_empty
    {R : Type*} [CommRing R] (hazard : ι → R) (carrier : Finset ι) :
    (∑ subset ∈ carrier.powerset.erase ∅, bernoulliWeight hazard carrier subset) =
      1 - ∏ coordinate ∈ carrier, (1 - hazard coordinate) := by
  have hsplit := Finset.sum_erase_add carrier.powerset
    (bernoulliWeight hazard carrier) (Finset.empty_mem_powerset carrier)
  have hempty : bernoulliWeight hazard carrier ∅ =
      ∏ coordinate ∈ carrier, (1 - hazard coordinate) := by simp [bernoulliWeight]
  rw [hempty, sum_bernoulliWeight] at hsplit
  exact eq_sub_of_add_eq hsplit

end Math.Finset
