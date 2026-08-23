/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.CollisionMass

/-!
# Small-hazard bounds for independent Bernoulli families

This file packages the first-order probability estimates for a finite family
of independent Bernoulli events.  If `q = ∑ i, x i`, then:

* no-event mass differs from `1 - q` by at most `q² / 2`;
* the total loss between the coordinate hazards and the exact singleton
  masses is at most `q²`; and
* the mass of coalitions of cardinality at least two is at most `q² / 2`.

Sharper forms retain the unordered pair sum `pairMulSum x univ`: the no-event
and collision errors are each bounded by one pair sum, while the singleton
shortfall is bounded by twice that sum.  These sharper defects vanish exactly
for a hazard family supported on at most one coordinate.

The collision estimate is `collisionMass_le_sq_sum_div_two`; it is restated
in the combined theorem below so consumers need only one probability packet.
-/

namespace Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact total mass of singleton Bernoulli outcomes. -/
noncomputable def singletonMass (x : ι → ℝ) : ℝ :=
  ∑ i : ι, coalitionMass x {i}

/-- A singleton coalition has its expected elementary product formula. -/
theorem coalitionMass_singleton (x : ι → ℝ) (i : ι) :
    coalitionMass x {i} =
      x i * ∏ j ∈ Finset.univ.erase i, (1 - x j) := by
  have hcompl : ({i} : Finset ι)ᶜ = Finset.univ.erase i := by
    ext j
    simp
  simp [coalitionMass, hcompl]

omit [DecidableEq ι] in
/-- The no-event mass lies above its first-order approximation `1 - ∑ x`. -/
theorem one_sub_sum_le_continueMass (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    1 - ∑ i, x i ≤ continueMass x := by
  have h := Math.one_sub_prod_one_sub_le_sum x Finset.univ
    (fun i _ => h0 i) (fun i _ => h1 i)
  simp only [continueMass] at h ⊢
  linarith

omit [DecidableEq ι] in
/-- The no-event mass exceeds `1 - ∑ x` by at most half the squared total
hazard. -/
theorem continueMass_sub_one_sub_sum_le_sq_sum_div_two (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    continueMass x - (1 - ∑ i, x i) ≤ (∑ i, x i) ^ 2 / 2 := by
  have h := Math.sum_sub_sq_sum_div_two_le_one_sub_prod_one_sub
    x Finset.univ (fun i _ => h0 i) (fun i _ => h1 i)
  simp only [continueMass] at h ⊢
  linarith

omit [DecidableEq ι] in
/-- Sharp no-event remainder bound by the unordered pair sum. -/
theorem continueMass_sub_one_sub_sum_le_pairMulSum (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    continueMass x - (1 - ∑ i, x i) ≤
      Math.pairMulSum x Finset.univ := by
  have h := Math.sum_sub_pairMulSum_le_one_sub_prod_one_sub
    x Finset.univ (fun i _ => h0 i) (fun i _ => h1 i)
  simp only [continueMass] at h ⊢
  linarith

omit [DecidableEq ι] in
/-- Two-sided packaging of the first-order no-event estimate. -/
theorem continueMass_firstOrder_bounds (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    0 ≤ continueMass x - (1 - ∑ i, x i) ∧
      continueMass x - (1 - ∑ i, x i) ≤ (∑ i, x i) ^ 2 / 2 := by
  exact ⟨sub_nonneg.mpr (one_sub_sum_le_continueMass x h0 h1),
    continueMass_sub_one_sub_sum_le_sq_sum_div_two x h0 h1⟩

/-- Every exact singleton mass is at most its coordinate hazard. -/
theorem coalitionMass_singleton_le (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (i : ι) :
    coalitionMass x {i} ≤ x i :=
  coalitionMass_le_coordinate_of_mem x h0 h1 (by simp)

/-- The total coordinate hazard dominates the total exact singleton mass. -/
theorem singletonMass_le_sum (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    singletonMass x ≤ ∑ i, x i := by
  unfold singletonMass
  exact Finset.sum_le_sum fun i _ => coalitionMass_singleton_le x h0 h1 i

/-- Absorption splits exactly into singleton mass and collision mass. -/
theorem singletonMass_add_collisionMass (x : ι → ℝ) :
    singletonMass x + collisionMass x = 1 - continueMass x := by
  rw [collisionMass_eq_one_sub_continueMass_sub_singletonMass]
  simp_rw [← coalitionMass_singleton]
  simp [singletonMass]

/-- The total first-order singleton shortfall is at most the squared total
hazard. -/
theorem sum_sub_singletonMass_le_sq_sum (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    (∑ i, x i) - singletonMass x ≤ (∑ i, x i) ^ 2 := by
  have hno := continueMass_sub_one_sub_sum_le_sq_sum_div_two x h0 h1
  have hcollision := collisionMass_le_sq_sum_div_two x h0 h1
  have hsplit := singletonMass_add_collisionMass x
  nlinarith

/-- Sharp singleton shortfall bound by twice the unordered pair sum. -/
theorem sum_sub_singletonMass_le_two_mul_pairMulSum (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    (∑ i, x i) - singletonMass x ≤
      2 * Math.pairMulSum x Finset.univ := by
  have hno := continueMass_sub_one_sub_sum_le_pairMulSum x h0 h1
  have hcollision := collisionMass_le_pairMulSum x h0 h1
  have hsplit := singletonMass_add_collisionMass x
  linarith

/-- Equivalent order-free form of the sharp singleton shortfall bound. -/
theorem sum_sub_singletonMass_le_sq_sum_sub_sum_sq (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    (∑ i, x i) - singletonMass x ≤
      (∑ i, x i) ^ 2 - ∑ i, x i ^ 2 := by
  have h := sum_sub_singletonMass_le_two_mul_pairMulSum x h0 h1
  rw [Math.pairMulSum_eq] at h
  calc
    (∑ i, x i) - singletonMass x ≤
        2 * (((∑ i, x i) ^ 2 - ∑ i, x i ^ 2) / 2) := by
      simpa only using h
    _ = (∑ i, x i) ^ 2 - ∑ i, x i ^ 2 := by ring

/-- Two-sided packaging of the exact-singleton shortfall estimate. -/
theorem singletonMass_firstOrder_bounds (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    0 ≤ (∑ i, x i) - singletonMass x ∧
      (∑ i, x i) - singletonMass x ≤ (∑ i, x i) ^ 2 := by
  exact ⟨sub_nonneg.mpr (singletonMass_le_sum x h0 h1),
    sum_sub_singletonMass_le_sq_sum x h0 h1⟩

/-- The three elementary first-order product estimates in one packet. -/
theorem smallHazard_probability_bounds (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    (0 ≤ continueMass x - (1 - ∑ i, x i) ∧
      continueMass x - (1 - ∑ i, x i) ≤ (∑ i, x i) ^ 2 / 2) ∧
    (0 ≤ (∑ i, x i) - singletonMass x ∧
      (∑ i, x i) - singletonMass x ≤ (∑ i, x i) ^ 2) ∧
    collisionMass x ≤ (∑ i, x i) ^ 2 / 2 := by
  exact ⟨continueMass_firstOrder_bounds x h0 h1,
    singletonMass_firstOrder_bounds x h0 h1,
    collisionMass_le_sq_sum_div_two x h0 h1⟩

/-- Squared row hazards aggregate below squared total hazard. -/
theorem sum_sq_le_sq_sum {Phase : Type*} [Fintype Phase]
    (q : Phase → ℝ) (hq : ∀ k, 0 ≤ q k) :
    ∑ k, q k ^ 2 ≤ (∑ k, q k) ^ 2 := by
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => hq k

end Math.PMFProduct
