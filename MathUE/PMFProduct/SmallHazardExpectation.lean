/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.SmallHazardBounds

/-!
# First-order expansion of finite Bernoulli expectations

This file turns the probability estimates in `SmallHazardBounds` into scalar
expectation estimates.  The continuation value is used when no coordinate
acts; a supplied value is used for every nonempty acting coalition.  Besides
the usual squared-total-hazard remainder, the sharp form retains the exact
unordered pair sum and therefore has zero remainder for a solo-hazard row.
-/

namespace Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The expectation of a continuation value on the empty outcome and a
terminal value on every nonempty Bernoulli coalition. -/
noncomputable def smallHazardExpectation
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ) : ℝ :=
  continueMass x * tail +
    ∑ S ∈ Finset.univ.erase (∅ : Finset ι), coalitionMass x S * terminal S

/-- The exact first-order singleton approximation. -/
noncomputable def smallHazardLinearization
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * (terminal {i} - tail)

/-- A bounded terminal expectation moves away from its tail by at most
absorption probability times the combined bounds. -/
theorem abs_smallHazardExpectation_sub_tail_le_absorption
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ)
    {K R : ℝ}
    (htail : |tail| ≤ K)
    (hterminal : ∀ S, S.Nonempty → |terminal S| ≤ R)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    |smallHazardExpectation terminal tail x - tail| ≤
      (K + R) * (1 - continueMass x) := by
  let nonempty : Finset (Finset ι) := Finset.univ.erase ∅
  have hmass0 : ∀ S, 0 ≤ coalitionMass x S :=
    fun S => coalitionMass_nonneg x h0 h1 S
  have habsorption0 : 0 ≤ 1 - continueMass x := by
    exact sub_nonneg.mpr (continueMass_le_one h0 h1)
  have hterminalSum :
      |∑ S ∈ nonempty, coalitionMass x S * terminal S| ≤
        R * (1 - continueMass x) := by
    calc
      |∑ S ∈ nonempty, coalitionMass x S * terminal S| ≤
          ∑ S ∈ nonempty, |coalitionMass x S * terminal S| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ nonempty, coalitionMass x S * R := by
        exact Finset.sum_le_sum fun S hS => by
          rw [abs_mul, abs_of_nonneg (hmass0 S)]
          apply mul_le_mul_of_nonneg_left _ (hmass0 S)
          apply hterminal S
          exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
      _ = R * (1 - continueMass x) := by
        simp only [nonempty]
        rw [← Finset.sum_mul, sum_coalitionMass_nonempty]
        ring
  have htailTerm : |(continueMass x - 1) * tail| ≤
      K * (1 - continueMass x) := by
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (continueMass_le_one h0 h1))]
    have habs : |tail| * (1 - continueMass x) ≤
        K * (1 - continueMass x) :=
      mul_le_mul_of_nonneg_right htail habsorption0
    simpa [mul_comm] using habs
  unfold smallHazardExpectation
  rw [show continueMass x * tail +
      ∑ S ∈ Finset.univ.erase (∅ : Finset ι), coalitionMass x S * terminal S - tail =
    (continueMass x - 1) * tail +
      ∑ S ∈ Finset.univ.erase (∅ : Finset ι), coalitionMass x S * terminal S by
    ring]
  change |(continueMass x - 1) * tail +
    ∑ S ∈ nonempty, coalitionMass x S * terminal S| ≤ _
  calc
    |_ + _| ≤ |(continueMass x - 1) * tail| +
        |∑ S ∈ nonempty, coalitionMass x S * terminal S| :=
      abs_add_le _ _
    _ ≤ K * (1 - continueMass x) + R * (1 - continueMass x) :=
      add_le_add htailTerm hterminalSum
    _ = (K + R) * (1 - continueMass x) := by ring

/-- The absorption bound weakened by the union bound to total hazard. -/
theorem abs_smallHazardExpectation_sub_tail_le
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ)
    {K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (htail : |tail| ≤ K)
    (hterminal : ∀ S, S.Nonempty → |terminal S| ≤ R)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    |smallHazardExpectation terminal tail x - tail| ≤
      (K + R) * ∑ i, x i := by
  refine (abs_smallHazardExpectation_sub_tail_le_absorption
    terminal tail x htail hterminal h0 h1).trans ?_
  have habsorption : 1 - continueMass x ≤ ∑ i, x i := by
    simpa [continueMass] using
      (Math.one_sub_prod_one_sub_le_sum x Finset.univ
        (fun i _ => h0 i) (fun i _ => h1 i))
  exact mul_le_mul_of_nonneg_left habsorption (add_nonneg hK hR)

/-- Exact decomposition of the nonlinear error into no-event, singleton,
and multiple-event pieces. -/
theorem smallHazardExpectation_sub_tail_sub_linearization_eq
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ) :
    smallHazardExpectation terminal tail x - tail -
        smallHazardLinearization terminal tail x =
      (continueMass x - (1 - ∑ i, x i)) * tail +
      ∑ i, (coalitionMass x {i} - x i) * terminal {i} +
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => 2 ≤ S.card),
        coalitionMass x S * terminal S := by
  let singles : Finset (Finset ι) :=
    Finset.univ.image fun i : ι => ({i} : Finset ι)
  let collisions : Finset (Finset ι) :=
    Finset.univ.filter fun S : Finset ι => 2 ≤ S.card
  have hdisjoint : Disjoint singles collisions := by
    rw [Finset.disjoint_left]
    intro S hS hcollision
    simp only [singles, Finset.mem_image, Finset.mem_univ, true_and] at hS
    obtain ⟨i, rfl⟩ := hS
    simp [collisions] at hcollision
  have hpartition :
      Finset.univ.erase (∅ : Finset ι) = singles ∪ collisions := by
    ext S
    simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union]
    constructor
    · intro hne
      have hpos : 0 < S.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hne.1)
      by_cases hone : S.card = 1
      · left
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
        simp [singles]
      · right
        simp only [collisions, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    · rintro (hsingle | hcollision)
      · simp only [singles, Finset.mem_image, Finset.mem_univ, true_and] at hsingle
        obtain ⟨i, rfl⟩ := hsingle
        simp
      · simp only [collisions, Finset.mem_filter, Finset.mem_univ, true_and]
          at hcollision
        exact ⟨fun hempty => by simp [hempty] at hcollision, trivial⟩
  have hsingleSum :
      ∑ S ∈ singles, coalitionMass x S * terminal S =
        ∑ i, coalitionMass x {i} * terminal {i} := by
    have hinj : Function.Injective (fun i : ι => ({i} : Finset ι)) := by
      intro i j hij
      simpa using hij
    rw [show singles = Finset.univ.image
      (fun i : ι => ({i} : Finset ι)) by rfl, Finset.sum_image hinj.injOn]
  rw [smallHazardExpectation, smallHazardLinearization, hpartition,
    Finset.sum_union hdisjoint, hsingleSum]
  simp only [collisions]
  simp_rw [mul_sub, sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- The Bernoulli expectation has a uniform quadratic remainder after its
singleton linearization. -/
theorem abs_smallHazardExpectation_sub_tail_sub_linearization_le
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ)
    {K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (htail : |tail| ≤ K)
    (hterminal : ∀ S, S.Nonempty → |terminal S| ≤ R)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    |smallHazardExpectation terminal tail x - tail -
        smallHazardLinearization terminal tail x| ≤
      (K / 2 + 3 * R / 2) * (∑ i, x i) ^ 2 := by
  let q := ∑ i, x i
  let collisions : Finset (Finset ι) :=
    Finset.univ.filter fun S : Finset ι => 2 ≤ S.card
  have hmass0 : ∀ S, 0 ≤ coalitionMass x S :=
    fun S => coalitionMass_nonneg x h0 h1 S
  have hno := continueMass_firstOrder_bounds x h0 h1
  have hsingle := singletonMass_firstOrder_bounds x h0 h1
  have hcollision := collisionMass_le_sq_sum_div_two x h0 h1
  have hnoTerm :
      |(continueMass x - (1 - q)) * tail| ≤ K / 2 * q ^ 2 := by
    rw [abs_mul, abs_of_nonneg hno.1]
    calc
      (continueMass x - (1 - q)) * |tail| ≤
          (continueMass x - (1 - q)) * K :=
        mul_le_mul_of_nonneg_left htail hno.1
      _ ≤ (q ^ 2 / 2) * K :=
        mul_le_mul_of_nonneg_right hno.2 hK
      _ = K / 2 * q ^ 2 := by ring
  have hsingletonTerm :
      |∑ i, (coalitionMass x {i} - x i) * terminal {i}| ≤ R * q ^ 2 := by
    calc
      |∑ i, (coalitionMass x {i} - x i) * terminal {i}| ≤
          ∑ i, |(coalitionMass x {i} - x i) * terminal {i}| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (x i - coalitionMass x {i}) * R := by
        exact Finset.sum_le_sum fun i _ => by
          have hle := coalitionMass_singleton_le x h0 h1 i
          rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hle)]
          rw [show -(coalitionMass x {i} - x i) =
            x i - coalitionMass x {i} by ring]
          apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hle)
          exact hterminal {i} (Finset.singleton_nonempty i)
      _ = (q - singletonMass x) * R := by
        rw [← Finset.sum_mul, Finset.sum_sub_distrib]
        simp [q, singletonMass]
      _ ≤ q ^ 2 * R := mul_le_mul_of_nonneg_right hsingle.2 hR
      _ = R * q ^ 2 := by ring
  have hcollisionTerm :
      |∑ S ∈ collisions, coalitionMass x S * terminal S| ≤
        R / 2 * q ^ 2 := by
    calc
      |∑ S ∈ collisions, coalitionMass x S * terminal S| ≤
          ∑ S ∈ collisions, |coalitionMass x S * terminal S| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ collisions, coalitionMass x S * R := by
        exact Finset.sum_le_sum fun S hS => by
          rw [abs_mul, abs_of_nonneg (hmass0 S)]
          apply mul_le_mul_of_nonneg_left _ (hmass0 S)
          apply hterminal S
          have hcard := (Finset.mem_filter.mp hS).2
          exact Finset.card_pos.mp (by omega)
      _ = collisionMass x * R := by
        rw [← Finset.sum_mul]
        rfl
      _ ≤ (q ^ 2 / 2) * R := mul_le_mul_of_nonneg_right hcollision hR
      _ = R / 2 * q ^ 2 := by ring
  rw [smallHazardExpectation_sub_tail_sub_linearization_eq]
  change |(continueMass x - (1 - q)) * tail +
      ∑ i, (coalitionMass x {i} - x i) * terminal {i} +
      ∑ S ∈ collisions, coalitionMass x S * terminal S| ≤ _
  calc
    |_ + _ + _| ≤
        |(continueMass x - (1 - q)) * tail| +
          |∑ i, (coalitionMass x {i} - x i) * terminal {i}| +
          |∑ S ∈ collisions, coalitionMass x S * terminal S| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ K / 2 * q ^ 2 + R * q ^ 2 + R / 2 * q ^ 2 :=
      add_le_add (add_le_add hnoTerm hsingletonTerm) hcollisionTerm
    _ = (K / 2 + 3 * R / 2) * q ^ 2 := by ring

/-- Sharper quadratic remainder measured by the exact unordered pair sum.
In particular, the remainder vanishes identically when at most one hazard is
nonzero. -/
theorem abs_smallHazardExpectation_sub_tail_sub_linearization_le_pairMulSum
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ)
    {K R : ℝ} (hR : 0 ≤ R)
    (htail : |tail| ≤ K)
    (hterminal : ∀ S, S.Nonempty → |terminal S| ≤ R)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    |smallHazardExpectation terminal tail x - tail -
        smallHazardLinearization terminal tail x| ≤
      (K + 3 * R) * Math.pairMulSum x Finset.univ := by
  let pair := Math.pairMulSum x Finset.univ
  let collisions : Finset (Finset ι) :=
    Finset.univ.filter fun S : Finset ι => 2 ≤ S.card
  have hmass0 : ∀ S, 0 ≤ coalitionMass x S :=
    fun S => coalitionMass_nonneg x h0 h1 S
  have hpair0 : 0 ≤ pair := Math.pairMulSum_nonneg x Finset.univ
    (fun i _ => h0 i)
  have hno0 : 0 ≤ continueMass x - (1 - ∑ i, x i) :=
    sub_nonneg.mpr (one_sub_sum_le_continueMass x h0 h1)
  have hno : continueMass x - (1 - ∑ i, x i) ≤ pair :=
    continueMass_sub_one_sub_sum_le_pairMulSum x h0 h1
  have hsingle : (∑ i, x i) - singletonMass x ≤ 2 * pair :=
    sum_sub_singletonMass_le_two_mul_pairMulSum x h0 h1
  have hcollision : collisionMass x ≤ pair :=
    collisionMass_le_pairMulSum x h0 h1
  have hnoTerm :
      |(continueMass x - (1 - ∑ i, x i)) * tail| ≤ K * pair := by
    rw [abs_mul, abs_of_nonneg hno0]
    calc
      (continueMass x - (1 - ∑ i, x i)) * |tail| ≤
          pair * |tail| := mul_le_mul_of_nonneg_right hno (abs_nonneg tail)
      _ ≤ pair * K := mul_le_mul_of_nonneg_left htail hpair0
      _ = K * pair := mul_comm _ _
  have hsingletonTerm :
      |∑ i, (coalitionMass x {i} - x i) * terminal {i}| ≤
        2 * R * pair := by
    calc
      |∑ i, (coalitionMass x {i} - x i) * terminal {i}| ≤
          ∑ i, |(coalitionMass x {i} - x i) * terminal {i}| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (x i - coalitionMass x {i}) * R := by
        exact Finset.sum_le_sum fun i _ => by
          have hle := coalitionMass_singleton_le x h0 h1 i
          rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hle)]
          rw [show -(coalitionMass x {i} - x i) =
            x i - coalitionMass x {i} by ring]
          exact mul_le_mul_of_nonneg_left
            (hterminal {i} (Finset.singleton_nonempty i))
            (sub_nonneg.mpr hle)
      _ = ((∑ i, x i) - singletonMass x) * R := by
        rw [← Finset.sum_mul, Finset.sum_sub_distrib]
        simp [singletonMass]
      _ ≤ (2 * pair) * R := mul_le_mul_of_nonneg_right hsingle hR
      _ = 2 * R * pair := by ring
  have hcollisionTerm :
      |∑ S ∈ collisions, coalitionMass x S * terminal S| ≤
        R * pair := by
    calc
      |∑ S ∈ collisions, coalitionMass x S * terminal S| ≤
          ∑ S ∈ collisions, |coalitionMass x S * terminal S| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ collisions, coalitionMass x S * R := by
        exact Finset.sum_le_sum fun S hS => by
          rw [abs_mul, abs_of_nonneg (hmass0 S)]
          apply mul_le_mul_of_nonneg_left _ (hmass0 S)
          apply hterminal S
          have hcard := (Finset.mem_filter.mp hS).2
          exact Finset.card_pos.mp (by omega)
      _ = collisionMass x * R := by
        rw [← Finset.sum_mul]
        rfl
      _ ≤ pair * R := mul_le_mul_of_nonneg_right hcollision hR
      _ = R * pair := mul_comm _ _
  rw [smallHazardExpectation_sub_tail_sub_linearization_eq]
  change |(continueMass x - (1 - ∑ i, x i)) * tail +
      ∑ i, (coalitionMass x {i} - x i) * terminal {i} +
      ∑ S ∈ collisions, coalitionMass x S * terminal S| ≤ _
  calc
    |_ + _ + _| ≤
        |(continueMass x - (1 - ∑ i, x i)) * tail| +
          |∑ i, (coalitionMass x {i} - x i) * terminal {i}| +
          |∑ S ∈ collisions, coalitionMass x S * terminal S| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ K * pair + 2 * R * pair + R * pair :=
      add_le_add (add_le_add hnoTerm hsingletonTerm) hcollisionTerm
    _ = (K + 3 * R) * pair := by ring

/-- A coarser but simpler quadratic remainder bound. -/
theorem abs_smallHazardExpectation_sub_tail_sub_linearization_le_two
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ)
    {K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (htail : |tail| ≤ K)
    (hterminal : ∀ S, S.Nonempty → |terminal S| ≤ R)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    |smallHazardExpectation terminal tail x - tail -
        smallHazardLinearization terminal tail x| ≤
      2 * (K + R) * (∑ i, x i) ^ 2 := by
  refine (abs_smallHazardExpectation_sub_tail_sub_linearization_le
    terminal tail x hK hR htail hterminal h0 h1).trans ?_
  have hsq : 0 ≤ (∑ i, x i) ^ 2 := sq_nonneg _
  apply mul_le_mul_of_nonneg_right _ hsq
  linarith

end Math.PMFProduct
