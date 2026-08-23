/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.ChargedOccupationAlternative

/-!
# Finite linear charged capacity

This file isolates the finite-dimensional linear program behind a family of
flat charged columns.  A charged circulation is exactly the recession
obstruction to finite capacity.  In the other branch, a Farkas separator can
be shifted to a strictly positive Lyapunov weight which decreases along every
column by at least its charge.

The results concern numerical vectors only.  They do not assert that a linear
combination of columns is a semantic state, an executable path, or a sequence
of conditioned game prefixes.
-/

noncomputable section

namespace Math
namespace FiniteLinearChargedCapacity

open Finset Probability

variable {Coordinate Action : Type*}

/-- The endpoint obtained by applying nonnegative action masses to a debt
vector in the linearized system. -/
def endpoint [Fintype Action]
    (debt : Coordinate → ℝ) (column : Action → Coordinate → ℝ)
    (mass : Action → ℝ) (i : Coordinate) : ℝ :=
  debt i + ∑ a, mass a * column a i

/-- Feasibility of a mass vector for the nonnegative debt orthant. -/
def IsFeasible [Fintype Action]
    (debt : Coordinate → ℝ) (column : Action → Coordinate → ℝ)
    (mass : Action → ℝ) : Prop :=
  (∀ a, 0 ≤ mass a) ∧ ∀ i, 0 ≤ endpoint debt column mass i

/-- Total charge accumulated by an action-mass vector. -/
def totalCharge [Fintype Action]
    (charge mass : Action → ℝ) : ℝ :=
  ∑ a, mass a * charge a

/-- Value of a coordinate vector under a linear weight. -/
def weightedValue [Fintype Coordinate]
    (weight value : Coordinate → ℝ) : ℝ :=
  ∑ i, weight i * value i

/-- Shift an arbitrary finite potential into a weight bounded below by one.
The shift disappears when paired with a flat column. -/
def positiveWeight [Fintype Coordinate]
    (potential : Coordinate → ℝ) (i : Coordinate) : ℝ :=
  (∑ j, |potential j|) + 1 - potential i

theorem one_le_positiveWeight [Fintype Coordinate]
    (potential : Coordinate → ℝ) (i : Coordinate) :
    1 ≤ positiveWeight potential i := by
  classical
  have habs : |potential i| ≤ ∑ j, |potential j| := by
    exact single_le_sum (fun j _ ↦ abs_nonneg (potential j)) (mem_univ i)
  have hself : potential i ≤ |potential i| := le_abs_self (potential i)
  simp only [positiveWeight]
  linarith

/-- On a flat column, the positive shifted weight pairs as the negative of
the original potential. -/
theorem positiveWeight_pair_flat [Fintype Coordinate]
    (potential column : Coordinate → ℝ)
    (hflat : ∑ i, column i = 0) :
    weightedValue (positiveWeight potential) column =
      -weightedValue potential column := by
  classical
  simp only [weightedValue, positiveWeight]
  calc
    (∑ i, ((∑ j, |potential j|) + 1 - potential i) * column i) =
        ((∑ j, |potential j|) + 1) * (∑ i, column i) -
          ∑ i, potential i * column i := by
            rw [mul_sum]
            rw [← sum_sub_distrib]
            apply sum_congr rfl
            intro i _
            ring
    _ = -weightedValue potential column := by simp [hflat, weightedValue]

/-- A separator for flat columns yields one strictly positive Lyapunov
weight which decreases along every column by at least its charge. -/
theorem strictWeight_of_potential
    [Fintype Coordinate]
    (column : Action → Coordinate → ℝ) (charge : Action → ℝ)
    (potential : Coordinate → ℝ)
    (hflat : ∀ a, ∑ i, column a i = 0)
    (hpotential : IsChargedOccupationPotential column charge potential) :
    (∀ i, 1 ≤ positiveWeight potential i) ∧
      ∀ a, weightedValue (positiveWeight potential) (column a) ≤ -charge a := by
  constructor
  · exact one_le_positiveWeight potential
  · intro a
    rw [positiveWeight_pair_flat potential (column a) (hflat a)]
    exact neg_le_neg (hpotential a)

/-- A positive charged circulation cannot coexist with a strictly positive
weight decreasing by every action's charge. -/
theorem normalizedPositiveChargedCirculation_not_strictWeight
    [Fintype Coordinate] [Fintype Action]
    {column : Action → Coordinate → ℝ} {charge : Action → ℝ}
    (hcirculation :
      HasNormalizedPositiveChargedCirculation column charge) :
    ¬ ∃ weight : Coordinate → ℝ,
      ∀ a, weightedValue weight (column a) ≤ -charge a := by
  classical
  rintro ⟨weight, hdescent⟩
  obtain ⟨mass, hmass, hbalance, hcharge⟩ := hcirculation
  have hweighted :
      (∑ a, mass a * weightedValue weight (column a)) ≤
        -(∑ a, mass a * charge a) := by
    calc
      (∑ a, mass a * weightedValue weight (column a)) ≤
          ∑ a, mass a * (-charge a) := by
            apply sum_le_sum
            intro a _
            exact mul_le_mul_of_nonneg_left (hdescent a) (hmass a)
      _ = -(∑ a, mass a * charge a) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro a _
        ring
  have hzero : ∑ a, mass a * weightedValue weight (column a) = 0 := by
    calc
      (∑ a, mass a * weightedValue weight (column a)) =
          ∑ i, weight i * (∑ a, mass a * column a i) := by
            simp only [weightedValue, mul_sum]
            rw [sum_comm]
            apply sum_congr rfl
            intro i _
            apply sum_congr rfl
            intro a _
            ring
      _ = 0 := by simp [hbalance]
  rw [hzero, hcharge] at hweighted
  norm_num at hweighted

/-- Exact finite Farkas alternative for flat charged columns: either there
is a normalized positive charged circulation, or there is a strictly
positive common Lyapunov weight. -/
theorem normalizedPositiveChargedCirculation_xor_strictWeight
    [Fintype Coordinate] [Fintype Action]
    (column : Action → Coordinate → ℝ) (charge : Action → ℝ)
    (hflat : ∀ a, ∑ i, column a i = 0) :
    Xor
      (HasNormalizedPositiveChargedCirculation column charge)
      (∃ weight : Coordinate → ℝ,
        (∀ i, 1 ≤ weight i) ∧
          ∀ a, weightedValue weight (column a) ≤ -charge a) := by
  rw [xor_def]
  rcases normalizedPositiveChargedCirculation_xor_potential column charge with
      hcirculation | hpotential
  · refine Or.inl ⟨hcirculation.1, ?_⟩
    exact fun hweight ↦
      normalizedPositiveChargedCirculation_not_strictWeight hcirculation.1
        ⟨hweight.choose, hweight.choose_spec.2⟩
  · obtain ⟨potential, hp⟩ := hpotential.1
    refine Or.inr ⟨?_, hpotential.2⟩
    exact ⟨positiveWeight potential,
      strictWeight_of_potential column charge potential hflat hp⟩

/-- A nonnegative Lyapunov weight bounds the charge of every feasible linear
plan by the weighted initial debt. -/
theorem totalCharge_le_weightedValue_of_feasible
    [Fintype Coordinate] [Fintype Action]
    {debt : Coordinate → ℝ} {column : Action → Coordinate → ℝ}
    {charge mass : Action → ℝ} {weight : Coordinate → ℝ}
    (hfeasible : IsFeasible debt column mass)
    (hweight : ∀ i, 0 ≤ weight i)
    (hdescent : ∀ a, weightedValue weight (column a) ≤ -charge a) :
    totalCharge charge mass ≤ weightedValue weight debt := by
  classical
  have hend : 0 ≤ weightedValue weight (endpoint debt column mass) := by
    apply sum_nonneg
    intro i _
    exact mul_nonneg (hweight i) (hfeasible.2 i)
  have hidentity :
      weightedValue weight (endpoint debt column mass) =
        weightedValue weight debt +
          ∑ a, mass a * weightedValue weight (column a) := by
    simp only [weightedValue, endpoint, mul_add, sum_add_distrib]
    congr 1
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro i _
    ring
  have hstep :
      weightedValue weight (endpoint debt column mass) ≤
        weightedValue weight debt - totalCharge charge mass := by
    rw [hidentity]
    simp only [totalCharge]
    have hsum :
        (∑ a, mass a * weightedValue weight (column a)) ≤
          ∑ a, mass a * (-charge a) := by
      apply sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hdescent a) (hfeasible.1 a)
    calc
      weightedValue weight debt +
            ∑ a, mass a * weightedValue weight (column a) ≤
          weightedValue weight debt + ∑ a, mass a * (-charge a) :=
        add_le_add (le_refl _) hsum
      _ = weightedValue weight debt - ∑ a, mass a * charge a := by
        rw [sub_eq_add_neg, ← sum_neg_distrib]
        apply congrArg (weightedValue weight debt + ·)
        apply sum_congr rfl
        intro a _
        ring
  linarith

/-- In the no-circulation branch, one common strictly positive weight gives
a finite charge bound for every feasible mass and every initial debt. -/
theorem exists_strictWeight_capacityBound_of_noCirculation
    [Fintype Coordinate] [Fintype Action]
    (column : Action → Coordinate → ℝ) (charge : Action → ℝ)
    (hflat : ∀ a, ∑ i, column a i = 0)
    (hnoCirculation :
      ¬HasNormalizedPositiveChargedCirculation column charge) :
    ∃ weight : Coordinate → ℝ,
      (∀ i, 1 ≤ weight i) ∧
        (∀ a, weightedValue weight (column a) ≤ -charge a) ∧
        ∀ (debt : Coordinate → ℝ) (mass : Action → ℝ),
          IsFeasible debt column mass →
            totalCharge charge mass ≤ weightedValue weight debt := by
  rcases normalizedPositiveChargedCirculation_xor_strictWeight
      column charge hflat with hcirculation | hweight
  · exact False.elim (hnoCirculation hcirculation.1)
  · obtain ⟨weight, hpositive, hdescent⟩ := hweight.1
    refine ⟨weight, hpositive, hdescent, ?_⟩
    intro debt mass hfeasible
    exact totalCharge_le_weightedValue_of_feasible hfeasible
      (fun i ↦ zero_le_one.trans (hpositive i)) hdescent

/-- A normalized positive charged circulation gives feasible masses of
arbitrarily large charge from every nonnegative initial debt. -/
theorem exists_feasible_charge_gt_of_circulation
    [Fintype Coordinate] [Fintype Action]
    {debt : Coordinate → ℝ} {column : Action → Coordinate → ℝ}
    {charge : Action → ℝ}
    (hdebt : ∀ i, 0 ≤ debt i)
    (hcirculation :
      HasNormalizedPositiveChargedCirculation column charge) :
    ∀ bound : ℝ, ∃ mass : Action → ℝ,
      IsFeasible debt column mass ∧ bound < totalCharge charge mass := by
  classical
  obtain ⟨circulation, hnonneg, hbalance, hcharge⟩ := hcirculation
  intro bound
  let scale : ℝ := max 0 bound + 1
  let mass : Action → ℝ := fun a ↦ scale * circulation a
  have hscale : 0 ≤ scale := by
    dsimp only [scale]
    have := le_max_left 0 bound
    linarith
  have hbound : bound < scale := by
    have := le_max_right 0 bound
    simp only [scale]
    linarith
  refine ⟨mass, ⟨?_, ?_⟩, ?_⟩
  · intro a
    exact mul_nonneg hscale (hnonneg a)
  · intro i
    simp only [endpoint, mass]
    have hzero : ∑ a, scale * circulation a * column a i = 0 := by
      calc
        (∑ a, scale * circulation a * column a i) =
            scale * (∑ a, circulation a * column a i) := by
              rw [Finset.mul_sum]
              apply sum_congr rfl
              intro a _
              ring
        _ = 0 := by rw [hbalance i, mul_zero]
    rw [hzero, add_zero]
    exact hdebt i
  · simp only [totalCharge, mass]
    calc
      bound < scale := hbound
      _ = ∑ a, scale * circulation a * charge a := by
        calc
          scale = scale * 1 := by ring
          _ = scale * (∑ a, circulation a * charge a) := by rw [hcharge]
          _ = ∑ a, scale * circulation a * charge a := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro a _
            ring

/-- For flat finite columns, a positive charged circulation exists exactly
when feasible charge is unbounded from a fixed nonnegative debt vector. This
is the recession theorem for the linearized charged-prefix problem. -/
theorem normalizedPositiveChargedCirculation_iff_unboundedFeasibleCharge
    [Fintype Coordinate] [Fintype Action]
    (debt : Coordinate → ℝ) (column : Action → Coordinate → ℝ)
    (charge : Action → ℝ) (hdebt : ∀ i, 0 ≤ debt i)
    (hflat : ∀ a, ∑ i, column a i = 0) :
    HasNormalizedPositiveChargedCirculation column charge ↔
      ∀ bound : ℝ, ∃ mass : Action → ℝ,
        IsFeasible debt column mass ∧ bound < totalCharge charge mass := by
  constructor
  · exact exists_feasible_charge_gt_of_circulation hdebt
  · intro hunbounded
    rcases normalizedPositiveChargedCirculation_xor_strictWeight
        column charge hflat with hcirculation | hweight
    · exact hcirculation.1
    · obtain ⟨weight, hpositive, hdescent⟩ := hweight.1
      obtain ⟨mass, hfeasible, hstrict⟩ :=
        hunbounded (weightedValue weight debt)
      have hbound := totalCharge_le_weightedValue_of_feasible
        hfeasible (fun i ↦ (zero_le_one.trans (hpositive i))) hdescent
      exact False.elim (not_lt_of_ge hbound hstrict)

/-- If one column has a negative coordinate, moving from a strictly positive
debt vector until the first coordinate hits zero gives a positive feasible
step.  This is the exact one-column boundary-face operation in the linear
system. -/
theorem exists_positive_step_to_boundary
    [Fintype Coordinate] [DecidableEq Coordinate]
    (debt column : Coordinate → ℝ)
    (hdebt : ∀ i, 0 < debt i) (hnegative : ∃ i, column i < 0) :
    ∃ step : ℝ, 0 < step ∧
      (∀ i, 0 ≤ debt i + step * column i) ∧
      ∃ pivot, debt pivot + step * column pivot = 0 := by
  let negative : Finset Coordinate := univ.filter fun i ↦ column i < 0
  have hnegativeSet : negative.Nonempty := by
    obtain ⟨i, hi⟩ := hnegative
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  obtain ⟨pivot, hpivotMem, hpivotMin⟩ :=
    exists_min_image negative (fun i ↦ debt i / (-column i)) hnegativeSet
  have hpivotNegative : column pivot < 0 := (mem_filter.mp hpivotMem).2
  let step : ℝ := debt pivot / (-column pivot)
  have hstep : 0 < step :=
    div_pos (hdebt pivot) (neg_pos.mpr hpivotNegative)
  refine ⟨step, hstep, ?_, pivot, ?_⟩
  · intro i
    by_cases hi : column i < 0
    · have hiMem : i ∈ negative := mem_filter.mpr ⟨mem_univ i, hi⟩
      have hratio : step ≤ debt i / (-column i) := hpivotMin i hiMem
      have hdenom : 0 < -column i := neg_pos.mpr hi
      have hscaled : step * (-column i) ≤ debt i := by
        exact (le_div_iff₀ hdenom).mp hratio
      linarith
    · have hcolumn : 0 ≤ column i := le_of_not_gt hi
      exact add_nonneg (hdebt i).le (mul_nonneg hstep.le hcolumn)
  · dsimp only [step]
    have hpivotNe : column pivot ≠ 0 := ne_of_lt hpivotNegative
    rw [div_neg, neg_mul]
    field_simp
    ring

/-- A flat one-column boundary step preserves total debt. -/
theorem sum_add_step_column_eq_sum
    [Fintype Coordinate]
    (debt column : Coordinate → ℝ) (step : ℝ)
    (hflat : ∑ i, column i = 0) :
    (∑ i, (debt i + step * column i)) = ∑ i, debt i := by
  rw [sum_add_distrib, ← Finset.mul_sum, hflat, mul_zero, add_zero]

/-- A strict Lyapunov column inequality gives quantitative decrease at every
positive one-column step. -/
theorem weightedValue_add_step_column_le
    [Fintype Coordinate]
    (debt column weight : Coordinate → ℝ) (step charge : ℝ)
    (hstep : 0 ≤ step)
    (hdescent : weightedValue weight column ≤ -charge) :
    weightedValue weight (fun i ↦ debt i + step * column i) ≤
      weightedValue weight debt - step * charge := by
  have hscaled := mul_le_mul_of_nonneg_left hdescent hstep
  simp only [weightedValue, mul_add, sum_add_distrib]
  have hidentity :
      (∑ i, weight i * (step * column i)) =
        step * weightedValue weight column := by
    simp only [weightedValue]
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [hidentity]
  linarith

/-- Add one nonnegative amount to a selected action mass. -/
def addActionMass [DecidableEq Action]
    (mass : Action → ℝ) (selected : Action) (step : ℝ) (a : Action) : ℝ :=
  mass a + if a = selected then step else 0

theorem endpoint_addActionMass
    [Fintype Action] [DecidableEq Action]
    (debt : Coordinate → ℝ) (column : Action → Coordinate → ℝ)
    (mass : Action → ℝ) (selected : Action) (step : ℝ) (i : Coordinate) :
    endpoint debt column (addActionMass mass selected step) i =
      endpoint debt column mass i + step * column selected i := by
  classical
  simp [endpoint, addActionMass, add_mul, sum_add_distrib]
  ring

theorem totalCharge_addActionMass
    [Fintype Action] [DecidableEq Action]
    (charge mass : Action → ℝ) (selected : Action) (step : ℝ) :
    totalCharge charge (addActionMass mass selected step) =
      totalCharge charge mass + step * charge selected := by
  classical
  simp [totalCharge, addActionMass, add_mul, sum_add_distrib]

/-- A feasible mass is charge-maximal when no other feasible mass has larger
total charge. -/
def IsChargeMaximizer [Fintype Action]
    (debt : Coordinate → ℝ) (column : Action → Coordinate → ℝ)
    (charge mass : Action → ℝ) : Prop :=
  IsFeasible debt column mass ∧
    ∀ other, IsFeasible debt column other →
      totalCharge charge other ≤ totalCharge charge mass

/-- If some action has positive charge, every charge maximizer lies on a
boundary face of the nonnegative endpoint orthant. -/
theorem exists_zero_endpoint_of_chargeMaximizer
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Action] [DecidableEq Action]
    (debt : Coordinate → ℝ) (column : Action → Coordinate → ℝ)
    (charge mass : Action → ℝ)
    (hpositive : ∃ a, 0 < charge a)
    (hmaximal : IsChargeMaximizer debt column charge mass) :
    ∃ i, endpoint debt column mass i = 0 := by
  classical
  by_contra hnozero
  have hendPositive : ∀ i, 0 < endpoint debt column mass i := by
    intro i
    have hne : endpoint debt column mass i ≠ 0 := by
      intro hi
      exact hnozero ⟨i, hi⟩
    exact lt_of_le_of_ne (hmaximal.1.2 i) (Ne.symm hne)
  obtain ⟨selected, hselectedCharge⟩ := hpositive
  have hstep :
      ∃ step : ℝ, 0 < step ∧
        ∀ i, 0 ≤ endpoint debt column mass i + step * column selected i := by
    by_cases hnegative : ∃ i, column selected i < 0
    · obtain ⟨step, hstep, hnonneg, _⟩ :=
        exists_positive_step_to_boundary
          (endpoint debt column mass) (column selected) hendPositive hnegative
      exact ⟨step, hstep, hnonneg⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      intro i
      have hcolumn : 0 ≤ column selected i := by
        exact le_of_not_gt fun hi ↦ hnegative ⟨i, hi⟩
      exact add_nonneg (hendPositive i).le (by simpa using hcolumn)
  obtain ⟨step, hstepPositive, hendpoint⟩ := hstep
  let larger := addActionMass mass selected step
  have hlargerFeasible : IsFeasible debt column larger := by
    constructor
    · intro a
      dsimp only [larger, addActionMass]
      exact add_nonneg (hmaximal.1.1 a) (by split <;> positivity)
    · intro i
      rw [endpoint_addActionMass]
      exact hendpoint i
  have hchargeLe := hmaximal.2 larger hlargerFeasible
  rw [totalCharge_addActionMass] at hchargeLe
  have hstrict : 0 < step * charge selected :=
    mul_pos hstepPositive hselectedCharge
  linarith

/-- A maximal potential coordinate with strictly positive separated charge
forces a strictly lower-potential coordinate to decrease in that column. -/
theorem exists_lowerPotential_negativeCoordinate
    [Fintype Coordinate]
    (column potential : Coordinate → ℝ) (mover : Coordinate)
    (charge : ℝ) (hcharge : 0 < charge)
    (hflat : ∑ i, column i = 0)
    (hmax : ∀ i, potential i ≤ potential mover)
    (hseparate : charge ≤ weightedValue potential column) :
    ∃ other, other ≠ mover ∧ potential other < potential mover ∧
      column other < 0 := by
  classical
  by_contra hnone
  have hterm :
      ∀ i, (potential i - potential mover) * column i ≤ 0 := by
    intro i
    by_cases hcolumn : column i < 0
    · have hpotential : potential mover ≤ potential i := by
        by_contra hnot
        have hlt : potential i < potential mover := lt_of_not_ge hnot
        have hne : i ≠ mover := by
          intro him
          subst i
          exact (lt_irrefl (potential mover)) hlt
        have hnonneg : 0 ≤ column i := by
          by_contra hnot
          apply hnone
          exact ⟨i, hne, hlt, lt_of_not_ge hnot⟩
        exact (not_lt_of_ge hnonneg) hcolumn
      have heq : potential i = potential mover := le_antisymm (hmax i) hpotential
      simp [heq]
    · exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hmax i)) (le_of_not_gt hcolumn)
  have hnonpos :
      ∑ i, (potential i - potential mover) * column i ≤ 0 :=
    sum_nonpos fun i _ ↦ hterm i
  have heq :
      ∑ i, (potential i - potential mover) * column i =
        weightedValue potential column := by
    simp only [weightedValue]
    calc
      (∑ i, (potential i - potential mover) * column i) =
          (∑ i, potential i * column i) -
            potential mover * (∑ i, column i) := by
              rw [Finset.mul_sum, ← sum_sub_distrib]
              apply sum_congr rfl
              intro i _
              ring
      _ = ∑ i, potential i * column i := by rw [hflat, mul_zero, sub_zero]
  rw [heq] at hnonpos
  linarith

end FiniteLinearChargedCapacity
end Math
