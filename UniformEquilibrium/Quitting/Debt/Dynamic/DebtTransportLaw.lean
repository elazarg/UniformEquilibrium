/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.MaxAffine.Paths
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebt

/-!
# Reflected directed transport of finite dynamic debt

At a live stage, define the *stage gap* `quittingStageGap` as how much the
fixed-opponents quit value exceeds the fixed-opponents continue value under
the prescribed tail.  Under residual-zero the raw Bellman maximum recursion
collapses to

`debt start (fuel + 1) = max 0 (continueMass * debt (start + 1) fuel -
  max 0 (stageGap start))`,

This is the action of `quittingDynamicDebtLabel`, a reflected max-affine label
with floor zero, shift minus the positive part of the stage gap, and slope the
opponents' Continue mass.  `quittingDynamicDebtLabelList` orders a finite
window backward from its terminal boundary.  Its composite label acts exactly
as `quittingFiniteDynamicDebt`, and its path slope is exactly the finite
opponent-survival weight.

Unrolling the action from the terminal boundary gives the closed form

`debt start fuel = max 0 (survivalWeight * terminalDebt -
  Σ survivalWeight * max 0 stageGap)`,

proved by `quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps`.
The return classification
`quittingFiniteDynamicDebt_eq_terminalDebt_iff` says that a positive terminal
debt returns unchanged precisely when every traversed opponent-survival factor
is one and every traversed stage gap is nonpositive.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The stage gap: how much the fixed-opponents quit value at a live stage
exceeds the fixed-opponents continue value evaluated at the prescribed next
value.  This is the quantity whose positive part is annihilated from the
transported debt at each step. -/
def quittingStageGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) : ℝ :=
  quittingFixedOpponentsQuitValue reward roots who time -
    (quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time * prescribed (time + 1))

/-- The reflected max-affine label of one exact dynamic-debt step. -/
def quittingDynamicDebtLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) :
    Math.MaxAffineTransport.Label :=
  Math.MaxAffineTransport.reflectedLabel
    (quittingFixedOpponentsContinueMass roots who time)
    (max 0 (quittingStageGap reward roots who prescribed time))

@[simp] theorem quittingDynamicDebtLabel_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) :
    (quittingDynamicDebtLabel reward roots who prescribed time).floor =
      (0 : WithBot ℝ) := rfl

@[simp] theorem quittingDynamicDebtLabel_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) :
    (quittingDynamicDebtLabel reward roots who prescribed time).shift =
      -max 0 (quittingStageGap reward roots who prescribed time) := rfl

@[simp] theorem quittingDynamicDebtLabel_slope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) :
    (quittingDynamicDebtLabel reward roots who prescribed time).slope =
      quittingFixedOpponentsContinueMass roots who time := rfl

@[simp] theorem quittingDynamicDebtLabel_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) (debt : ℝ) :
    (quittingDynamicDebtLabel reward roots who prescribed time).apply debt =
      max 0 (quittingFixedOpponentsContinueMass roots who time * debt -
        max 0 (quittingStageGap reward roots who prescribed time)) := by
  exact Math.MaxAffineTransport.apply_reflectedLabel _ _ _

theorem quittingDynamicDebtLabel_slope_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) :
    0 ≤ (quittingDynamicDebtLabel reward roots who prescribed time).slope := by
  rw [quittingDynamicDebtLabel_slope]
  exact quittingStationaryContinueMass_nonneg
    (Function.update (roots time) who (PMF.pure false))

theorem quittingDynamicDebtLabel_slope_le_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) :
    (quittingDynamicDebtLabel reward roots who prescribed time).slope ≤ 1 := by
  rw [quittingDynamicDebtLabel_slope]
  exact quittingStationaryContinueMass_le_one
    (Function.update (roots time) who (PMF.pure false))

/-- A reflected dynamic-debt step cannot increase a nonnegative debt. -/
theorem quittingDynamicDebtLabel_apply_le_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) {debt : ℝ}
    (hdebt : 0 ≤ debt) :
    (quittingDynamicDebtLabel reward roots who prescribed time).apply debt ≤ debt := by
  rw [quittingDynamicDebtLabel_apply, max_le_iff]
  constructor
  · exact hdebt
  · have hslope := quittingDynamicDebtLabel_slope_le_one
      reward roots who prescribed time
    rw [quittingDynamicDebtLabel_slope] at hslope
    have hgap : 0 ≤ max 0 (quittingStageGap reward roots who prescribed time) :=
      le_max_left _ _
    nlinarith

/-- A positive debt is fixed by one reflected step exactly when opponent
survival is one and the stage gap is nonpositive. -/
theorem quittingDynamicDebtLabel_apply_eq_self_iff_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) {debt : ℝ}
    (hdebt : 0 < debt) :
    (quittingDynamicDebtLabel reward roots who prescribed time).apply debt = debt ↔
      quittingFixedOpponentsContinueMass roots who time = 1 ∧
        quittingStageGap reward roots who prescribed time ≤ 0 := by
  rw [quittingDynamicDebtLabel_apply]
  constructor
  · intro hfixed
    have hins : 0 <
        quittingFixedOpponentsContinueMass roots who time * debt -
          max 0 (quittingStageGap reward roots who prescribed time) := by
      by_contra hnonpos
      have hmax : max 0
          (quittingFixedOpponentsContinueMass roots who time * debt -
            max 0 (quittingStageGap reward roots who prescribed time)) = 0 :=
        max_eq_left (le_of_not_gt hnonpos)
      rw [hmax] at hfixed
      linarith
    rw [max_eq_right hins.le] at hfixed
    have hslope := quittingDynamicDebtLabel_slope_le_one
      reward roots who prescribed time
    rw [quittingDynamicDebtLabel_slope] at hslope
    have hgapNonneg :
        0 ≤ max 0 (quittingStageGap reward roots who prescribed time) :=
      le_max_left _ _
    have hslopeEq : quittingFixedOpponentsContinueMass roots who time = 1 := by
      nlinarith
    have hgapEq : max 0 (quittingStageGap reward roots who prescribed time) = 0 := by
      nlinarith
    exact ⟨hslopeEq, (le_max_right 0 _).trans_eq hgapEq⟩
  · rintro ⟨hslope, hgap⟩
    rw [hslope, max_eq_left hgap, sub_zero, one_mul, max_eq_right hdebt.le]

/-- Backward chronological labels of a dynamic-debt window.  The last game
stage acts first on the terminal debt. -/
def quittingDynamicDebtLabelList
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (start : ℕ) : ℕ →
    List Math.MaxAffineTransport.Label
  | 0 => []
  | fuel + 1 =>
      quittingDynamicDebtLabelList reward roots who prescribed (start + 1) fuel ++
        [quittingDynamicDebtLabel reward roots who prescribed start]

theorem quittingDynamicDebtLabelList_slope_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) : ∀ start fuel label,
    label ∈ quittingDynamicDebtLabelList reward roots who prescribed start fuel →
      0 ≤ label.slope := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingDynamicDebtLabelList]
  | succ fuel ih =>
      intro label hlabel
      rw [quittingDynamicDebtLabelList] at hlabel
      rcases List.mem_append.mp hlabel with htail | hlast
      · exact ih (start + 1) label htail
      · simp only [List.mem_singleton] at hlast
        subst label
        exact quittingDynamicDebtLabel_slope_nonneg
          reward roots who prescribed start

/-- The slope of the composite dynamic-debt label is exactly opponent
survival through the window. -/
theorem quittingDynamicDebtLabelList_pathSlope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) : ∀ start fuel,
    Math.MaxAffineTransport.Label.pathSlope
        (quittingDynamicDebtLabelList reward roots who prescribed start fuel) =
      quittingOpponentSurvivalWeight roots who start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingDynamicDebtLabelList, quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      rw [quittingDynamicDebtLabelList,
        Math.MaxAffineTransport.Label.pathSlope_append,
        ih (start + 1), quittingOpponentSurvivalWeight_succ_left]
      simp only [Math.MaxAffineTransport.Label.pathSlope_cons,
        Math.MaxAffineTransport.Label.pathSlope_nil,
        quittingDynamicDebtLabel_slope, mul_one]
      ring

/-- Shifting a common summand `Γ` out of a difference of two maxima. -/
theorem max_sub_max_eq_of_add_eq (Q Γ y : ℝ) :
    max Q (Γ + y) - max Q Γ = max (Q - Γ) y - max (Q - Γ) 0 := by
  have heq : Γ + (Q - Γ) = Q := by ring
  have e1 : max Q (Γ + y) = Γ + max (Q - Γ) y := by
    have hshift := add_max Γ (Q - Γ) y
    rw [heq] at hshift
    exact hshift.symm
  have e2 : max Q Γ = Γ + max (Q - Γ) 0 := by
    have hshift := add_max Γ (Q - Γ) 0
    rw [heq, add_zero] at hshift
    exact hshift.symm
  rw [e1, e2]
  ring

/-- For a nonnegative `x`, subtracting `max h 0` from `max h x` agrees with
flooring `x - max h 0` at zero.  This is the elementary real-number fact
underlying the one-step transport law; it fails without `0 ≤ x`. -/
theorem max_sub_max_zero_eq_max_zero_sub_of_nonneg {h x : ℝ} (hx : 0 ≤ x) :
    max h x - max h 0 = max 0 (x - max 0 h) := by
  rcases le_total h 0 with hh | hh
  · rw [max_eq_right (hh.trans hx), max_eq_right hh, max_eq_left hh, sub_zero,
      max_eq_right hx]
  · rw [max_eq_left hh, max_eq_right hh]
    rcases le_total h x with hhx | hhx
    · rw [max_eq_right hhx, max_eq_right (show (0 : ℝ) ≤ x - h by linarith)]
    · rw [max_eq_left hhx, sub_self, max_eq_left (show x - h ≤ 0 by linarith)]

/-- Flooring at zero absorbs a nested flooring: subtracting a nonnegative
`z` from `max 0 Y` and flooring again agrees with subtracting `z` from `Y`
directly and flooring once. -/
theorem max_zero_sub_of_nonneg {Y z : ℝ} (hz : 0 ≤ z) :
    max 0 (max 0 Y - z) = max 0 (Y - z) := by
  rcases le_total 0 Y with hY | hY
  · rw [max_eq_right hY]
  · rw [max_eq_left hY, max_eq_left (show (0 : ℝ) - z ≤ 0 by linarith),
      max_eq_left (show Y - z ≤ 0 by linarith)]

/-- The defining one-step exact dynamic-debt recursion, collapsed under
residual-zero to the positive-part stage-gap form: transported next debt
minus the positive part of the current stage gap, floored at zero. -/
theorem quittingFiniteDynamicDebt_succ_eq_max_zero_stageGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (start fuel : ℕ)
    (hresidual :
      quittingPrescribedOneStepResidual reward roots who prescribed start = 0) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) =
      max 0
        (quittingFixedOpponentsContinueMass roots who start *
            quittingFiniteDynamicDebt reward roots who prescribed
              terminalDebt (start + 1) fuel -
          max 0 (quittingStageGap reward roots who prescribed start)) := by
  set q := quittingFixedOpponentsContinueMass roots who start with hqdef
  set d' := quittingFiniteDynamicDebt reward roots who prescribed
    terminalDebt (start + 1) fuel with hd'def
  set Q := quittingFixedOpponentsQuitValue reward roots who start with hQdef
  set Γ := quittingFixedOpponentsContinueReward reward roots who start +
    q * prescribed (start + 1) with hΓdef
  have hgap : quittingStageGap reward roots who prescribed start = Q - Γ := by
    unfold quittingStageGap
    rw [← hQdef, ← hqdef, ← hΓdef]
  have hpres : prescribed start = max Q Γ := by
    have hres' := hresidual
    unfold quittingPrescribedOneStepResidual quittingLiveBellmanValue at hres'
    rw [← hQdef, ← hqdef] at hres'
    linarith
  have hd'_nonneg : 0 ≤ d' := by
    rw [hd'def]
    exact quittingFiniteDynamicDebt_nonneg reward roots who prescribed
      hprescribed hterminalDebt (start + 1) fuel
  have hq_nonneg : 0 ≤ q := by
    rw [hqdef]
    exact quittingStationaryContinueMass_nonneg
      (Function.update (roots start) who (PMF.pure false))
  have hx_nonneg : 0 ≤ q * d' := mul_nonneg hq_nonneg hd'_nonneg
  have hstep : quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
      start (fuel + 1) = max Q (Γ + q * d') - max Q Γ := by
    rw [quittingFiniteDynamicDebt_succ, hpres]
    congr 2
    rw [hΓdef]
    ring
  calc
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) = max Q (Γ + q * d') - max Q Γ := hstep
    _ = max (Q - Γ) (q * d') - max (Q - Γ) 0 :=
        max_sub_max_eq_of_add_eq Q Γ (q * d')
    _ = max 0 (q * d' - max 0 (Q - Γ)) :=
        max_sub_max_zero_eq_max_zero_sub_of_nonneg hx_nonneg
    _ = max 0 (q * d' - max 0 (quittingStageGap reward roots who prescribed start)) := by
        rw [hgap]

/-- Under residual zero, the exact one-step dynamic-debt recursion is the
action of its reflected transport label. -/
theorem quittingFiniteDynamicDebt_succ_eq_label_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (start fuel : ℕ)
    (hresidual :
      quittingPrescribedOneStepResidual reward roots who prescribed start = 0) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) =
      (quittingDynamicDebtLabel reward roots who prescribed start).apply
        (quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          (start + 1) fuel) := by
  rw [quittingDynamicDebtLabel_apply]
  exact quittingFiniteDynamicDebt_succ_eq_max_zero_stageGap
    reward roots who prescribed hprescribed hterminalDebt start fuel hresidual

/-- Exact finite dynamic debt is the action of the composite reflected label
of the traversed window. -/
theorem quittingFiniteDynamicDebt_eq_compList_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt start fuel =
        (Math.MaxAffineTransport.Label.compList
          (quittingDynamicDebtLabelList reward roots who prescribed start fuel)).apply
            terminalDebt := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _
      simp [quittingDynamicDebtLabelList]
  | succ fuel ih =>
      intro hwindow
      have hstart : start < bound := by omega
      have htailWindow : start + 1 + fuel ≤ bound := by omega
      rw [quittingFiniteDynamicDebt_succ_eq_label_apply
        reward roots who prescribed hprescribed hterminalDebt start fuel
          (hresidual start hstart)]
      rw [ih (start + 1) htailWindow, quittingDynamicDebtLabelList]
      symm
      apply Math.MaxAffineTransport.Label.apply_compList_append_singleton
      · intro label hlabel
        exact quittingDynamicDebtLabelList_slope_nonneg
          reward roots who prescribed (start + 1) fuel label hlabel
      · exact quittingDynamicDebtLabel_slope_nonneg
          reward roots who prescribed start

/-- Coefficient form of exact dynamic-debt transport.  The path floor records
the last reset, the path shift records accumulated positive stage gaps, and
the path slope is cumulative opponent survival. -/
theorem quittingFiniteDynamicDebt_eq_pathCoefficients_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0)
    (start fuel : ℕ) (hwindow : start + fuel ≤ bound) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt start fuel =
      (⟨Math.MaxAffineTransport.Label.pathFloor
          (quittingDynamicDebtLabelList reward roots who prescribed start fuel),
        Math.MaxAffineTransport.Label.pathShift
          (quittingDynamicDebtLabelList reward roots who prescribed start fuel),
        Math.MaxAffineTransport.Label.pathSlope
          (quittingDynamicDebtLabelList reward roots who prescribed start fuel)⟩ :
        Math.MaxAffineTransport.Label).apply terminalDebt := by
  rw [quittingFiniteDynamicDebt_eq_compList_apply
    reward roots who prescribed hprescribed hterminalDebt bound hresidual
      start fuel hwindow]
  exact Math.MaxAffineTransport.Label.apply_compList_eq_pathCoefficients
    (fun label hlabel ↦ quittingDynamicDebtLabelList_slope_nonneg
      reward roots who prescribed start fuel label hlabel) terminalDebt

/-- The unrolled exact dynamic-debt law: the transported terminal debt
minus the accumulated survival-weighted positive stage gaps, floored at
zero.  Only residual-zero on the traversed window `[start, start + fuel)`
is used, matching the localized hypothesis of the coarse survival-weighted
bound.

`HEADLINE` — all debt is transported terminal debt, less credit spendable
only where a coordinate is pure.  **The hypothesis `0 ≤ terminalDebt` is not
removable**: it fails on genuine absorbing cycles, so this law must not be
used to compute cyclic mismatch.  See `QuittingCycleMismatchContraction` for
the sign-free route and for the counterexample. -/
theorem quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel =
        max 0
          (quittingOpponentSurvivalWeight roots who start fuel * terminalDebt -
            ∑ offset ∈ Finset.range fuel,
              quittingOpponentSurvivalWeight roots who start offset *
                max 0 (quittingStageGap reward roots who prescribed
                  (start + offset))) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _
      simp only [quittingFiniteDynamicDebt_zero, quittingOpponentSurvivalWeight,
        Finset.range_zero, Finset.prod_empty, Finset.sum_empty, one_mul, sub_zero]
      exact (max_eq_right hterminalDebt).symm
  | succ fuel ih =>
      intro hwindow
      have hstart : start < bound := by omega
      have htailWindow : start + 1 + fuel ≤ bound := by omega
      have hres_start := hresidual start hstart
      have hstep := quittingFiniteDynamicDebt_succ_eq_max_zero_stageGap
        reward roots who prescribed hprescribed hterminalDebt start fuel hres_start
      rw [hstep, ih (start + 1) htailWindow]
      have hq_nonneg : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      -- Move the nonnegative continue mass inside the inner floor, then
      -- absorb the nested floor using `max_zero_sub_of_nonneg`.
      rw [mul_max_of_nonneg _ _ hq_nonneg, mul_zero,
        max_zero_sub_of_nonneg (le_max_left 0
          (quittingStageGap reward roots who prescribed start))]
      congr 1
      have hW : quittingOpponentSurvivalWeight roots who start (fuel + 1) =
          quittingFixedOpponentsContinueMass roots who start *
            quittingOpponentSurvivalWeight roots who (start + 1) fuel := by
        rw [show fuel + 1 = 1 + fuel by omega, quittingOpponentSurvivalWeight_add]
        have hone : quittingOpponentSurvivalWeight roots who start 1 =
            quittingFixedOpponentsContinueMass roots who start := by
          simp [quittingOpponentSurvivalWeight]
        rw [hone]
      have hS : (∑ offset ∈ Finset.range (fuel + 1),
            quittingOpponentSurvivalWeight roots who start offset *
              max 0 (quittingStageGap reward roots who prescribed (start + offset))) =
          max 0 (quittingStageGap reward roots who prescribed start) +
            quittingFixedOpponentsContinueMass roots who start *
              ∑ offset ∈ Finset.range fuel,
                quittingOpponentSurvivalWeight roots who (start + 1) offset *
                  max 0 (quittingStageGap reward roots who prescribed
                    (start + 1 + offset)) := by
        rw [Finset.sum_range_succ' (fun offset =>
          quittingOpponentSurvivalWeight roots who start offset *
            max 0 (quittingStageGap reward roots who prescribed (start + offset)))]
        have hzero : quittingOpponentSurvivalWeight roots who start 0 = 1 := by
          simp [quittingOpponentSurvivalWeight]
        rw [hzero, one_mul, add_comm]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        have hshift : quittingOpponentSurvivalWeight roots who start (offset + 1) =
            quittingFixedOpponentsContinueMass roots who start *
              quittingOpponentSurvivalWeight roots who (start + 1) offset := by
          rw [show offset + 1 = 1 + offset by omega, quittingOpponentSurvivalWeight_add]
          have hone : quittingOpponentSurvivalWeight roots who start 1 =
              quittingFixedOpponentsContinueMass roots who start := by
            simp [quittingOpponentSurvivalWeight]
          rw [hone]
        rw [hshift, show start + (offset + 1) = start + 1 + offset by omega]
        ring
      rw [hW, hS]
      ring

/-- The unrolled closed form implies the coarse survival-weighted bound of
`quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on`,
since the accumulated stage-gap sum being subtracted is nonnegative.  This
is a direct coefficient consequence of the exact reflected action. -/
theorem quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on_of_transportLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel ≤
        quittingOpponentSurvivalWeight roots who start fuel * terminalDebt := by
  intro start fuel hwindow
  rw [quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
    reward roots who prescribed hprescribed hterminalDebt bound hresidual
    start fuel hwindow]
  have hsum_nonneg :
      0 ≤ ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          max 0 (quittingStageGap reward roots who prescribed (start + offset)) := by
    apply Finset.sum_nonneg
    intro offset _
    exact mul_nonneg (quittingOpponentSurvivalWeight_nonneg roots who start offset)
      (le_max_left 0 _)
  have hweight_nonneg : 0 ≤ quittingOpponentSurvivalWeight roots who start fuel :=
    quittingOpponentSurvivalWeight_nonneg roots who start fuel
  apply max_le
  · exact mul_nonneg hweight_nonneg hterminalDebt
  · linarith

/-- Exact reflected transport never exceeds its nonnegative terminal debt. -/
theorem quittingFiniteDynamicDebt_le_terminalDebt_of_transportLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0)
    (start fuel : ℕ) (hwindow : start + fuel ≤ bound) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start fuel ≤ terminalDebt := by
  have htransport :=
    quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on_of_transportLaw
      reward roots who prescribed hprescribed hterminalDebt bound hresidual
        start fuel hwindow
  have hweight := quittingOpponentSurvivalWeight_le_one roots who start fuel
  have hweightNonneg := quittingOpponentSurvivalWeight_nonneg roots who start fuel
  nlinarith

/-- A positive terminal debt returns unchanged across a residual-zero window
exactly when every traversed opponent-survival factor is one and every stage
gap is nonpositive. -/
theorem quittingFiniteDynamicDebt_eq_terminalDebt_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 < terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      (quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel = terminalDebt ↔
        ∀ offset < fuel,
          quittingFixedOpponentsContinueMass roots who (start + offset) = 1 ∧
            quittingStageGap reward roots who prescribed (start + offset) ≤ 0) := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      intro hwindow
      have hstart : start < bound := by omega
      have htailWindow : start + 1 + fuel ≤ bound := by omega
      let nextDebt := quittingFiniteDynamicDebt reward roots who prescribed
        terminalDebt (start + 1) fuel
      have hnextNonneg : 0 ≤ nextDebt :=
        quittingFiniteDynamicDebt_nonneg reward roots who prescribed
          hprescribed hterminalDebt.le (start + 1) fuel
      have hnextLe : nextDebt ≤ terminalDebt := by
        exact quittingFiniteDynamicDebt_le_terminalDebt_of_transportLaw
          reward roots who prescribed hprescribed hterminalDebt.le bound hresidual
            (start + 1) fuel htailWindow
      have hstep : quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start (fuel + 1) =
        (quittingDynamicDebtLabel reward roots who prescribed start).apply nextDebt := by
        exact quittingFiniteDynamicDebt_succ_eq_label_apply
          reward roots who prescribed hprescribed hterminalDebt.le start fuel
            (hresidual start hstart)
      constructor
      · intro hreturn
        have hcurrentLeNext :
            quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
                start (fuel + 1) ≤ nextDebt := by
          rw [hstep]
          exact quittingDynamicDebtLabel_apply_le_self
            reward roots who prescribed start hnextNonneg
        have hnextEq : nextDebt = terminalDebt := by
          rw [hreturn] at hcurrentLeNext
          exact le_antisymm hnextLe hcurrentLeNext
        have hstage :
            quittingFixedOpponentsContinueMass roots who start = 1 ∧
              quittingStageGap reward roots who prescribed start ≤ 0 := by
          apply (quittingDynamicDebtLabel_apply_eq_self_iff_of_pos
            reward roots who prescribed start hterminalDebt).mp
          calc
            (quittingDynamicDebtLabel reward roots who prescribed start).apply
                terminalDebt =
              (quittingDynamicDebtLabel reward roots who prescribed start).apply
                nextDebt := congrArg _ hnextEq.symm
            _ = quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
                start (fuel + 1) := hstep.symm
            _ = terminalDebt := hreturn
        have htail := (ih (start + 1) htailWindow).mp hnextEq
        intro offset hoffset
        cases offset with
        | zero => simpa using hstage
        | succ offset =>
            have htailOffset := htail offset (by omega)
            rw [show start + (offset + 1) = start + 1 + offset by omega]
            exact htailOffset
      · intro hphases
        have hstage := hphases 0 (by omega)
        simp only [Nat.add_zero] at hstage
        have htailPhases : ∀ offset < fuel,
            quittingFixedOpponentsContinueMass roots who (start + 1 + offset) = 1 ∧
              quittingStageGap reward roots who prescribed (start + 1 + offset) ≤ 0 := by
          intro offset hoffset
          have hphase := hphases (offset + 1) (by omega)
          rw [show start + 1 + offset = start + (offset + 1) by omega]
          exact hphase
        have hnextEq : nextDebt = terminalDebt :=
          (ih (start + 1) htailWindow).mpr htailPhases
        rw [hstep, hnextEq]
        exact (quittingDynamicDebtLabel_apply_eq_self_iff_of_pos
          reward roots who prescribed start hterminalDebt).mpr hstage

/-! ## Corollaries of the transport law -/

/-- **Fence-free equality.**  If every stage gap on the traversed window is
nonpositive, the positive-part floor in the transport law never activates,
and the exact dynamic debt equals the plain transported terminal debt.
This strengthens the general `≤` bound to an equality. -/
theorem quittingFiniteDynamicDebt_eq_survivalWeight_mul_terminalDebt_of_stageGap_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0)
    (hgap : ∀ time, time < bound →
      quittingStageGap reward roots who prescribed time ≤ 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel =
        quittingOpponentSurvivalWeight roots who start fuel * terminalDebt := by
  intro start fuel hwindow
  rw [quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
    reward roots who prescribed hprescribed hterminalDebt bound hresidual
    start fuel hwindow]
  have hsum_zero :
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          max 0 (quittingStageGap reward roots who prescribed (start + offset))) = 0 := by
    apply Finset.sum_eq_zero
    intro offset hoffset
    have hle : quittingStageGap reward roots who prescribed (start + offset) ≤ 0 :=
      hgap (start + offset) (by
        have := Finset.mem_range.mp hoffset
        omega)
    rw [max_eq_left hle, mul_zero]
  rw [hsum_zero, sub_zero]
  exact max_eq_right (mul_nonneg
    (quittingOpponentSurvivalWeight_nonneg roots who start fuel) hterminalDebt)

/-- **Monotone in the terminal debt.**  Raising the terminal debt (while
keeping it nonnegative) never decreases the exact dynamic debt: the
subtracted stage-gap sum does not depend on the terminal debt, and the
transported term scales monotonically with it. -/
theorem quittingFiniteDynamicDebt_mono_terminalDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {terminalDebt terminalDebt' : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (hle : terminalDebt ≤ terminalDebt')
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel ≤
        quittingFiniteDynamicDebt reward roots who prescribed terminalDebt'
          start fuel := by
  intro start fuel hwindow
  rw [quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
        reward roots who prescribed hprescribed hterminalDebt bound hresidual
        start fuel hwindow,
      quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
        reward roots who prescribed hprescribed (hterminalDebt.trans hle) bound hresidual
        start fuel hwindow]
  exact max_le_max le_rfl (sub_le_sub_right
    (mul_le_mul_of_nonneg_left hle
      (quittingOpponentSurvivalWeight_nonneg roots who start fuel)) _)

/-- **Zero terminal debt gives zero debt.**  With no terminal debt to
transport, the transported term vanishes and the subtracted stage-gap sum
is nonnegative, so the outer floor collapses the whole expression to
zero. -/
theorem quittingFiniteDynamicDebt_eq_zero_of_terminalDebt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (bound : ℕ)
    (hresidual : ∀ time, time < bound →
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0) :
    ∀ start fuel, start + fuel ≤ bound →
      quittingFiniteDynamicDebt reward roots who prescribed 0 start fuel = 0 := by
  intro start fuel hwindow
  rw [quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
    reward roots who prescribed hprescribed le_rfl bound hresidual start fuel hwindow]
  have hsum_nonneg :
      0 ≤ ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          max 0 (quittingStageGap reward roots who prescribed (start + offset)) :=
    Finset.sum_nonneg fun offset _ => mul_nonneg
      (quittingOpponentSurvivalWeight_nonneg roots who start offset) (le_max_left 0 _)
  rw [mul_zero, zero_sub]
  exact max_eq_left (by linarith)

/-- **The stage gap ignores its own coordinate.**  `quittingStageGap` at
`time` reads `roots time` only through `Function.update (roots time) who _`,
which overwrites the `who` marginal before it is ever read.  Consequently
replacing `roots time who` by an arbitrary `ρ` leaves the stage gap at
`time` unchanged. -/
theorem quittingStageGap_update_own_marginal_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) (ρ : PMF Bool) :
    quittingStageGap reward
        (Function.update roots time (Function.update (roots time) who ρ))
        who prescribed time =
      quittingStageGap reward roots who prescribed time := by
  simp [quittingStageGap, quittingFixedOpponentsQuitValue,
    quittingFixedOpponentsContinueReward, quittingFixedOpponentsContinueMass,
    Function.update_idem]

end GameTheory
