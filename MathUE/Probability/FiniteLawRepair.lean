/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Finite-law support repair

A nonnegative finite law can be supported on a chosen nonempty good set by
moving all mass outside that set to one selected anchor. The repair preserves
total mass, and its exact L1 cost is twice the mass removed from the bad set.
-/

noncomputable section

namespace Math.Probability.FiniteLawRepair

open scoped BigOperators

/-! ## Finite-law repair -/

section LawRepair

variable {Outcome : Type} [Fintype Outcome] [DecidableEq Outcome]

/-- Mass outside a chosen good set. -/
def badMass (law : Outcome → ℝ) (good : Finset Outcome) : ℝ :=
  ∑ outcome ∈ goodᶜ, law outcome

/-- Move all bad mass to one fixed good anchor. -/
def repairLaw (law : Outcome → ℝ) (good : Finset Outcome)
    (anchor : Outcome) : Outcome → ℝ := fun outcome ↦
  if outcome = anchor then law outcome + badMass law good
  else if outcome ∈ good then law outcome else 0

theorem badMass_nonneg (law : Outcome → ℝ) (good : Finset Outcome)
    (hlaw : ∀ outcome, 0 ≤ law outcome) :
    0 ≤ badMass law good := by
  exact Finset.sum_nonneg fun outcome _ ↦ hlaw outcome

theorem repairLaw_nonneg (law : Outcome → ℝ) (good : Finset Outcome)
    (anchor : Outcome) (hlaw : ∀ outcome, 0 ≤ law outcome) :
    ∀ outcome, 0 ≤ repairLaw law good anchor outcome := by
  intro outcome
  unfold repairLaw
  split_ifs
  · exact add_nonneg (hlaw outcome) (badMass_nonneg law good hlaw)
  · exact hlaw outcome
  · exact le_rfl

theorem repairLaw_supported (law : Outcome → ℝ) (good : Finset Outcome)
    {anchor outcome : Outcome} (hanchor : anchor ∈ good)
    (houtcome : outcome ∉ good) :
    repairLaw law good anchor outcome = 0 := by
  unfold repairLaw
  have hne : outcome ≠ anchor := fun heq ↦ houtcome (heq ▸ hanchor)
  simp [hne, houtcome]

/-- The repaired law has the same total mass. -/
theorem sum_repairLaw (law : Outcome → ℝ) (good : Finset Outcome)
    {anchor : Outcome} (hanchor : anchor ∈ good) :
    ∑ outcome, repairLaw law good anchor outcome = ∑ outcome, law outcome := by
  classical
  have hsplit :
      (∑ outcome ∈ good, law outcome) + badMass law good =
        ∑ outcome, law outcome := by
    simpa [badMass] using good.sum_add_sum_compl law
  calc
    (∑ outcome, repairLaw law good anchor outcome) =
        ∑ outcome, if outcome ∈ good then
          repairLaw law good anchor outcome else 0 := by
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases hgood : outcome ∈ good
      · simp [hgood]
      · have hne : outcome ≠ anchor := fun heq ↦ hgood (heq ▸ hanchor)
        simp [hgood, hne, repairLaw]
    _ = ∑ outcome ∈ good, repairLaw law good anchor outcome := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ outcome ∈ good,
        (law outcome + if outcome = anchor then badMass law good else 0) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      by_cases heq : outcome = anchor <;>
        simp [repairLaw, houtcome, heq]
    _ = (∑ outcome ∈ good, law outcome) + badMass law good := by
      rw [Finset.sum_add_distrib]
      simp [hanchor]
    _ = ∑ outcome, law outcome := hsplit

/-- Exact `L¹` cost of repairing a nonnegative law.  Consequently the
usual total-variation distance (half the displayed sum) is exactly the bad
mass. -/
theorem sum_abs_repairLaw_sub
    (law : Outcome → ℝ) (good : Finset Outcome)
    {anchor : Outcome} (hanchor : anchor ∈ good)
    (hlaw : ∀ outcome, 0 ≤ law outcome) :
    (∑ outcome, |repairLaw law good anchor outcome - law outcome|) =
      2 * badMass law good := by
  classical
  have hbad0 := badMass_nonneg law good hlaw
  have hpoint : ∀ outcome,
      |repairLaw law good anchor outcome - law outcome| =
        if outcome = anchor then badMass law good
        else if outcome ∈ good then 0 else law outcome := by
    intro outcome
    by_cases hanchorEq : outcome = anchor
    · subst outcome
      simp [repairLaw, abs_of_nonneg hbad0]
    · by_cases hgood : outcome ∈ good
      · simp [repairLaw, hanchorEq, hgood]
      · simp [repairLaw, hanchorEq, hgood, abs_of_nonneg (hlaw outcome)]
  calc
    (∑ outcome, |repairLaw law good anchor outcome - law outcome|) =
        ∑ outcome,
          (if outcome = anchor then badMass law good
          else if outcome ∈ good then 0 else law outcome) := by
      apply Finset.sum_congr rfl
      intro outcome _
      exact hpoint outcome
    _ = badMass law good + ∑ outcome ∈ goodᶜ, law outcome := by
      let rest : Outcome → ℝ := fun outcome ↦
        if outcome ∈ good then 0 else law outcome
      have hsplitAnchor :
          (∑ outcome,
              if outcome = anchor then badMass law good
              else if outcome ∈ good then 0 else law outcome) =
            badMass law good +
              ∑ outcome ∈ Finset.univ.erase anchor, rest outcome := by
        let expression : Outcome → ℝ := fun outcome ↦
          if outcome = anchor then badMass law good
          else if outcome ∈ good then 0 else law outcome
        have hsplit := Finset.sum_erase_add Finset.univ expression
          (Finset.mem_univ anchor)
        have hanchorValue : expression anchor = badMass law good := by
          simp [expression]
        have heraseExpression :
            (∑ outcome ∈ Finset.univ.erase anchor, expression outcome) =
              ∑ outcome ∈ Finset.univ.erase anchor, rest outcome := by
          apply Finset.sum_congr rfl
          intro outcome houtcome
          have hne := Finset.ne_of_mem_erase houtcome
          simp [expression, rest, hne]
        change (∑ outcome, expression outcome) = _
        rw [← hsplit, hanchorValue, heraseExpression, add_comm]
      rw [hsplitAnchor]
      congr 1
      have herase :
          (∑ outcome ∈ Finset.univ.erase anchor, rest outcome) =
            ∑ outcome, rest outcome := by
        have h := Finset.sum_erase_add Finset.univ rest
          (Finset.mem_univ anchor)
        have hzero : rest anchor = 0 := by simp [rest, hanchor]
        rw [hzero, add_zero] at h
        exact h
      rw [herase]
      unfold rest
      calc
        (∑ outcome, if outcome ∈ good then 0 else law outcome) =
            ∑ outcome, if outcome ∈ goodᶜ then law outcome else 0 := by
          apply Finset.sum_congr rfl
          intro outcome _
          simp
        _ = ∑ outcome ∈ goodᶜ, law outcome := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext outcome
            simp
          · intro outcome _
            rfl
    _ = 2 * badMass law good := by
      simp [badMass]
      ring

/-- Full finite-law repair package. The conclusion is a same-mass law
supported on `good` at L1 cost exactly twice `badMass`. -/
theorem exists_supported_repair
    (law : Outcome → ℝ) (good : Finset Outcome)
    {anchor : Outcome} (hanchor : anchor ∈ good)
    (hlaw : ∀ outcome, 0 ≤ law outcome) :
    ∃ repaired : Outcome → ℝ,
      (∀ outcome, 0 ≤ repaired outcome) ∧
      (∀ outcome, outcome ∉ good → repaired outcome = 0) ∧
      (∑ outcome, repaired outcome = ∑ outcome, law outcome) ∧
      (∑ outcome, |repaired outcome - law outcome|) =
        2 * badMass law good := by
  exact ⟨repairLaw law good anchor,
    repairLaw_nonneg law good anchor hlaw,
    fun outcome houtcome ↦ repairLaw_supported law good hanchor houtcome,
    sum_repairLaw law good hanchor,
    sum_abs_repairLaw_sub law good hanchor hlaw⟩

end LawRepair

end Math.Probability.FiniteLawRepair
