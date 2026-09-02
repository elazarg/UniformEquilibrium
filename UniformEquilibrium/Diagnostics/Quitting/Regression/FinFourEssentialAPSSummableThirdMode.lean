/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Regression.FinFourEssentialAPSCarrier
import UniformEquilibrium.Quitting.EssentialAPS.InfiniteContraction
import UniformEquilibrium.Quitting.Chronology.SummableExactTailTerminalGap
import MathUE.SummableChargeSurvival

/-!
# The summable positive third mode in the four-player essential-APS carrier

This file executes the forced carrier circuit literally.  Its singleton mass
is positive at every date from a positive start but summable, its values tend
to the common singleton baseline, and its exact Bellman annotation retains a
nonzero survival-weighted residual over the terminal payoff.  It also excludes
both raw-row and normalized-row nonnegative homogeneous balances.

The displayed roots are Bellman roots only.  No Nash property or source
chronology is asserted.
-/

noncomputable section

namespace GameTheory
namespace FinFourEssentialAPSSummableThirdMode

open Filter Math.Probability Set StochasticGame
open FinFourEssentialAPSCarrier

/-- Total displacement from the common singleton baseline on a carrier fiber. -/
def carrierDisplacement (current : Payoff Player) : ℝ :=
  (current 0 - baseline 0) + (current 1 - baseline 1) +
    (current 2 - baseline 2)

@[simp] theorem carrierDisplacement_valueZero (x : ℝ) :
    carrierDisplacement (valueZero x) = x := by
  norm_num [carrierDisplacement, valueZero, baseline]

@[simp] theorem carrierDisplacement_valueOne (y : ℝ) :
    carrierDisplacement (valueOne y) = y := by
  norm_num [carrierDisplacement, valueOne, baseline]

@[simp] theorem carrierDisplacement_valueTwo (z : ℝ) :
    carrierDisplacement (valueTwo z) = z := by
  norm_num [carrierDisplacement, valueTwo, baseline]

theorem valueZero_eq_baseline_iff (x : ℝ) : valueZero x = baseline ↔ x = 0 := by
  constructor
  · intro heq
    have hcoordinate := congrFun heq (1 : Player)
    simpa [valueZero, baseline] using hcoordinate
  · rintro rfl
    funext who
    simp [valueZero, baseline]

theorem valueOne_eq_baseline_iff (y : ℝ) : valueOne y = baseline ↔ y = 0 := by
  constructor
  · intro heq
    have hcoordinate := congrFun heq (2 : Player)
    simpa [valueOne, baseline] using hcoordinate
  · rintro rfl
    funext who
    simp [valueOne, baseline]

theorem valueTwo_eq_baseline_iff (z : ℝ) : valueTwo z = baseline ↔ z = 0 := by
  constructor
  · intro heq
    have hcoordinate := congrFun heq (0 : Player)
    simpa [valueTwo, baseline] using hcoordinate
  · rintro rfl
    funext who
    simp [valueTwo, baseline]

/-- Every Flesch-faithful edge of any infinite run in this greatest family is
one of the three displayed coordinate recurrences.  The explicit edge
hypothesis rules out the zero-mass self-loop allowed by the bare run type. -/
theorem fleschFaithful_run_forced_step
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) (time : ℕ) :
    (owner time = 0 ∧ ∃ x ∈ Icc (0 : ℝ) (1 / 2),
      value time = valueZero x ∧ mass time = massZero x ∧
        owner (time + 1) = 1 ∧
          value (time + 1) = valueOne (nextOneCoordinate x)) ∨
    (owner time = 1 ∧ ∃ y ∈ Icc (0 : ℝ) (1 / 3),
      value time = valueOne y ∧ mass time = massOne y ∧
        owner (time + 1) = 2 ∧
          value (time + 1) = valueTwo (nextTwoCoordinate y)) ∨
    (owner time = 2 ∧ ∃ z ∈ Icc (0 : ℝ) (1 / 5),
      value time = valueTwo z ∧ mass time = massTwo z ∧
        owner (time + 1) = 0 ∧
          value (time + 1) = valueZero (nextZeroCoordinate z)) := by
  have hcurrent := hrun.2.1 time
  rw [greatestFamily_eq_carrier] at hcurrent
  have hnext : value (time + 1) ∈
      quittingEssentialAPSSuccessorSet completionAReward
        (quittingEssentialAPSGreatestFamily completionAReward carrier)
        (owner time) :=
    ⟨owner (time + 1), hedge time, hrun.2.1 (time + 1)⟩
  have harc := (hrun.2.2 time).2
  have hedgeTime := hedge time
  generalize howner : owner time = currentOwner at hcurrent hnext harc hedgeTime ⊢
  fin_cases currentOwner
  · have hcurrentZero : value time ∈ carrier 0 := by simpa using hcurrent
    rw [carrier_zero] at hcurrentZero
    rcases hcurrentZero with ⟨x, hx, hvalue⟩
    have hnextZero : value (time + 1) ∈
        quittingEssentialAPSSuccessorSet completionAReward
          (quittingEssentialAPSGreatestFamily completionAReward carrier) 0 := by
      simpa using hnext
    have harcZero : value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward completionAReward 0) (value (time + 1)) := by
      simpa using harc
    have hnextOwner : owner (time + 1) = 1 := by
      exact (fleschSuccessor_zero_iff _).1 (by simpa using hedgeTime)
    obtain ⟨hmass, hvalueNext⟩ := forced_segment_zero hx
      hnextZero (by simpa [← hvalue] using harcZero)
    left
    norm_num at hx ⊢
    exact ⟨x, hx, hvalue.symm, hmass, hnextOwner, hvalueNext⟩
  · have hcurrentOne : value time ∈ carrier 1 := by simpa using hcurrent
    rw [carrier_one] at hcurrentOne
    rcases hcurrentOne with ⟨y, hy, hvalue⟩
    have hnextOne : value (time + 1) ∈
        quittingEssentialAPSSuccessorSet completionAReward
          (quittingEssentialAPSGreatestFamily completionAReward carrier) 1 := by
      simpa using hnext
    have harcOne : value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward completionAReward 1) (value (time + 1)) := by
      simpa using harc
    have hnextOwner : owner (time + 1) = 2 := by
      exact (fleschSuccessor_one_iff _).1 (by simpa using hedgeTime)
    obtain ⟨hmass, hvalueNext⟩ := forced_segment_one hy
      hnextOne (by simpa [← hvalue] using harcOne)
    right
    left
    norm_num at hy ⊢
    exact ⟨y, hy, hvalue.symm, hmass, hnextOwner, hvalueNext⟩
  · have hcurrentTwo : value time ∈ carrier 2 := by simpa using hcurrent
    rw [carrier_two] at hcurrentTwo
    rcases hcurrentTwo with ⟨z, hz, hvalue⟩
    have hnextTwo : value (time + 1) ∈
        quittingEssentialAPSSuccessorSet completionAReward
          (quittingEssentialAPSGreatestFamily completionAReward carrier) 2 := by
      simpa using hnext
    have harcTwo : value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward completionAReward 2) (value (time + 1)) := by
      simpa using harc
    have hnextOwner : owner (time + 1) = 0 := by
      exact (fleschSuccessor_two_iff _).1 (by simpa using hedgeTime)
    obtain ⟨hmass, hvalueNext⟩ := forced_segment_two hz
      hnextTwo (by simpa [← hvalue] using harcTwo)
    right
    right
    norm_num at hz ⊢
    exact ⟨Fin.ext rfl, z, hz, hvalue.symm, hmass, hnextOwner, hvalueNext⟩
  · have hcurrentThree : value time ∈ carrier 3 := by exact hcurrent
    simp only [carrier_three, Set.mem_empty_iff_false] at hcurrentThree

private theorem nextOneCoordinate_le_two_thirds_mul {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    nextOneCoordinate x ≤ (2 / 3 : ℝ) * x := by
  have hdenom : 0 < 2 - x := by linarith [hx.2]
  rw [nextOneCoordinate, div_le_iff₀ hdenom]
  nlinarith [hx.1, hx.2]

private theorem nextTwoCoordinate_le_two_thirds_mul {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) (1 / 3)) :
    nextTwoCoordinate y ≤ (2 / 3 : ℝ) * y := by
  have hdenom : 0 < 2 - y := by linarith [hy.2]
  rw [nextTwoCoordinate, div_le_iff₀ hdenom]
  nlinarith [hy.1, hy.2]

private theorem nextZeroCoordinate_le_two_thirds_mul {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) (1 / 5)) :
    nextZeroCoordinate z ≤ (2 / 3 : ℝ) * z := by
  have hdenom : 0 < 2 - z := by linarith [hz.2]
  rw [nextZeroCoordinate, div_le_iff₀ hdenom]
  nlinarith [hz.1, hz.2]

private theorem fleschFaithful_run_step_preserves_nonbaseline
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) (time : ℕ)
    (hne : value time ≠ baseline) :
    0 < mass time ∧ value (time + 1) ≠ baseline := by
  rcases fleschFaithful_run_forced_step hrun hedge time with hzero | hone | htwo
  · rcases hzero.2 with ⟨x, hx, hvalue, hmass, _hownerNext, hvalueNext⟩
    have hxne : x ≠ 0 := by
      intro hxzero
      apply hne
      rw [hvalue, valueZero_eq_baseline_iff]
      exact hxzero
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
    have hdenom : 0 < 2 - x := by linarith [hx.2]
    constructor
    · rw [hmass, massZero]
      exact div_pos hxpos (by norm_num)
    · rw [hvalueNext]
      exact mt (valueOne_eq_baseline_iff _).mp
        (ne_of_gt (div_pos hxpos hdenom))
  · rcases hone.2 with ⟨y, hy, hvalue, hmass, _hownerNext, hvalueNext⟩
    have hyne : y ≠ 0 := by
      intro hyzero
      apply hne
      rw [hvalue, valueOne_eq_baseline_iff]
      exact hyzero
    have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hyne)
    have hdenom : 0 < 2 - y := by linarith [hy.2]
    constructor
    · rw [hmass, massOne]
      exact div_pos hypos (by norm_num)
    · rw [hvalueNext]
      exact mt (valueTwo_eq_baseline_iff _).mp
        (ne_of_gt (div_pos hypos hdenom))
  · rcases htwo.2 with ⟨z, hz, hvalue, hmass, _hownerNext, hvalueNext⟩
    have hzne : z ≠ 0 := by
      intro hzzero
      apply hne
      rw [hvalue, valueTwo_eq_baseline_iff]
      exact hzzero
    have hzpos : 0 < z := lt_of_le_of_ne hz.1 (Ne.symm hzne)
    have hdenom : 0 < 2 - z := by linarith [hz.2]
    constructor
    · rw [hmass, massTwo]
      exact div_pos hzpos (by norm_num)
    · rw [hvalueNext]
      exact mt (valueZero_eq_baseline_iff _).mp
        (ne_of_gt (div_pos hzpos hdenom))

/-- A Flesch-faithful run from a nonbaseline carrier point never reaches the
baseline false-progress state. -/
theorem fleschFaithful_run_value_ne_baseline
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) (hinitial : initial ≠ baseline) :
    ∀ time, value time ≠ baseline := by
  intro time
  induction time with
  | zero => simpa [hrun.1] using hinitial
  | succ time ih =>
      exact (fleschFaithful_run_step_preserves_nonbaseline
        hrun hedge time ih).2

/-- Every mass of a Flesch-faithful run from a nonbaseline carrier point is
strictly positive. -/
theorem fleschFaithful_run_mass_positive
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) (hinitial : initial ≠ baseline) :
    ∀ time, 0 < mass time := fun time =>
  (fleschFaithful_run_step_preserves_nonbaseline hrun hedge time
    (fleschFaithful_run_value_ne_baseline hrun hedge hinitial time)).1

/-- Along every Flesch-faithful run, the singleton mass is exactly half of
the current carrier displacement. -/
theorem fleschFaithful_run_mass_eq_half_displacement
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) (time : ℕ) :
    mass time = carrierDisplacement (value time) / 2 := by
  rcases fleschFaithful_run_forced_step hrun hedge time with hzero | hone | htwo
  · rcases hzero.2 with ⟨x, _hx, hvalue, hmass, _hownerNext, _hvalueNext⟩
    rw [hvalue, hmass, carrierDisplacement_valueZero, massZero]
  · rcases hone.2 with ⟨y, _hy, hvalue, hmass, _hownerNext, _hvalueNext⟩
    rw [hvalue, hmass, carrierDisplacement_valueOne, massOne]
  · rcases htwo.2 with ⟨z, _hz, hvalue, hmass, _hownerNext, _hvalueNext⟩
    rw [hvalue, hmass, carrierDisplacement_valueTwo, massTwo]

/-- Every Flesch-faithful step contracts total carrier displacement by at
least the uniform factor `2 / 3`. -/
theorem fleschFaithful_run_displacement_next_le_two_thirds
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) (time : ℕ) :
    carrierDisplacement (value (time + 1)) ≤
      (2 / 3 : ℝ) * carrierDisplacement (value time) := by
  rcases fleschFaithful_run_forced_step hrun hedge time with hzero | hone | htwo
  · rcases hzero.2 with ⟨x, hx, hvalue, _hmass, _hownerNext, hvalueNext⟩
    rw [hvalue, hvalueNext, carrierDisplacement_valueZero,
      carrierDisplacement_valueOne]
    exact nextOneCoordinate_le_two_thirds_mul hx
  · rcases hone.2 with ⟨y, hy, hvalue, _hmass, _hownerNext, hvalueNext⟩
    rw [hvalue, hvalueNext, carrierDisplacement_valueOne,
      carrierDisplacement_valueTwo]
    exact nextTwoCoordinate_le_two_thirds_mul hy
  · rcases htwo.2 with ⟨z, hz, hvalue, _hmass, _hownerNext, hvalueNext⟩
    rw [hvalue, hvalueNext, carrierDisplacement_valueTwo,
      carrierDisplacement_valueZero]
    exact nextZeroCoordinate_le_two_thirds_mul hz

/-- Every value on any run in the greatest family has nonnegative carrier
displacement. -/
theorem run_carrierDisplacement_nonneg
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value) (time : ℕ) :
    0 ≤ carrierDisplacement (value time) := by
  have hcurrent := hrun.2.1 time
  rw [greatestFamily_eq_carrier] at hcurrent
  generalize howner : owner time = currentOwner at hcurrent
  fin_cases currentOwner
  · have hcurrentZero : value time ∈ carrier 0 := by exact hcurrent
    rw [carrier_zero] at hcurrentZero
    rcases hcurrentZero with ⟨x, hx, hvalue⟩
    rw [← hvalue, carrierDisplacement_valueZero]
    exact hx.1
  · have hcurrentOne : value time ∈ carrier 1 := by exact hcurrent
    rw [carrier_one] at hcurrentOne
    rcases hcurrentOne with ⟨y, hy, hvalue⟩
    rw [← hvalue, carrierDisplacement_valueOne]
    exact hy.1
  · have hcurrentTwo : value time ∈ carrier 2 := by exact hcurrent
    rw [carrier_two] at hcurrentTwo
    rcases hcurrentTwo with ⟨z, hz, hvalue⟩
    rw [← hvalue, carrierDisplacement_valueTwo]
    exact hz.1
  · have hcurrentThree : value time ∈ carrier 3 := by exact hcurrent
    simp only [carrier_three, Set.mem_empty_iff_false] at hcurrentThree

/-- Universal geometric decay of displacement for every Flesch-faithful run. -/
theorem fleschFaithful_run_displacement_le_geometric
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) :
    ∀ time, carrierDisplacement (value time) ≤
      carrierDisplacement initial * (2 / 3 : ℝ) ^ time := by
  intro time
  induction time with
  | zero => simp [hrun.1]
  | succ time ih =>
      calc
        carrierDisplacement (value (time + 1)) ≤
            (2 / 3 : ℝ) * carrierDisplacement (value time) :=
          fleschFaithful_run_displacement_next_le_two_thirds hrun hedge time
        _ ≤ (2 / 3 : ℝ) *
            (carrierDisplacement initial * (2 / 3 : ℝ) ^ time) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = carrierDisplacement initial * (2 / 3 : ℝ) ^ (time + 1) := by
          rw [pow_succ]
          ring

/-- Every Flesch-faithful run has finite total singleton mass, even when all
of its masses are positive. -/
theorem summable_fleschFaithful_run_mass
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) : Summable mass := by
  exact Summable.of_nonneg_of_le
    (fun time => (hrun.2.2 time).1.1)
    (fun time => by
      rw [fleschFaithful_run_mass_eq_half_displacement hrun hedge time]
      have hbound :=
        fleschFaithful_run_displacement_le_geometric hrun hedge time
      have hpower : 0 ≤ (2 / 3 : ℝ) ^ time := pow_nonneg (by norm_num) _
      nlinarith)
    ((summable_geometric_of_norm_lt_one (by norm_num :
      ‖(2 / 3 : ℝ)‖ < 1)).mul_left (carrierDisplacement initial / 2))

/-- Coordinatewise distance from the baseline is bounded by the carrier
displacement at every date of any greatest-family run. -/
theorem abs_run_value_sub_baseline_le_carrierDisplacement
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value) (who : Player) (time : ℕ) :
    |value time who - baseline who| ≤ carrierDisplacement (value time) := by
  have hcurrent := hrun.2.1 time
  rw [greatestFamily_eq_carrier] at hcurrent
  generalize howner : owner time = currentOwner at hcurrent
  fin_cases currentOwner
  · have hcurrentZero : value time ∈ carrier 0 := by exact hcurrent
    rw [carrier_zero] at hcurrentZero
    rcases hcurrentZero with ⟨x, hx, hvalue⟩
    rw [← hvalue, carrierDisplacement_valueZero]
    fin_cases who <;> simp [valueZero, baseline, abs_of_nonneg hx.1]
    all_goals exact hx.1
  · have hcurrentOne : value time ∈ carrier 1 := by exact hcurrent
    rw [carrier_one] at hcurrentOne
    rcases hcurrentOne with ⟨y, hy, hvalue⟩
    rw [← hvalue, carrierDisplacement_valueOne]
    fin_cases who <;> simp [valueOne, baseline, abs_of_nonneg hy.1]
    all_goals exact hy.1
  · have hcurrentTwo : value time ∈ carrier 2 := by exact hcurrent
    rw [carrier_two] at hcurrentTwo
    rcases hcurrentTwo with ⟨z, hz, hvalue⟩
    rw [← hvalue, carrierDisplacement_valueTwo]
    fin_cases who <;> simp [valueTwo, baseline, abs_of_nonneg hz.1]
    all_goals exact hz.1
  · have hcurrentThree : value time ∈ carrier 3 := by exact hcurrent
    simp only [carrier_three, Set.mem_empty_iff_false] at hcurrentThree

/-- Every Flesch-faithful run in the carrier converges coordinatewise to the
common singleton baseline. -/
theorem fleschFaithful_run_value_tendsto_baseline
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) (who : Player) :
    Tendsto (fun time => value time who) atTop (nhds (baseline who)) := by
  have hbound : ∀ time, |value time who - baseline who| ≤
      carrierDisplacement initial * (2 / 3 : ℝ) ^ time := fun time =>
    (abs_run_value_sub_baseline_le_carrierDisplacement hrun who time).trans
      (fleschFaithful_run_displacement_le_geometric hrun hedge time)
  have hgeometric : Tendsto
      (fun time : ℕ => carrierDisplacement initial * (2 / 3 : ℝ) ^ time)
      atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)).const_mul
        (carrierDisplacement initial)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm'
  · exact Filter.Eventually.of_forall fun time => by
      simpa [Real.norm_eq_abs] using hbound time
  · exact hgeometric

/-- Literal singleton product roots extracted from an arbitrary infinite run. -/
def infiniteRunSingletonRoots
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value) : ℕ → Player → PMF Bool :=
  quittingEssentialAPSSingletonRoots owner mass
    (fun time => (hrun.2.2 time).1.1)
    (fun time => (hrun.2.2 time).1.2.le)

@[simp] theorem infiniteRunSingletonRoots_absorptionMass
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value) (time : ℕ) :
    quittingRootAbsorptionMass (infiniteRunSingletonRoots hrun time) = mass time := by
  simp [infiniteRunSingletonRoots, quittingEssentialAPSSingletonRoots,
    quittingRootAbsorptionMass_soloStationaryRoot]

/-- Terminal-semantics data attached to any Flesch-faithful run in the
carrier.  Its Bellman equations come from the run; its convergence and finite
charge are consequences of the forced edge recurrence. -/
def fleschFaithfulRunSummableExactValueTail
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) :
    QuittingSummableExactValueTail completionAReward where
  roots := infiniteRunSingletonRoots hrun
  value := value
  boundary := baseline
  bellman := hrun.policy_singletonRoots
    (fun time => (hrun.2.2 time).1.1)
    (fun time => (hrun.2.2 time).1.2.le)
  value_tendsto := fleschFaithful_run_value_tendsto_baseline hrun hedge
  absorption_summable := by
    simpa using summable_fleschFaithful_run_mass hrun hedge

theorem infiniteRun_jointSurvivalWeight_eq_prod_one_sub_mass
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value) (fuel : ℕ) :
    quittingJointSurvivalWeight (infiniteRunSingletonRoots hrun) 0 fuel =
      ∏ time ∈ Finset.range fuel, (1 - mass time) := by
  rw [quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_congr rfl
  intro time _
  simp [infiniteRunSingletonRoots, quittingEssentialAPSSingletonRoots,
    quittingStationaryContinueMass_solo, quittingHazardCoin_false_toReal]

/-- Finite total mass and the strict run bound leave positive probability of
Never along every Flesch-faithful run. -/
theorem fleschFaithful_run_jointSurvivalLimit_positive
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) :
    0 < quittingJointSurvivalLimit (infiniteRunSingletonRoots hrun) 0 := by
  obtain ⟨lower, hlower0, hlower⟩ :=
    Math.exists_pos_le_prod_one_sub_of_summable mass
      (fun time => (hrun.2.2 time).1.1)
      (fun time => (hrun.2.2 time).1.2)
      (summable_fleschFaithful_run_mass hrun hedge)
  have hweight : ∀ fuel,
      lower ≤ quittingJointSurvivalWeight
        (infiniteRunSingletonRoots hrun) 0 fuel := by
    intro fuel
    rw [infiniteRun_jointSurvivalWeight_eq_prod_one_sub_mass hrun fuel]
    exact hlower fuel
  have hlimit : lower ≤
      quittingJointSurvivalLimit (infiniteRunSingletonRoots hrun) 0 :=
    ge_of_tendsto
      (tendsto_quittingJointSurvivalLimit (infiniteRunSingletonRoots hrun) 0)
      (Filter.Eventually.of_forall hweight)
  exact hlower0.trans_le hlimit

/-- For every Flesch-faithful run, the initial Bellman annotation differs
from its literal terminal payoff by exactly survival times the common
baseline. -/
theorem fleschFaithful_run_value_sub_terminalPayoff_eq_survival_mul_baseline
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) :
    (fun who => initial who - quittingTerminalPayoff completionAReward
      ((fleschFaithfulRunSummableExactValueTail hrun hedge).suffixProfile 0) who) =
    fun who => quittingJointSurvivalLimit (infiniteRunSingletonRoots hrun) 0 *
      baseline who := by
  have hid :=
    QuittingSummableExactValueTail.value_eq_terminalPayoff_add_survival_mul_boundary
      (fleschFaithfulRunSummableExactValueTail hrun hedge) 0
  funext who
  have hwho := congrFun hid who
  change value 0 who =
    quittingTerminalPayoff completionAReward
        ((fleschFaithfulRunSummableExactValueTail hrun hedge).suffixProfile 0) who +
      quittingJointSurvivalLimit (infiniteRunSingletonRoots hrun) 0 *
        baseline who at hwho
  rw [hrun.1] at hwho
  linarith

/-- The exact survival-weighted residual of a Flesch-faithful run is nonzero. -/
theorem fleschFaithful_run_value_sub_terminalPayoff_ne_zero
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) :
    (fun who => initial who - quittingTerminalPayoff completionAReward
      ((fleschFaithfulRunSummableExactValueTail hrun hedge).suffixProfile 0) who) ≠
      (0 : Payoff Player) := by
  intro heq
  have hresidual :=
    fleschFaithful_run_value_sub_terminalPayoff_eq_survival_mul_baseline hrun hedge
  have hwho := congrFun (heq.symm.trans hresidual) (3 : Player)
  simp [baseline] at hwho
  exact (ne_of_gt (fleschFaithful_run_jointSurvivalLimit_positive hrun hedge))
    hwho.symm

/-- Universal Theorem-A adapter: every nonbaseline run in any carrier fiber
whose successive owners follow literal Flesch edges has positive but summable
masses, converges to the baseline, retains positive survival, and has the
exact nonzero terminal residual.  The forced owner/mass/value recurrence is
the separate literal theorem `fleschFaithful_run_forced_step`. -/
theorem every_nonbaseline_fleschFaithful_run_has_summable_third_mode
    {owner : ℕ → Player} {initial : Payoff Player}
    {mass : ℕ → ℝ} {value : ℕ → Payoff Player}
    (hrun : IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      owner initial mass value)
    (hedge : ∀ time, QuittingFleschSuccessor completionAReward
      (owner time) (owner (time + 1))) (hinitial : initial ≠ baseline) :
    (∀ time, 0 < mass time) ∧ Summable mass ∧
      (∀ who, Tendsto (fun time => value time who) atTop (nhds (baseline who))) ∧
      0 < quittingJointSurvivalLimit (infiniteRunSingletonRoots hrun) 0 ∧
      (fun who => initial who - quittingTerminalPayoff completionAReward
        ((fleschFaithfulRunSummableExactValueTail hrun hedge).suffixProfile 0) who) =
        (fun who => quittingJointSurvivalLimit
          (infiniteRunSingletonRoots hrun) 0 * baseline who) ∧
      (fun who => initial who - quittingTerminalPayoff completionAReward
        ((fleschFaithfulRunSummableExactValueTail hrun hedge).suffixProfile 0) who) ≠
        (0 : Payoff Player) := by
  exact ⟨fleschFaithful_run_mass_positive hrun hedge hinitial,
    summable_fleschFaithful_run_mass hrun hedge,
    fleschFaithful_run_value_tendsto_baseline hrun hedge,
    fleschFaithful_run_jointSurvivalLimit_positive hrun hedge,
    fleschFaithful_run_value_sub_terminalPayoff_eq_survival_mul_baseline hrun hedge,
    fleschFaithful_run_value_sub_terminalPayoff_ne_zero hrun hedge⟩

/-- Owner-zero coordinate at the start of each three-date circuit. -/
def circuitCoordinate (initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => circuitMap (circuitCoordinate initial n)

@[simp] theorem circuitCoordinate_zero (initial : ℝ) :
    circuitCoordinate initial 0 = initial := rfl

@[simp] theorem circuitCoordinate_succ (initial : ℝ) (n : ℕ) :
    circuitCoordinate initial (n + 1) =
      circuitMap (circuitCoordinate initial n) := rfl

/-- The periodic owner chronology `0,1,2,0,1,2,...`. -/
def executionOwner (time : ℕ) : Player :=
  if time % 3 = 0 then 0 else if time % 3 = 1 then 1 else 2

/-- The literal carrier value at every date. -/
def executionValue (initial : ℝ) (time : ℕ) : Payoff Player :=
  let x := circuitCoordinate initial (time / 3)
  if time % 3 = 0 then valueZero x
  else if time % 3 = 1 then valueOne (nextOneCoordinate x)
  else valueTwo (nextTwoCoordinate (nextOneCoordinate x))

/-- The forced singleton mass at every date. -/
def executionMass (initial : ℝ) (time : ℕ) : ℝ :=
  let x := circuitCoordinate initial (time / 3)
  if time % 3 = 0 then massZero x
  else if time % 3 = 1 then massOne (nextOneCoordinate x)
  else massTwo (nextTwoCoordinate (nextOneCoordinate x))

@[simp] theorem executionOwner_three_mul (n : ℕ) : executionOwner (3 * n) = 0 := by
  simp [executionOwner]

@[simp] theorem executionOwner_three_mul_add_one (n : ℕ) :
    executionOwner (3 * n + 1) = 1 := by
  simp [executionOwner]

@[simp] theorem executionOwner_three_mul_add_two (n : ℕ) :
    executionOwner (3 * n + 2) = 2 := by
  simp [executionOwner]

@[simp] theorem executionValue_three_mul (initial : ℝ) (n : ℕ) :
    executionValue initial (3 * n) = valueZero (circuitCoordinate initial n) := by
  simp [executionValue]

@[simp] theorem executionValue_three_mul_add_one (initial : ℝ) (n : ℕ) :
    executionValue initial (3 * n + 1) =
      valueOne (nextOneCoordinate (circuitCoordinate initial n)) := by
  simp [executionValue]
  congr 3
  omega

@[simp] theorem executionValue_three_mul_add_two (initial : ℝ) (n : ℕ) :
    executionValue initial (3 * n + 2) =
      valueTwo (nextTwoCoordinate
        (nextOneCoordinate (circuitCoordinate initial n))) := by
  simp [executionValue]
  congr 4
  omega

@[simp] theorem executionMass_three_mul (initial : ℝ) (n : ℕ) :
    executionMass initial (3 * n) = massZero (circuitCoordinate initial n) := by
  simp [executionMass]

@[simp] theorem executionMass_three_mul_add_one (initial : ℝ) (n : ℕ) :
    executionMass initial (3 * n + 1) =
      massOne (nextOneCoordinate (circuitCoordinate initial n)) := by
  simp [executionMass]
  congr 4
  omega

@[simp] theorem executionMass_three_mul_add_two (initial : ℝ) (n : ℕ) :
    executionMass initial (3 * n + 2) =
      massTwo (nextTwoCoordinate
        (nextOneCoordinate (circuitCoordinate initial n))) := by
  simp [executionMass]
  congr 4
  omega

theorem circuitCoordinate_mem {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ n, circuitCoordinate initial n ∈ Icc (0 : ℝ) (1 / 2) := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      have hsmall := circuitMap_mem ih
      exact ⟨hsmall.1, hsmall.2.trans (by norm_num)⟩

theorem circuitCoordinate_positive {initial : ℝ}
    (hinitial : initial ∈ Ioc (0 : ℝ) (1 / 2)) :
    ∀ n, 0 < circuitCoordinate initial n := by
  intro n
  induction n with
  | zero => exact hinitial.1
  | succ n ih =>
      rw [circuitCoordinate_succ, circuitMap]
      have hupper : circuitCoordinate initial n ≤ 1 / 2 :=
        (circuitCoordinate_mem ⟨hinitial.1.le, hinitial.2⟩ n).2
      exact div_pos ih (by linarith)

theorem circuitCoordinate_le_geometric {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ n, circuitCoordinate initial n ≤ initial * (2 / 9 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [circuitCoordinate_succ, pow_succ]
      calc
        circuitMap (circuitCoordinate initial n) ≤
            (2 / 9 : ℝ) * circuitCoordinate initial n :=
          circuitMap_le_two_ninth_mul (circuitCoordinate_mem hinitial n)
        _ ≤ (2 / 9 : ℝ) * (initial * (2 / 9 : ℝ) ^ n) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = initial * ((2 / 9 : ℝ) ^ n * (2 / 9 : ℝ)) := by ring

theorem summable_circuitCoordinate {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    Summable (circuitCoordinate initial) := by
  apply Summable.of_nonneg_of_le
  · exact fun n => (circuitCoordinate_mem hinitial n).1
  · exact circuitCoordinate_le_geometric hinitial
  · exact (summable_geometric_of_norm_lt_one (by norm_num :
      ‖(2 / 9 : ℝ)‖ < 1)).mul_left initial

theorem circuit_mass_sum_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    massZero x + massOne (nextOneCoordinate x) +
        massTwo (nextTwoCoordinate (nextOneCoordinate x)) ≤
      (31 / 30 : ℝ) * x := by
  have hdenom0 : 0 < 2 - x := by linarith [hx.2]
  have hy := nextOneCoordinate_mem hx
  have hdenom1 : 0 < 2 - nextOneCoordinate x := by linarith [hy.2]
  have hmass1 : massOne (nextOneCoordinate x) ≤ x / 3 := by
    rw [massOne, nextOneCoordinate]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ hdenom0]
    nlinarith [hx.1, hx.2]
  have hmass2 : massTwo (nextTwoCoordinate (nextOneCoordinate x)) ≤ x / 5 := by
    have hformula : nextTwoCoordinate (nextOneCoordinate x) = x / (4 - 3 * x) := by
      rw [nextTwoCoordinate, nextOneCoordinate]
      field_simp [ne_of_gt hdenom0]
      ring
    rw [massTwo, hformula]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ (by linarith [hx.2] : 0 < 4 - 3 * x)]
    nlinarith [hx.1, hx.2]
  rw [massZero]
  linarith

theorem executionMass_nonneg {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ time, 0 ≤ executionMass initial time := by
  intro time
  have hdecomp : time = 3 * (time / 3) + time % 3 := by omega
  have hmod : time % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : time % 3 <;> rw [hdecomp]
  · simpa using (massZero_mem (circuitCoordinate_mem hinitial (time / 3))).1
  · simpa using (massOne_mem
      (nextOneCoordinate_mem (circuitCoordinate_mem hinitial (time / 3)))).1
  · simpa using (massTwo_mem (nextTwoCoordinate_mem
      (nextOneCoordinate_mem (circuitCoordinate_mem hinitial (time / 3))))).1

theorem executionMass_le_one_quarter {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ time, executionMass initial time ≤ 1 / 4 := by
  intro time
  have hdecomp : time = 3 * (time / 3) + time % 3 := by omega
  have hmod : time % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : time % 3 <;> rw [hdecomp]
  · have hx := circuitCoordinate_mem hinitial (time / 3)
    norm_num [massZero] at hx ⊢
    linarith
  · have hy := nextOneCoordinate_mem (circuitCoordinate_mem hinitial (time / 3))
    norm_num [massOne] at hy ⊢
    linarith
  · have hz := nextTwoCoordinate_mem
      (nextOneCoordinate_mem (circuitCoordinate_mem hinitial (time / 3)))
    norm_num [massTwo] at hz ⊢
    linarith

theorem executionMass_positive {initial : ℝ}
    (hinitial : initial ∈ Ioc (0 : ℝ) (1 / 2)) :
    ∀ time, 0 < executionMass initial time := by
  intro time
  have hdecomp : time = 3 * (time / 3) + time % 3 := by omega
  have hmod : time % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : time % 3 <;> rw [hdecomp]
  · simp only [Nat.add_zero, executionMass_three_mul]
    rw [massZero]
    exact div_pos (circuitCoordinate_positive hinitial (time / 3)) (by norm_num)
  · rw [executionMass_three_mul_add_one]
    rw [massOne, nextOneCoordinate]
    have hx := circuitCoordinate_mem ⟨hinitial.1.le, hinitial.2⟩ (time / 3)
    exact div_pos (div_pos (circuitCoordinate_positive hinitial (time / 3))
      (by linarith [hx.2])) (by norm_num)
  · rw [executionMass_three_mul_add_two]
    rw [massTwo, nextTwoCoordinate]
    have hx := circuitCoordinate_mem ⟨hinitial.1.le, hinitial.2⟩ (time / 3)
    have hdenom0 : 0 < 2 - circuitCoordinate initial (time / 3) := by
      linarith [hx.2]
    have hy := nextOneCoordinate_mem hx
    have hypos : 0 < nextOneCoordinate (circuitCoordinate initial (time / 3)) :=
      div_pos (circuitCoordinate_positive hinitial (time / 3)) hdenom0
    exact div_pos (div_pos hypos (by linarith [hy.2])) (by norm_num)

theorem executionMass_le_half_circuitCoordinate {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ time, executionMass initial time ≤
      circuitCoordinate initial (time / 3) / 2 := by
  intro time
  have hdecomp : time = 3 * (time / 3) + time % 3 := by omega
  have hmod : time % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : time % 3 <;> rw [hdecomp]
  · have hdiv : (3 * (time / 3) + 0) / 3 = time / 3 := by omega
    rw [hdiv, Nat.add_zero, executionMass_three_mul]
    rfl
  · have hdiv : (3 * (time / 3) + 1) / 3 = time / 3 := by omega
    rw [hdiv, executionMass_three_mul_add_one]
    have hx := circuitCoordinate_mem hinitial (time / 3)
    have hdenom : 0 < 2 - circuitCoordinate initial (time / 3) := by
      linarith [hx.2]
    rw [massOne, nextOneCoordinate]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    rw [div_le_iff₀ hdenom]
    nlinarith [hx.1, hx.2]
  · have hdiv : (3 * (time / 3) + 2) / 3 = time / 3 := by omega
    rw [hdiv, executionMass_three_mul_add_two]
    have hx := circuitCoordinate_mem hinitial (time / 3)
    have hy := nextOneCoordinate_mem hx
    rw [massTwo]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc
      nextTwoCoordinate (nextOneCoordinate (circuitCoordinate initial (time / 3))) ≤
          nextOneCoordinate (circuitCoordinate initial (time / 3)) := by
        rw [nextTwoCoordinate]
        apply (div_le_iff₀ (by linarith [hy.2] :
          0 < 2 - nextOneCoordinate (circuitCoordinate initial (time / 3)))).2
        nlinarith [hy.1, hy.2]
      _ ≤ circuitCoordinate initial (time / 3) := by
        rw [nextOneCoordinate]
        apply (div_le_iff₀ (by linarith [hx.2] :
          0 < 2 - circuitCoordinate initial (time / 3))).2
        nlinarith [hx.1, hx.2]

theorem executionMass_le_geometric {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ time, executionMass initial time ≤
      2 * initial * (2 / 3 : ℝ) ^ time := by
  intro time
  have hdecomp : time = 3 * (time / 3) + time % 3 := by omega
  have hmod : time % 3 < 3 := Nat.mod_lt _ (by omega)
  have hc := executionMass_le_half_circuitCoordinate hinitial time
  have hcoord := circuitCoordinate_le_geometric hinitial (time / 3)
  have hpower : (2 / 9 : ℝ) ^ (time / 3) ≤
      ((2 / 3 : ℝ) ^ 3) ^ (time / 3) := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  interval_cases h : time % 3
  · rw [hdecomp] at hc ⊢
    have hdiv : (3 * (time / 3) + 0) / 3 = time / 3 := by omega
    rw [hdiv] at hc
    simp only [Nat.add_zero, executionMass_three_mul] at hc ⊢
    rw [pow_mul]
    norm_num at hpower ⊢
    have hmul := mul_le_mul_of_nonneg_left hpower hinitial.1
    have hnonneg : 0 ≤ initial * (8 / 27 : ℝ) ^ (time / 3) :=
      mul_nonneg hinitial.1 (pow_nonneg (by norm_num) _)
    linarith
  · rw [hdecomp] at hc ⊢
    have hdiv : (3 * (time / 3) + 1) / 3 = time / 3 := by omega
    rw [hdiv] at hc
    rw [executionMass_three_mul_add_one] at hc ⊢
    rw [pow_add, pow_mul]
    norm_num at hpower ⊢
    have hmul := mul_le_mul_of_nonneg_left hpower hinitial.1
    have hnonneg : 0 ≤ initial * (8 / 27 : ℝ) ^ (time / 3) :=
      mul_nonneg hinitial.1 (pow_nonneg (by norm_num) _)
    linarith
  · rw [hdecomp] at hc ⊢
    have hdiv : (3 * (time / 3) + 2) / 3 = time / 3 := by omega
    rw [hdiv] at hc
    rw [executionMass_three_mul_add_two] at hc ⊢
    rw [pow_add, pow_mul]
    norm_num at hpower ⊢
    have hmul := mul_le_mul_of_nonneg_left hpower hinitial.1
    have hnonneg : 0 ≤ initial * (8 / 27 : ℝ) ^ (time / 3) :=
      mul_nonneg hinitial.1 (pow_nonneg (by norm_num) _)
    linarith

theorem summable_executionMass {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    Summable (executionMass initial) := by
  apply Summable.of_nonneg_of_le
  · exact executionMass_nonneg hinitial
  · exact executionMass_le_geometric hinitial
  · exact (summable_geometric_of_norm_lt_one (by norm_num :
      ‖(2 / 3 : ℝ)‖ < 1)).mul_left (2 * initial)

/-- The displayed chronology, mass, and value are a literal infinite run in
the greatest carrier-restricted essential-APS family. -/
theorem isInfiniteRun {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    IsQuittingEssentialAPSInfiniteRun completionAReward
      (quittingEssentialAPSGreatestFamily completionAReward carrier)
      executionOwner (valueZero initial) (executionMass initial)
      (executionValue initial) := by
  refine ⟨by simp [executionValue], ?_, ?_⟩
  · intro time
    rw [greatestFamily_eq_carrier]
    have hdecomp : time = 3 * (time / 3) + time % 3 := by omega
    have hmod : time % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases h : time % 3 <;> rw [hdecomp]
    · simp only [Nat.add_zero]
      rw [executionOwner_three_mul, executionValue_three_mul, carrier_zero]
      exact ⟨_, circuitCoordinate_mem hinitial (time / 3), rfl⟩
    · rw [executionOwner_three_mul_add_one,
        executionValue_three_mul_add_one, carrier_one]
      exact ⟨_, nextOneCoordinate_mem (circuitCoordinate_mem hinitial (time / 3)), rfl⟩
    · rw [executionOwner_three_mul_add_two,
        executionValue_three_mul_add_two, carrier_two]
      exact ⟨_, nextTwoCoordinate_mem
        (nextOneCoordinate_mem (circuitCoordinate_mem hinitial (time / 3))), rfl⟩
  · intro time
    refine ⟨⟨executionMass_nonneg hinitial time,
      (executionMass_le_one_quarter hinitial time).trans_lt (by norm_num)⟩, ?_⟩
    have hdecomp : time = 3 * (time / 3) + time % 3 := by omega
    have hmod : time % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases h : time % 3 <;> rw [hdecomp]
    · simp only [Nat.add_zero]
      rw [executionValue_three_mul, executionMass_three_mul,
        executionOwner_three_mul, executionValue_three_mul_add_one,
        quittingSoloReward_completionAReward]
      exact valueZero_arc _ (by
        have hx := circuitCoordinate_mem hinitial (time / 3)
        linarith [hx.2])
    · rw [executionValue_three_mul_add_one, executionMass_three_mul_add_one,
        executionOwner_three_mul_add_one, executionValue_three_mul_add_two,
        quittingSoloReward_completionAReward]
      exact valueOne_arc _ (by
        have hy := nextOneCoordinate_mem (circuitCoordinate_mem hinitial (time / 3))
        linarith [hy.2])
    · have hx := circuitCoordinate_mem hinitial (time / 3)
      have hz := nextTwoCoordinate_mem (nextOneCoordinate_mem hx)
      rw [executionValue_three_mul_add_two, executionMass_three_mul_add_two,
        executionOwner_three_mul_add_two]
      have hnextTime : 3 * (time / 3) + 2 + 1 = 3 * (time / 3 + 1) := by omega
      rw [hnextTime, executionValue_three_mul, circuitCoordinate_succ,
        ← nextZero_after_three_eq_circuitMap hx,
        quittingSoloReward_completionAReward]
      exact valueTwo_arc _ (by linarith [hz.2])

theorem circuitCoordinate_tendsto_zero {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    Tendsto (circuitCoordinate initial) atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun n => (circuitCoordinate_mem hinitial n).1
  · exact circuitCoordinate_le_geometric hinitial
  · have hpow : Tendsto (fun n : ℕ => (2 / 9 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    simpa using hpow.const_mul initial

theorem nextOneCoordinate_le_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    nextOneCoordinate x ≤ x := by
  have hdenom : 0 < 2 - x := by linarith [hx.2]
  rw [nextOneCoordinate, div_le_iff₀ hdenom]
  nlinarith [hx.1, hx.2]

theorem nextTwo_after_nextOne_le_self {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    nextTwoCoordinate (nextOneCoordinate x) ≤ x := by
  have hy := nextOneCoordinate_mem hx
  have hstep : nextTwoCoordinate (nextOneCoordinate x) ≤
      nextOneCoordinate x := by
    have hdenom : 0 < 2 - nextOneCoordinate x := by linarith [hy.2]
    rw [nextTwoCoordinate, div_le_iff₀ hdenom]
    nlinarith [hy.1, hy.2]
  exact hstep.trans (nextOneCoordinate_le_self hx)

theorem abs_executionValue_sub_baseline_le {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) (who : Player) :
    ∀ time, |executionValue initial time who - baseline who| ≤
      circuitCoordinate initial (time / 3) := by
  intro time
  have hdecomp : time = 3 * (time / 3) + time % 3 := by omega
  have hmod : time % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : time % 3 <;> rw [hdecomp]
  · have hx := circuitCoordinate_mem hinitial (time / 3)
    have hdiv : (3 * (time / 3) + 0) / 3 = time / 3 := by omega
    rw [hdiv, Nat.add_zero]
    rw [executionValue_three_mul]
    have habs : |circuitCoordinate initial (time / 3)| =
        circuitCoordinate initial (time / 3) := abs_of_nonneg hx.1
    fin_cases who <;> simp [valueZero, baseline, habs, hx.1]
  · have hx := circuitCoordinate_mem hinitial (time / 3)
    have hdiv : (3 * (time / 3) + 1) / 3 = time / 3 := by omega
    rw [hdiv]
    have hy0 := (nextOneCoordinate_mem hx).1
    have hyx := nextOneCoordinate_le_self hx
    rw [executionValue_three_mul_add_one]
    have habs : |nextOneCoordinate (circuitCoordinate initial (time / 3))| =
        nextOneCoordinate (circuitCoordinate initial (time / 3)) := abs_of_nonneg hy0
    fin_cases who <;> simp [valueOne, baseline, habs, hx.1]
    all_goals linarith
  · have hx := circuitCoordinate_mem hinitial (time / 3)
    have hdiv : (3 * (time / 3) + 2) / 3 = time / 3 := by omega
    rw [hdiv]
    have hz0 := (nextTwoCoordinate_mem (nextOneCoordinate_mem hx)).1
    have hzx := nextTwo_after_nextOne_le_self hx
    rw [executionValue_three_mul_add_two]
    have habs : |nextTwoCoordinate
        (nextOneCoordinate (circuitCoordinate initial (time / 3)))| =
      nextTwoCoordinate (nextOneCoordinate (circuitCoordinate initial (time / 3))) :=
        abs_of_nonneg hz0
    fin_cases who <;> simp [valueTwo, baseline, habs, hx.1]
    all_goals linarith

theorem executionValue_tendsto_baseline {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) (who : Player) :
    Tendsto (fun time => executionValue initial time who) atTop
      (nhds (baseline who)) := by
  have hdiv : Tendsto (fun time : ℕ => time / 3) atTop atTop :=
    Nat.tendsto_div_const_atTop (by omega)
  have hcoord := (circuitCoordinate_tendsto_zero hinitial).comp hdiv
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm'
  · exact Filter.Eventually.of_forall fun time => by
      simpa [Real.norm_eq_abs] using
        abs_executionValue_sub_baseline_le hinitial who time
  · simpa only [Function.comp_def] using hcoord

private theorem massNonnegative {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ time, 0 ≤ executionMass initial time := executionMass_nonneg hinitial

private theorem massAtMostOne {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ time, executionMass initial time ≤ 1 := fun time =>
  (executionMass_le_one_quarter hinitial time).trans (by norm_num)

/-- The literal singleton product roots implementing the forced APS run. -/
def executionRoots {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ℕ → Player → PMF Bool :=
  quittingEssentialAPSSingletonRoots executionOwner (executionMass initial)
    (massNonnegative hinitial) (massAtMostOne hinitial)

@[simp] theorem executionRoots_absorptionMass {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) (time : ℕ) :
    quittingRootAbsorptionMass (executionRoots hinitial time) =
      executionMass initial time := by
  simp [executionRoots, quittingEssentialAPSSingletonRoots,
    quittingRootAbsorptionMass_soloStationaryRoot]

/-- The forced APS run satisfies exact Bellman transport under its literal
singleton roots. -/
theorem executionValue_bellman {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ time, executionValue initial time =
      quittingRootSuccessorPayoff completionAReward
        (executionValue initial (time + 1)) (executionRoots hinitial time) := by
  exact (isInfiniteRun hinitial).policy_singletonRoots
    (massNonnegative hinitial) (massAtMostOne hinitial)

/-- The forced path, regarded as literal terminal-semantics data. -/
def summableExactValueTail {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    QuittingSummableExactValueTail completionAReward where
  roots := executionRoots hinitial
  value := executionValue initial
  boundary := baseline
  bellman := executionValue_bellman hinitial
  value_tendsto := executionValue_tendsto_baseline hinitial
  absorption_summable := by
    simpa using summable_executionMass hinitial

theorem jointSurvivalWeight_eq_prod_one_sub_executionMass {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) (fuel : ℕ) :
    quittingJointSurvivalWeight (executionRoots hinitial) 0 fuel =
      ∏ time ∈ Finset.range fuel, (1 - executionMass initial time) := by
  rw [quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_congr rfl
  intro time _
  simp [executionRoots, quittingEssentialAPSSingletonRoots,
    quittingStationaryContinueMass_solo, quittingHazardCoin_false_toReal]

/-- Summability and the strict mass bound leave a positive probability that
the singleton execution never absorbs. -/
theorem executionJointSurvivalLimit_positive {initial : ℝ}
    (hinitial : initial ∈ Ioc (0 : ℝ) (1 / 2)) :
    0 < quittingJointSurvivalLimit
      (executionRoots ⟨hinitial.1.le, hinitial.2⟩) 0 := by
  let hclosed : initial ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨hinitial.1.le, hinitial.2⟩
  obtain ⟨lower, hlower0, hlower⟩ :=
    Math.exists_pos_le_prod_one_sub_of_summable
      (executionMass initial) (executionMass_nonneg hclosed)
      (fun time => (executionMass_le_one_quarter hclosed time).trans_lt (by norm_num))
      (summable_executionMass hclosed)
  have hweight : ∀ fuel,
      lower ≤ quittingJointSurvivalWeight (executionRoots hclosed) 0 fuel := by
    intro fuel
    rw [jointSurvivalWeight_eq_prod_one_sub_executionMass hclosed]
    exact hlower fuel
  have hlimit : lower ≤ quittingJointSurvivalLimit (executionRoots hclosed) 0 :=
    ge_of_tendsto (tendsto_quittingJointSurvivalLimit (executionRoots hclosed) 0)
      (Filter.Eventually.of_forall hweight)
  exact hlower0.trans_le hlimit

/-- Exact survival-weighted residual between the annotation and the literal
terminal payoff of the executable singleton-root profile. -/
theorem executionValue_sub_terminalPayoff_eq_survival_mul_baseline {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) :
    (fun who => valueZero initial who -
      quittingTerminalPayoff completionAReward
        ((summableExactValueTail hinitial).suffixProfile 0) who) =
      fun who => quittingJointSurvivalLimit (executionRoots hinitial) 0 *
        baseline who := by
  have hid := QuittingSummableExactValueTail.value_eq_terminalPayoff_add_survival_mul_boundary
      (summableExactValueTail hinitial) 0
  funext who
  have hwho := congrFun hid who
  change executionValue initial 0 who =
    quittingTerminalPayoff completionAReward
        ((summableExactValueTail hinitial).suffixProfile 0) who +
      quittingJointSurvivalLimit (executionRoots hinitial) 0 * baseline who at hwho
  simp only [executionValue, Nat.zero_div, circuitCoordinate_zero, Nat.zero_mod,
    ↓reduceIte] at hwho
  linarith

/-- From a positive start, the annotation/terminal residual is literally
nonzero. -/
theorem executionValue_sub_terminalPayoff_ne_zero {initial : ℝ}
    (hinitial : initial ∈ Ioc (0 : ℝ) (1 / 2)) :
    (fun who => valueZero initial who -
      quittingTerminalPayoff completionAReward
        ((summableExactValueTail ⟨hinitial.1.le, hinitial.2⟩).suffixProfile 0) who) ≠
      (0 : Payoff Player) := by
  intro heq
  have hresidual := executionValue_sub_terminalPayoff_eq_survival_mul_baseline
    ⟨hinitial.1.le, hinitial.2⟩
  have hwho := congrFun (heq.symm.trans hresidual) (3 : Player)
  simp [baseline] at hwho
  exact (ne_of_gt (executionJointSurvivalLimit_positive hinitial)) hwho.symm

/-- Literal suffix terminal payoffs vanish despite convergence of the
annotation to the nonzero common face. -/
theorem executionTerminalPayoff_tendsto_zero {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) (who : Player) :
    Tendsto (fun start => quittingTerminalPayoff completionAReward
      ((summableExactValueTail hinitial).suffixProfile start) who) atTop
      (nhds 0) :=
  (summableExactValueTail hinitial).terminalPayoff_tendsto_zero who

/-- Unrestricted behavioral exploitability of the literal suffixes tends to
one.  This does not assert that a displayed APS row is Nash. -/
theorem executionSuffixGain_tendsto_one {initial : ℝ}
    (hinitial : initial ∈ Icc (0 : ℝ) (1 / 2)) (who : Player) :
    Tendsto (fun start => (summableExactValueTail hinitial).suffixGain start who)
      atTop (nhds 1) := by
  have hgain := (summableExactValueTail hinitial).suffixGain_tendsto_max_solo who
  fin_cases who <;>
    norm_num +decide [completionAReward, singletonReward,
      quittingSingletonTerminal] at hgain ⊢
  all_goals exact hgain

/-- A raw nonnegative homogeneous balance of the four singleton rows is
necessarily zero. -/
theorem raw_singletonRow_nonnegative_balance_eq_zero
    (weight : Player → ℝ) (hweight : ∀ owner, 0 ≤ weight owner)
    (hbalance : (fun who => ∑ owner, weight owner * singletonReward owner who) =
      (0 : Payoff Player)) :
    ∀ owner, weight owner = 0 := by
  have hthree := congrFun hbalance (3 : Player)
  norm_num [singletonReward, Fin.sum_univ_succ] at hthree
  have h0 := hweight (0 : Player)
  have h1 := hweight (1 : Player)
  have h2 := hweight (2 : Player)
  have h3 := hweight (3 : Player)
  change weight 0 + (weight 1 + (weight 2 + weight 3)) = 0 at hthree
  have hz0 : weight 0 = 0 := by linarith
  have hz1 : weight 1 = 0 := by linarith
  have hz2 : weight 2 = 0 := by linarith
  have hz3 : weight 3 = 0 := by linarith
  intro owner
  fin_cases owner <;> assumption

/-- A nonnegative homogeneous balance of the normalized effects `R_i-s` is
necessarily zero. -/
theorem normalized_singletonEffect_nonnegative_balance_eq_zero
    (weight : Player → ℝ) (hweight : ∀ owner, 0 ≤ weight owner)
    (hbalance : (fun who => ∑ owner,
      weight owner * (singletonReward owner who - baseline who)) =
        (0 : Payoff Player)) :
    ∀ owner, weight owner = 0 := by
  have hzero := congrFun hbalance (0 : Player)
  have hone := congrFun hbalance (1 : Player)
  have htwo := congrFun hbalance (2 : Player)
  norm_num [singletonReward, baseline, Fin.sum_univ_succ] at hzero hone htwo
  have h0 := hweight (0 : Player)
  have h1 := hweight (1 : Player)
  have h2 := hweight (2 : Player)
  have h3 := hweight (3 : Player)
  change -weight 1 + (weight 2 * 2 + weight 3) = 0 at hzero
  change weight 0 * 2 + (-weight 2 + weight 3) = 0 at hone
  change -weight 0 + (weight 1 * 2 + weight 3) = 0 at htwo
  have hz0 : weight 0 = 0 := by linarith
  have hz1 : weight 1 = 0 := by linarith
  have hz2 : weight 2 = 0 := by linarith
  have hz3 : weight 3 = 0 := by linarith
  intro owner
  fin_cases owner <;> assumption

/-- Literal capstone for the summable third mode.  Every conjunct is derived
from the concrete reward table and execution, rather than stored as supplied
certificate data. -/
theorem exists_positive_summable_terminalFree_essentialAPS_execution :
    ∃ (initial : ℝ) (hinitial : initial ∈ Ioc (0 : ℝ) (1 / 2)),
      IsQuittingEssentialAPSInfiniteRun completionAReward
        (quittingEssentialAPSGreatestFamily completionAReward carrier)
        executionOwner (valueZero initial) (executionMass initial)
        (executionValue initial) ∧
      (∀ time, 0 < executionMass initial time) ∧
      Summable (executionMass initial) ∧
      0 < quittingJointSurvivalLimit
        (executionRoots ⟨hinitial.1.le, hinitial.2⟩) 0 := by
  refine ⟨1 / 4, by norm_num, isInfiniteRun (by norm_num),
    executionMass_positive (by norm_num), summable_executionMass (by norm_num), ?_⟩
  exact executionJointSurvivalLimit_positive (by norm_num)

end FinFourEssentialAPSSummableThirdMode
end GameTheory
