import UniformEquilibrium.Diagnostics.Quitting.DuplicatedCyclicReactivationRegression
import UniformEquilibrium.Quitting.Root.TerminalSemanticDebt

/-! Literal boundary corollaries for every cyclic choice of first removed owner. -/

noncomputable section

namespace GameTheory
namespace DuplicatedCyclicReactivationRegression

open Filter Math.Probability Math.PMFProduct
open QuittingLCPClassification
open scoped Topology

/-- The next owner in the cyclic order; this is the final surviving core owner. -/
def nextOwner : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- The preceding owner in the cyclic order; this is the second Never mover. -/
def previousOwner : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

def firstChildRootAt (first : Fin 3) (index : ℕ) : Player → PMF Bool :=
  Function.update (root index) (some first) (PMF.pure false)

def singletonChildRootAt (first : Fin 3) (index : ℕ) : Player → PMF Bool :=
  Function.update (firstChildRootAt first index) (some (previousOwner first)) (PMF.pure false)

def firstChildProfileAt (first : Fin 3) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (firstChildRootAt first index)

def singletonChildProfileAt (first : Fin 3) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (singletonChildRootAt first index)

def finalQuitNowProfileAt (first : Fin 3) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (singletonChildProfileAt first index) (some first)
    (quittingPureTimeBehaviorStrategy reward (some first) (some 0))

@[simp] theorem firstChildRootAt_totalHazard (first : Fin 3) (index : ℕ) :
    quittingStationaryTotalHazard (firstChildRootAt first index) =
      2 * hazard index + hazard index ^ 2 := by
  fin_cases first <;>
    simp [quittingStationaryTotalHazard, firstChildRootAt, Fintype.sum_option,
      Fin.sum_univ_succ] <;> ring

@[simp] theorem singletonChildRootAt_totalHazard (first : Fin 3) (index : ℕ) :
    quittingStationaryTotalHazard (singletonChildRootAt first index) =
      hazard index + hazard index ^ 2 := by
  fin_cases first <;>
    simp [quittingStationaryTotalHazard, singletonChildRootAt, firstChildRootAt,
      previousOwner, Fintype.sum_option, Fin.sum_univ_succ] <;> ring

def firstDirectionAt (first : Fin 3) : Player → ℝ := fun who =>
  if who = none ∨ who = some first then 0 else 1 / 2

def singletonDirectionAt (first : Fin 3) : Player → ℝ := fun who =>
  if who = some (nextOwner first) then 1 else 0

theorem firstChildRootAt_direction_tendsto (first : Fin 3) (who : Player) :
    Tendsto (fun index ↦ (firstChildRootAt first index who true).toReal /
      quittingStationaryTotalHazard (firstChildRootAt first index)) atTop
      (nhds (firstDirectionAt first who)) := by
  simp_rw [firstChildRootAt_totalHazard]
  fin_cases first <;> cases who with
  | none =>
      simpa [firstChildRootAt, firstDirectionAt] using
        hazardSquare_div_linearSquare_tendsto 2 (by norm_num)
  | some who =>
      fin_cases who <;> simp [firstChildRootAt, firstDirectionAt] <;>
        first | simpa [one_div] using
          (hazard_div_linearSquare_tendsto 2 (by norm_num))

theorem singletonChildRootAt_direction_tendsto (first : Fin 3) (who : Player) :
    Tendsto (fun index ↦ (singletonChildRootAt first index who true).toReal /
      quittingStationaryTotalHazard (singletonChildRootAt first index)) atTop
      (nhds (singletonDirectionAt first who)) := by
  simp_rw [singletonChildRootAt_totalHazard]
  fin_cases first <;> cases who with
  | none =>
      simpa [singletonChildRootAt, firstChildRootAt, previousOwner,
        singletonDirectionAt, nextOwner] using
        hazardSquare_div_linearSquare_tendsto 1 one_ne_zero
  | some who =>
      fin_cases who <;>
        simp [singletonChildRootAt, firstChildRootAt, previousOwner,
          singletonDirectionAt, nextOwner]
      all_goals simpa [one_div] using
        (hazard_div_linearSquare_tendsto 1 one_ne_zero)

theorem firstChildRootAt_totalHazard_tendsto_zero (first : Fin 3) :
    Tendsto (fun index ↦ quittingStationaryTotalHazard (firstChildRootAt first index))
      atTop (nhds 0) := by
  simp_rw [firstChildRootAt_totalHazard]
  simpa using (hazard_tendsto_zero.const_mul 2).add (hazard_tendsto_zero.pow 2)

theorem singletonChildRootAt_totalHazard_tendsto_zero (first : Fin 3) :
    Tendsto (fun index ↦ quittingStationaryTotalHazard (singletonChildRootAt first index))
      atTop (nhds 0) := by
  simp_rw [singletonChildRootAt_totalHazard]
  simpa using hazard_tendsto_zero.add (hazard_tendsto_zero.pow 2)

theorem firstChildRootAt_totalHazard_pos (first : Fin 3) (index : ℕ) :
    0 < quittingStationaryTotalHazard (firstChildRootAt first index) := by
  rw [firstChildRootAt_totalHazard]
  nlinarith [hazard_pos index, sq_nonneg (hazard index)]

theorem singletonChildRootAt_totalHazard_pos (first : Fin 3) (index : ℕ) :
    0 < quittingStationaryTotalHazard (singletonChildRootAt first index) := by
  rw [singletonChildRootAt_totalHazard]
  nlinarith [hazard_pos index, sq_nonneg (hazard index)]

theorem firstChildAt_first_payoff_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (firstChildProfileAt first index)
      (some first)) atTop (nhds (1 / 2 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter (firstChildRootAt first)
    (firstChildRootAt_totalHazard_pos first) (firstChildRootAt_totalHazard_tendsto_zero first)
    (firstDirectionAt first) (firstChildRootAt_direction_tendsto first) (some first)
  convert h using 1
  congr 1
  fin_cases first <;>
    simp [firstDirectionAt, Fintype.sum_option, Fin.sum_univ_succ,
      StandardQSideExample.duplicatedCyclicMatrix,
      StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix] <;>
    norm_num

theorem source_core_payoff_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (profile index) (some first))
      atTop (nhds (1 / 3 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter root totalHazard_pos
    totalHazard_tendsto_zero sourceDirection source_direction_tendsto (some first)
  convert h using 1
  congr 1
  fin_cases first <;>
    norm_num [profile, sourceDirection, soloReward_eq_matrix,
      Fintype.sum_option, Fin.sum_univ_succ,
      StandardQSideExample.duplicatedCyclicMatrix,
      StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix]

/-- Every leading core owner has first-Never gain tending to `1/6`. -/
theorem firstNeverGain_tendsto_all_core (first : Fin 3) : Tendsto (fun index ↦
    quittingTerminalPayoff reward (firstChildProfileAt first index) (some first) -
      quittingTerminalPayoff reward (profile index) (some first)) atTop
    (nhds (1 / 6 : ℝ)) := by
  convert (firstChildAt_first_payoff_tendsto first).sub (source_core_payoff_tendsto first) using 1
  norm_num

theorem firstChildAt_previous_payoff_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (firstChildProfileAt first index)
      (some (previousOwner first))) atTop (nhds (1 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter (firstChildRootAt first)
    (firstChildRootAt_totalHazard_pos first) (firstChildRootAt_totalHazard_tendsto_zero first)
    (firstDirectionAt first) (firstChildRootAt_direction_tendsto first)
    (some (previousOwner first))
  convert h using 1
  congr 1
  have hcard : ({x : Fin 2 | x.succ = (1 : Fin 3)} : Finset (Fin 2)).card = 1 := by
    decide
  fin_cases first <;>
    norm_num [firstDirectionAt, previousOwner, Fintype.sum_option, Fin.sum_univ_succ, hcard,
      Option.some_ne_none,
      StandardQSideExample.duplicatedCyclicMatrix,
      StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix]
  all_goals rfl

theorem singletonChildAt_previous_payoff_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (singletonChildProfileAt first index)
      (some (previousOwner first))) atTop (nhds (2 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter (singletonChildRootAt first)
    (singletonChildRootAt_totalHazard_pos first)
    (singletonChildRootAt_totalHazard_tendsto_zero first)
    (singletonDirectionAt first) (singletonChildRootAt_direction_tendsto first)
    (some (previousOwner first))
  convert h using 1
  congr 1
  fin_cases first <;>
    simp [singletonDirectionAt, previousOwner, nextOwner, Fintype.sum_option,
      Fin.sum_univ_succ, StandardQSideExample.duplicatedCyclicMatrix,
      StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix]

theorem singletonChildAt_first_payoff_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (singletonChildProfileAt first index)
      (some first)) atTop (nhds (-1 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter (singletonChildRootAt first)
    (singletonChildRootAt_totalHazard_pos first)
    (singletonChildRootAt_totalHazard_tendsto_zero first)
    (singletonDirectionAt first) (singletonChildRootAt_direction_tendsto first) (some first)
  convert h using 1
  congr 1
  fin_cases first <;>
    simp [singletonDirectionAt, nextOwner, Fintype.sum_option, Fin.sum_univ_succ,
      StandardQSideExample.duplicatedCyclicMatrix,
      StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix]

theorem firstChildRootAt_continue_tendsto_one (first : Fin 3) (who : Player) :
    Tendsto (fun index ↦ (firstChildRootAt first index who false).toReal) atTop (nhds 1) := by
  by_cases hwho : who = some first
  · subst who
    simp [firstChildRootAt]
  · simpa [firstChildRootAt, Function.update_of_ne hwho] using root_continue_tendsto_one who

theorem singletonChildRootAt_continue_tendsto_one (first : Fin 3) (who : Player) :
    Tendsto (fun index ↦ (singletonChildRootAt first index who false).toReal)
      atTop (nhds 1) := by
  by_cases hwho : who = some (previousOwner first)
  · subst who
    simp [singletonChildRootAt]
  · simpa [singletonChildRootAt, Function.update_of_ne hwho] using
      firstChildRootAt_continue_tendsto_one first who

theorem sourceAt_quitNow_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ stationaryQuitNowPayoff reward (root index) (some first))
      atTop (nhds 0) := by
  simpa [soloReward_eq_matrix] using stationaryQuitNowPayoff_tendsto_solo
    root (some first) root_continue_tendsto_one

theorem firstChildAt_previous_quitNow_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ stationaryQuitNowPayoff reward (firstChildRootAt first index)
      (some (previousOwner first))) atTop (nhds 0) := by
  simpa [soloReward_eq_matrix] using stationaryQuitNowPayoff_tendsto_solo
    (firstChildRootAt first) (some (previousOwner first))
      (firstChildRootAt_continue_tendsto_one first)

theorem singletonChildAt_first_quitNow_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ stationaryQuitNowPayoff reward (singletonChildRootAt first index)
      (some first)) atTop (nhds 0) := by
  simpa [soloReward_eq_matrix] using stationaryQuitNowPayoff_tendsto_solo
    (singletonChildRootAt first) (some first)
      (singletonChildRootAt_continue_tendsto_one first)

theorem firstChildProfileAt_eq_update_never (first : Fin 3) (index : ℕ) :
    firstChildProfileAt first index = Function.update (profile index) (some first)
      (quittingPureTimeBehaviorStrategy reward (some first) none) := by
  simp [firstChildProfileAt, profile, firstChildRootAt,
    quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]

theorem singletonChildProfileAt_eq_update_never (first : Fin 3) (index : ℕ) :
    singletonChildProfileAt first index =
      Function.update (firstChildProfileAt first index) (some (previousOwner first))
        (quittingPureTimeBehaviorStrategy reward (some (previousOwner first)) none) := by
  simp [singletonChildProfileAt, firstChildProfileAt, singletonChildRootAt,
    quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]

theorem sourceAt_never_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ stationaryNeverPayoff reward (root index) (some first))
      atTop (nhds (1 / 2 : ℝ)) := by
  apply (firstChildAt_first_payoff_tendsto first).congr'
  filter_upwards [] with index
  rw [firstChildProfileAt_eq_update_never]
  rfl

theorem firstChildAt_previous_never_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ stationaryNeverPayoff reward (firstChildRootAt first index)
      (some (previousOwner first))) atTop (nhds (2 : ℝ)) := by
  apply (singletonChildAt_previous_payoff_tendsto first).congr'
  filter_upwards [] with index
  rw [singletonChildProfileAt_eq_update_never]
  rfl

theorem singletonChildAt_first_never_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ stationaryNeverPayoff reward (singletonChildRootAt first index)
      (some first)) atTop (nhds (-1 : ℝ)) := by
  apply (singletonChildAt_first_payoff_tendsto first).congr'
  filter_upwards [] with index
  rw [stationaryNeverPayoff, quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]
  have hroot : Function.update (singletonChildRootAt first index) (some first)
      (PMF.pure false) = singletonChildRootAt first index := by
    fin_cases first <;>
      simp [singletonChildRootAt, firstChildRootAt, previousOwner]
  rw [hroot]
  rfl

theorem secondNeverGain_tendsto_all_core (first : Fin 3) : Tendsto (fun index ↦
    quittingTerminalPayoff reward (singletonChildProfileAt first index)
        (some (previousOwner first)) -
      quittingTerminalPayoff reward (firstChildProfileAt first index)
        (some (previousOwner first))) atTop (nhds (1 : ℝ)) := by
  convert (singletonChildAt_previous_payoff_tendsto first).sub
    (firstChildAt_previous_payoff_tendsto first) using 1
  norm_num

theorem finalQuitNowAt_payoff_tendsto (first : Fin 3) : Tendsto (fun index ↦
    quittingTerminalPayoff reward (finalQuitNowProfileAt first index) (some first))
    atTop (nhds 0) := by
  simpa [finalQuitNowProfileAt, singletonChildProfileAt, stationaryQuitNowPayoff] using
    singletonChildAt_first_quitNow_tendsto first

theorem reactivationGain_tendsto_all_core (first : Fin 3) : Tendsto (fun index ↦
    quittingTerminalPayoff reward (finalQuitNowProfileAt first index) (some first) -
      quittingTerminalPayoff reward (singletonChildProfileAt first index) (some first))
    atTop (nhds (1 : ℝ)) := by
  simpa using (finalQuitNowAt_payoff_tendsto first).sub
    (singletonChildAt_first_payoff_tendsto first)

def otherSecondChildRootAt (first : Fin 3) (index : ℕ) : Player → PMF Bool :=
  Function.update (firstChildRootAt first index) (some (nextOwner first)) (PMF.pure false)

def otherSecondChildProfileAt (first : Fin 3) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (otherSecondChildRootAt first index)

@[simp] theorem otherSecondChildRootAt_totalHazard (first : Fin 3) (index : ℕ) :
    quittingStationaryTotalHazard (otherSecondChildRootAt first index) =
      hazard index + hazard index ^ 2 := by
  fin_cases first <;>
    simp [quittingStationaryTotalHazard, otherSecondChildRootAt, firstChildRootAt,
      nextOwner, Fintype.sum_option, Fin.sum_univ_succ] <;> ring

def otherSingletonDirectionAt (first : Fin 3) : Player → ℝ := fun who =>
  if who = some (previousOwner first) then 1 else 0

theorem otherSecondChildRootAt_direction_tendsto (first : Fin 3) (who : Player) :
    Tendsto (fun index ↦ (otherSecondChildRootAt first index who true).toReal /
      quittingStationaryTotalHazard (otherSecondChildRootAt first index)) atTop
      (nhds (otherSingletonDirectionAt first who)) := by
  simp_rw [otherSecondChildRootAt_totalHazard]
  fin_cases first <;> cases who with
  | none =>
      simpa [otherSecondChildRootAt, firstChildRootAt, nextOwner,
        otherSingletonDirectionAt, previousOwner] using
        hazardSquare_div_linearSquare_tendsto 1 one_ne_zero
  | some who =>
      fin_cases who <;>
        simp [otherSecondChildRootAt, firstChildRootAt, nextOwner,
          otherSingletonDirectionAt, previousOwner]
      all_goals simpa [one_div] using
        (hazard_div_linearSquare_tendsto 1 one_ne_zero)

theorem otherSecondChildRootAt_totalHazard_tendsto_zero (first : Fin 3) :
    Tendsto (fun index ↦ quittingStationaryTotalHazard (otherSecondChildRootAt first index))
      atTop (nhds 0) := by
  simp_rw [otherSecondChildRootAt_totalHazard]
  simpa using hazard_tendsto_zero.add (hazard_tendsto_zero.pow 2)

theorem otherSecondChildRootAt_totalHazard_pos (first : Fin 3) (index : ℕ) :
    0 < quittingStationaryTotalHazard (otherSecondChildRootAt first index) := by
  rw [otherSecondChildRootAt_totalHazard]
  nlinarith [hazard_pos index, sq_nonneg (hazard index)]

theorem firstChildAt_next_payoff_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (firstChildProfileAt first index)
      (some (nextOwner first))) atTop (nhds (-1 / 2 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter (firstChildRootAt first)
    (firstChildRootAt_totalHazard_pos first) (firstChildRootAt_totalHazard_tendsto_zero first)
    (firstDirectionAt first) (firstChildRootAt_direction_tendsto first) (some (nextOwner first))
  convert h using 1
  congr 1
  fin_cases first <;>
    simp [firstDirectionAt, nextOwner, Fintype.sum_option, Fin.sum_univ_succ,
      StandardQSideExample.duplicatedCyclicMatrix,
      StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix] <;>
    norm_num

theorem otherSecondChildAt_next_payoff_tendsto (first : Fin 3) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (otherSecondChildProfileAt first index)
      (some (nextOwner first))) atTop (nhds (-1 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter (otherSecondChildRootAt first)
    (otherSecondChildRootAt_totalHazard_pos first)
    (otherSecondChildRootAt_totalHazard_tendsto_zero first)
    (otherSingletonDirectionAt first) (otherSecondChildRootAt_direction_tendsto first)
    (some (nextOwner first))
  convert h using 1
  congr 1
  fin_cases first <;>
    simp [otherSingletonDirectionAt, previousOwner, nextOwner, Fintype.sum_option,
      Fin.sum_univ_succ, StandardQSideExample.duplicatedCyclicMatrix,
      StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix]

/-- The other remaining leading-core owner has limiting Never gain `-1/2`.
Together with `secondNeverGain_tendsto_all_core`, this is literal uniqueness of the
positive limiting-gain owner among the two retained leading-core labels. -/
theorem otherRemainingNeverGain_tendsto_neg_half (first : Fin 3) : Tendsto (fun index ↦
    quittingTerminalPayoff reward (otherSecondChildProfileAt first index)
        (some (nextOwner first)) -
      quittingTerminalPayoff reward (firstChildProfileAt first index)
        (some (nextOwner first))) atTop (nhds (-1 / 2 : ℝ)) := by
  convert (otherSecondChildAt_next_payoff_tendsto first).sub
    (firstChildAt_next_payoff_tendsto first) using 1
  norm_num

/-- Eventually the selected preceding owner is the unique positive-gain Never mover
among the two retained leading-core owners. -/
theorem eventually_selectedRemainingGain_pos_and_otherGain_neg (first : Fin 3) :
    ∀ᶠ index in atTop,
      0 < quittingTerminalPayoff reward (singletonChildProfileAt first index)
          (some (previousOwner first)) -
        quittingTerminalPayoff reward (firstChildProfileAt first index)
          (some (previousOwner first)) ∧
      quittingTerminalPayoff reward (otherSecondChildProfileAt first index)
          (some (nextOwner first)) -
        quittingTerminalPayoff reward (firstChildProfileAt first index)
          (some (nextOwner first)) < 0 := by
  have hpos := (secondNeverGain_tendsto_all_core first).eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hneg := (otherRemainingNeverGain_tendsto_neg_half first).eventually
    (Iio_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0))
  exact hpos.and hneg

/-- For every cyclic choice of first core owner, that owner's first Never gain tends to
`1/6`, the displayed preceding owner's second Never gain tends to `1`, and after both
deletions the first owner reawakens by Quit0 with gain tending to `1`. -/
theorem eventually_all_core_twoNever_then_quitNow_exactCapChronology (first : Fin 3) :
    ∀ᶠ index in atTop,
      quittingTerminalPayoff reward (firstChildProfileAt first index) (some first) =
        quittingContinuationBestResponseValue reward (profile index) (some first) ∧
      1 / 12 ≤ quittingTerminalPayoff reward (firstChildProfileAt first index) (some first) -
        quittingTerminalPayoff reward (profile index) (some first) ∧
      quittingTerminalPayoff reward (singletonChildProfileAt first index)
          (some (previousOwner first)) =
        quittingContinuationBestResponseValue reward (firstChildProfileAt first index)
          (some (previousOwner first)) ∧
      1 / 2 ≤ quittingTerminalPayoff reward (singletonChildProfileAt first index)
          (some (previousOwner first)) -
        quittingTerminalPayoff reward (firstChildProfileAt first index)
          (some (previousOwner first)) ∧
      quittingTerminalPayoff reward (finalQuitNowProfileAt first index) (some first) =
        quittingContinuationBestResponseValue reward (singletonChildProfileAt first index)
          (some first) ∧
      1 / 2 ≤ quittingTerminalPayoff reward (finalQuitNowProfileAt first index) (some first) -
        quittingTerminalPayoff reward (singletonChildProfileAt first index) (some first) := by
  have hfirst := eventually_never_eq_completeCap_and_gain_ge_of_tendsto reward root (some first)
    0 (1 / 2) (1 / 3) (sourceAt_quitNow_tendsto first) (sourceAt_never_tendsto first)
    (source_core_payoff_tendsto first) (by norm_num) (by norm_num)
  have hsecond := eventually_never_eq_completeCap_and_gain_ge_of_tendsto reward
    (firstChildRootAt first) (some (previousOwner first)) 0 2 1
    (firstChildAt_previous_quitNow_tendsto first) (firstChildAt_previous_never_tendsto first)
    (firstChildAt_previous_payoff_tendsto first) (by norm_num) (by norm_num)
  have hfinal := eventually_quitNow_eq_completeCap_and_gain_ge_of_tendsto reward
    (singletonChildRootAt first) (some first) 0 (-1) (-1)
    (singletonChildAt_first_quitNow_tendsto first) (singletonChildAt_first_never_tendsto first)
    (singletonChildAt_first_payoff_tendsto first) (by norm_num) (by norm_num)
  filter_upwards [hfirst, hsecond, hfinal] with index hf hs hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [firstChildProfileAt_eq_update_never first index]
    exact hf.1
  · have heq : quittingTerminalPayoff reward (firstChildProfileAt first index) (some first) =
        stationaryNeverPayoff reward (root index) (some first) := by
      rw [firstChildProfileAt_eq_update_never]
      rfl
    rw [heq]
    norm_num at hf ⊢
    simpa [profile] using hf.2
  · rw [singletonChildProfileAt_eq_update_never first index]
    exact hs.1
  · have heq : quittingTerminalPayoff reward (singletonChildProfileAt first index)
        (some (previousOwner first)) = stationaryNeverPayoff reward
          (firstChildRootAt first index) (some (previousOwner first)) := by
      rw [singletonChildProfileAt_eq_update_never]
      rfl
    rw [heq]
    norm_num at hs ⊢
    simpa [firstChildProfileAt] using hs.2
  · simpa [finalQuitNowProfileAt, singletonChildProfileAt, stationaryQuitNowPayoff] using hq.1
  · simpa [finalQuitNowProfileAt, singletonChildProfileAt, stationaryQuitNowPayoff] using hq.2

/-- The all-Never semantic pair realizes, and hence minimizes, total debt zero. -/
theorem carrier_minimum_totalDebt_eq_zero :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair = 0 ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤ quittingTerminalSemanticDebtSum candidate := by
  let pair := quittingTerminalSemanticPair reward (quittingAlwaysContinueProfile reward)
  refine ⟨pair, subset_closure ⟨_, rfl⟩, ?_, ?_⟩
  · unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebt pair
    simp [quittingTerminalSemanticPair,
      quittingTerminalPayoff_quittingAlwaysContinue,
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      reward_singleton]
  · intro candidate hcandidate
    rw [show quittingTerminalSemanticDebtSum pair = 0 by
      unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebt pair
      simp [quittingTerminalSemanticPair,
        quittingTerminalPayoff_quittingAlwaysContinue,
        quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
        reward_singleton]]
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ ↦
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hcandidate who

end DuplicatedCyclicReactivationRegression
end GameTheory
