/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.StandardQSideExample
import UniformEquilibrium.Quitting.Stationary.StrictEndpointSelection
import UniformEquilibrium.Quitting.Boundary.Repair.NegativeQuitPrefixRegression
import UniformEquilibrium.Quitting.Circulation.DirectionBarycenter
import UniformEquilibrium.Diagnostics.Quitting.PeriodOnePaidPortAdapters
import MathUE.ProbabilityMassFunction.Simplex
import MathUE.Topology.FiniteLimitDecomposition

/-! # The duplicated-cyclic support-descent reactivation regression -/

noncomputable section

namespace GameTheory
namespace DuplicatedCyclicReactivationRegression

open Filter Math.Probability Math.PMFProduct
open QuittingLCPClassification
open scoped Topology

abbrev Player := QuittingLCPClassification.StandardQSideExample.Player

def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who ↦ if terminal.val.card = 1 then
    QuittingLCPClassification.StandardQSideExample.duplicatedCyclicMatrix who
      (Classical.choose terminal.property)
  else 0

@[simp] theorem reward_singleton (who owner : Player) :
    reward (quittingSingletonTerminal owner) who =
      QuittingLCPClassification.StandardQSideExample.duplicatedCyclicMatrix who owner := by
  simp only [reward, quittingSingletonTerminal, Finset.card_singleton, ↓reduceIte]
  congr 1
  have hmem := Classical.choose_spec (Finset.singleton_nonempty owner)
  simpa using hmem

@[simp] theorem soloReward_eq_matrix (owner who : Player) :
    quittingSoloReward reward owner who =
      StandardQSideExample.duplicatedCyclicMatrix who owner := by
  exact reward_singleton who owner

theorem reward_nonsingleton (terminal : {S : Finset Player // S.Nonempty})
    (hcard : terminal.val.card ≠ 1) : reward terminal = 0 := by
  funext who
  simp [reward, hcard]

theorem normalizedSoloMatrix_reward :
    normalizedSoloMatrix reward =
      QuittingLCPClassification.StandardQSideExample.duplicatedCyclicMatrix := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  funext who owner
  rw [quittingProjectiveLCPMatrix]
  rw [show reward (quittingProjectiveSingletonTerminal owner) who =
      StandardQSideExample.duplicatedCyclicMatrix who owner by
    simpa [quittingProjectiveSingletonTerminal, quittingSingletonTerminal] using
      reward_singleton who owner]
  rw [show reward (quittingProjectiveSingletonTerminal who) who = 0 by
    calc
      reward (quittingProjectiveSingletonTerminal who) who =
          StandardQSideExample.duplicatedCyclicMatrix who who := by
        simpa [quittingProjectiveSingletonTerminal, quittingSingletonTerminal] using
          reward_singleton who who
      _ = 0 := StandardQSideExample.duplicatedCyclicMatrix_diagonal who]
  simp

/-- The common leading hazard `h_n`; the duplicated coordinate uses its square. -/
def hazard (index : ℕ) : ℝ := 1 / (index + 2 : ℝ)

theorem hazard_pos (index : ℕ) : 0 < hazard index := by
  apply one_div_pos.mpr
  positivity

theorem hazard_le_one (index : ℕ) : hazard index ≤ 1 := by
  dsimp [hazard]
  apply (div_le_one (by positivity)).2
  have hindex : (0 : ℝ) ≤ index := Nat.cast_nonneg index
  linarith

theorem hazard_lt_one (index : ℕ) : hazard index < 1 := by
  rw [hazard, div_lt_one (by positivity)]
  have hindex : (0 : ℝ) ≤ index := Nat.cast_nonneg index
  linarith

theorem hazard_tendsto_zero : Tendsto hazard atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  funext index
  simp [hazard, Function.comp_apply, Nat.cast_add]
  ring

def root (index : ℕ) : Player → PMF Bool
  | none => Math.ProbabilityMassFunction.bernoulliBool (hazard index ^ 2)
      (sq_nonneg _) (by nlinarith [hazard_pos index, hazard_le_one index])
  | some _ => Math.ProbabilityMassFunction.bernoulliBool (hazard index)
      (hazard_pos index).le (hazard_le_one index)

@[simp] theorem root_core_quit (index : ℕ) (owner : Fin 3) :
    (root index (some owner) true).toReal = hazard index := by
  simp [root]

@[simp] theorem root_duplicate_quit (index : ℕ) :
    (root index none true).toReal = hazard index ^ 2 := by
  simp [root]

theorem root_quit_tendsto_zero (who : Player) :
    Tendsto (fun index ↦ (root index who true).toReal) atTop (nhds 0) := by
  cases who with
  | none => simpa using hazard_tendsto_zero.pow 2
  | some owner => simpa using hazard_tendsto_zero

@[simp] theorem totalHazard_eq (index : ℕ) :
    quittingStationaryTotalHazard (root index) = 3 * hazard index + hazard index ^ 2 := by
  rw [quittingStationaryTotalHazard, Fintype.sum_option]
  simp
  ring

theorem totalHazard_pos (index : ℕ) :
    0 < quittingStationaryTotalHazard (root index) := by
  rw [totalHazard_eq]
  nlinarith [hazard_pos index, sq_nonneg (hazard index)]

theorem core_normalizedHazard_tendsto_third (owner : Fin 3) :
    Tendsto (fun index ↦ (root index (some owner) true).toReal /
      quittingStationaryTotalHazard (root index)) atTop (nhds (1 / 3 : ℝ)) := by
  simp_rw [root_core_quit, totalHazard_eq]
  have hevent : ∀ᶠ index in atTop, hazard index ≠ 0 :=
    Filter.Eventually.of_forall fun index ↦ (hazard_pos index).ne'
  have hden : Tendsto (fun index : ℕ ↦ (3 : ℝ) + hazard index) atTop (nhds 3) :=
    by simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (nhds 3)).add
        hazard_tendsto_zero
  have hlim : Tendsto (fun index : ℕ ↦ (1 : ℝ) / (3 + hazard index))
      atTop (nhds (1 / 3 : ℝ)) := tendsto_const_nhds.div hden (by norm_num)
  exact hlim.congr' (hevent.mono fun index hne ↦ by
    field_simp)

theorem duplicate_normalizedHazard_tendsto_zero :
    Tendsto (fun index ↦ (root index none true).toReal /
      quittingStationaryTotalHazard (root index)) atTop (nhds 0) := by
  simp_rw [root_duplicate_quit, totalHazard_eq]
  have hevent : ∀ᶠ index in atTop, hazard index ≠ 0 :=
    Filter.Eventually.of_forall fun index ↦ (hazard_pos index).ne'
  have hden : Tendsto (fun index : ℕ ↦ (3 : ℝ) + hazard index) atTop (nhds 3) :=
    by simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (nhds 3)).add
        hazard_tendsto_zero
  have hlim : Tendsto (fun index : ℕ ↦ hazard index / (3 + hazard index))
      atTop (nhds 0) := by
    convert hazard_tendsto_zero.div hden (by norm_num : (3 : ℝ) ≠ 0) using 1
    · funext index
      rfl
    · norm_num
  exact hlim.congr' (hevent.mono fun index hne ↦ by
    field_simp)

def profile (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (root index)

/-- A small direct stationary-law adapter used by the concrete regression. -/
theorem stationaryPayoff_tendsto_singletonBarycenter
    (roots : ℕ → Player → PMF Bool)
    (hpositive : ∀ index, 0 < quittingStationaryTotalHazard (roots index))
    (htotal : Tendsto (fun index ↦ quittingStationaryTotalHazard (roots index))
      atTop (nhds 0)) (direction : Player → ℝ)
    (hdirection : ∀ owner, Tendsto (fun index ↦
      (roots index owner true).toReal / quittingStationaryTotalHazard (roots index))
      atTop (nhds (direction owner))) (who : Player) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (quittingStationaryProfile reward (roots index)) who) atTop
      (nhds (∑ owner, direction owner * quittingSoloReward reward owner who)) := by
  have hbary := tendsto_finsetSum Finset.univ fun owner _ ↦
    (hdirection owner).mul_const (quittingSoloReward reward owner who)
  have hbary' : Tendsto (fun index ↦ quittingStationarySingletonDirectionBarycenter
      reward (roots index) who) atTop
      (nhds (∑ owner, direction owner * quittingSoloReward reward owner who)) := by
    simpa [quittingStationarySingletonDirectionBarycenter] using hbary
  have hhalf : ∀ᶠ index in atTop,
      quittingStationaryTotalHazard (roots index) ≤ 1 / 2 :=
    (htotal.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ h ↦ h.le
  have hdiff := Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _
    (by simpa using htotal.const_mul (6 * quittingRewardBound reward))
    (hhalf.mono fun index h ↦
      abs_stationaryPayoff_sub_singletonDirectionBarycenter_le reward
        (abs_reward_le_quittingRewardBound reward) (roots index) who
        (hpositive index) h)
  simpa using hdiff.add hbary'

def firstChildRoot (index : ℕ) : Player → PMF Bool :=
  Function.update (root index) (some 0) (PMF.pure false)

def singletonChildRoot (index : ℕ) : Player → PMF Bool :=
  Function.update (firstChildRoot index) (some 2) (PMF.pure false)

def firstChildProfile (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (firstChildRoot index)

def singletonChildProfile (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (singletonChildRoot index)

theorem firstChildProfile_eq_update_never (index : ℕ) :
    firstChildProfile index = Function.update (profile index) (some 0)
      (quittingPureTimeBehaviorStrategy reward (some 0) none) := by
  simp [firstChildProfile, profile, firstChildRoot,
    quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]

theorem singletonChildProfile_eq_update_never (index : ℕ) :
    singletonChildProfile index = Function.update (firstChildProfile index) (some 2)
      (quittingPureTimeBehaviorStrategy reward (some 2) none) := by
  simp [singletonChildProfile, firstChildProfile, singletonChildRoot,
    quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]

@[simp] theorem firstChild_totalHazard_eq (index : ℕ) :
    quittingStationaryTotalHazard (firstChildRoot index) =
      2 * hazard index + hazard index ^ 2 := by
  rw [quittingStationaryTotalHazard, Fintype.sum_option]
  simp [firstChildRoot, Fin.sum_univ_succ]
  ring

@[simp] theorem singletonChild_totalHazard_eq (index : ℕ) :
    quittingStationaryTotalHazard (singletonChildRoot index) =
      hazard index + hazard index ^ 2 := by
  rw [quittingStationaryTotalHazard, Fintype.sum_option]
  simp [singletonChildRoot, firstChildRoot, Fin.sum_univ_succ]
  ring

theorem hazard_div_linearSquare_tendsto (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun index ↦ hazard index / (c * hazard index + hazard index ^ 2))
      atTop (nhds (1 / c)) := by
  have hden : Tendsto (fun index ↦ c + hazard index) atTop (nhds c) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (nhds c)).add
      hazard_tendsto_zero
  have hlim : Tendsto (fun index ↦ (1 : ℝ) / (c + hazard index))
      atTop (nhds (1 / c)) := tendsto_const_nhds.div hden hc
  exact hlim.congr' (Filter.Eventually.of_forall fun index ↦ by
    field_simp [(hazard_pos index).ne'])

theorem hazardSquare_div_linearSquare_tendsto (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun index ↦ hazard index ^ 2 / (c * hazard index + hazard index ^ 2))
      atTop (nhds 0) := by
  have hden : Tendsto (fun index ↦ c + hazard index) atTop (nhds c) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (nhds c)).add
      hazard_tendsto_zero
  have hlim : Tendsto (fun index ↦ hazard index / (c + hazard index))
      atTop (nhds 0) := by
    convert hazard_tendsto_zero.div hden hc using 1
    · funext index
      rfl
    · simp
  exact hlim.congr' (Filter.Eventually.of_forall fun index ↦ by
    field_simp [(hazard_pos index).ne'])

def firstChildDirection : Player → ℝ
  | none => 0
  | some 0 => 0
  | some _ => 1 / 2

def singletonChildDirection : Player → ℝ
  | some 1 => 1
  | _ => 0

def sourceDirection : Player → ℝ
  | none => 0
  | some _ => 1 / 3

theorem source_direction_tendsto (who : Player) :
    Tendsto (fun index ↦ (root index who true).toReal /
      quittingStationaryTotalHazard (root index)) atTop (nhds (sourceDirection who)) := by
  cases who with
  | none => simpa [sourceDirection] using duplicate_normalizedHazard_tendsto_zero
  | some who => simpa [sourceDirection] using core_normalizedHazard_tendsto_third who

theorem firstChild_direction_tendsto (who : Player) :
    Tendsto (fun index ↦ (firstChildRoot index who true).toReal /
      quittingStationaryTotalHazard (firstChildRoot index)) atTop
      (nhds (firstChildDirection who)) := by
  simp_rw [firstChild_totalHazard_eq]
  cases who with
  | none => simpa [firstChildRoot, firstChildDirection] using
      hazardSquare_div_linearSquare_tendsto 2 (by norm_num)
  | some who =>
      fin_cases who
      · simp [firstChildRoot, firstChildDirection]
      · simpa [firstChildRoot, firstChildDirection] using
          hazard_div_linearSquare_tendsto 2 (by norm_num)
      · simpa [firstChildRoot, firstChildDirection] using
          hazard_div_linearSquare_tendsto 2 (by norm_num)

theorem singletonChild_direction_tendsto (who : Player) :
    Tendsto (fun index ↦ (singletonChildRoot index who true).toReal /
      quittingStationaryTotalHazard (singletonChildRoot index)) atTop
      (nhds (singletonChildDirection who)) := by
  simp_rw [singletonChild_totalHazard_eq]
  cases who with
  | none => simpa [singletonChildRoot, firstChildRoot, singletonChildDirection] using
      hazardSquare_div_linearSquare_tendsto 1 one_ne_zero
  | some who =>
      fin_cases who
      · simp [singletonChildRoot, firstChildRoot, singletonChildDirection]
      · simpa [singletonChildRoot, firstChildRoot, singletonChildDirection] using
          hazard_div_linearSquare_tendsto 1 one_ne_zero
      · simp [singletonChildRoot, firstChildRoot, singletonChildDirection]

theorem totalHazard_tendsto_zero :
    Tendsto (fun index ↦ quittingStationaryTotalHazard (root index)) atTop (nhds 0) := by
  simp_rw [totalHazard_eq]
  simpa using (hazard_tendsto_zero.const_mul 3).add (hazard_tendsto_zero.pow 2)

theorem firstChild_totalHazard_tendsto_zero :
    Tendsto (fun index ↦ quittingStationaryTotalHazard (firstChildRoot index))
      atTop (nhds 0) := by
  simp_rw [firstChild_totalHazard_eq]
  simpa using (hazard_tendsto_zero.const_mul 2).add (hazard_tendsto_zero.pow 2)

theorem singletonChild_totalHazard_tendsto_zero :
    Tendsto (fun index ↦ quittingStationaryTotalHazard (singletonChildRoot index))
      atTop (nhds 0) := by
  simp_rw [singletonChild_totalHazard_eq]
  simpa using hazard_tendsto_zero.add (hazard_tendsto_zero.pow 2)

theorem firstChild_totalHazard_pos (index : ℕ) :
    0 < quittingStationaryTotalHazard (firstChildRoot index) := by
  rw [firstChild_totalHazard_eq]
  nlinarith [hazard_pos index, sq_nonneg (hazard index)]

theorem singletonChild_totalHazard_pos (index : ℕ) :
    0 < quittingStationaryTotalHazard (singletonChildRoot index) := by
  rw [singletonChild_totalHazard_eq]
  nlinarith [hazard_pos index, sq_nonneg (hazard index)]

theorem source_playerZero_payoff_tendsto :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (profile index) (some 0))
      atTop (nhds (1 / 3 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter root totalHazard_pos
    totalHazard_tendsto_zero sourceDirection source_direction_tendsto (some 0)
  convert h using 1
  congr 1
  norm_num [profile, sourceDirection, soloReward_eq_matrix,
    Fintype.sum_option, Fin.sum_univ_succ,
    StandardQSideExample.duplicatedCyclicMatrix,
    StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix]

theorem firstChild_playerZero_payoff_tendsto :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (firstChildProfile index) (some 0))
      atTop (nhds (1 / 2 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter firstChildRoot
    firstChild_totalHazard_pos firstChild_totalHazard_tendsto_zero firstChildDirection
    firstChild_direction_tendsto (some 0)
  convert h using 1
  congr 1
  norm_num [firstChildProfile, firstChildDirection, soloReward_eq_matrix,
    Fintype.sum_option, Fin.sum_univ_succ,
    StandardQSideExample.duplicatedCyclicMatrix,
    StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix]

theorem firstChild_playerTwo_payoff_tendsto :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (firstChildProfile index) (some 2))
      atTop (nhds (1 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter firstChildRoot
    firstChild_totalHazard_pos firstChild_totalHazard_tendsto_zero firstChildDirection
    firstChild_direction_tendsto (some 2)
  convert h using 1
  congr 1
  norm_num [firstChildProfile, firstChildDirection, soloReward_eq_matrix,
    Fintype.sum_option, Fin.sum_univ_succ,
    StandardQSideExample.duplicatedCyclicMatrix,
    StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix]
  have hcard : ({x : Fin 2 | x.succ = (1 : Fin 3)} : Finset (Fin 2)).card = 1 := by decide
  rw [hcard]
  norm_num

theorem singletonChild_playerTwo_payoff_tendsto :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (singletonChildProfile index) (some 2))
      atTop (nhds (2 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter singletonChildRoot
    singletonChild_totalHazard_pos singletonChild_totalHazard_tendsto_zero
    singletonChildDirection singletonChild_direction_tendsto (some 2)
  simpa [singletonChildProfile, singletonChildDirection,
    Fintype.sum_option, Fin.sum_univ_succ,
    StandardQSideExample.duplicatedCyclicMatrix,
    StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix] using h

theorem singletonChild_playerZero_payoff_tendsto :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (singletonChildProfile index) (some 0))
      atTop (nhds (-1 : ℝ)) := by
  have h := stationaryPayoff_tendsto_singletonBarycenter singletonChildRoot
    singletonChild_totalHazard_pos singletonChild_totalHazard_tendsto_zero
    singletonChildDirection singletonChild_direction_tendsto (some 0)
  simpa [singletonChildProfile, singletonChildDirection,
    Fintype.sum_option, Fin.sum_univ_succ,
    StandardQSideExample.duplicatedCyclicMatrix,
    StandardQSideExample.duplicateCollapse, StandardQSideExample.cyclicMatrix] using h

theorem stationaryQuitNowPayoff_tendsto_solo
    (roots : ℕ → Player → PMF Bool) (payer : Player)
    (hcontinue : ∀ who, Tendsto (fun index ↦ (roots index who false).toReal)
      atTop (nhds 1)) :
    Tendsto (fun index ↦ stationaryQuitNowPayoff reward (roots index) payer)
      atTop (nhds (quittingSoloReward reward payer payer)) := by
  have hlaw := stationaryProfile_quitNow_terminalOutcomeMass_tendsto_singleton
    (reward := reward) roots payer hcontinue
  have hmoment := (continuous_quittingTerminalRewardMoment reward).tendsto
    (quittingSingletonTerminalOutcomeMass payer) |>.comp hlaw
  have hcoordinate := (continuous_apply payer).tendsto
    (quittingTerminalRewardMoment reward (quittingSingletonTerminalOutcomeMass payer)) |>.comp
      hmoment
  have hp : Tendsto (fun index ↦ stationaryQuitNowPayoff reward (roots index) payer)
      atTop (nhds (quittingTerminalRewardMoment reward
        (quittingSingletonTerminalOutcomeMass payer) payer)) := by
    apply hcoordinate.congr'
    filter_upwards [] with index
    change (quittingTerminalRewardMoment reward
      (quittingTerminalOutcomeMass reward
        (Function.update (quittingStationaryProfile reward (roots index)) payer
          (quittingPureTimeBehaviorStrategy reward payer (some 0))))) payer = _
    exact congrFun (quittingTerminalRewardMoment_outcomeMass reward _) payer
  convert hp using 1
  congr 2
  simp [quittingTerminalRewardMoment, quittingSingletonTerminalOutcomeMass,
    quittingTerminalOutcomeReward, quittingSoloReward]
  unfold reward
  simp only [Finset.card_singleton, ↓reduceIte]
  have hchoose : Classical.choose (show ({payer} : Finset Player).Nonempty by simp) = payer := by
    have hmem := Classical.choose_spec (show ({payer} : Finset Player).Nonempty by simp)
    simpa using hmem
  rw [hchoose, StandardQSideExample.duplicatedCyclicMatrix_diagonal]

theorem root_continue_tendsto_one (who : Player) :
    Tendsto (fun index ↦ (root index who false).toReal) atTop (nhds 1) := by
  simpa [pmfBool_false_toReal] using (root_quit_tendsto_zero who).const_sub 1

theorem firstChild_continue_tendsto_one (who : Player) :
    Tendsto (fun index ↦ (firstChildRoot index who false).toReal) atTop (nhds 1) := by
  by_cases hwho : who = some 0
  · subst who
    simp [firstChildRoot]
  · simpa [firstChildRoot, Function.update_of_ne hwho] using root_continue_tendsto_one who

theorem singletonChild_continue_tendsto_one (who : Player) :
    Tendsto (fun index ↦ (singletonChildRoot index who false).toReal) atTop (nhds 1) := by
  by_cases hwho : who = some 2
  · subst who
    simp [singletonChildRoot]
  · simpa [singletonChildRoot, Function.update_of_ne hwho] using
      firstChild_continue_tendsto_one who

theorem source_playerZero_quitNow_tendsto :
    Tendsto (fun index ↦ stationaryQuitNowPayoff reward (root index) (some 0))
      atTop (nhds 0) := by
  simpa [soloReward_eq_matrix] using stationaryQuitNowPayoff_tendsto_solo
    root (some 0) root_continue_tendsto_one

theorem firstChild_playerTwo_quitNow_tendsto :
    Tendsto (fun index ↦ stationaryQuitNowPayoff reward (firstChildRoot index) (some 2))
      atTop (nhds 0) := by
  simpa [soloReward_eq_matrix] using stationaryQuitNowPayoff_tendsto_solo
    firstChildRoot (some 2) firstChild_continue_tendsto_one

theorem singletonChild_playerZero_quitNow_tendsto :
    Tendsto (fun index ↦ stationaryQuitNowPayoff reward (singletonChildRoot index) (some 0))
      atTop (nhds 0) := by
  simpa [soloReward_eq_matrix] using stationaryQuitNowPayoff_tendsto_solo
    singletonChildRoot (some 0) singletonChild_continue_tendsto_one

theorem source_playerZero_never_tendsto :
    Tendsto (fun index ↦ stationaryNeverPayoff reward (root index) (some 0))
      atTop (nhds (1 / 2 : ℝ)) := by
  apply firstChild_playerZero_payoff_tendsto.congr'
  filter_upwards [] with index
  rw [firstChildProfile_eq_update_never]
  rfl

theorem firstChild_playerTwo_never_tendsto :
    Tendsto (fun index ↦ stationaryNeverPayoff reward (firstChildRoot index) (some 2))
      atTop (nhds (2 : ℝ)) := by
  apply singletonChild_playerTwo_payoff_tendsto.congr'
  filter_upwards [] with index
  rw [singletonChildProfile_eq_update_never]
  rfl

theorem singletonChild_playerZero_never_tendsto :
    Tendsto (fun index ↦ stationaryNeverPayoff reward (singletonChildRoot index) (some 0))
      atTop (nhds (-1 : ℝ)) := by
  apply singletonChild_playerZero_payoff_tendsto.congr'
  filter_upwards [] with index
  rw [stationaryNeverPayoff, quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]
  have hroot : Function.update (singletonChildRoot index) (some 0) (PMF.pure false) =
      singletonChildRoot index := by
    simp [singletonChildRoot, firstChildRoot]
  rw [hroot]
  rw [singletonChildProfile]

theorem source_playerZero_never_eq_firstChildPayoff (index : ℕ) :
    stationaryNeverPayoff reward (root index) (some 0) =
      quittingTerminalPayoff reward (firstChildProfile index) (some 0) := by
  rw [firstChildProfile_eq_update_never]
  rfl

theorem firstChild_playerTwo_never_eq_singletonChildPayoff (index : ℕ) :
    stationaryNeverPayoff reward (firstChildRoot index) (some 2) =
      quittingTerminalPayoff reward (singletonChildProfile index) (some 2) := by
  rw [singletonChildProfile_eq_update_never]
  rfl

theorem firstNeverGain_tendsto : Tendsto (fun index ↦
    quittingTerminalPayoff reward (firstChildProfile index) (some 0) -
      quittingTerminalPayoff reward (profile index) (some 0)) atTop
    (nhds (1 / 6 : ℝ)) := by
  have h := source_playerZero_never_tendsto.sub source_playerZero_payoff_tendsto
  convert h.congr' (Filter.Eventually.of_forall fun index ↦ by
    rw [source_playerZero_never_eq_firstChildPayoff index]) using 1
  norm_num

theorem secondNeverGain_tendsto : Tendsto (fun index ↦
    quittingTerminalPayoff reward (singletonChildProfile index) (some 2) -
      quittingTerminalPayoff reward (firstChildProfile index) (some 2)) atTop
    (nhds (1 : ℝ)) := by
  convert singletonChild_playerTwo_payoff_tendsto.sub
    firstChild_playerTwo_payoff_tendsto using 1
  norm_num

def finalQuitNowProfile (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (singletonChildProfile index) (some 0)
    (quittingPureTimeBehaviorStrategy reward (some 0) (some 0))

theorem finalQuitNowPayoff_tendsto : Tendsto (fun index ↦
    quittingTerminalPayoff reward (finalQuitNowProfile index) (some 0))
    atTop (nhds 0) := by
  simpa [finalQuitNowProfile, stationaryQuitNowPayoff, singletonChildProfile] using
    singletonChild_playerZero_quitNow_tendsto

theorem reactivationGain_tendsto : Tendsto (fun index ↦
    quittingTerminalPayoff reward (finalQuitNowProfile index) (some 0) -
      quittingTerminalPayoff reward (singletonChildProfile index) (some 0)) atTop
    (nhds (1 : ℝ)) := by
  simpa using finalQuitNowPayoff_tendsto.sub singletonChild_playerZero_payoff_tendsto

/-- The exact packet chronology: two literal Never children followed by the
first removed player's literal Quit-now reactivation. Every selected endpoint
is the unrestricted behavioral cap at its actual predecessor. -/
theorem eventually_literal_twoNever_then_quitNow_exactCapChronology :
    ∀ᶠ index in atTop,
      firstChildProfile index = Function.update (profile index) (some 0)
        (quittingPureTimeBehaviorStrategy reward (some 0) none) ∧
      quittingTerminalPayoff reward (firstChildProfile index) (some 0) =
        quittingContinuationBestResponseValue reward (profile index) (some 0) ∧
      1 / 12 ≤ quittingTerminalPayoff reward (firstChildProfile index) (some 0) -
        quittingTerminalPayoff reward (profile index) (some 0) ∧
      singletonChildProfile index = Function.update (firstChildProfile index) (some 2)
        (quittingPureTimeBehaviorStrategy reward (some 2) none) ∧
      quittingTerminalPayoff reward (singletonChildProfile index) (some 2) =
        quittingContinuationBestResponseValue reward (firstChildProfile index) (some 2) ∧
      1 / 2 ≤ quittingTerminalPayoff reward (singletonChildProfile index) (some 2) -
        quittingTerminalPayoff reward (firstChildProfile index) (some 2) ∧
      finalQuitNowProfile index = Function.update (singletonChildProfile index) (some 0)
        (quittingPureTimeBehaviorStrategy reward (some 0) (some 0)) ∧
      quittingTerminalPayoff reward (finalQuitNowProfile index) (some 0) =
        quittingContinuationBestResponseValue reward (singletonChildProfile index) (some 0) ∧
      1 / 2 ≤ quittingTerminalPayoff reward (finalQuitNowProfile index) (some 0) -
        quittingTerminalPayoff reward (singletonChildProfile index) (some 0) := by
  have hfirst := eventually_never_eq_completeCap_and_gain_ge_of_tendsto reward root (some 0)
    0 (1 / 2) (1 / 3) source_playerZero_quitNow_tendsto
    source_playerZero_never_tendsto source_playerZero_payoff_tendsto (by norm_num) (by norm_num)
  have hsecond := eventually_never_eq_completeCap_and_gain_ge_of_tendsto reward
    firstChildRoot (some 2) 0 2 1 firstChild_playerTwo_quitNow_tendsto
    firstChild_playerTwo_never_tendsto firstChild_playerTwo_payoff_tendsto
    (by norm_num) (by norm_num)
  have hfinal := eventually_quitNow_eq_completeCap_and_gain_ge_of_tendsto reward
    singletonChildRoot (some 0) 0 (-1) (-1) singletonChild_playerZero_quitNow_tendsto
    singletonChild_playerZero_never_tendsto singletonChild_playerZero_payoff_tendsto
    (by norm_num) (by norm_num)
  filter_upwards [hfirst, hsecond, hfinal] with index hf hs hq
  refine ⟨firstChildProfile_eq_update_never index, ?_, ?_,
    singletonChildProfile_eq_update_never index, ?_, ?_, rfl, ?_, ?_⟩
  · rw [← source_playerZero_never_eq_firstChildPayoff index]
    exact hf.1
  · rw [← source_playerZero_never_eq_firstChildPayoff index]
    norm_num at hf ⊢
    exact hf.2
  · rw [← firstChild_playerTwo_never_eq_singletonChildPayoff index]
    exact hs.1
  · rw [← firstChild_playerTwo_never_eq_singletonChildPayoff index]
    norm_num at hs ⊢
    exact hs.2
  · simpa [finalQuitNowProfile, singletonChildProfile, stationaryQuitNowPayoff] using hq.1
  · simpa [finalQuitNowProfile, singletonChildProfile, stationaryQuitNowPayoff] using hq.2

/-- Despite the profitable local descent and reactivation below, the same
table has literal all-Never as an exact terminal Nash profile. -/
theorem alwaysContinue_isExactTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAlwaysContinueProfile reward) := by
  apply (isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl).2
  intro who
  rw [reward_singleton,
    QuittingLCPClassification.StandardQSideExample.duplicatedCyclicMatrix_diagonal]

end DuplicatedCyclicReactivationRegression
end GameTheory
