/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCoreStrictnessExample
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.AnchoredCyclicRenewal
import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicRenewal

/-!
# An exact interior anchored solo-periodic calibration of the strictness table

`UniformEquilibrium/Quitting/Classification/LCP/NormalCoreStrictnessExample.lean`
fixes the literal three-player quitting reward table `reward`, whose normalized
singleton comparison matrix is the diagnostic for the distinct-witness
normal-player recursion (`normalizedSoloMatrix_eq_comparisonMatrix`).  This
module asks whether that table admits an
`IsExactAnchoredSoloPeriodic` profile (`UniformEquilibrium/Quitting/Cycles/
AnchoredSoloPeriodic.lean`) with an *interior* hazard family — every phase
hazard strictly between `0` and `1` — and answers yes, at period one.

Player `2`'s solo exit pays every other player `1` and pays itself `0`
(`reward`'s singleton rows), so scheduling player `2` alone, every phase,
period one, is exactly Nash against its own on-path value at *any* interior
hazard: the owner is indifferent by construction (its own row pays it what a
degenerate period-one on-path value must equal), and both other players'
spectator floors are the exact reward `1` regardless of the hazard used,
because the pair reward and both players' own singleton rows are already `0`.
The hazard therefore cancels out of the calibration entirely; the witness
below fixes it at `1 / 2` only to exhibit one concrete interior value, and
`isExactAnchoredSoloPeriodic_calibration` proves the same conclusion for an
arbitrary interior hazard.

## Reproduction

This module can be checked independently with Lean.

## Scope

This is a checked statement about the one literal table fixed in
`NormalCoreStrictnessExample.lean`, restricted to the anchored solo-periodic
profile class of `AnchoredSoloPeriodic.lean` (one designated quitter per
phase, every other player surely continuing).  No claim is made about other
profile classes or other tables.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification
namespace NormalCoreStrictnessExample

open Math.Probability

/-! ## The witness schedule and hazard -/

/-- Period one: player `2` quits, every phase. -/
def calibrationSchedule : Fin 1 → Player := fun _ => 2

/-- The constant hazard family at rate `p`. -/
def calibrationHazard (p : ℝ) : Fin 1 → ℝ := fun _ => p

theorem calibrationHazard_nonneg {p : ℝ} (hp0 : 0 ≤ p) :
    ∀ k, 0 ≤ calibrationHazard p k := fun _ => hp0

theorem calibrationHazard_le_one {p : ℝ} (hp1 : p ≤ 1) :
    ∀ k, calibrationHazard p k ≤ 1 := fun _ => hp1

/-! ## Every singleton row, decided by unfolding the reward table directly -/

/-- Every singleton row of the reward table, read off the table's own
`if`-chain by discharging each Finset comparison with `decide`, kept separate
from the real-number entries. -/
theorem reward_singletonTerminal_eval (owner : Player) :
    reward (quittingSingletonTerminal owner) =
      ![![0, -1, 1], ![1, 0, -1], ![1, 1, 0]] owner := by
  fin_cases owner
  · show (if (({0} : Finset Player) = {0}) then (![0, -1, 1] : Payoff Player)
        else if ({0} : Finset Player) = {1} then ![1, 0, -1]
        else if ({0} : Finset Player) = {2} then ![1, 1, 0] else 0) = ![0, -1, 1]
    rw [if_pos rfl]
  · show (if (({1} : Finset Player) = {0}) then (![0, -1, 1] : Payoff Player)
        else if ({1} : Finset Player) = {1} then ![1, 0, -1]
        else if ({1} : Finset Player) = {2} then ![1, 1, 0] else 0) = ![1, 0, -1]
    rw [if_neg (by decide), if_pos rfl]
  · show (if (({2} : Finset Player) = {0}) then (![0, -1, 1] : Payoff Player)
        else if ({2} : Finset Player) = {1} then ![1, 0, -1]
        else if ({2} : Finset Player) = {2} then ![1, 1, 0] else 0) = ![1, 1, 0]
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- Player `2`'s explicit singleton row. -/
theorem reward_singletonTerminal_two :
    reward (quittingSingletonTerminal (2 : Player)) = ![1, 1, 0] := by
  rw [reward_singletonTerminal_eval]
  rfl

/-- Every diagonal entry (a player's own singleton row, at itself) is `0`. -/
theorem reward_singletonTerminal_self (owner : Player) :
    reward (quittingSingletonTerminal owner) owner = 0 := by
  rw [reward_singletonTerminal_eval]
  fin_cases owner <;> rfl

/-- Every pair reward is `0`: the table pays every coalition of size other
than one exactly `0`. -/
theorem reward_pair_eq_zero (first second : Player) (hne : first ≠ second) :
    reward ⟨{first, second}, Finset.insert_nonempty first {second}⟩ = 0 := by
  have hnotsingle : ∀ o : Player, ({first, second} : Finset Player) ≠ {o} := by
    intro o heq
    have hmem : second ∈ ({o} : Finset Player) := heq ▸ (by simp)
    have hmem' : first ∈ ({o} : Finset Player) := heq ▸ (by simp)
    rw [Finset.mem_singleton] at hmem hmem'
    exact hne (hmem'.trans hmem.symm)
  show (if ({first, second} : Finset Player) = {0} then (![0, -1, 1] : Payoff Player)
      else if ({first, second} : Finset Player) = {1} then ![1, 0, -1]
      else if ({first, second} : Finset Player) = {2} then ![1, 1, 0] else 0) = 0
  rw [if_neg (hnotsingle 0), if_neg (hnotsingle 1), if_neg (hnotsingle 2)]

/-! ## The on-path value is player `2`'s own singleton row, for any hazard -/

/-- The constant family at player `2`'s singleton row solves the renewal
system of the calibration schedule, whatever the hazard rate. -/
theorem isAnchoredCyclicRenewalSolution_calibration (p : ℝ) :
    IsAnchoredCyclicRenewalSolution reward calibrationSchedule (calibrationHazard p)
      (fun _ ↦ reward (quittingSingletonTerminal (2 : Player))) := by
  intro phase who
  show reward (quittingSingletonTerminal (2 : Player)) who =
    p * reward (quittingSingletonTerminal (calibrationSchedule phase)) who +
      (1 - p) * reward (quittingSingletonTerminal (2 : Player)) who
  rw [show calibrationSchedule phase = 2 from rfl]
  ring

theorem prod_one_sub_calibrationHazard_ne_one {p : ℝ} (hppos : 0 < p) :
    ∏ k, (1 - calibrationHazard p k) ≠ 1 := by
  rw [Fin.prod_univ_one]
  simp only [calibrationHazard]
  intro h
  linarith

/-- **The on-path value of the calibration schedule, pointwise.**  At any
interior hazard the anchored cyclic on-path value at every phase is exactly
player `2`'s own singleton row. -/
theorem quittingAnchoredCyclicOnPathValue_eq_calibration {p : ℝ}
    (hppos : 0 < p) (hp1 : p ≤ 1) (phase : Fin 1) :
    quittingAnchoredCyclicOnPathValue reward calibrationSchedule (calibrationHazard p)
        (calibrationHazard_nonneg hppos.le) (calibrationHazard_le_one hp1) phase =
      reward (quittingSingletonTerminal (2 : Player)) :=
  congrFun
    (eq_of_isAnchoredCyclicRenewalSolution
      (quittingAnchoredCyclicOnPathValue_isAnchoredCyclicRenewalSolution reward
        calibrationSchedule (calibrationHazard p) (calibrationHazard_nonneg hppos.le)
        (calibrationHazard_le_one hp1))
      (isAnchoredCyclicRenewalSolution_calibration p)
      (prod_one_sub_calibrationHazard_ne_one hppos))
    phase

/-! ## Exactness -/

/-- **An exact interior anchored solo-periodic calibration, for every interior
hazard.**  Period one, player `2` scheduled at every phase, is exactly Nash
against its own on-path value at every hazard strictly between `0` and `1`. -/
theorem isExactAnchoredSoloPeriodic_calibration {p : ℝ}
    (hppos : 0 < p) (hp1 : p ≤ 1) :
    IsExactAnchoredSoloPeriodic reward calibrationSchedule (calibrationHazard p)
      (calibrationHazard_nonneg hppos.le) (calibrationHazard_le_one hp1) := by
  intro phase
  show IsεQuittingRootEndpointNash reward
      (quittingAnchoredCyclicOnPathValue reward calibrationSchedule
        (calibrationHazard p) (calibrationHazard_nonneg hppos.le)
        (calibrationHazard_le_one hp1) (finRotate 1 phase))
      0 (quittingSoloMixedRoot (calibrationSchedule phase)
        (quittingHazardCoin (calibrationHazard p phase)
          (calibrationHazard_nonneg hppos.le phase)
          (calibrationHazard_le_one hp1 phase)))
  rw [quittingAnchoredCyclicOnPathValue_eq_calibration hppos hp1,
    show calibrationSchedule phase = 2 from rfl]
  refine isZeroQuittingRootEndpointNash_soloMixedRoot reward
    (reward (quittingSingletonTerminal (2 : Player))) 2 _ rfl fun who hwho ↦ ?_
  have hpair : reward ⟨{(2 : Player), who}, Finset.insert_nonempty 2 {who}⟩ who = 0 := by
    rw [reward_pair_eq_zero 2 who (Ne.symm hwho)]
    rfl
  have hself : reward (quittingSingletonTerminal who) who = 0 :=
    reward_singletonTerminal_self who
  rw [hpair, hself]
  simp only [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  have htwo : reward (quittingSingletonTerminal (2 : Player)) who = 1 := by
    rw [reward_singletonTerminal_two]
    fin_cases who
    · rfl
    · rfl
    · exact absurd rfl hwho
  rw [htwo]
  nlinarith

/-- The concrete interior witness at hazard `1 / 2`. -/
theorem isExactAnchoredSoloPeriodic_calibration_half :
    IsExactAnchoredSoloPeriodic reward calibrationSchedule (calibrationHazard (1 / 2))
      (calibrationHazard_nonneg (by norm_num)) (calibrationHazard_le_one (by norm_num)) :=
  isExactAnchoredSoloPeriodic_calibration (by norm_num) (by norm_num)

end NormalCoreStrictnessExample
end QuittingLCPClassification
end GameTheory
