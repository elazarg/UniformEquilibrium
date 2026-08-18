/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.StandardQSideExample
import Research.Quitting.AnchoredCyclicRenewal

/-!
# An exact interior anchored solo-periodic calibration of the cyclic block

`UniformEquilibrium/Quitting/Classification/LCP/StandardQSideExample.lean` fixes
`cyclicMatrix`, the `3 × 3` textbook standard-Q block realized there as a
four-player reward table via `singletonRewardOfMatrix`.  That realization's
own docstring records that rewards of coalitions larger than a singleton are
*immaterial* to the standard-Q witness: they are assigned to an arbitrary
chosen member of the coalition via `Classical.choose`, so no concrete real
number is exhibited for any pair or larger reward there.

This module asks the calibration question of `cyclicMatrix` itself, which
needs concrete values on every coalition, not only singletons.  It fixes its
own three-player completion `reward` below: the singleton rows are exactly
`cyclicMatrix`'s rows (`reward_singletonTerminal_eq_cyclicMatrix`), and every
coalition of two or three players is paid `0`, the same convention already
used for the concrete completion in `NormalCoreStrictnessExample.lean`. This
completion is this module's own choice, not part of `StandardQSideExample.lean`.

On that completion, the period-three schedule visiting each player once in
order, at the uniform interior hazard `1 / 2`, is an exact
`IsExactAnchoredSoloPeriodic` profile
(`isExactAnchoredSoloPeriodic_cyclicCalibration`). Solving the renewal system
by hand under the ansatz that the on-path value depends only on the phase
lag `(who - phase) mod 3` pins the hazard uniquely to `1 / 2`, with on-path
value `1` at lag `1` and `0` at lags `0` and `2`; one of the two spectator
floor inequalities at each phase holds with equality, so the calibration is
tight, not merely a witness with room to spare.

## Reproduction

`lake env lean Experiments/counterexample_search/CyclicBlockExactPeriodicCalibration.lean`

## Scope

This is a checked statement about the one reward table fixed below, whose
singleton data is `cyclicMatrix`'s, restricted to the anchored solo-periodic
profile class of `AnchoredSoloPeriodic.lean`. It says nothing about any
completion of `cyclicMatrix` other than the zero-elsewhere one fixed here, and
nothing about `StandardQSideExample.lean`'s own four-player realizations
`reward` or `duplicatedReward`, whose pair data is not concretely fixed.
-/

noncomputable section

namespace GameTheory
namespace CyclicBlockExactPeriodicCalibration

open Math.Probability GameTheory.QuittingLCPClassification.StandardQSideExample

abbrev Player := Fin 3

/-! ## The concrete completion of the cyclic block -/

/-- The three-player reward table whose singleton rows are `cyclicMatrix`'s and
whose pair and triple rewards are `0`. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player := fun S =>
  if S.1 = {0} then ![0, 2, -1]
  else if S.1 = {1} then ![-1, 0, 2]
  else if S.1 = {2} then ![2, -1, 0]
  else 0

/-- Every singleton row of the reward table, read off the table's own
`if`-chain by discharging each Finset comparison with `decide`, kept separate
from the real-number entries. -/
theorem reward_singletonTerminal_eval (owner : Player) :
    reward (quittingSingletonTerminal owner) =
      ![![0, 2, -1], ![-1, 0, 2], ![2, -1, 0]] owner := by
  fin_cases owner
  · show (if (({0} : Finset Player) = {0}) then (![0, 2, -1] : Payoff Player)
        else if ({0} : Finset Player) = {1} then ![-1, 0, 2]
        else if ({0} : Finset Player) = {2} then ![2, -1, 0] else 0) = ![0, 2, -1]
    rw [if_pos rfl]
  · show (if (({1} : Finset Player) = {0}) then (![0, 2, -1] : Payoff Player)
        else if ({1} : Finset Player) = {1} then ![-1, 0, 2]
        else if ({1} : Finset Player) = {2} then ![2, -1, 0] else 0) = ![-1, 0, 2]
    rw [if_neg (by decide), if_pos rfl]
  · show (if (({2} : Finset Player) = {0}) then (![0, 2, -1] : Payoff Player)
        else if ({2} : Finset Player) = {1} then ![-1, 0, 2]
        else if ({2} : Finset Player) = {2} then ![2, -1, 0] else 0) = ![2, -1, 0]
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- The singleton rows are exactly `cyclicMatrix`'s rows, substantiating the
docstring's description of this completion. -/
theorem reward_singletonTerminal_eq_cyclicMatrix (owner who : Player) :
    reward (quittingSingletonTerminal owner) who = cyclicMatrix who owner := by
  rw [reward_singletonTerminal_eval]
  fin_cases owner <;> fin_cases who <;> norm_num [cyclicMatrix]

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
  show (if ({first, second} : Finset Player) = {0} then (![0, 2, -1] : Payoff Player)
      else if ({first, second} : Finset Player) = {1} then ![-1, 0, 2]
      else if ({first, second} : Finset Player) = {2} then ![2, -1, 0] else 0) = 0
  rw [if_neg (hnotsingle 0), if_neg (hnotsingle 1), if_neg (hnotsingle 2)]

/-! ## The witness schedule, hazard, and value family -/

/-- Period three: each player quits exactly once, in order. -/
def calibrationSchedule : Fin 3 → Player := fun k ↦ k

/-- The uniform interior hazard `1 / 2`. -/
def calibrationHazard : Fin 3 → ℝ := fun _ ↦ 1 / 2

theorem calibrationHazard_nonneg : ∀ k, 0 ≤ calibrationHazard k :=
  fun _ ↦ by norm_num [calibrationHazard]
theorem calibrationHazard_le_one : ∀ k, calibrationHazard k ≤ 1 :=
  fun _ ↦ by norm_num [calibrationHazard]

/-- The proposed on-path value: at phase `k`, the vector reading `1` at
coordinate `k + 1` and `0` elsewhere. -/
def calibrationValue : Fin 3 → Payoff Player :=
  ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]

/-! ## The value family solves the renewal system -/

theorem isAnchoredCyclicRenewalSolution_calibration :
    IsAnchoredCyclicRenewalSolution reward calibrationSchedule calibrationHazard
      calibrationValue := by
  intro phase who
  show calibrationValue phase who =
    calibrationHazard phase *
        reward (quittingSingletonTerminal (calibrationSchedule phase)) who +
      (1 - calibrationHazard phase) * calibrationValue (finRotate 3 phase) who
  fin_cases phase <;> fin_cases who <;>
    simp [calibrationSchedule, calibrationValue, calibrationHazard, finRotate_apply,
      reward_singletonTerminal_eval] <;>
    norm_num

theorem prod_one_sub_calibrationHazard_ne_one :
    ∏ k, (1 - calibrationHazard k) ≠ 1 := by
  simp only [calibrationHazard]
  norm_num [Fin.prod_univ_three]

/-- **The on-path value of the calibration schedule, in closed form,
pointwise.** -/
theorem quittingAnchoredCyclicOnPathValue_eq_calibration (phase : Fin 3) :
    quittingAnchoredCyclicOnPathValue reward calibrationSchedule calibrationHazard
        calibrationHazard_nonneg calibrationHazard_le_one phase =
      calibrationValue phase :=
  congrFun
    (eq_of_isAnchoredCyclicRenewalSolution
      (quittingAnchoredCyclicOnPathValue_isAnchoredCyclicRenewalSolution reward
        calibrationSchedule calibrationHazard calibrationHazard_nonneg
        calibrationHazard_le_one)
      isAnchoredCyclicRenewalSolution_calibration
      prod_one_sub_calibrationHazard_ne_one)
    phase

/-! ## Exactness -/

/-- **An exact interior anchored solo-periodic calibration of the cyclic
block.**  Period three, each player scheduled once in cyclic order, at the
uniform interior hazard `1 / 2`, is exactly Nash against its own on-path
value. -/
theorem isExactAnchoredSoloPeriodic_cyclicCalibration :
    IsExactAnchoredSoloPeriodic reward calibrationSchedule calibrationHazard
      calibrationHazard_nonneg calibrationHazard_le_one := by
  intro phase
  show IsεQuittingRootEndpointNash reward
      (quittingAnchoredCyclicOnPathValue reward calibrationSchedule calibrationHazard
        calibrationHazard_nonneg calibrationHazard_le_one (finRotate 3 phase))
      0 (quittingSoloMixedRoot (calibrationSchedule phase)
        (quittingHazardCoin (calibrationHazard phase) (calibrationHazard_nonneg phase)
          (calibrationHazard_le_one phase)))
  rw [quittingAnchoredCyclicOnPathValue_eq_calibration (finRotate 3 phase)]
  refine isZeroQuittingRootEndpointNash_soloMixedRoot reward
    (calibrationValue (finRotate 3 phase)) (calibrationSchedule phase) _ ?_
    fun who hwho ↦ ?_
  · fin_cases phase <;>
      simp [calibrationSchedule, calibrationValue, finRotate_apply,
        reward_singletonTerminal_eval]
  · have hpair : reward ⟨{calibrationSchedule phase, who},
        Finset.insert_nonempty (calibrationSchedule phase) {who}⟩ who = 0 := by
      rw [reward_pair_eq_zero (calibrationSchedule phase) who (Ne.symm hwho)]
      rfl
    have hself : reward (quittingSingletonTerminal who) who = 0 :=
      reward_singletonTerminal_self who
    rw [hpair, hself]
    simp only [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal,
      calibrationHazard]
    fin_cases phase <;> fin_cases who <;>
      first
        | exact absurd rfl hwho
        | (simp [calibrationSchedule, calibrationValue, finRotate_apply,
              reward_singletonTerminal_eval] <;>
            norm_num)

end CyclicBlockExactPeriodicCalibration
end GameTheory
