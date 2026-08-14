/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.General.ORCoupledCalibrationGame
import UniformEquilibrium.Quitting.Classification.ThreePlayer.SharedPunishmentThreePlayer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge

/-!
# Realizing the coupled calibrator as a quitting reward table

Two distinguished players `host` and `clock` receive the table coordinates

`r_host(S)  = 1_{host in S} (1_{clock in S} - targetClock)`,

`r_clock(S) = 1_{clock in S} (targetHost - 1_{host in S})`.

All other coordinates are zero in this standalone gadget.  At a one-stage
root with zero continuation, the host's Quit-minus-Continue value is exactly
`clockQuit - targetClock`, while the clock's is
`targetHost - hostQuit`.  Their actual quitting-root Nash defects therefore
sum to the abstract coupled calibration debt and vanish at exactly the
prescribed interior pair.

Since terminal payoff coordinates are independent, a later compiler may
replace the zero coordinates of the other players by a protected OR audit
without changing these two calibrator calculations.
-/

noncomputable section

namespace GameTheory
namespace CoupledCalibrationQuittingRoot

open StochasticGame Math.Probability Math.PMFProduct
open Experiments.ORCoupledCalibrationGame
open Experiments.QuittingORRankReduction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The two-coordinate coupled calibration reward table. -/
def reward (host clock : ι) (targetHost targetClock : ℝ) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal who =>
    if who = host then
      if host ∈ terminal.val then
        (if clock ∈ terminal.val then 1 else 0) - targetClock
      else 0
    else if who = clock then
      if clock ∈ terminal.val then
        targetHost - (if host ∈ terminal.val then 1 else 0)
      else 0
    else 0

theorem rootPayoff_host_of_quit
    (host clock : ι)
    (targetHost targetClock : ℝ) (action : ι → Bool)
    (hhost : action host = true) :
    quittingRootPayoff (reward host clock targetHost targetClock) 0 action host =
      (if action clock = true then 1 else 0) - targetClock := by
  have hnonempty : (quittingQuitters action).Nonempty := by
    exact (quittingQuitters_nonempty_iff action).2 ⟨host, hhost⟩
  unfold quittingRootPayoff
  rw [dif_pos hnonempty]
  simp [reward, quittingQuitters, hhost]

theorem rootPayoff_host_of_continue
    (host clock : ι) (targetHost targetClock : ℝ) (action : ι → Bool)
    (hhost : action host = false) :
    quittingRootPayoff (reward host clock targetHost targetClock) 0 action host =
      0 := by
  unfold quittingRootPayoff
  split_ifs with hnonempty
  · simp [reward, quittingQuitters, hhost]
  · rfl

theorem rootPayoff_clock_of_quit
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (action : ι → Bool)
    (hclock : action clock = true) :
    quittingRootPayoff (reward host clock targetHost targetClock) 0 action clock =
      targetHost - (if action host = true then 1 else 0) := by
  have hnonempty : (quittingQuitters action).Nonempty := by
    exact (quittingQuitters_nonempty_iff action).2 ⟨clock, hclock⟩
  unfold quittingRootPayoff
  rw [dif_pos hnonempty]
  simp [reward, quittingQuitters, hclock, Ne.symm hne]

theorem rootPayoff_clock_of_continue
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (action : ι → Bool)
    (hclock : action clock = false) :
    quittingRootPayoff (reward host clock targetHost targetClock) 0 action clock =
      0 := by
  unfold quittingRootPayoff
  split_ifs with hnonempty
  · simp [reward, quittingQuitters, hclock, Ne.symm hne]
  · rfl

theorem rootPayoff_host_eq
    (host clock : ι)
    (targetHost targetClock : ℝ) (action : ι → Bool) :
    quittingRootPayoff (reward host clock targetHost targetClock) 0 action host =
      if action host = true then
        (if action clock = true then 1 else 0) - targetClock
      else 0 := by
  by_cases hhost : action host = true
  · rw [if_pos hhost]
    exact rootPayoff_host_of_quit host clock targetHost targetClock action
      hhost
  · have hhostFalse : action host = false := Bool.eq_false_of_not_eq_true hhost
    rw [if_neg hhost]
    exact rootPayoff_host_of_continue host clock targetHost targetClock action
      hhostFalse

theorem rootPayoff_clock_eq
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (action : ι → Bool) :
    quittingRootPayoff (reward host clock targetHost targetClock) 0 action clock =
      if action clock = true then
        targetHost - (if action host = true then 1 else 0)
      else 0 := by
  by_cases hclock : action clock = true
  · rw [if_pos hclock]
    exact rootPayoff_clock_of_quit host clock hne targetHost targetClock action
      hclock
  · have hclockFalse : action clock = false :=
      Bool.eq_false_of_not_eq_true hclock
    rw [if_neg hclock]
    exact rootPayoff_clock_of_continue host clock hne targetHost targetClock action
      hclockFalse

/-- The host's literal pure-Quit endpoint value. -/
theorem quittingRootQuitPayoff_host
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootQuitPayoff (reward host clock targetHost targetClock) 0 root
        host =
      (root clock true).toReal - targetClock := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  let updated := Function.update root host (PMF.pure true)
  have hpoint : (fun action : ι → Bool =>
      quittingRootPayoff (reward host clock targetHost targetClock) 0 action
        host) =
      (fun action => if action host = true then
        (if action clock = true then 1 else 0) - targetClock else 0) := by
    funext action
    exact rootPayoff_host_eq host clock targetHost targetClock action
  rw [hpoint]
  have htwo := QuittingSharedThreePlayer.expect_pmfPi_two_coordinates
    updated hne (fun a b => if a = true then
      (if b = true then 1 else 0) - targetClock else 0)
  rw [htwo]
  simp [updated, Ne.symm hne, expect_eq_sum]
  rw [pmfBool_false_toReal]
  ring

/-- The host's literal pure-Continue endpoint value is zero. -/
theorem quittingRootContinuePayoff_host
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootContinuePayoff (reward host clock targetHost targetClock) 0 root
        host = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  let updated := Function.update root host (PMF.pure false)
  have hpoint : (fun action : ι → Bool =>
      quittingRootPayoff (reward host clock targetHost targetClock) 0 action
        host) =
      (fun action => if action host = true then
        (if action clock = true then 1 else 0) - targetClock else 0) := by
    funext action
    exact rootPayoff_host_eq host clock targetHost targetClock action
  rw [hpoint]
  have htwo := QuittingSharedThreePlayer.expect_pmfPi_two_coordinates
    updated hne (fun a b => if a = true then
      (if b = true then 1 else 0) - targetClock else 0)
  rw [htwo]
  simp [updated, Ne.symm hne, expect_eq_sum]

/-- The clock's literal pure-Quit endpoint value. -/
theorem quittingRootQuitPayoff_clock
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootQuitPayoff (reward host clock targetHost targetClock) 0 root
        clock =
      targetHost - (root host true).toReal := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  let updated := Function.update root clock (PMF.pure true)
  have hpoint : (fun action : ι → Bool =>
      quittingRootPayoff (reward host clock targetHost targetClock) 0 action
        clock) =
      (fun action => if action clock = true then
        targetHost - (if action host = true then 1 else 0) else 0) := by
    funext action
    exact rootPayoff_clock_eq host clock hne targetHost targetClock action
  rw [hpoint]
  have htwo := QuittingSharedThreePlayer.expect_pmfPi_two_coordinates
    updated hne (fun a b => if b = true then
      targetHost - (if a = true then 1 else 0) else 0)
  rw [htwo]
  simp [updated, hne, expect_eq_sum]
  rw [pmfBool_false_toReal]
  ring

/-- The clock's literal pure-Continue endpoint value is zero. -/
theorem quittingRootContinuePayoff_clock
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootContinuePayoff (reward host clock targetHost targetClock) 0 root
        clock = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  let updated := Function.update root clock (PMF.pure false)
  have hpoint : (fun action : ι → Bool =>
      quittingRootPayoff (reward host clock targetHost targetClock) 0 action
        clock) =
      (fun action => if action clock = true then
        targetHost - (if action host = true then 1 else 0) else 0) := by
    funext action
    exact rootPayoff_clock_eq host clock hne targetHost targetClock action
  rw [hpoint]
  have htwo := QuittingSharedThreePlayer.expect_pmfPi_two_coordinates
    updated hne (fun a b => if b = true then
      targetHost - (if a = true then 1 else 0) else 0)
  rw [htwo]
  simp [updated, hne, expect_eq_sum]

/-- Host endpoint difference in the literal quitting root. -/
theorem quittingRootEndpointDifference_host
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootEndpointDifference
        (reward host clock targetHost targetClock) 0 root host =
      (root clock true).toReal - targetClock := by
  rw [quittingRootEndpointDifference, quittingRootQuitPayoff_host _ _ hne,
    quittingRootContinuePayoff_host _ _ hne]
  ring

/-- Clock endpoint difference in the literal quitting root. -/
theorem quittingRootEndpointDifference_clock
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootEndpointDifference
        (reward host clock targetHost targetClock) 0 root clock =
      targetHost - (root host true).toReal := by
  rw [quittingRootEndpointDifference, quittingRootQuitPayoff_clock _ _ hne,
    quittingRootContinuePayoff_clock _ _ hne]
  ring

/-- Host Nash defect is exactly the abstract host calibration debt. -/
theorem quittingRootCoordinateNashDefect_host
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootCoordinateNashDefect
        (reward host clock targetHost targetClock) 0 root host =
      binaryDebt (root host true).toReal
        (hostCalibrationValue targetClock (root clock true).toReal) := by
  unfold quittingRootCoordinateNashDefect binaryDebt bestBinaryValue
    prescribedBinaryValue
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_host _ _ hne,
    quittingRootContinuePayoff_host _ _ hne]
  simp [hostCalibrationValue]
  rw [max_comm]

/-- Clock Nash defect is exactly the abstract clock calibration debt. -/
theorem quittingRootCoordinateNashDefect_clock
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootCoordinateNashDefect
        (reward host clock targetHost targetClock) 0 root clock =
      binaryDebt (root clock true).toReal
        (clockCalibrationValue targetHost (root host true).toReal) := by
  unfold quittingRootCoordinateNashDefect binaryDebt bestBinaryValue
    prescribedBinaryValue
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_clock _ _ hne,
    quittingRootContinuePayoff_clock _ _ hne]
  simp [clockCalibrationValue]
  rw [max_comm]

/-- The sum of the two literal quitting-root defects is the coupled
calibration potential. -/
theorem sum_calibratorDefects_eq_coupledCalibrationDebt
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootCoordinateNashDefect
          (reward host clock targetHost targetClock) 0 root host +
        quittingRootCoordinateNashDefect
          (reward host clock targetHost targetClock) 0 root clock =
      coupledCalibrationDebt targetHost targetClock
        (root host true).toReal (root clock true).toReal := by
  rw [quittingRootCoordinateNashDefect_host _ _ hne,
    quittingRootCoordinateNashDefect_clock _ _ hne]
  rfl

/-- At interior targets, zero total calibrator defect pins the two literal
Quit marginals exactly. -/
theorem sum_calibratorDefects_eq_zero_iff
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ)
    (htargetHost0 : 0 < targetHost) (htargetHost1 : targetHost < 1)
    (htargetClock0 : 0 < targetClock) (htargetClock1 : targetClock < 1)
    (root : ι → PMF Bool) :
    quittingRootCoordinateNashDefect
          (reward host clock targetHost targetClock) 0 root host +
        quittingRootCoordinateNashDefect
          (reward host clock targetHost targetClock) 0 root clock = 0 ↔
      (root host true).toReal = targetHost ∧
        (root clock true).toReal = targetClock := by
  rw [sum_calibratorDefects_eq_coupledCalibrationDebt _ _ hne]
  have hhost1 : (root host true).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      simpa using PMF.coe_le_one (root host) true)
  have hclock1 : (root clock true).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      simpa using PMF.coe_le_one (root clock) true)
  exact coupledCalibrationDebt_eq_zero_iff targetHost targetClock
    (root host true).toReal (root clock true).toReal htargetHost0
    htargetHost1 htargetClock0 htargetClock1 ENNReal.toReal_nonneg
    hhost1 ENNReal.toReal_nonneg hclock1

/-! ## Coordinatewise superposition with a protected audit table -/

/-- Overwrite exactly the host and clock payoff coordinates of an arbitrary
base table by the coupled calibrator. -/
def overlayReward
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal who =>
    if who = host ∨ who = clock then
      reward host clock targetHost targetClock terminal who
    else base terminal who

omit [Fintype ι] in
@[simp] theorem overlayReward_host
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    overlayReward base host clock targetHost targetClock terminal host =
      reward host clock targetHost targetClock terminal host := by
  simp [overlayReward]

omit [Fintype ι] in
@[simp] theorem overlayReward_clock
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    overlayReward base host clock targetHost targetClock terminal clock =
      reward host clock targetHost targetClock terminal clock := by
  simp [overlayReward]

omit [Fintype ι] in
@[simp] theorem overlayReward_protected
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι)
    (hhost : who ≠ host) (hclock : who ≠ clock) :
    overlayReward base host clock targetHost targetClock terminal who =
      base terminal who := by
  simp [overlayReward, hhost, hclock]

/-- The one-stage payoff of every protected coordinate is unchanged by the
overlay, for every action and continuation vector. -/
theorem quittingRootPayoff_overlay_protected
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ)
    (tail : Payoff ι) (action : ι → Bool) (who : ι)
    (hhost : who ≠ host) (hclock : who ≠ clock) :
    quittingRootPayoff
        (overlayReward base host clock targetHost targetClock) tail action who =
      quittingRootPayoff base tail action who := by
  unfold quittingRootPayoff
  split_ifs with hnonempty
  · exact overlayReward_protected base host clock targetHost targetClock
      ⟨quittingQuitters action, hnonempty⟩ who hhost hclock
  · rfl

/-- The prescribed root value of a protected coordinate is unchanged. -/
theorem quittingRootSuccessorPayoff_overlay_protected
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hhost : who ≠ host) (hclock : who ≠ clock) :
    quittingRootSuccessorPayoff
        (overlayReward base host clock targetHost targetClock) tail root who =
      quittingRootSuccessorPayoff base tail root who := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  apply congrArg (expect (pmfPi root))
  funext action
  exact quittingRootPayoff_overlay_protected base host clock targetHost
    targetClock tail action who hhost hclock

/-- The pure-Quit endpoint value of a protected coordinate is unchanged. -/
theorem quittingRootQuitPayoff_overlay_protected
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hhost : who ≠ host) (hclock : who ≠ clock) :
    quittingRootQuitPayoff
        (overlayReward base host clock targetHost targetClock) tail root who =
      quittingRootQuitPayoff base tail root who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  apply congrArg (expect (pmfPi (Function.update root who (PMF.pure true))))
  funext action
  exact quittingRootPayoff_overlay_protected base host clock targetHost
    targetClock tail action who hhost hclock

/-- The pure-Continue endpoint value of a protected coordinate is unchanged. -/
theorem quittingRootContinuePayoff_overlay_protected
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hhost : who ≠ host) (hclock : who ≠ clock) :
    quittingRootContinuePayoff
        (overlayReward base host clock targetHost targetClock) tail root who =
      quittingRootContinuePayoff base tail root who := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  apply congrArg (expect (pmfPi (Function.update root who (PMF.pure false))))
  funext action
  exact quittingRootPayoff_overlay_protected base host clock targetHost
    targetClock tail action who hhost hclock

/-- Hence the complete one-coordinate root Nash defect of every protected
player is unchanged. -/
theorem quittingRootCoordinateNashDefect_overlay_protected
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hhost : who ≠ host) (hclock : who ≠ clock) :
    quittingRootCoordinateNashDefect
        (overlayReward base host clock targetHost targetClock) tail root who =
      quittingRootCoordinateNashDefect base tail root who := by
  unfold quittingRootCoordinateNashDefect
  rw [quittingRootQuitPayoff_overlay_protected base host clock targetHost
      targetClock tail root who hhost hclock,
    quittingRootContinuePayoff_overlay_protected base host clock targetHost
      targetClock tail root who hhost hclock,
    quittingRootSuccessorPayoff_overlay_protected base host clock targetHost
      targetClock tail root who hhost hclock]

/-- At zero continuation, the host payoff coordinate of the overlay is
literally the standalone calibrator coordinate. -/
theorem quittingRootPayoff_overlay_host_zero
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ) (action : ι → Bool) :
    quittingRootPayoff
        (overlayReward base host clock targetHost targetClock) 0 action host =
      quittingRootPayoff (reward host clock targetHost targetClock) 0 action
        host := by
  unfold quittingRootPayoff
  split_ifs with hnonempty
  · exact overlayReward_host base host clock targetHost targetClock
      ⟨quittingQuitters action, hnonempty⟩
  · rfl

/-- At zero continuation, the clock payoff coordinate of the overlay is
literally the standalone calibrator coordinate. -/
theorem quittingRootPayoff_overlay_clock_zero
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ) (action : ι → Bool) :
    quittingRootPayoff
        (overlayReward base host clock targetHost targetClock) 0 action clock =
      quittingRootPayoff (reward host clock targetHost targetClock) 0 action
        clock := by
  unfold quittingRootPayoff
  split_ifs with hnonempty
  · exact overlayReward_clock base host clock targetHost targetClock
      ⟨quittingQuitters action, hnonempty⟩
  · rfl

theorem quittingRootCoordinateNashDefect_overlay_host_zero
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootCoordinateNashDefect
        (overlayReward base host clock targetHost targetClock) 0 root host =
      quittingRootCoordinateNashDefect
        (reward host clock targetHost targetClock) 0 root host := by
  unfold quittingRootCoordinateNashDefect quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootSuccessorPayoff
    quittingRootExpectedPayoff
  rw [show (fun action => quittingRootPayoff
      (overlayReward base host clock targetHost targetClock) 0 action host) =
      (fun action => quittingRootPayoff
        (reward host clock targetHost targetClock) 0 action host) by
        funext action
        exact quittingRootPayoff_overlay_host_zero base host clock targetHost
          targetClock action]

theorem quittingRootCoordinateNashDefect_overlay_clock_zero
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (targetHost targetClock : ℝ) (root : ι → PMF Bool) :
    quittingRootCoordinateNashDefect
        (overlayReward base host clock targetHost targetClock) 0 root clock =
      quittingRootCoordinateNashDefect
        (reward host clock targetHost targetClock) 0 root clock := by
  unfold quittingRootCoordinateNashDefect quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootSuccessorPayoff
    quittingRootExpectedPayoff
  rw [show (fun action => quittingRootPayoff
      (overlayReward base host clock targetHost targetClock) 0 action clock) =
      (fun action => quittingRootPayoff
        (reward host clock targetHost targetClock) 0 action clock) by
        funext action
        exact quittingRootPayoff_overlay_clock_zero base host clock targetHost
          targetClock action]

/-- **Exact modular calibration theorem.**  The overlay preserves every
protected coordinate defect and pins the two calibration marginals on its
zero-defect locus. -/
theorem overlay_protected_and_calibrated
    (base : {S : Finset ι // S.Nonempty} → Payoff ι)
    (host clock : ι) (hne : host ≠ clock)
    (targetHost targetClock : ℝ)
    (htargetHost0 : 0 < targetHost) (htargetHost1 : targetHost < 1)
    (htargetClock0 : 0 < targetClock) (htargetClock1 : targetClock < 1)
    (root : ι → PMF Bool) :
    (∀ who, who ≠ host → who ≠ clock →
      quittingRootCoordinateNashDefect
          (overlayReward base host clock targetHost targetClock) 0 root who =
        quittingRootCoordinateNashDefect base 0 root who) ∧
    (quittingRootCoordinateNashDefect
          (overlayReward base host clock targetHost targetClock) 0 root host +
        quittingRootCoordinateNashDefect
          (overlayReward base host clock targetHost targetClock) 0 root clock =
          0 ↔
      (root host true).toReal = targetHost ∧
        (root clock true).toReal = targetClock) := by
  constructor
  · intro who hhost hclock
    exact quittingRootCoordinateNashDefect_overlay_protected base host clock
      targetHost targetClock 0 root who hhost hclock
  · rw [quittingRootCoordinateNashDefect_overlay_host_zero,
      quittingRootCoordinateNashDefect_overlay_clock_zero]
    exact sum_calibratorDefects_eq_zero_iff host clock hne targetHost
      targetClock htargetHost0 htargetHost1 htargetClock0 htargetClock1 root

end CoupledCalibrationQuittingRoot
end GameTheory
