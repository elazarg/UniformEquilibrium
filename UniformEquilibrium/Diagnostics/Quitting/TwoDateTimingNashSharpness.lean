/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TwoDateTimingNashSharpnessUniqueness

/-!
# Exact debt of the sharp two-date timing Nash law

The unique timing Nash law of the concrete normalized four-player table has
its advertised literal behavioral realization and unrestricted terminal debt
exactly `1 / 2` for player zero.
-/

noncomputable section

namespace GameTheory
namespace TwoDateTimingNashSharpness

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

theorem equilibriumProfile_terminalPayoff_zero :
    quittingTerminalPayoff reward
        (quittingTwoDateTimingProfile reward equilibriumProfile) 0 = 1 / 2 := by
  rw [quittingTerminalPayoff_twoDateTimingProfile_eq_mixedEU]
  exact equilibrium_row_payoff

def late : Option (Fin 3) := some ⟨2, by omega⟩

def liftAction : Action → Option (Fin 3)
  | none => none
  | some time => some ⟨time.val, by omega⟩

theorem pure_row_late_value (columnAction : Action) :
    timingPurePayoff reward 3 ![late, liftAction columnAction, none, none] 0 = 1 := by
  cases columnAction with
  | none =>
      rw [timingPurePayoff_succ_of_current_empty]
      · have htail : timingChoicesTail ![late, liftAction none, none, none] =
            ![next, never, never, never] := by
          funext who
          fin_cases who <;> rfl
        rw [htail]
        simpa [next, never] using pure_row_next_value never
      · decide
  | some time =>
      fin_cases time
      · rw [timingPurePayoff_succ_of_current_nonempty]
        · let current : Player → Bool := fun player =>
            timingActionCurrent (![late, liftAction now, none, none] player)
          have hzero : 0 ∉ quittingQuitters current := by decide
          have hone : 1 ∈ quittingQuitters current := by decide
          change reward ⟨quittingQuitters current, _⟩ 0 = 1
          simp [reward, hzero, hone]
        · exact ⟨1, by decide⟩
      · rw [timingPurePayoff_succ_of_current_empty]
        · have htail : timingChoicesTail
              ![late, liftAction (some ⟨1, by omega⟩), none, none] =
              ![next, now, never, never] := by
            funext who
            fin_cases who <;> rfl
          rw [htail]
          simpa [next, now] using pure_row_next_value now
        · decide

def lateCoordinateTime (player : Player) (action : Action) :
    Math.Probability.CompactStoppingTime :=
  if player = 0 then WithTop.some 2 else quittingTwoDateTimingActionTime action

theorem terminalPayoff_lateCoordinateTime
    (rowAction columnAction : Action) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun player =>
          lateCoordinateTime player
            (![rowAction, columnAction, never, never] player)) 0 = 1 := by
  have htimes : (fun player => lateCoordinateTime player
      (![rowAction, columnAction, never, never] player)) =
      (fun player => quittingFiniteDeadlineTimingActionTime
        (![late, liftAction columnAction, none, none] player)) := by
    funext player
    fin_cases player <;> cases columnAction <;> rfl
  rw [htimes]
  exact pure_row_late_value columnAction

private theorem pureDeviationLaws_eq_map_lateCoordinateTime :
    (fun player =>
      (quittingPureDeviationCompactLaws
        (fun who => quittingTwoDateTimingLaw (equilibriumProfile who)) 0
        (WithTop.some 2) player).toPMF) =
      (fun player =>
        (equilibriumProfile player).map (lateCoordinateTime player)) := by
  funext player
  fin_cases player
  · have hplayer : (⟨0, by omega⟩ : Player) = 0 := by decide
    rw [quittingPureDeviationCompactLaws, if_pos hplayer,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    have htime : lateCoordinateTime (⟨0, by omega⟩ : Player) =
        Function.const Action (WithTop.some 2) := by
      funext action
      simp [lateCoordinateTime]
    rw [htime, PMF.map_const]
  · have hplayer : (⟨1, by omega⟩ : Player) ≠ 0 := by decide
    rw [quittingPureDeviationCompactLaws, if_neg hplayer,
      quittingTwoDateTimingLaw, quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    have htime : lateCoordinateTime (⟨1, by omega⟩ : Player) =
        quittingTwoDateTimingActionTime := by
      funext action
      simp [lateCoordinateTime]
    rw [htime]
  · have hplayer : (⟨2, by omega⟩ : Player) ≠ 0 := by decide
    rw [quittingPureDeviationCompactLaws, if_neg hplayer,
      quittingTwoDateTimingLaw, quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    have htime : lateCoordinateTime (⟨2, by omega⟩ : Player) =
        quittingTwoDateTimingActionTime := by
      funext action
      simp [lateCoordinateTime]
    rw [htime]
  · have hplayer : (⟨3, by omega⟩ : Player) ≠ 0 := by decide
    rw [quittingPureDeviationCompactLaws, if_neg hplayer,
      quittingTwoDateTimingLaw, quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    have htime : lateCoordinateTime (⟨3, by omega⟩ : Player) =
        quittingTwoDateTimingActionTime := by
      funext action
      simp [lateCoordinateTime]
    rw [htime]

theorem equilibriumProfile_quit_two_payoff_zero :
    quittingTerminalPayoff reward
        (Function.update
          (quittingTwoDateTimingProfile reward equilibriumProfile) 0
          (quittingPureTimeBehaviorStrategy reward 0 (WithTop.some 2))) 0 = 1 := by
  rw [quittingTwoDateTimingProfile, quittingFiniteDeadlineTimingProfile,
    quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect,
    pureDeviationLaws_eq_map_lateCoordinateTime]
  change Math.Probability.expect
      (pmfPi (fun player => Math.ProbabilityMassFunction.pushforward
        (equilibriumProfile player) (lateCoordinateTime player)))
      (fun choices => quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) 0) = 1
  rw [← pmfPi_push_coordwise]
  change Math.Probability.expect
      ((pmfPi equilibriumProfile).map fun choices player =>
        lateCoordinateTime player (choices player))
      (fun choices => quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) 0) = 1
  rw [Math.Probability.expect_map, expect_pmfPi_fin4]
  simp only [equilibriumProfile, activeProfile,
    Math.Probability.expect_pure, Fin.isValue]
  simp_rw [terminalPayoff_lateCoordinateTime]
  simp

theorem equilibriumProfile_terminalDeviationDebt_zero_eq_half :
    quittingTerminalDeviationDebt reward
        (quittingTwoDateTimingProfile reward equilibriumProfile) 0 = 1 / 2 := by
  apply le_antisymm
  · exact quittingTerminalDeviationDebt_twoDateTimingProfile_le_half
      reward equilibriumProfile 0 (by norm_num) abs_reward_le_one
      equilibriumProfile_isNash
  · have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue reward
        (quittingTwoDateTimingProfile reward equilibriumProfile) 0
        (quittingPureTimeBehaviorStrategy reward 0 (WithTop.some 2))
    rw [equilibriumProfile_quit_two_payoff_zero] at hdeviation
    unfold quittingTerminalDeviationDebt
    rw [equilibriumProfile_terminalPayoff_zero]
    linarith


end TwoDateTimingNashSharpness
end GameTheory
