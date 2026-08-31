/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedSemanticCarrier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashStrictMinimum
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess

/-!
# A negative-orientation Fin4 maximal-root regression

This file checks the finite table used to delimit the maximal-root reduction.
The low-debt all-Continue endpoint has zero opponent incidence, while a
displayed sibling payoff-difference atom has positive sign.  Thus these two
local statistics alone do not force the minimum-fibre branch.

The regression does not assert that all Continue is the unique exact root at
the zero cap.  It is not a hard-residual source, a renewal construction, or a
uniform-equilibrium counterexample.
-/

noncomputable section

namespace GameTheory
namespace FinFourMaximalRootNegativeOrientation

open Math.Probability QuittingSureSetOwnerRepair

abbrev Player := Fin 4

def mover : Player := 0
def observer : Player := 1
def firstAuxiliary : Player := 2
def secondAuxiliary : Player := 3

/-- The exact four-player reward table used by the orientation regression. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if who = mover then
      if mover ∈ terminal.1 then -1 else 0
    else if who = observer then
      if observer ∈ terminal.1 then -2
      else if mover ∈ terminal.1 then -1 else 0
    else if who ∈ terminal.1 then
      if mover ∈ terminal.1 ∧ observer ∈ terminal.1 then 1 else -1
    else 0

/-- Stationary pure-set profile for the displayed quitters. -/
def profile (quitters : Finset Player) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot quitters)

def X : (quittingGame reward).BehaviorProfile := profile {mover, observer}
def Y : (quittingGame reward).BehaviorProfile := profile {observer}
def R : (quittingGame reward).BehaviorProfile := profile ∅
def Q : (quittingGame reward).BehaviorProfile := profile {mover}

private theorem terminalPayoff_profile (quitters : Finset Player) (who : Player) :
    quittingTerminalPayoff reward (profile quitters) who =
      quittingSetReward reward quitters who := by
  exact quittingTerminalPayoff_pureSetRoot reward quitters who

private theorem cap_profile (quitters : Finset Player) (who : Player) :
    quittingContinuationBestResponseValue reward (profile quitters) who =
      max (quittingSetReward reward (insert who quitters) who)
        (quittingSetReward reward (quitters.erase who) who) := by
  rw [quittingContinuationBestResponseValue_eq_bestReplyValue,
    profile,
    quittingBestReplyValue_stationary,
    quittingStationaryUnilateralCap_pureSetRoot]

theorem terminalPayoff_X : quittingTerminalPayoff reward X = ![-1, -2, 0, 0] := by
  funext who
  rw [show X = profile {mover, observer} by rfl, terminalPayoff_profile]
  fin_cases who <;>
    simp +decide [quittingSetReward, reward]

theorem cap_X :
    quittingContinuationBestResponseValue reward X = ![0, -1, 1, 1] := by
  funext who
  rw [show X = profile {mover, observer} by rfl, cap_profile]
  fin_cases who <;>
    simp +decide [quittingSetReward, reward]

theorem terminalPayoff_Y : quittingTerminalPayoff reward Y = ![0, -2, 0, 0] := by
  funext who
  rw [show Y = profile {observer} by rfl, terminalPayoff_profile]
  fin_cases who <;>
    simp +decide [quittingSetReward, reward]

theorem cap_Y :
    quittingContinuationBestResponseValue reward Y = ![0, 0, 0, 0] := by
  funext who
  rw [show Y = profile {observer} by rfl, cap_profile]
  fin_cases who <;>
    simp +decide [quittingSetReward, reward]

theorem terminalPayoff_R : quittingTerminalPayoff reward R = 0 := by
  funext who
  rw [show R = profile ∅ by rfl, terminalPayoff_profile]
  simp [quittingSetReward]

theorem cap_R : quittingContinuationBestResponseValue reward R = 0 := by
  funext who
  rw [show R = profile ∅ by rfl, cap_profile]
  fin_cases who <;>
    simp +decide [quittingSetReward, reward]

theorem debt_X :
    (fun who => quittingTerminalDeviationDebt reward X who) = ![1, 1, 1, 1] := by
  funext who
  unfold quittingTerminalDeviationDebt
  rw [congrFun cap_X who, congrFun terminalPayoff_X who]
  fin_cases who <;> norm_num

theorem debt_Y :
    (fun who => quittingTerminalDeviationDebt reward Y who) = ![0, 2, 0, 0] := by
  funext who
  unfold quittingTerminalDeviationDebt
  rw [congrFun cap_Y who, congrFun terminalPayoff_Y who]
  fin_cases who <;> norm_num

theorem debt_R : (fun who => quittingTerminalDeviationDebt reward R who) = 0 := by
  funext who
  unfold quittingTerminalDeviationDebt
  rw [congrFun cap_R who, congrFun terminalPayoff_R who]
  simp

private theorem terminalOutcomeMass_profile_some (quitters : Finset Player)
    (terminal : {S : Finset Player // S.Nonempty}) :
    quittingTerminalOutcomeMass reward (profile quitters) (some terminal) =
      if quitters = terminal.val then 1 else 0 := by
  classical
  let indicator : {S : Finset Player // S.Nonempty} → Payoff Player :=
    fun candidate _ => if candidate = terminal then 1 else 0
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass indicator
      (quittingStationaryProfile indicator (quittingPureSetRoot quitters))) mover
  rw [quittingTerminalPayoff_pureSetRoot] at hmoment
  change quittingAbsorbedMassLimit reward (profile quitters) terminal = _
  rw [quittingAbsorbedMassLimit_reward_irrelevant reward indicator]
  change quittingAbsorbedMassLimit indicator
    (quittingStationaryProfile indicator (quittingPureSetRoot quitters)) terminal = _
  unfold quittingTerminalRewardMoment quittingTerminalOutcomeMass
    quittingTerminalOutcomeReward at hmoment
  by_cases hquitters : quitters.Nonempty
  · have hmoment' : quittingAbsorbedMassLimit indicator
        (quittingStationaryProfile indicator (quittingPureSetRoot quitters))
          terminal = if (⟨quitters, hquitters⟩ :
            {S : Finset Player // S.Nonempty}) = terminal then 1 else 0 := by
      simpa [indicator, quittingSetReward, hquitters] using hmoment
    simpa only [Subtype.ext_iff] using hmoment'
  · have hempty : quitters = ∅ := Finset.not_nonempty_iff_eq_empty.mp hquitters
    subst quitters
    have hne : (∅ : Finset Player) ≠ terminal.val := by
      intro heq
      have hnonempty := terminal.property
      rw [← heq] at hnonempty
      exact Finset.not_nonempty_empty hnonempty
    rw [if_neg hne]
    simpa [indicator, quittingSetReward] using hmoment

def moverTerminal : {S : Finset Player // S.Nonempty} :=
  ⟨{mover}, Finset.singleton_nonempty mover⟩

@[simp] theorem moverTerminal_val : moverTerminal.val = {mover} := rfl

theorem terminalOutcomeMass_R_mover_eq_zero :
    quittingTerminalOutcomeMass reward R (some moverTerminal) = 0 := by
  rw [show R = profile ∅ by rfl,
    terminalOutcomeMass_profile_some]
  simp [moverTerminal]

theorem terminalOutcomeMass_Q_mover_eq_one :
    quittingTerminalOutcomeMass reward Q (some moverTerminal) = 1 := by
  rw [show Q = profile {mover} by rfl,
    terminalOutcomeMass_profile_some]
  simp [moverTerminal]

theorem reward_moverTerminal_observer : reward moverTerminal observer = -1 := by
  norm_num [reward, moverTerminal, mover, observer]

/-- The displayed atom is positive because its mass and reward differences
have the same negative sign. -/
theorem payoffDifferenceAtom_R_Q_observer_mover_eq_one :
    quittingTerminalPayoffDifferenceAtom reward R Q observer
      (some moverTerminal) = 1 := by
  unfold quittingTerminalPayoffDifferenceAtom
  rw [terminalOutcomeMass_R_mover_eq_zero,
    terminalOutcomeMass_Q_mover_eq_one]
  simp [quittingTerminalOutcomeReward, reward_moverTerminal_observer]

/-- The low-debt endpoint nevertheless has no finite opponent incidence. -/
theorem totalOpponentIncidence_R_observer_eq_zero :
    quittingTerminalTotalOpponentIncidenceMass observer
      (quittingTerminalOutcomeMass reward R) = 0 := by
  unfold quittingTerminalTotalOpponentIncidenceMass
    quittingTerminalOpponentIncidenceMass
  apply Finset.sum_eq_zero
  intro other _
  apply Finset.sum_eq_zero
  intro terminal _
  rw [show R = profile ∅ by rfl,
    terminalOutcomeMass_profile_some]
  rw [if_neg]
  intro heq
  have hnonempty := terminal.property
  rw [← heq] at hnonempty
  exact Finset.not_nonempty_empty hnonempty

/-- Against the zero cap at the low-debt endpoint, all Continue is exact. -/
theorem allContinue_isZeroNash_at_cap_R :
    IsεQuittingRootNash reward
      (quittingContinuationBestResponseValue reward R) 0
      (quittingAllContinueRoot : Player → PMF Bool) := by
  rw [cap_R]
  apply (isZeroQuittingRootNash_allContinue_iff_singleton_le reward 0).2
  intro who
  fin_cases who <;>
    norm_num [reward, quittingSingletonTerminal, mover, observer]

end FinFourMaximalRootNegativeOrientation
end GameTheory
