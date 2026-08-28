/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ConstrainedRootNormalWork
import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Quitting.Stationary.MinMax
import Mathlib.Probability.Distributions.Uniform

/-!
# Fin4 zero-minimum boundary regression for constrained normal work

This module realizes the four-row matching-pennies circulation described by
the constrained-root normal-work packet.  Every displayed pure row uses the
full behavioral best-response cap, not a one-row or pure-deviation surrogate.
Its unique unit debt moves around a unilateral four-cycle while total debt and
debt-support cardinality remain fixed.

The same reward table has an actual stationary half--half root of zero debt.
Since every point of the terminal-semantic carrier has nonnegative coordinate
debt, zero is the genuine global carrier minimum.  Thus the example is only a
zero-minimum boundary regression.  It supplies no positive-minimum source,
normal-work orientation, cancellation, or renewable consumer.
-/

noncomputable section

namespace GameTheory
namespace FinFourConstrainedRootNormalWorkRegression

open Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

abbrev Player := Fin 4
abbrev Phase := Fin 4

abbrev hostFirst : Player := 0
abbrev hostSecond : Player := 1
abbrev strategicFirst : Player := 2
abbrev strategicSecond : Player := 3

/-- The four coalitions of the Boolean strategic square, with both hosts
present throughout. -/
def phaseCoalition : Phase → Finset Player :=
  ![{hostFirst, hostSecond},
    {hostFirst, hostSecond, strategicFirst},
    {hostFirst, hostSecond, strategicFirst, strategicSecond},
    {hostFirst, hostSecond, strategicSecond}]

def phaseMover : Phase → Player :=
  ![strategicFirst, strategicSecond, strategicFirst, strategicSecond]

def nextPhase : Phase → Phase := ![1, 2, 3, 0]

@[simp] theorem phaseCoalition_zero :
    phaseCoalition 0 = {hostFirst, hostSecond} := rfl

@[simp] theorem phaseCoalition_one :
    phaseCoalition 1 = {hostFirst, hostSecond, strategicFirst} := rfl

@[simp] theorem phaseCoalition_two :
    phaseCoalition 2 =
      {hostFirst, hostSecond, strategicFirst, strategicSecond} := rfl

@[simp] theorem phaseCoalition_three :
    phaseCoalition 3 = {hostFirst, hostSecond, strategicSecond} := rfl

@[simp] theorem phaseMover_zero : phaseMover 0 = strategicFirst := rfl
@[simp] theorem phaseMover_one : phaseMover 1 = strategicSecond := rfl
@[simp] theorem phaseMover_two : phaseMover 2 = strategicFirst := rfl
@[simp] theorem phaseMover_three : phaseMover 3 = strategicSecond := rfl

@[simp] theorem nextPhase_zero : nextPhase 0 = 1 := rfl
@[simp] theorem nextPhase_one : nextPhase 1 = 2 := rfl
@[simp] theorem nextPhase_two : nextPhase 2 = 3 := rfl
@[simp] theorem nextPhase_three : nextPhase 3 = 0 := rfl

theorem phaseCoalition_nonempty (phase : Phase) :
    (phaseCoalition phase).Nonempty := by
  fin_cases phase <;> simp [phaseCoalition]

theorem phaseMover_toggle (phase : Phase) :
    phaseCoalition (nextPhase phase) =
      if phaseMover phase ∈ phaseCoalition phase then
        (phaseCoalition phase).erase (phaseMover phase)
      else insert (phaseMover phase) (phaseCoalition phase) := by
  fin_cases phase <;> ext who <;> fin_cases who <;> decide

/-- Two passive zero-payoff hosts and a matching-pennies pair on coalition
membership. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who ↦
    if who = hostFirst then 0
    else if who = hostSecond then 0
    else if who = strategicFirst then
      if (strategicFirst ∈ terminal.1) =
          (strategicSecond ∈ terminal.1) then 0 else 1
    else if (strategicFirst ∈ terminal.1) =
        (strategicSecond ∈ terminal.1) then 1 else 0

theorem reward_bound (terminal player) : |reward terminal player| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

def root (phase : Phase) : Player → PMF Bool :=
  quittingPureSetRoot (phaseCoalition phase)

def profile (phase : Phase) : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (root phase)

def pair (phase : Phase) : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward (profile phase)

/-- Each displayed profile pays its sure-exit coalition at date zero. -/
theorem pair_fst (phase : Phase) (who : Player) :
    (pair phase).1 who =
      quittingSetReward reward (phaseCoalition phase) who := by
  exact quittingTerminalPayoff_pureSetRoot
    reward (phaseCoalition phase) who

/-- The second coordinate is the unrestricted behavioral cap.  The pure-set
formula is exact because at least two hosts quit surely; no pure-deviation
restriction is being imposed. -/
theorem pair_snd (phase : Phase) (who : Player) :
    (pair phase).2 who =
      max (quittingSetReward reward
          (insert who (phaseCoalition phase)) who)
        (quittingSetReward reward
          ((phaseCoalition phase).erase who) who) := by
  change quittingContinuationBestResponseValue reward (profile phase) who = _
  calc
    quittingContinuationBestResponseValue reward (profile phase) who =
        quittingBestReplyValue reward (profile phase) who := rfl
    _ = quittingStationaryUnilateralCap reward (root phase) who := by
      simpa [profile] using
        (quittingBestReplyValue_stationary reward (root phase) who)
    _ = max (quittingSetReward reward
          (insert who (phaseCoalition phase)) who)
        (quittingSetReward reward
          ((phaseCoalition phase).erase who) who) := by
      simpa [root] using
        (quittingStationaryUnilateralCap_pureSetRoot
          reward (phaseCoalition phase) who)

/-- At each cyclic row the current mover is the unique unit debtor. -/
theorem phase_debt (phase : Phase) (who : Player) :
    quittingTerminalSemanticDebt (pair phase) who =
      if who = phaseMover phase then 1 else 0 := by
  rw [quittingTerminalSemanticDebt, pair_fst, pair_snd]
  fin_cases phase <;> fin_cases who <;>
    simp +decide [reward, quittingSetReward]

theorem phase_debtSum_eq_one (phase : Phase) :
    quittingTerminalSemanticDebtSum (pair phase) = 1 := by
  unfold quittingTerminalSemanticDebtSum
  simp_rw [phase_debt]
  exact Fintype.sum_ite_eq' (phaseMover phase) (fun _ : Player ↦ (1 : ℝ))

theorem phase_debt_pos_iff (phase : Phase) (who : Player) :
    0 < quittingTerminalSemanticDebt (pair phase) who ↔
      who = phaseMover phase := by
  rw [phase_debt]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem phase_positiveDebtSupport_eq_singleton (phase : Phase) :
    Finset.univ.filter
        (fun who ↦ 0 < quittingTerminalSemanticDebt (pair phase) who) =
      {phaseMover phase} := by
  ext who
  simp [phase_debt_pos_iff]

/-- Consecutive displayed profiles differ only in the named mover's complete
stationary strategy. -/
theorem update_profile_phaseMover (phase : Phase) :
    Function.update (profile phase) (phaseMover phase)
        (profile (nextPhase phase) (phaseMover phase)) =
      profile (nextPhase phase) := by
  funext who time history
  fin_cases phase <;> fin_cases who <;>
    simp [profile, root, phaseCoalition, phaseMover, nextPhase,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
      quittingPureSetRoot, quittingSetAction, hostFirst, hostSecond,
      strategicFirst, strategicSecond]

/-- Every unilateral cyclic reset raises the mover's actual payoff by one. -/
theorem phaseMover_payoffGain_eq_one (phase : Phase) :
    (pair (nextPhase phase)).1 (phaseMover phase) -
        (pair phase).1 (phaseMover phase) = 1 := by
  rw [pair_fst, pair_fst]
  fin_cases phase <;>
    simp +decide [reward, quittingSetReward]

theorem nextPhase_moverDebt_eq_zero (phase : Phase) :
    quittingTerminalSemanticDebt (pair (nextPhase phase))
        (phaseMover phase) = 0 := by
  rw [phase_debt]
  fin_cases phase <;>
    simp +decide

theorem phaseMover_debt_eq_one (phase : Phase) :
    quittingTerminalSemanticDebt (pair phase) (phaseMover phase) = 1 := by
  simp [phase_debt]

theorem nextPhase_nextMoverDebt_eq_one (phase : Phase) :
    quittingTerminalSemanticDebt (pair (nextPhase phase))
        (phaseMover (nextPhase phase)) = 1 := by
  exact phaseMover_debt_eq_one (nextPhase phase)

theorem nextPhase_mover_ne (phase : Phase) :
    phaseMover (nextPhase phase) ≠ phaseMover phase := by
  fin_cases phase <;> decide

/-! ## The actual zero-debt stationary minimum -/

def fairMarginal : PMF Bool := PMF.uniformOfFintype Bool

def fairRoot : Player → PMF Bool :=
  ![PMF.pure true, PMF.pure true, fairMarginal, fairMarginal]

def fairProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward fairRoot

def fairPair : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward fairProfile

def fairValue : Payoff Player := ![0, 0, (1 / 2 : ℝ), (1 / 2 : ℝ)]

@[simp] theorem fairMarginal_apply_toReal (action : Bool) :
    (fairMarginal action).toReal = (1 / 2 : ℝ) := by
  unfold fairMarginal
  rw [PMF.uniformOfFintype_apply]
  norm_num

@[simp] theorem quittingQuitters_vec4 (a b c d : Bool) :
    quittingQuitters ![a, b, c, d] =
      (if a then {hostFirst} else ∅) ∪
        (if b then {hostSecond} else ∅) ∪
          (if c then {strategicFirst} else ∅) ∪
            (if d then {strategicSecond} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [quittingQuitters, hostFirst, hostSecond,
      strategicFirst, strategicSecond]

theorem fairRoot_continueMass_eq_zero :
    quittingStationaryContinueMass fairRoot = 0 := by
  exact quittingStationaryContinueMass_of_sureQuitter
    (quitter := hostFirst) rfl

theorem fairRoot_absorbingContribution (who : Player) :
    quittingRootAbsorbingContribution reward fairRoot who = fairValue who := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp [fairRoot, fairValue, fairMarginal, expect_eq_sum,
      quittingRootPayoff, reward, quittingQuitters_vec4,
      PMF.uniformOfFintype_apply, hostFirst, hostSecond,
      strategicFirst, strategicSecond, Fin.ext_iff] <;>
    norm_num

theorem fairRoot_fixedOpponentsQuitValue (who : Player) :
    quittingStationaryFixedOpponentsQuitValue reward fairRoot who =
      fairValue who := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp [fairRoot, fairValue, fairMarginal, expect_eq_sum,
      quittingRootPayoff, reward, quittingQuitters_vec4,
      PMF.uniformOfFintype_apply, hostFirst, hostSecond,
      strategicFirst, strategicSecond, Fin.ext_iff]

theorem fairRoot_fixedOpponentsContinueReward (who : Player) :
    quittingStationaryFixedOpponentsContinueReward reward fairRoot who =
      fairValue who := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp [fairRoot, fairValue, fairMarginal, expect_eq_sum,
      quittingRootPayoff, reward, quittingQuitters_vec4,
      PMF.uniformOfFintype_apply, hostFirst, hostSecond,
      strategicFirst, strategicSecond, Fin.ext_iff]

theorem fairRoot_fixedOpponentsContinueMass (who : Player) :
    quittingStationaryFixedOpponentsContinueMass fairRoot who = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  fin_cases who
  · exact quittingStationaryContinueMass_of_sureQuitter
      (quitter := hostSecond) rfl
  · exact quittingStationaryContinueMass_of_sureQuitter
      (quitter := hostFirst) rfl
  · exact quittingStationaryContinueMass_of_sureQuitter
      (quitter := hostFirst) rfl
  · exact quittingStationaryContinueMass_of_sureQuitter
      (quitter := hostFirst) rfl

/-- The fair row's selected full behavioral cap is its prescribed value. -/
theorem fairRoot_unilateralCap (who : Player) :
    quittingStationaryUnilateralCap reward fairRoot who = fairValue who := by
  rw [quittingStationaryUnilateralCap_eq_max_div,
    fairRoot_fixedOpponentsQuitValue,
    fairRoot_fixedOpponentsContinueReward,
    fairRoot_fixedOpponentsContinueMass]
  fin_cases who <;> norm_num [fairValue]

theorem fairPair_fst (who : Player) : (fairPair).1 who = fairValue who := by
  change quittingTerminalPayoff reward fairProfile who = fairValue who
  rw [fairProfile, quittingTerminalPayoff_stationary_eq_absorbingContribution_div,
    fairRoot_absorbingContribution, fairRoot_continueMass_eq_zero]
  · norm_num
  · rw [fairRoot_continueMass_eq_zero]
    norm_num

/-- The fair row's second coordinate is the unrestricted behavioral reply
cap, as supplied by the stationary min--max theorem. -/
theorem fairPair_snd (who : Player) : (fairPair).2 who = fairValue who := by
  change quittingContinuationBestResponseValue reward fairProfile who = _
  calc
    quittingContinuationBestResponseValue reward fairProfile who =
        quittingBestReplyValue reward fairProfile who := rfl
    _ = quittingStationaryUnilateralCap reward fairRoot who := by
      simpa [fairProfile] using
        (quittingBestReplyValue_stationary reward fairRoot who)
    _ = fairValue who := fairRoot_unilateralCap who

theorem fairPair_debt_eq_zero (who : Player) :
    quittingTerminalSemanticDebt fairPair who = 0 := by
  rw [quittingTerminalSemanticDebt, fairPair_fst, fairPair_snd]
  ring

theorem fairPair_debtSum_eq_zero :
    quittingTerminalSemanticDebtSum fairPair = 0 := by
  unfold quittingTerminalSemanticDebtSum
  simp [fairPair_debt_eq_zero]

theorem fairPair_mem_carrier :
    fairPair ∈ quittingTerminalSemanticCarrier reward := by
  exact quittingTerminalSemanticPair_mem_carrier reward fairProfile

/-- Zero is the genuine minimum of total semantic debt on the entire compact
carrier, not merely on the displayed cyclic family. -/
theorem zero_isMinimum_terminalSemanticDebtSum :
    IsLeast
      (quittingTerminalSemanticDebtSum ''
        quittingTerminalSemanticCarrier reward) 0 := by
  constructor
  · exact ⟨fairPair, fairPair_mem_carrier, fairPair_debtSum_eq_zero⟩
  · rintro _ ⟨candidate, hcandidate, rfl⟩
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ ↦
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hcandidate who

/-- Literal regression capstone.  It records a unit-debt unilateral cycle
and, separately, an actual zero-debt global minimizer for the same table. -/
theorem finite_boundaryRegression :
    (∀ phase, quittingTerminalSemanticDebtSum (pair phase) = 1) ∧
      (∀ phase,
        Function.update (profile phase) (phaseMover phase)
            (profile (nextPhase phase) (phaseMover phase)) =
          profile (nextPhase phase) ∧
        (pair (nextPhase phase)).1 (phaseMover phase) -
            (pair phase).1 (phaseMover phase) = 1 ∧
        quittingTerminalSemanticDebt (pair phase) (phaseMover phase) = 1 ∧
        quittingTerminalSemanticDebt (pair (nextPhase phase))
            (phaseMover phase) = 0 ∧
        quittingTerminalSemanticDebt (pair (nextPhase phase))
            (phaseMover (nextPhase phase)) = 1) ∧
      IsLeast
        (quittingTerminalSemanticDebtSum ''
          quittingTerminalSemanticCarrier reward) 0 := by
  exact ⟨phase_debtSum_eq_one, fun phase ↦
    ⟨update_profile_phaseMover phase, phaseMover_payoffGain_eq_one phase,
      phaseMover_debt_eq_one phase, nextPhase_moverDebt_eq_zero phase,
      nextPhase_nextMoverDebt_eq_one phase⟩,
    zero_isMinimum_terminalSemanticDebtSum⟩

end FinFourConstrainedRootNormalWorkRegression
end GameTheory
