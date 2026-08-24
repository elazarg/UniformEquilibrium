/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# Exact stationary equilibrium for participant-only quitting rewards

A quitting table is participant-only when a player receives zero at every
terminal coalition that does not contain that player.  Finite mixed Nash
existence at continuation value zero then selects a product root.  Repeating
that root is an exact terminal Nash profile against all behavioral deviations,
including on the all-Continue and unique-active-player boundary faces.

No inhabitance assumption is made on the finite player type.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A quitting reward table is participant-only when absent players receive
zero at every terminal coalition. -/
def IsQuittingParticipantOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ terminal who, who ∉ terminal.1 → reward terminal who = 0

/-- Participant-only rewards give zero unconditional absorbing contribution
to a player who Continues against a stationary opponent row. -/
theorem quittingStationaryFixedOpponentsContinueReward_eq_zero_of_participantOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hparticipant : IsQuittingParticipantOnly reward)
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryFixedOpponentsContinueReward reward root who = 0 := by
  classical
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [expect_eq_sum]
  apply Finset.sum_eq_zero
  intro action _
  unfold quittingRootPayoff
  split_ifs with hquit
  · by_cases haction : action who = false
    · rw [hparticipant]
      · simp
      · simp [quittingQuitters, haction]
    · have htrue : action who = true := Bool.eq_true_of_not_eq_false haction
      have hlawZero :
          ((pmfPi (Function.update root who (PMF.pure false))) action).toReal = 0 := by
        rw [pmfPi_apply, ENNReal.toReal_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ who)
        simp [htrue]
      rw [hlawZero, zero_mul]
  · simp

/-- A one-shot exact Nash root at continuation zero has stationary gain
complementarity when passive terminal rewards vanish. -/
theorem isQuittingStationaryGainComplementary_of_participantOnly_of_rootNash_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hparticipant : IsQuittingParticipantOnly reward)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    IsQuittingStationaryGainComplementary reward root := by
  have hendpoint :
      IsεQuittingRootEndpointNash reward (0 : Payoff ι) 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (0 : Payoff ι) root).mpr hnash
  intro who
  have hcontinueReward :=
    quittingStationaryFixedOpponentsContinueReward_eq_zero_of_participantOnly
      reward hparticipant root who
  have hcontinueEndpoint :
      quittingRootContinuePayoff reward (0 : Payoff ι) root who = 0 := by
    have hfixed := quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who (0 : Payoff ι) 0
    change quittingFixedOpponentsContinueReward reward (fun _ => root) who 0 =
      0 at hcontinueReward
    simpa only [Pi.zero_apply, mul_zero, add_zero, hcontinueReward] using hfixed
  have hquitEndpoint :
      quittingRootQuitPayoff reward (0 : Payoff ι) root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who (0 : Payoff ι) 0)
  have hdifference :
      quittingRootEndpointDifference reward (0 : Payoff ι) root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    unfold quittingRootEndpointDifference
    rw [hquitEndpoint, hcontinueEndpoint, sub_zero]
  have hmassNonneg :
      0 ≤ 1 - quittingStationaryFixedOpponentsContinueMass root who :=
    sub_nonneg.mpr (quittingStationaryContinueMass_le_one
      (Function.update root who (PMF.pure false)))
  have hgain :
      quittingStationaryGain reward root who =
        (1 - quittingStationaryFixedOpponentsContinueMass root who) *
          quittingStationaryFixedOpponentsQuitValue reward root who := by
    unfold quittingStationaryGain
    rw [hcontinueReward, sub_zero]
  have hsign := hendpoint who
  rw [hdifference] at hsign
  constructor
  · rw [hgain]
    calc
      (root who false).toReal *
          ((1 - quittingStationaryFixedOpponentsContinueMass root who) *
            quittingStationaryFixedOpponentsQuitValue reward root who) =
        (1 - quittingStationaryFixedOpponentsContinueMass root who) *
          ((root who false).toReal *
            quittingStationaryFixedOpponentsQuitValue reward root who) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmassNonneg hsign.1
  · rw [hgain]
    calc
      0 ≤ (1 - quittingStationaryFixedOpponentsContinueMass root who) *
          ((root who true).toReal *
            quittingStationaryFixedOpponentsQuitValue reward root who) :=
        mul_nonneg hmassNonneg (by simpa using hsign.2)
      _ = (root who true).toReal *
          ((1 - quittingStationaryFixedOpponentsContinueMass root who) *
            quittingStationaryFixedOpponentsQuitValue reward root who) := by ring

/-- The one-shot Nash selection supplies the exact boundary inequality when
all opponents Continue surely.  This includes both an inactive coordinate
and the unique-active-player face. -/
theorem isQuittingStationaryBoundaryAdmissible_of_participantOnly_of_rootNash_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hparticipant : IsQuittingParticipantOnly reward)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    IsQuittingStationaryBoundaryAdmissible reward root
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) := by
  have hendpoint :
      IsεQuittingRootEndpointNash reward (0 : Payoff ι) 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (0 : Payoff ι) root).mpr hnash
  intro who hmass
  have hpure :=
    opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
      root who hmass
  have hquitEndpoint :=
    (quittingRoot_endpoints_eq_singleton_tail_of_opponents_pureContinue
      reward (0 : Payoff ι) root who hpure).1
  have hquitFixed :
      quittingRootQuitPayoff reward (0 : Payoff ι) root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who (0 : Payoff ι) 0)
  have hcontinueReward :=
    quittingStationaryFixedOpponentsContinueReward_eq_zero_of_participantOnly
      reward hparticipant root who
  have hcontinueEndpoint :
      quittingRootContinuePayoff reward (0 : Payoff ι) root who = 0 := by
    have hfixed := quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who (0 : Payoff ι) 0
    change quittingFixedOpponentsContinueReward reward (fun _ => root) who 0 =
      0 at hcontinueReward
    simpa only [Pi.zero_apply, mul_zero, add_zero, hcontinueReward] using hfixed
  have hdifference :
      quittingRootEndpointDifference reward (0 : Payoff ι) root who =
        reward (quittingSingletonTerminal who) who := by
    unfold quittingRootEndpointDifference
    rw [hquitEndpoint, hcontinueEndpoint, sub_zero]
  let quitProbability := (root who true).toReal
  let value := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  change max 0 (reward (quittingSingletonTerminal who) who) ≤ value
  by_cases hquitZero : quitProbability = 0
  · have hown : root who = PMF.pure false :=
      Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
        (root who) hquitZero
    have hroot : root = fun _ : ι => PMF.pure false := by
      funext player
      by_cases hplayer : player = who
      · subst player
        exact hown
      · exact hpure player hplayer
    have hvalue : value = 0 := by
      dsimp [value]
      rw [show quittingStationaryProfile reward root =
          quittingAlwaysContinueProfile reward by rw [hroot]; rfl,
        quittingTerminalPayoff_quittingAlwaysContinue]
    have hsingleton : reward (quittingSingletonTerminal who) who ≤ 0 := by
      have hsign := (hendpoint who).1
      rw [hdifference] at hsign
      have hcontinueProbability :=
        quittingRoot_continueProbability_add_quitProbability root who
      dsimp [quitProbability] at hquitZero
      nlinarith
    rw [max_eq_left hsingleton, hvalue]
  · have hquitNonneg : 0 ≤ quitProbability := ENNReal.toReal_nonneg
    have hquitPos : 0 < quitProbability := lt_of_le_of_ne hquitNonneg
      (Ne.symm hquitZero)
    have habsorption : quittingRootAbsorptionMass root = quitProbability := by
      rw [quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul,
        hmass]
      have hsum := quittingRoot_continueProbability_add_quitProbability root who
      dsimp [quitProbability]
      linarith
    have hpayoff :=
      quittingRootAbsorptionMass_mul_stationaryTerminalValue reward root who
    rw [habsorption, hcontinueReward, mul_zero, add_zero, ← hquitFixed,
      hquitEndpoint] at hpayoff
    have hvalueEq : value = reward (quittingSingletonTerminal who) who := by
      change quitProbability * value = quitProbability *
        reward (quittingSingletonTerminal who) who at hpayoff
      exact mul_left_cancel₀ (ne_of_gt hquitPos) hpayoff
    have hsingletonNonneg :
        0 ≤ reward (quittingSingletonTerminal who) who := by
      have hsign := (hendpoint who).2
      rw [hdifference] at hsign
      dsimp [quitProbability] at hquitPos
      exact nonneg_of_mul_nonneg_left
        (by simpa [mul_comm] using hsign) hquitPos
    rw [max_eq_right hsingletonNonneg, hvalueEq]

/-- Repeating a one-shot exact Nash root at continuation zero is exact
terminal Nash for every participant-only reward table. -/
theorem isZeroAsymptoticNash_stationary_of_participantOnly_of_rootNash_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hparticipant : IsQuittingParticipantOnly reward)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) := by
  apply (isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary
    reward root).mpr
  refine ⟨?_,
    isQuittingStationaryBoundaryAdmissible_of_participantOnly_of_rootNash_zero
      reward hparticipant root hnash⟩
  by_cases habsorption : 0 < quittingRootAbsorptionMass root
  · exact (isQuittingStationaryGainComplementary_iff_endpointNash
      reward root habsorption).mp
        (isQuittingStationaryGainComplementary_of_participantOnly_of_rootNash_zero
          reward hparticipant root hnash)
  · have habsorptionZero : quittingRootAbsorptionMass root = 0 :=
      le_antisymm (le_of_not_gt habsorption)
        (quittingRootAbsorptionMass_nonneg root)
    have hcontinueMass : quittingStationaryContinueMass root = 1 := by
      unfold quittingRootAbsorptionMass at habsorptionZero
      linarith
    have hroot : root = fun _ : ι => PMF.pure false := by
      funext player
      exact eq_pure_false_of_quittingStationaryContinueMass_eq_one
        hcontinueMass player
    have hvalue :
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player) = (0 : Payoff ι) := by
      funext player
      rw [show quittingStationaryProfile reward root =
          quittingAlwaysContinueProfile reward by rw [hroot]; rfl,
        quittingTerminalPayoff_quittingAlwaysContinue]
      simp
    have hendpoint :
        IsεQuittingRootEndpointNash reward (0 : Payoff ι) 0 root :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (0 : Payoff ι) root).mpr hnash
    rw [hvalue]
    change IsεQuittingRootEndpointNash reward (0 : Payoff ι) 0 root
    exact hendpoint

/-- Every finite participant-only quitting table, including one over an empty
player type, has an exact stationary terminal Nash profile. -/
theorem exists_stationary_isZeroAsymptoticNash_of_participantOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hparticipant : IsQuittingParticipantOnly reward) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) := by
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) (0 : Payoff ι)
  exact ⟨root,
    isZeroAsymptoticNash_stationary_of_participantOnly_of_rootNash_zero
      reward hparticipant root hnash⟩

/-- The exact stationary terminal Nash payoff of a participant-only table is
a uniform-equilibrium payoff. -/
theorem exists_stationary_uniformEquilibriumPayoff_of_participantOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hparticipant : IsQuittingParticipantOnly reward) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0
          (quittingStationaryProfile reward root) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) := by
  obtain ⟨root, hnash⟩ :=
    exists_stationary_isZeroAsymptoticNash_of_participantOnly
      reward hparticipant
  exact ⟨root, hnash,
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
      reward (quittingStationaryProfile reward root) hnash⟩

end GameTheory
