/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Finset.ProdLtOne
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# Empty-base semantic dispatch for a strict-toggle face

This file checks the behavioral compiler behind the empty-base alternative.
The displayed residuals are the denominator-free forms of the active-player
indifference equations and passive-player join inequalities.  Thus the input
is finite product-law algebra, while the output controls every behavioral
stopping deviation through the stationary endpoint compiler.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The active equation `H_i = d_i Q_i - N_i` written with the checked
product-law primitives. -/
def quittingEmptyBaseActiveResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  (1 - quittingStationaryFixedOpponentsContinueMass root who) *
      quittingStationaryFixedOpponentsQuitValue reward root who -
    quittingStationaryFixedOpponentsContinueReward reward root who

/-- The passive equation after clearing the positive joint absorption
denominator: `P_o = δ J_o - A_o`. -/
def quittingEmptyBasePassiveResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  (1 - quittingStationaryContinueMass root) *
      quittingStationaryFixedOpponentsQuitValue reward root who -
    quittingRootAbsorbingContribution reward root who

/-- Exact finite data for the empty-base feasible branch.  Active players
mix strictly, inactive players Continue surely, active `H` residuals vanish,
and passive cleared join residuals are nonpositive. -/
structure QuittingEmptyBaseInteriorCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (root : ι → PMF Bool) : Prop where
  two_le_card : 2 ≤ active.card
  active_quit_pos : ∀ who ∈ active, 0 < (root who true).toReal
  active_continue_pos : ∀ who ∈ active, 0 < (root who false).toReal
  inactive_continue : ∀ who ∉ active, root who = PMF.pure false
  active_residual_eq_zero : ∀ who ∈ active,
    quittingEmptyBaseActiveResidual reward root who = 0
  passive_residual_nonpos : ∀ who ∉ active,
    quittingEmptyBasePassiveResidual reward root who ≤ 0

namespace QuittingEmptyBaseInteriorCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {active : Finset ι} {root : ι → PMF Bool}

/-- Every player has an active opponent. -/
theorem exists_active_opponent
    (certificate : QuittingEmptyBaseInteriorCertificate reward active root)
    (who : ι) : ∃ opponent ∈ active, opponent ≠ who := by
  have hnontrivial : active.Nontrivial :=
    Finset.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le Nat.one_lt_two certificate.two_le_card)
  obtain ⟨opponent, hopponent⟩ := hnontrivial.erase_nonempty (a := who)
  exact ⟨opponent, Finset.mem_of_mem_erase hopponent,
    Finset.ne_of_mem_erase hopponent⟩

/-- At least one active coordinate makes the product row absorbing. -/
theorem absorbs
    (certificate : QuittingEmptyBaseInteriorCertificate reward active root) :
    quittingStationaryContinueMass root < 1 := by
  obtain ⟨who, hwho⟩ :=
    (Finset.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le Nat.one_lt_two certificate.two_le_card)).nonempty
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Math.Finset.prod_lt_one_of_mem Finset.univ
    (fun player => (root player false).toReal) who (Finset.mem_univ who)
  · intro player _ _
    exact ENNReal.toReal_nonneg
  · intro player _ _
    exact ENNReal.toReal_mono ENNReal.one_ne_top ((root player).coe_le_one false)
  · have hsum := quittingRoot_continueProbability_add_quitProbability root who
    linarith [certificate.active_quit_pos who hwho]

/-- Two strictly active labels make every fixed-opponent row contracting. -/
theorem opponents_contract
    (certificate : QuittingEmptyBaseInteriorCertificate reward active root)
    (who : ι) :
    quittingStationaryFixedOpponentsContinueMass root who < 1 := by
  obtain ⟨opponent, hopponent, hne⟩ := certificate.exists_active_opponent who
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Math.Finset.prod_lt_one_of_mem Finset.univ
    (fun player =>
      ((Function.update root who (PMF.pure false) player) false).toReal)
    opponent (Finset.mem_univ opponent)
  · intro player _ _
    exact ENNReal.toReal_nonneg
  · intro player _ _
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (((Function.update root who (PMF.pure false)) player).coe_le_one false)
  · rw [Function.update_of_ne hne]
    have hsum := quittingRoot_continueProbability_add_quitProbability root opponent
    linarith [certificate.active_quit_pos opponent hopponent]

/-- Vanishing `H_i` forces the active player's stationary terminal payoff to
equal its pure-Quit endpoint. -/
theorem terminalPayoff_eq_quitValue_of_mem
    (certificate : QuittingEmptyBaseInteriorCertificate reward active root)
    {who : ι} (hwho : who ∈ active) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who =
      quittingStationaryFixedOpponentsQuitValue reward root who := by
  let value := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  let quit := quittingStationaryFixedOpponentsQuitValue reward root who
  let continuationReward :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let opponentsContinue :=
    quittingStationaryFixedOpponentsContinueMass root who
  let ownContinue := (root who false).toReal
  let ownQuit := (root who true).toReal
  have hfixed := quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
    reward root who
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward (fun player => quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player) root who
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward (fun _ => root) who
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) 0
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward (fun _ => root) who
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) 0
  have hmass := quittingStationaryContinueMass_eq_forcedContinue_mul_own root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hresidual := certificate.active_residual_eq_zero who hwho
  have habsorbs := certificate.absorbs
  change value = quittingRootSuccessorPayoff reward
    (fun player => quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player) root who at hfixed
  change _ = ownQuit * _ + ownContinue * _ at hmix
  change _ = quit at hquit
  change _ = continuationReward + opponentsContinue * value at hcontinue
  change quittingStationaryContinueMass root = opponentsContinue * ownContinue at hmass
  change ownContinue + ownQuit = 1 at hsum
  change (1 - opponentsContinue) * quit - continuationReward = 0 at hresidual
  rw [hmix, hquit, hcontinue] at hfixed
  have hcontract : opponentsContinue * ownContinue < 1 := by
    rw [← hmass]
    exact habsorbs
  have heq :
      (1 - opponentsContinue * ownContinue) * (value - quit) = 0 := by
    linear_combination hfixed - ownContinue * hresidual + quit * hsum
  change value = quit
  have hfactor : 0 < 1 - opponentsContinue * ownContinue := sub_pos.mpr hcontract
  rcases mul_eq_zero.mp heq with hzero | hzero
  · exact (hfactor.ne' hzero).elim
  · exact sub_eq_zero.mp hzero

/-- The active equations imply exact endpoint indifference. -/
theorem active_endpointDifference_eq_zero
    (certificate : QuittingEmptyBaseInteriorCertificate reward active root)
    {who : ι} (hwho : who ∈ active) :
    quittingRootEndpointDifference reward
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) root who = 0 := by
  rw [quittingRootEndpointDifference]
  have hquitEq :
      quittingRootQuitPayoff reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) 0)
  have hcontinueEq :
      quittingRootContinuePayoff reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) root who =
        quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who *
            quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) who := by
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
      (quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ => root) who
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) 0)
  rw [hquitEq, hcontinueEq]
  have hvalue := certificate.terminalPayoff_eq_quitValue_of_mem hwho
  have hresidual := certificate.active_residual_eq_zero who hwho
  change (1 - quittingStationaryFixedOpponentsContinueMass root who) *
      quittingStationaryFixedOpponentsQuitValue reward root who -
    quittingStationaryFixedOpponentsContinueReward reward root who = 0 at hresidual
  rw [hvalue]
  linear_combination hresidual

/-- A nonpositive cleared passive defect is exactly the passive pure-Quit
inequality against the actual stationary payoff. -/
theorem passive_quitValue_le_terminalPayoff
    (certificate : QuittingEmptyBaseInteriorCertificate reward active root)
    {who : ι} (hwho : who ∉ active) :
    quittingStationaryFixedOpponentsQuitValue reward root who ≤
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who := by
  have hbalance := one_sub_continueMass_mul_quittingTerminalPayoff_stationary
    reward root who
  have hresidual := certificate.passive_residual_nonpos who hwho
  have hpositive : 0 < 1 - quittingStationaryContinueMass root :=
    sub_pos.mpr certificate.absorbs
  change (1 - quittingStationaryContinueMass root) *
      quittingStationaryFixedOpponentsQuitValue reward root who -
    quittingRootAbsorbingContribution reward root who ≤ 0 at hresidual
  nlinarith

/-- The finite `H/P` system is an exact one-stage endpoint Nash certificate
at the actual stationary payoff. -/
theorem endpointNash
    (certificate : QuittingEmptyBaseInteriorCertificate reward active root) :
    IsεQuittingRootEndpointNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) 0 root := by
  intro who
  by_cases hwho : who ∈ active
  · rw [certificate.active_endpointDifference_eq_zero hwho]
    simp
  · have hinactive := certificate.inactive_continue who hwho
    have hquit := certificate.passive_quitValue_le_terminalPayoff hwho
    have hfixed := quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
      reward root who
    have hfalse : (root who false).toReal = 1 := by simp [hinactive]
    have htrue : (root who true).toReal = 0 := by simp [hinactive]
    have hquitEq :
        quittingRootQuitPayoff reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player) root who =
          quittingStationaryFixedOpponentsQuitValue reward root who := by
      simpa [quittingStationaryFixedOpponentsQuitValue] using
        (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
          reward (fun _ => root) who
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player) 0)
    have hsuccessor :
        quittingRootSuccessorPayoff reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player) root who =
          quittingRootContinuePayoff reward
            (fun player => quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) player) root who := by
      rw [quittingRootSuccessorPayoff_eq_endpointMix, hfalse, htrue]
      ring
    change quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) who =
        quittingRootSuccessorPayoff reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) root who at hfixed
    have hdiff : quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player) root who ≤ 0 := by
      rw [quittingRootEndpointDifference, hquitEq, hsuccessor.symm, ← hfixed]
      linarith
    constructor
    · simpa [hfalse] using hdiff
    · simp [htrue]

/-- **Empty-base all-behavior compiler.**  A solution of the finite
denominator-free system yields the stationary terminal payoff as a fixed
uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff
    (certificate : QuittingEmptyBaseInteriorCertificate reward active root) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) := by
  let value : Payoff ι := fun player => quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) player
  apply isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    reward root value certificate.absorbs
  · funext who
    exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  · exact certificate.endpointNash
  · exact certificate.opponents_contract

end QuittingEmptyBaseInteriorCertificate

end GameTheory
