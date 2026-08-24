/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Classification.InstantPunishmentEquivalence
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics

/-!
# Singleton persistent-base semantic dispatch

The sole persistent quitter can remove date-zero absorption by deviating to
Continue.  The correct face inequality therefore prices that branch at the
player's exact punishment value.  A near-minmax constant row realizes this
price with arbitrarily small error, while the nominal terminal payoff remains
the same fixed date-zero product payoff at every accuracy.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite successful-face data when the persistent base is the singleton
`owner`.  Other players satisfy their exact date-zero endpoint inequalities;
the owner's Continue endpoint is evaluated at the exact punishment value. -/
structure QuittingSingletonBaseCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool) : Prop where
  owner_quits : root owner = PMF.pure true
  other_endpointNash : ∀ who, who ≠ owner →
    (root who false).toReal *
        quittingRootEndpointDifference reward 0 root who ≤ 0 ∧
      0 ≤ (root who true).toReal *
        quittingRootEndpointDifference reward 0 root who
  owner_floor_balance :
    quittingStationaryFixedOpponentsContinueReward reward root owner +
        quittingStationaryFixedOpponentsContinueMass root owner *
          quittingPunishmentValue reward owner ≤
      quittingRootAbsorbingContribution reward root owner

namespace QuittingSingletonBaseCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner : ι} {root : ι → PMF Bool}

/-- The nominal row absorbs surely. -/
theorem continueMass_eq_zero
    (certificate : QuittingSingletonBaseCertificate reward owner root) :
    quittingStationaryContinueMass root = 0 :=
  quittingStationaryContinueMass_of_sureQuitter certificate.owner_quits

/-- The sure owner's pure-Quit endpoint is the nominal date-zero payoff. -/
theorem owner_quitValue_eq_target
    (certificate : QuittingSingletonBaseCertificate reward owner root) :
    quittingStationaryFixedOpponentsQuitValue reward root owner =
      quittingRootAbsorbingContribution reward root owner := by
  change quittingRootAbsorbingContribution reward
    (Function.update root owner (PMF.pure true)) owner = _
  rw [← certificate.owner_quits, Function.update_eq_self]

/-- Every other player still faces the sure owner, so its opponent Continue
mass vanishes. -/
theorem other_opponentsContinueMass_eq_zero
    (certificate : QuittingSingletonBaseCertificate reward owner root)
    {who : ι} (hne : who ≠ owner) :
    quittingStationaryFixedOpponentsContinueMass root who = 0 := by
  exact quittingStationaryContinueMass_update_of_sureQuitter
    hne certificate.owner_quits (PMF.pure false)

/-- The nominal successor payoff at zero tail is the date-zero target. -/
theorem successorPayoff_zero_eq_target
    (certificate : QuittingSingletonBaseCertificate reward owner root)
    (who : ι) :
    quittingRootSuccessorPayoff reward 0 root who =
      quittingRootAbsorbingContribution reward root who := by
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    certificate.continueMass_eq_zero]
  simp

/-- The finite endpoint conditions bound both date-zero pure actions of every
nonowner by the fixed nominal target. -/
theorem other_pure_endpoints_le_target
    (certificate : QuittingSingletonBaseCertificate reward owner root)
    {who : ι} (hne : who ≠ owner) :
    quittingStationaryFixedOpponentsQuitValue reward root who ≤
        quittingRootAbsorbingContribution reward root who ∧
      quittingStationaryFixedOpponentsContinueReward reward root who ≤
        quittingRootAbsorbingContribution reward root who := by
  have hsign := certificate.other_endpointNash who hne
  have hquitRegret := quittingRootQuitPayoff_sub_successorPayoff
    reward 0 root who
  have hcontinueRegret := quittingRootContinuePayoff_sub_successorPayoff
    reward 0 root who
  have hquitEq : quittingRootQuitPayoff reward 0 root who =
      quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who 0 0)
  have hcontinueEq : quittingRootContinuePayoff reward 0 root who =
      quittingStationaryFixedOpponentsContinueReward reward root who := by
    have hraw := quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who 0 0
    have hmass : quittingFixedOpponentsContinueMass
        (fun _ => root) who 0 = 0 := by
      exact certificate.other_opponentsContinueMass_eq_zero hne
    rw [hraw, hmass]
    simp [quittingStationaryFixedOpponentsContinueReward]
  rw [hquitEq, certificate.successorPayoff_zero_eq_target] at hquitRegret
  rw [hcontinueEq, certificate.successorPayoff_zero_eq_target] at hcontinueRegret
  constructor
  · linarith [hsign.1]
  · linarith [hsign.2]

/-- At every positive accuracy, the exact punishment value can be realized
closely enough to make the one-stage splice a terminal approximate Nash
profile against all behavioral deviations, with the same nominal target. -/
theorem exists_terminalNash_fixedTarget
    (certificate : QuittingSingletonBaseCertificate reward owner root)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) epsilon profile ∧
        quittingTerminalPayoff reward profile =
          quittingRootAbsorbingContribution reward root := by
  have hhalf : 0 < epsilon / 2 := by linarith
  obtain ⟨punishRow, hpunish⟩ :=
    exists_punishRow_stationaryUnilateralCap_le reward owner hhalf
  let profile := quittingOneStagePunishedProfile reward root punishRow
  refine ⟨profile, ?_, ?_⟩
  · intro who deviation
    have hcap := quittingTerminalPayoff_update_oneStagePunishedProfile_le
      reward root punishRow who deviation
    have hvalue := quittingTerminalPayoff_oneStagePunishedProfile
      reward root punishRow who certificate.continueMass_eq_zero
    change quittingTerminalPayoff reward
      (Function.update profile who deviation) who ≤
        quittingTerminalPayoff reward profile who + epsilon
    change quittingTerminalPayoff reward
      (Function.update
        (quittingOneStagePunishedProfile reward root punishRow) who deviation) who ≤ _
    rw [hvalue]
    refine hcap.trans ?_
    by_cases hwho : who = owner
    · subst who
      rw [certificate.owner_quitValue_eq_target]
      apply max_le
      · linarith
      · have hmassNonneg :=
          quittingStationaryFixedOpponentsContinueMass_nonneg root owner
        have hmassLe :=
          quittingStationaryFixedOpponentsContinueMass_le_one root owner
        have hscaled := mul_le_mul_of_nonneg_left hpunish hmassNonneg
        have herror :
            quittingStationaryFixedOpponentsContinueMass root owner *
                (epsilon / 2) ≤ epsilon / 2 := by
          simpa using mul_le_mul_of_nonneg_right hmassLe hhalf.le
        nlinarith [certificate.owner_floor_balance]
    · obtain ⟨hquit, hcontinue⟩ :=
        certificate.other_pure_endpoints_le_target hwho
      rw [certificate.other_opponentsContinueMass_eq_zero hwho]
      simp only [zero_mul, add_zero]
      exact max_le (hquit.trans (by linarith)) (hcontinue.trans (by linarith))
  · funext who
    exact quittingTerminalPayoff_oneStagePunishedProfile
      reward root punishRow who certificate.continueMass_eq_zero

/-- **Singleton-base all-behavior compiler.**  The floor-priced face
inequality gives the nominal date-zero payoff as one fixed uniform-equilibrium
payoff. -/
theorem isUniformEquilibriumPayoff
    (certificate : QuittingSingletonBaseCertificate reward owner root) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingRootAbsorbingContribution reward root) := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget
  intro epsilon hepsilon
  exact certificate.exists_terminalNash_fixedTarget hepsilon

end QuittingSingletonBaseCertificate

end GameTheory
