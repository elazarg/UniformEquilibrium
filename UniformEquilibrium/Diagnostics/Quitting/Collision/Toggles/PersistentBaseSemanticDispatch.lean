/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Finset.ProdLtOne
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# Persistent-base semantic dispatch for a strict-toggle face

For a face with at least two persistent quitters, one unilateral deviation
cannot remove date-zero absorption.  This file assembles the induced
free-player Nash inequalities, persistent-player leave inequalities, and
outsider join inequalities into an exact all-behavior stationary compiler.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite face data for the persistent-base successful branch.  The three
sign fields are precisely the free Nash, base leave, and outsider join
conditions, expressed in the common endpoint-difference coordinate. -/
structure QuittingPersistentBaseCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (root : ι → PMF Bool) : Prop where
  disjoint : Disjoint base free
  two_le_base_card : 2 ≤ base.card
  base_quits : ∀ who ∈ base, root who = PMF.pure true
  outsiders_continue : ∀ who ∉ base ∪ free, root who = PMF.pure false
  free_nash : ∀ who ∈ free,
    (root who false).toReal *
        quittingRootEndpointDifference reward 0 root who ≤ 0 ∧
      0 ≤ (root who true).toReal *
        quittingRootEndpointDifference reward 0 root who
  base_leave : ∀ who ∈ base,
    0 ≤ quittingRootEndpointDifference reward 0 root who
  outsider_join : ∀ who ∉ base ∪ free,
    quittingRootEndpointDifference reward 0 root who ≤ 0

namespace QuittingPersistentBaseCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {base free : Finset ι} {root : ι → PMF Bool}

/-- The persistent base is nonempty. -/
theorem base_nonempty
    (certificate : QuittingPersistentBaseCertificate reward base free root) :
    base.Nonempty :=
  (Finset.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le Nat.one_lt_two certificate.two_le_base_card)).nonempty

/-- Every player has a distinct persistent base quitter. -/
theorem exists_base_opponent
    (certificate : QuittingPersistentBaseCertificate reward base free root)
    (who : ι) : ∃ quitter ∈ base, quitter ≠ who := by
  have hnontrivial : base.Nontrivial :=
    Finset.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le Nat.one_lt_two certificate.two_le_base_card)
  obtain ⟨quitter, hquitter⟩ := hnontrivial.erase_nonempty (a := who)
  exact ⟨quitter, Finset.mem_of_mem_erase hquitter,
    Finset.ne_of_mem_erase hquitter⟩

/-- The row absorbs surely at date zero. -/
theorem continueMass_eq_zero
    (certificate : QuittingPersistentBaseCertificate reward base free root) :
    quittingStationaryContinueMass root = 0 := by
  obtain ⟨quitter, hquitter⟩ := certificate.base_nonempty
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_zero (Finset.mem_univ quitter)
  simp [certificate.base_quits quitter hquitter]

/-- Even after one coordinate is forced to Continue, another persistent base
quitter makes the fixed-opponent Continue mass zero. -/
theorem opponents_continueMass_eq_zero
    (certificate : QuittingPersistentBaseCertificate reward base free root)
    (who : ι) :
    quittingStationaryFixedOpponentsContinueMass root who = 0 := by
  obtain ⟨quitter, hquitter, hne⟩ := certificate.exists_base_opponent who
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_zero (Finset.mem_univ quitter)
  change ((Function.update root who (PMF.pure false) quitter) false).toReal = 0
  rw [Function.update_of_ne hne, certificate.base_quits quitter hquitter]
  simp

/-- With sure absorption, the actual stationary payoff is the one-stage
absorbing contribution. -/
theorem terminalPayoff_eq_absorbingContribution
    (certificate : QuittingPersistentBaseCertificate reward base free root) :
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) =
      quittingRootAbsorbingContribution reward root := by
  funext who
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · rw [certificate.continueMass_eq_zero]
    simp
  · rw [certificate.continueMass_eq_zero]
    norm_num

/-- Since no all-Continue branch is reached, replacing the displayed tail
zero by the actual stationary payoff does not change any endpoint difference. -/
theorem endpointDifference_actual_eq_zeroTail
    (certificate : QuittingPersistentBaseCertificate reward base free root)
    (who : ι) :
    quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player) root who =
      quittingRootEndpointDifference reward 0 root who := by
  let actual : Payoff ι := fun player => quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) player
  have hquitActual :
      quittingRootQuitPayoff reward actual root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [actual, quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who actual 0)
  have hquitZero :
      quittingRootQuitPayoff reward 0 root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who 0 0)
  have hcontinueActual :
      quittingRootContinuePayoff reward actual root who =
        quittingStationaryFixedOpponentsContinueReward reward root who := by
    have hraw := quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who actual 0
    have hmass : quittingFixedOpponentsContinueMass
        (fun _ => root) who 0 = 0 := by
      exact certificate.opponents_continueMass_eq_zero who
    rw [hraw, hmass]
    simp [quittingStationaryFixedOpponentsContinueReward]
  have hcontinueZero :
      quittingRootContinuePayoff reward 0 root who =
        quittingStationaryFixedOpponentsContinueReward reward root who := by
    have hraw := quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => root) who 0 0
    have hmass : quittingFixedOpponentsContinueMass
        (fun _ => root) who 0 = 0 := by
      exact certificate.opponents_continueMass_eq_zero who
    rw [hraw, hmass]
    simp [quittingStationaryFixedOpponentsContinueReward]
  change quittingRootEndpointDifference reward actual root who = _
  simp [quittingRootEndpointDifference, hquitActual, hquitZero,
    hcontinueActual, hcontinueZero]

/-- The three finite sign packets assemble into exact endpoint Nash at the
actual terminal payoff. -/
theorem endpointNash
    (certificate : QuittingPersistentBaseCertificate reward base free root) :
    IsεQuittingRootEndpointNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) 0 root := by
  intro who
  rw [certificate.endpointDifference_actual_eq_zeroTail who]
  by_cases hbase : who ∈ base
  · have hquit := certificate.base_quits who hbase
    have hsign := certificate.base_leave who hbase
    simp [hquit, hsign]
  · by_cases hfree : who ∈ free
    · simpa using certificate.free_nash who hfree
    · have houtside : who ∉ base ∪ free := by simp [hbase, hfree]
      have hcontinue := certificate.outsiders_continue who houtside
      have hsign := certificate.outsider_join who houtside
      simp [hcontinue, hsign]

/-- **Persistent-base all-behavior compiler.**  The successful finite face
screen with two persistent quitters produces the actual stationary terminal
payoff as a fixed uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff
    (certificate : QuittingPersistentBaseCertificate reward base free root) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (fun player => quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) := by
  let value : Payoff ι := fun player => quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) player
  apply isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    reward root value
  · rw [certificate.continueMass_eq_zero]
    norm_num
  · funext who
    exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  · exact certificate.endpointNash
  · intro who
    rw [certificate.opponents_continueMass_eq_zero who]
    norm_num

end QuittingPersistentBaseCertificate

end GameTheory
