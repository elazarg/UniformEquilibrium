/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargeBaseStationarySemanticHandoff
import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder

/-!
# Prescribed-owner fixed-law reset alignment on four players

For a selected `Fin 4` owner, the next two cyclic labels form a sure-quitting
base and the remaining cyclic label joins the owner as the free pair.  Any
induced Nash point gives an actual stationary semantic/law target with zero
owner debt and unit incidence in the first base label.  This is precisely the
actual-data adapter needed by the existing fixed-law reset dispatch.

The adapter and the separately available prescribed-owner stationary handoff
select independent induced Nash profiles.  No equality of their profiles,
laws, observers, payoffs, or chronology is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

/-- First sure-quitting label cyclically following a prescribed `Fin 4`
owner. -/
def finFourPrescribedResetFirstBase (owner : Fin 4) : Fin 4 := owner + 1

/-- Second sure-quitting label cyclically following a prescribed `Fin 4`
owner. -/
def finFourPrescribedResetSecondBase (owner : Fin 4) : Fin 4 := owner + 2

/-- The remaining free label for a prescribed `Fin 4` owner. -/
def finFourPrescribedResetOtherFree (owner : Fin 4) : Fin 4 := owner + 3

/-- Complementary sure pair used by the prescribed-owner reset adapter. -/
def finFourPrescribedResetBase (owner : Fin 4) : Finset (Fin 4) :=
  {finFourPrescribedResetFirstBase owner,
    finFourPrescribedResetSecondBase owner}

/-- Complementary free pair used by the prescribed-owner reset adapter. -/
def finFourPrescribedResetFree (owner : Fin 4) : Finset (Fin 4) :=
  {owner, finFourPrescribedResetOtherFree owner}

private theorem finFourPrescribedResetBase_nonempty (owner : Fin 4) :
    (finFourPrescribedResetBase owner).Nonempty := by
  simp [finFourPrescribedResetBase]

private theorem finFourPrescribedResetBase_disjoint_free (owner : Fin 4) :
    Disjoint (finFourPrescribedResetBase owner)
      (finFourPrescribedResetFree owner) := by
  fin_cases owner <;> decide

private theorem finFourPrescribedResetFirstBase_ne_owner (owner : Fin 4) :
    finFourPrescribedResetFirstBase owner ≠ owner := by
  fin_cases owner <;> decide

private theorem finFourPrescribedReset_owner_mem_free (owner : Fin 4) :
    owner ∈ finFourPrescribedResetFree owner := by
  simp [finFourPrescribedResetFree]

/-- A product root in which a genuine opponent Quits surely has one full unit
of first-stage incidence in that opponent. -/
private theorem quittingRootOpponentIncidenceMass_eq_one_of_pureQuit
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (root : ι → PMF Bool) (owner other : ι) (hne : other ≠ owner)
    (hother : root other = PMF.pure true) :
    quittingRootOpponentIncidenceMass owner other root = 1 := by
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hother
  have hzero : ∀ terminal : {S : Finset ι // S.Nonempty},
      other ∉ terminal.val → quittingRootCoalitionMass root terminal.val = 0 := by
    intro terminal hnot
    have hupper := quittingRootCoalitionMass_le_continueProbability_of_not_mem
      root terminal.val other hnot
    rw [hother] at hupper
    norm_num at hupper
    exact le_antisymm hupper
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        root terminal.val)
  have hfilter :
      (∑ terminal ∈ (Finset.univ.filter fun terminal :
          {S : Finset ι // S.Nonempty} ↦ other ∈ terminal.val),
        quittingRootCoalitionMass root terminal.val) =
        ∑ terminal : {S : Finset ι // S.Nonempty},
          quittingRootCoalitionMass root terminal.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro terminal _
    by_cases hmem : other ∈ terminal.val
    · simp [hmem]
    · simp [hmem, hzero terminal hmem]
  unfold quittingRootOpponentIncidenceMass
  have hevent : (Finset.univ.filter fun terminal :
      {S : Finset ι // S.Nonempty} ↦
        other ∈ terminal.val ∧ other ≠ owner) =
      Finset.univ.filter fun terminal : {S : Finset ι // S.Nonempty} ↦
        other ∈ terminal.val := by
    ext terminal
    simp [hne]
  rw [hevent]
  rw [hfilter]
  rw [← Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι))
    (fun coalition ↦ by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact Finset.nonempty_iff_ne_empty.symm)
    (quittingRootCoalitionMass root)]
  rw [quittingRootCoalitionMass_sum_nonempty, hcontinue]
  norm_num

/-- Every free coordinate of an induced persistent-base Nash row with a sure
base player has zero debt in the actual stationary semantic pair.  The result
uses the unrestricted stationary stopping cap, not stationary-only regret. -/
private theorem quittingTerminalSemanticDebt_stationaryPersistentBase_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hbase : base.Nonempty)
    (hdisjoint : Disjoint base free)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward base free)
    (who : ι) (hwho : who ∈ free) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStationaryProfile reward
            (quittingPersistentBaseRoot base free point))) who = 0 := by
  let root := quittingPersistentBaseRoot base free point
  let profile := quittingStationaryProfile reward root
  have hbaseCopy := hbase
  obtain ⟨quitter, hquitter⟩ := hbase
  have hquitterRoot : root quitter = PMF.pure true :=
    quittingPersistentBaseRoot_apply_of_mem_base base free point hquitter
  have hne : who ≠ quitter := by
    intro heq
    subst quitter
    exact (Finset.disjoint_left.mp hdisjoint hquitter hwho)
  have hcontinueMass : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hquitterRoot
  have hopponentMass :
      quittingStationaryFixedOpponentsContinueMass root who = 0 :=
    quittingStationaryContinueMass_update_of_sureQuitter
      hne hquitterRoot (PMF.pure false)
  have hpure := quittingPersistentBaseRoot_free_purePayoff_le
    reward base free hbaseCopy hdisjoint point hpoint who hwho
  have htarget : quittingTerminalPayoff reward profile who =
      quittingRootAbsorbingContribution reward root who := by
    rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
    · rw [hcontinueMass]
      norm_num
    · rw [hcontinueMass]
      norm_num
  have hsuccessor : quittingRootSuccessorPayoff reward 0 root who =
      quittingRootAbsorbingContribution reward root who := by
    unfold quittingRootSuccessorPayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      hcontinueMass]
    simp
  have hquit : quittingStationaryFixedOpponentsQuitValue reward root who ≤
      quittingTerminalPayoff reward profile who := by
    have hquitEq : quittingRootQuitPayoff reward 0 root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
      simpa [quittingStationaryFixedOpponentsQuitValue] using
        (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
          reward (fun _ ↦ root) who 0 0)
    calc
      quittingStationaryFixedOpponentsQuitValue reward root who =
          quittingRootQuitPayoff reward 0 root who := hquitEq.symm
      _ ≤ quittingRootSuccessorPayoff reward 0 root who := hpure.1
      _ = quittingRootAbsorbingContribution reward root who := hsuccessor
      _ = quittingTerminalPayoff reward profile who := htarget.symm
  have hcontinue :
      quittingStationaryFixedOpponentsContinueReward reward root who ≤
        quittingTerminalPayoff reward profile who := by
    have hcontinueEq : quittingRootContinuePayoff reward 0 root who =
        quittingStationaryFixedOpponentsContinueReward reward root who := by
      have hraw := quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ ↦ root) who 0 0
      simpa [quittingStationaryFixedOpponentsContinueReward] using hraw
    calc
      quittingStationaryFixedOpponentsContinueReward reward root who =
          quittingRootContinuePayoff reward 0 root who := hcontinueEq.symm
      _ ≤ quittingRootSuccessorPayoff reward 0 root who := hpure.2
      _ = quittingRootAbsorbingContribution reward root who := hsuccessor
      _ = quittingTerminalPayoff reward profile who := htarget.symm
  have hcapUpper : quittingStationaryUnilateralCap reward root who ≤
      quittingTerminalPayoff reward profile who := by
    rw [quittingStationaryUnilateralCap_eq_max_div, hopponentMass]
    norm_num
    exact ⟨hquit, hcontinue⟩
  have hpayoffLower : quittingTerminalPayoff reward profile who ≤
      quittingStationaryUnilateralCap reward root who := by
    rw [← quittingBestReplyValue_stationary]
    have hself := le_quittingBestReplyValue reward profile who (profile who)
    simpa only [Function.update_eq_self] using hself
  have heq : quittingTerminalPayoff reward profile who =
      quittingStationaryUnilateralCap reward root who :=
    le_antisymm hpayoffLower hcapUpper
  unfold quittingTerminalSemanticDebt
  rw [quittingTerminalSemanticPair_stationary_envelope_eq_cap]
  change quittingStationaryUnilateralCap reward root who -
    quittingTerminalPayoff reward profile who = 0
  rw [heq]
  exact sub_self _

/-- Any selected positive debtor at a global minimum on the literal four-player
carrier admits an actual unit-incidence fixed-law reset dispatch with that
same selected player as reset owner.

The stationary target and its complete law are selected together from the
pair-base induced Nash carrier.  The conclusion does not identify this profile
with a singleton-base stationary handoff selected elsewhere. -/
theorem QuittingTerminalExploitabilityWitness.exists_finFour_prescribedOwner_reset_of_inducedNash
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (source : QuittingTerminalSemanticPair (Fin 4)) (owner : Fin 4)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hownerPositive : 0 < quittingTerminalSemanticDebt source owner)
    (point : mixedPolytope
      (quittingBinaryForm (finFourPrescribedResetFree owner)).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward
      (finFourPrescribedResetBase owner)
      (finFourPrescribedResetFree owner)) :
    let root := quittingPersistentBaseRoot
      (finFourPrescribedResetBase owner)
      (finFourPrescribedResetFree owner) point
    let profile := quittingStationaryProfile reward root
    let target := quittingTerminalSemanticPair reward profile
    let mass := quittingTerminalOutcomeMass reward profile
    (target, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt target owner = 0 ∧
      quittingTerminalOpponentIncidenceMass owner
        (finFourPrescribedResetFirstBase owner) mass = 1 ∧
      ∃ returned, QuittingFixedLawResetDispatch (reward := reward)
        source target mass owner
          (finFourPrescribedResetFirstBase owner) returned := by
  let root := quittingPersistentBaseRoot
    (finFourPrescribedResetBase owner)
    (finFourPrescribedResetFree owner) point
  let profile := quittingStationaryProfile reward root
  let target := quittingTerminalSemanticPair reward profile
  let mass := quittingTerminalOutcomeMass reward profile
  have hjoint : (target, mass) ∈
      quittingTerminalSemanticLawCarrier reward := by
    exact quittingTerminalSemanticLawPoint_mem_carrier reward profile
  have hreset : quittingTerminalSemanticDebt target owner = 0 := by
    exact quittingTerminalSemanticDebt_stationaryPersistentBase_eq_zero
      reward (finFourPrescribedResetBase owner)
        (finFourPrescribedResetFree owner)
        (finFourPrescribedResetBase_nonempty owner)
        (finFourPrescribedResetBase_disjoint_free owner)
        point hpoint owner (finFourPrescribedReset_owner_mem_free owner)
  have hfirstRoot : root (finFourPrescribedResetFirstBase owner) =
      PMF.pure true := by
    exact quittingPersistentBaseRoot_apply_of_mem_base
      (finFourPrescribedResetBase owner)
      (finFourPrescribedResetFree owner) point (by
        simp [finFourPrescribedResetBase])
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hfirstRoot
  have hrootIncidence : quittingRootOpponentIncidenceMass owner
      (finFourPrescribedResetFirstBase owner) root = 1 :=
    quittingRootOpponentIncidenceMass_eq_one_of_pureQuit root owner
      (finFourPrescribedResetFirstBase owner)
      (finFourPrescribedResetFirstBase_ne_owner owner) hfirstRoot
  have hlaw : mass = quittingTerminalOutcomeLawPrefix root mass := by
    symm
    simpa only [mass, profile,
      quittingRootThenContinuationProfile_stationary] using
      (quittingTerminalOutcomeLawPrefix_outcomeMass reward root profile)
  have hincidence : quittingTerminalOpponentIncidenceMass owner
      (finFourPrescribedResetFirstBase owner) mass = 1 := by
    rw [hlaw, quittingTerminalOpponentIncidenceMass_lawPrefix,
      hrootIncidence, hcontinue]
    simp
  have hsourcePositive : 0 < quittingTerminalSemanticDebtSum source := by
    apply hownerPositive.trans_le
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ ↦
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hsource player)
      (Finset.mem_univ owner)
  obtain ⟨returned, hreturned⟩ := witness.exists_fixedLawResetDispatch
    source target mass owner (finFourPrescribedResetFirstBase owner)
      hminimum hsourcePositive hjoint hreset (by linarith [hincidence])
  exact ⟨hjoint, hreset, hincidence, returned, hreturned⟩

/-- The complementary pair-base induced Nash carrier is nonempty, so the
pointwise prescribed-owner reset adapter always has an actual stationary
source. -/
theorem QuittingTerminalExploitabilityWitness.exists_finFour_prescribedOwner_resetDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (source : QuittingTerminalSemanticPair (Fin 4)) (owner : Fin 4)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hownerPositive : 0 < quittingTerminalSemanticDebt source owner) :
    ∃ point ∈ quittingPersistentBaseNashSet reward
        (finFourPrescribedResetBase owner)
        (finFourPrescribedResetFree owner),
      let root := quittingPersistentBaseRoot
        (finFourPrescribedResetBase owner)
        (finFourPrescribedResetFree owner) point
      let profile := quittingStationaryProfile reward root
      let target := quittingTerminalSemanticPair reward profile
      let mass := quittingTerminalOutcomeMass reward profile
      (target, mass) ∈ quittingTerminalSemanticLawCarrier reward ∧
        quittingTerminalSemanticDebt target owner = 0 ∧
        quittingTerminalOpponentIncidenceMass owner
          (finFourPrescribedResetFirstBase owner) mass = 1 ∧
        ∃ returned, QuittingFixedLawResetDispatch (reward := reward)
          source target mass owner
            (finFourPrescribedResetFirstBase owner) returned := by
  obtain ⟨point, hpoint⟩ := quittingPersistentBaseNashSet_nonempty reward
    (finFourPrescribedResetBase owner)
    (finFourPrescribedResetFree owner)
  exact ⟨point, hpoint,
    witness.exists_finFour_prescribedOwner_reset_of_inducedNash
      source owner hsource hminimum hownerPositive point hpoint⟩

end GameTheory
