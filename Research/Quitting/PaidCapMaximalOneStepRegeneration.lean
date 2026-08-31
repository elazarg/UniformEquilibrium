/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourPaidResetDescentRegeneration
import Research.Quitting.CausalTailEscapeMaxAbsorptionCore

/-!
# Canonical maximal-root regeneration of an attained paid/reset source

The summable paid-cap port uses an arbitrary exact cap--Nash selector, so its
zero-absorption inert branch is selector-dependent.  This module replaces that
branch by the canonical maximal-absorption root at the same actual source.

If the maximal root has positive absorption, positive global minimum debt
forces positive continuation.  One literal prefix then strictly lowers actual
total debt, transports a positive pure-time paid row, preserves a zero-debt
reset coordinate and positive same-law opponent incidence, and reruns the
fixed-law reset dispatch.  If maximal absorption is zero, maximality forces
every exact root at the source cap to be literally all Continue.

This eliminates arbitrary-selector inertness.  It does not prove that the
remaining unique-all-Continue cap is impossible, and strict real-valued debt
descent is not itself well founded.
-/

noncomputable section

namespace GameTheory

open Finset
open Math.Probability Math.PMFProduct

namespace QuittingPaidCapLiftedSource

variable
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Selector-independent obstruction at the cap of one attained paid source:
every exact cap--Nash root is literally all Continue. -/
def HasUniqueAllContinueAtCap
    (source : QuittingPaidCapLiftedSource reward) : Prop :=
  ∀ candidate : ι → PMF Bool,
    IsεQuittingRootNash reward
        (quittingTerminalSemanticPair reward source.profile).2 0 candidate →
      candidate = (quittingAllContinueRoot : ι → PMF Bool)

/-- A positive maximal-absorption exact root gives one actual paid/reset
successor.  Unlike `FinitePaidResetRegeneration`, this successor is formed by
the canonical maximal root rather than the arbitrary cap-prefix selector. -/
structure MaximalOneStepPaidResetRegeneration
    (source : QuittingPaidCapLiftedSource reward)
    (resetOwner other : ι) where
  root_absorption_pos : 0 < quittingRootAbsorptionMass
    (quittingMaximalCapPrefixRoot reward source.profile)
  root_continue_pos : 0 < quittingStationaryContinueMass
    (quittingMaximalCapPrefixRoot reward source.profile)
  descendant : QuittingPaidCapLiftedSource reward
  descendant_profile : descendant.profile =
    quittingMaximalCapPrefixProfile reward source.profile 1
  descendant_minimum : descendant.minimum = source.minimum
  descendant_observer : descendant.observer = source.observer
  descendant_gain : descendant.gain =
    quittingStationaryContinueMass
        (quittingMaximalCapPrefixRoot reward source.profile) * source.gain
  descendant_row_sourceWitness : descendant.row.sourceWitness =
    quittingCapLiftPureTimeShift 1 source.row.sourceWitness
  descendant_row_receivingWitness : descendant.row.receivingWitness =
    quittingCapLiftPureTimeShift 1 source.row.receivingWitness
  descendant_debt_coordinate : ∀ who,
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward descendant.profile) who =
      quittingStationaryContinueMass
          (quittingMaximalCapPrefixRoot reward source.profile) *
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source.profile) who
  descendant_initialDebt : descendant.initialDebt =
    quittingStationaryContinueMass
        (quittingMaximalCapPrefixRoot reward source.profile) *
      source.initialDebt
  strict_debt : descendant.initialDebt < source.initialDebt
  target_joint :
    (quittingTerminalSemanticPair reward descendant.profile,
      quittingTerminalOutcomeMass reward descendant.profile) ∈
      quittingTerminalSemanticLawCarrier reward
  reset_debt : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward descendant.profile) resetOwner = 0
  reset_incidence : 0 <
    quittingTerminalOpponentIncidenceMass resetOwner other
      (quittingTerminalOutcomeMass reward descendant.profile)
  reset_incidence_lower :
    quittingStationaryContinueMass
          (quittingMaximalCapPrefixRoot reward source.profile) *
        quittingTerminalOpponentIncidenceMass resetOwner other
          (quittingTerminalOutcomeMass reward source.profile) ≤
      quittingTerminalOpponentIncidenceMass resetOwner other
        (quittingTerminalOutcomeMass reward descendant.profile)
  returned : QuittingTerminalSemanticPair ι
  dispatch : QuittingFixedLawResetDispatch (reward := reward)
    source.minimum
    (quittingTerminalSemanticPair reward descendant.profile)
    (quittingTerminalOutcomeMass reward descendant.profile)
    resetOwner other returned

/-- The arbitrary-selector inert branch can be replaced by a canonical
alternative.  Positive maximal absorption produces a strictly lower-debt
actual paid/reset source in one step.  Zero maximal absorption forces every
exact root at the same cap to be all Continue. -/
theorem maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
    (source : QuittingPaidCapLiftedSource reward)
    (witness : QuittingTerminalExploitabilityWitness reward)
    (resetOwner other : ι)
    (hreset : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source.profile) resetOwner = 0)
    (hincidence : 0 < quittingTerminalOpponentIncidenceMass resetOwner other
      (quittingTerminalOutcomeMass reward source.profile)) :
    Nonempty (source.MaximalOneStepPaidResetRegeneration resetOwner other) ∨
      source.HasUniqueAllContinueAtCap := by
  let root := quittingMaximalCapPrefixRoot reward source.profile
  let nextProfile := quittingMaximalCapPrefixProfile reward source.profile 1
  have hnash : IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward source.profile).2 0 root := by
    simpa [root] using
      (quittingMaximalCapPrefixRoot_exactNash reward source.profile)
  have hnextProfile : nextProfile =
      quittingRootThenContinuationProfile reward root source.profile := by
    simp [nextProfile, root]
  have hstep : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward nextProfile) =
      quittingStationaryContinueMass root * source.initialDebt := by
    simpa [nextProfile, root, QuittingPaidCapLiftedSource.initialDebt] using
      (quittingMaximalCapPrefixProfile_debt_succ
        reward source.profile 0)
  have hnextLower := source.minimum_le
    (quittingTerminalSemanticPair reward nextProfile)
    (quittingTerminalSemanticPair_mem_carrier reward nextProfile)
  have hnextPos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward nextProfile) :=
    source.minimum_pos.trans_le hnextLower
  have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
    quittingStationaryContinueMass_nonneg root
  have hcontinue : 0 < quittingStationaryContinueMass root := by
    rw [hstep] at hnextPos
    nlinarith [source.initialDebt_pos]
  by_cases habsorption : 0 < quittingRootAbsorptionMass root
  · have hcontinueLt : quittingStationaryContinueMass root < 1 := by
      unfold quittingRootAbsorptionMass at habsorption
      linarith
    have hstrict : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward nextProfile) <
        source.initialDebt := by
      rw [hstep]
      nlinarith [source.initialDebt_pos]
    have hsourceEdge : source.gain ≤
        quittingPureTimeDeviationPayoff reward source.profile source.observer
            source.row.receivingWitness -
          quittingPureTimeDeviationPayoff reward source.profile source.observer
            source.row.sourceWitness :=
      source.row.gain_le_paid.trans_eq source.row.edge_identity.symm
    have hfixedNonneg : 0 ≤
        quittingStationaryFixedOpponentsContinueMass root source.observer :=
      quittingStationaryFixedOpponentsContinueMass_nonneg root source.observer
    have hscaled : quittingStationaryContinueMass root * source.gain ≤
        quittingStationaryFixedOpponentsContinueMass root source.observer *
          (quittingPureTimeDeviationPayoff reward source.profile source.observer
              source.row.receivingWitness -
            quittingPureTimeDeviationPayoff reward source.profile source.observer
              source.row.sourceWitness) := by
      calc
        quittingStationaryContinueMass root * source.gain ≤
            quittingStationaryFixedOpponentsContinueMass root source.observer *
              source.gain :=
          mul_le_mul_of_nonneg_right
            (quittingStationaryContinueMass_le_fixedOpponentsContinueMass
              root source.observer) source.gain_pos.le
        _ ≤ _ := mul_le_mul_of_nonneg_left hsourceEdge hfixedNonneg
    have hnewEdge : quittingStationaryContinueMass root * source.gain ≤
        quittingPureTimeDeviationPayoff reward nextProfile source.observer
            (quittingCapLiftPureTimeShift 1 source.row.receivingWitness) -
          quittingPureTimeDeviationPayoff reward nextProfile source.observer
            (quittingCapLiftPureTimeShift 1 source.row.sourceWitness) := by
      rw [hnextProfile,
        quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one]
      exact hscaled
    have hgainPos : 0 < quittingStationaryContinueMass root * source.gain :=
      mul_pos hcontinue source.gain_pos
    obtain ⟨row, hsourceWitness, hreceivingWitness⟩ :=
      exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward
        nextProfile source.observer
        (quittingCapLiftPureTimeShift 1 source.row.sourceWitness)
        (quittingCapLiftPureTimeShift 1 source.row.receivingWitness)
        (quittingStationaryContinueMass root * source.gain)
        hgainPos hnewEdge
    let descendant : QuittingPaidCapLiftedSource reward := {
      minimum := source.minimum
      minimum_le := source.minimum_le
      minimum_pos := source.minimum_pos
      profile := nextProfile
      observer := source.observer
      gain := quittingStationaryContinueMass root * source.gain
      gain_pos := hgainPos
      row := row }
    have hdebtCoordinate : ∀ who,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward nextProfile) who =
          quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward source.profile) who := by
      intro who
      rw [hnextProfile,
        quittingTerminalSemanticPair_rootThenContinuation reward root
          source.profile,
        quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
          (reward := reward)
          (quittingTerminalSemanticPair reward source.profile) root who hnash]
    have hresetNext : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward nextProfile) resetOwner = 0 := by
      rw [hnextProfile,
        quittingTerminalSemanticPair_rootThenContinuation reward root
          source.profile,
        quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
          (reward := reward)
          (quittingTerminalSemanticPair reward source.profile) root resetOwner
          hnash,
        hreset, mul_zero]
    have hincidenceLower :
        quittingStationaryContinueMass root *
            quittingTerminalOpponentIncidenceMass resetOwner other
              (quittingTerminalOutcomeMass reward source.profile) ≤
          quittingTerminalOpponentIncidenceMass resetOwner other
            (quittingTerminalOutcomeMass reward nextProfile) := by
      rw [hnextProfile,
        ← quittingTerminalOutcomeLawPrefix_outcomeMass
          reward root source.profile]
      exact quittingStationaryContinueMass_mul_incidence_le_lawPrefix
        resetOwner other root
          (quittingTerminalOutcomeMass reward source.profile)
    have hincidenceNext : 0 <
        quittingTerminalOpponentIncidenceMass resetOwner other
          (quittingTerminalOutcomeMass reward nextProfile) := by
      exact (mul_pos hcontinue hincidence).trans_le hincidenceLower
    have hjoint := quittingTerminalSemanticLawPoint_mem_carrier reward
      nextProfile
    obtain ⟨returned, dispatch⟩ := witness.exists_fixedLawResetDispatch
      source.minimum
      (quittingTerminalSemanticPair reward nextProfile)
      (quittingTerminalOutcomeMass reward nextProfile)
      resetOwner other source.minimum_le source.minimum_pos hjoint
      hresetNext hincidenceNext
    exact Or.inl ⟨{
      root_absorption_pos := by simpa [root] using habsorption
      root_continue_pos := by simpa [root] using hcontinue
      descendant := descendant
      descendant_profile := rfl
      descendant_minimum := rfl
      descendant_observer := rfl
      descendant_gain := rfl
      descendant_row_sourceWitness := by
        simpa [descendant] using hsourceWitness
      descendant_row_receivingWitness := by
        simpa [descendant] using hreceivingWitness
      descendant_debt_coordinate := by
        intro who
        simpa [descendant, root] using hdebtCoordinate who
      descendant_initialDebt := by
        simpa [descendant, root, QuittingPaidCapLiftedSource.initialDebt]
          using hstep
      strict_debt := by
        simpa [descendant, QuittingPaidCapLiftedSource.initialDebt] using hstrict
      target_joint := by simpa [descendant] using hjoint
      reset_debt := by simpa [descendant] using hresetNext
      reset_incidence := by simpa [descendant] using hincidenceNext
      reset_incidence_lower := by
        simpa [descendant, root] using hincidenceLower
      returned := returned
      dispatch := by simpa [descendant] using dispatch }⟩
  · right
    have hrootZero : quittingRootAbsorptionMass root = 0 :=
      le_antisymm (le_of_not_gt habsorption)
        (quittingRootAbsorptionMass_nonneg root)
    intro candidate hcandidate
    have hle := quittingMaximalCapPrefixRoot_maximal
      reward source.profile candidate hcandidate
    have hcandidateZero : quittingRootAbsorptionMass candidate = 0 := by
      apply le_antisymm
      · simpa [root, hrootZero] using hle
      · exact quittingRootAbsorptionMass_nonneg candidate
    have hcandidateContinue : quittingStationaryContinueMass candidate = 1 := by
      unfold quittingRootAbsorptionMass at hcandidateZero
      linarith
    funext who
    simpa [quittingAllContinueRoot] using
      eq_pure_false_of_quittingStationaryContinueMass_eq_one
        hcandidateContinue who

end QuittingPaidCapLiftedSource

end GameTheory
