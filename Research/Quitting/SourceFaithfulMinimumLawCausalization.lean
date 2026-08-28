/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.NonsingletonMinimumLawLinearTransfer
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration

/-!
# Source-faithful minimum-law causalization

This file causalizes one supplied joint-law realizing sequence without
selecting a replacement sequence or replacement marked dates.  Only the
finite exact cap--Nash words and finite window cutoffs are chosen.

It also proves the source-independent behavioral response transport used by
the causalization: two arbitrary complete responses which both Continue
through the chosen word retain their exact suffix payoff contrast, scaled by
the observer-deleted survival of that word.  No stopping-time boundedness,
compact response menu, or measurable selector is assumed.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open QuittingNonsingletonMinimumLawTransfer
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Arbitrary behavioral response transport -/

/-- Shift one complete behavioral response behind a literal root word by
forcing the responder to Continue throughout the word and then following the
supplied response literally. -/
def quittingShiftedBehavioralResponse
    (roots : List (ι → PMF Bool)) (who : ι)
    (response : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).BehaviorStrategy who :=
  quittingLiteralRootStackContinueDeviation reward roots response

/-- Exact two-counterfactual transport for arbitrary complete behavioral
responses.  The survival factor deletes the responder's own hazards because
both shifted counterfactuals force that player to Continue in the prefix. -/
theorem quittingTerminalPayoff_shiftedBehavioralResponse_sub_eq
    (roots : List (ι → PMF Bool))
    (suffix : (quittingGame reward).BehaviorProfile) (who : ι)
    (first second : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward roots suffix) who
            (quittingShiftedBehavioralResponse
              (reward := reward) roots who first)) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward roots suffix) who
            (quittingShiftedBehavioralResponse
              (reward := reward) roots who second)) who =
      quittingLiteralRootStackOpponentSurvival roots who *
        (quittingTerminalPayoff reward (Function.update suffix who first) who -
          quittingTerminalPayoff reward
            (Function.update suffix who second) who) := by
  rw [quittingShiftedBehavioralResponse,
    quittingShiftedBehavioralResponse,
    update_quittingLiteralRootStackProfile_continueDeviation,
    update_quittingLiteralRootStackProfile_continueDeviation,
    quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul]
  change quittingLiteralRootStackJointSurvival
      (quittingLiteralRootStackForceContinue roots who) * _ = _
  rw [quittingLiteralRootStackJointSurvival_forceContinue]

/-- Every supplied suffix contrast lower bound transports with the exact
opponent-survival coefficient. -/
theorem quittingTerminalPayoff_shiftedBehavioralResponse_sub_ge_mul
    (roots : List (ι → PMF Bool))
    (suffix : (quittingGame reward).BehaviorProfile) (who : ι)
    (first second : (quittingGame reward).BehaviorStrategy who)
    (lower : ℝ)
    (hbound : lower ≤
      quittingTerminalPayoff reward (Function.update suffix who first) who -
        quittingTerminalPayoff reward
          (Function.update suffix who second) who) :
    quittingLiteralRootStackOpponentSurvival roots who * lower ≤
      quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward roots suffix) who
            (quittingShiftedBehavioralResponse
              (reward := reward) roots who first)) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward roots suffix) who
            (quittingShiftedBehavioralResponse
              (reward := reward) roots who second)) who := by
  rw [quittingTerminalPayoff_shiftedBehavioralResponse_sub_eq]
  exact mul_le_mul_of_nonneg_left hbound
    (quittingLiteralRootStackOpponentSurvival_nonneg roots who)

/-- Joint survival is bounded by every player-deleted survival factor. -/
theorem quittingLiteralRootStackJointSurvival_le_opponentSurvival
    (roots : List (ι → PMF Bool)) (who : ι) :
    quittingLiteralRootStackJointSurvival roots ≤
      quittingLiteralRootStackOpponentSurvival roots who := by
  rw [← quittingLiteralRootStackJointSurvival_forceContinue]
  exact quittingLiteralRootStackJointSurvival_le_forceContinue roots who

/-- When the joint survival of a sequence of words tends to one, every fixed
player-deleted survival tends to one as well. -/
theorem tendsto_quittingLiteralRootStackOpponentSurvival_one
    (roots : ℕ → List (ι → PMF Bool)) (who : ι)
    (hjoint : Tendsto
      (fun rank ↦ quittingLiteralRootStackJointSurvival (roots rank))
      atTop (nhds 1)) :
    Tendsto (fun rank ↦
      quittingLiteralRootStackOpponentSurvival (roots rank) who)
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hjoint tendsto_const_nhds
  · exact fun rank ↦
      quittingLiteralRootStackJointSurvival_le_opponentSurvival
        (roots rank) who
  · exact fun rank ↦
      quittingLiteralRootStackOpponentSurvival_le_one (roots rank) who

/-! ## One supplied causal chronology -/

/-- A minimum-law chronology built over the literal supplied profiles and
literal supplied marked dates.  Indexing the structure by those two families
prevents a hidden realizer or mark reselection.

The cutoffs and exact cap--Nash root words are new finite witnesses.  The
suffix profiles and their marks are not new witnesses. -/
structure QuittingSourceFaithfulMinimumCausalization
    (point : QuittingTerminalSemanticLawPoint ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mark : ℕ → ℕ) (lambda : ℝ) where
  cutoff : ℕ → ℕ
  roots : ℕ → List (ι → PMF Bool)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  profiles_tendsto : Tendsto (fun rank ↦
    (quittingTerminalSemanticPair reward (profiles rank),
      quittingTerminalOutcomeMass reward (profiles rank)))
    atTop (nhds point)
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum point.1 ≤
      quittingTerminalSemanticDebtSum candidate
  debt_eq_inf : quittingTerminalSemanticDebtSum point.1 =
    quittingTerminalDebtSumInf reward
  inf_pos : 0 < quittingTerminalDebtSumInf reward
  lambda_pos : 0 < lambda
  marked_mass_floor : ∀ rank,
    lambda ≤ quittingStageCoalitionMass reward
      (profiles rank) (mark rank) terminal
  roots_length : ∀ rank, (roots rank).length = rank + 1
  roots_nash : ∀ rank,
    IsQuittingCapNashRootStack reward (roots rank) (profiles rank)
  prefix_debt_tendsto : Tendsto (fun rank ↦
    quittingTerminalDebtSum reward
      (quittingLiteralRootStackProfile reward (roots rank) (profiles rank)))
    atTop (nhds (quittingTerminalDebtSumInf reward))
  continueProduct_tendsto_one : Tendsto (fun rank ↦
    quittingCapNashStackContinueProduct (roots rank)) atTop (nhds 1)
  shifted_mark_mass_eq : ∀ rank,
    quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
        (rank + 1 + mark rank) terminal =
      quittingCapNashStackContinueProduct (roots rank) *
        quittingStageCoalitionMass reward
          (profiles rank) (mark rank) terminal
  eventually_shifted_mark_mass_floor : ∀ᶠ rank in atTop,
    lambda / 2 ≤ quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
      (rank + 1 + mark rank) terminal
  causal : ∀ᶠ rank in atTop,
    point.2 (some terminal) / 2 <
        ∑ time ∈ Finset.range (cutoff rank),
          quittingStageCoalitionMass reward (profiles rank) time terminal ∧
      mark rank < cutoff rank ∧
      0 < quittingStageCoalitionMass reward
        (profiles rank) (mark rank) terminal ∧
      0 < quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
        (rank + 1 + mark rank) terminal

namespace QuittingSourceFaithfulMinimumCausalization

/-- Exact total-debt scaling for each public source-faithful prefix. -/
theorem prefix_debt_eq_continueProduct_mul
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda) (rank : ℕ) :
    quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward
          (causal.roots rank) (profiles rank)) =
      quittingCapNashStackContinueProduct (causal.roots rank) *
        quittingTerminalDebtSum reward (profiles rank) :=
  quittingTerminalDebtSum_capNashRootStack_eq
    (causal.roots rank) (profiles rank) (causal.roots_nash rank)

/-- The limiting law coordinate of the retained terminal is bounded below by
the same supplied literal stage-mass floor. -/
theorem lambda_le_terminalMass
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda) :
    lambda ≤ point.2 (some terminal) := by
  have hmass : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (profiles rank) (some terminal))
      atTop (nhds (point.2 (some terminal))) :=
    ((continuous_apply (some terminal)).comp continuous_snd).tendsto point |>.comp
      causal.profiles_tendsto
  apply ge_of_tendsto hmass
  exact Eventually.of_forall fun rank ↦
    (causal.marked_mass_floor rank).trans
      (quittingStageCoalitionMass_le_terminalOutcomeMass
        reward (profiles rank) (mark rank) terminal)

/-- The retained limiting terminal-law coordinate is strictly positive. -/
theorem terminalMass_pos
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda) :
    0 < point.2 (some terminal) :=
  causal.lambda_pos.trans_le causal.lambda_le_terminalMass

/-- The player-deleted survival of the same causal word tends to one. -/
theorem opponentSurvival_tendsto_one
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda) (who : ι) :
    Tendsto (fun rank ↦
      quittingLiteralRootStackOpponentSurvival (causal.roots rank) who)
      atTop (nhds 1) := by
  apply tendsto_quittingLiteralRootStackOpponentSurvival_one
  simpa only [quittingLiteralRootStackJointSurvival,
    quittingCapNashStackContinueProduct] using
    causal.continueProduct_tendsto_one

/-- Every rank and every response-menu label retains its exact behavioral
contrast.  The label type may be finite, but finiteness is not needed for the
pointwise identity. -/
theorem responseMenu_transport
    {point : QuittingTerminalSemanticLawPoint ι}
    {terminal : {S : Finset ι // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (who : ι) {κ : Type}
    (first second : κ → ℕ → (quittingGame reward).BehaviorStrategy who) :
    ∀ label rank,
      quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward
              (causal.roots rank) (profiles rank)) who
            (quittingShiftedBehavioralResponse
              (reward := reward) (causal.roots rank) who
                (first label rank))) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward
              (causal.roots rank) (profiles rank)) who
            (quittingShiftedBehavioralResponse
              (reward := reward) (causal.roots rank) who
                (second label rank))) who =
      quittingLiteralRootStackOpponentSurvival (causal.roots rank) who *
        (quittingTerminalPayoff reward
            (Function.update (profiles rank) who (first label rank)) who -
          quittingTerminalPayoff reward
            (Function.update (profiles rank) who (second label rank)) who) := by
  intro label rank
  exact quittingTerminalPayoff_shiftedBehavioralResponse_sub_eq
    (causal.roots rank) (profiles rank) who
      (first label rank) (second label rank)

end QuittingSourceFaithfulMinimumCausalization

/-! ## Construction from supplied realizers -/

/-- A supplied minimum-law realizing sequence with one uniformly positive
literal marked atom admits arbitrarily deep exact causal prefixes while
retaining the suffix family and its marked dates. -/
theorem nonempty_sourceFaithfulMinimumCausalization
    (point : QuittingTerminalSemanticLawPoint ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mark : ℕ → ℕ) (lambda : ℝ)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hprofiles : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (profiles rank),
        quittingTerminalOutcomeMass reward (profiles rank)))
      atTop (nhds point))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdebt : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hlambda : 0 < lambda)
    (hmark : ∀ rank, lambda ≤ quittingStageCoalitionMass reward
      (profiles rank) (mark rank) terminal) :
    Nonempty (QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda) := by
  have hrootChoice : ∀ rank : ℕ,
      ∃ roots : List (ι → PMF Bool),
        roots.length = rank + 1 ∧
          IsQuittingCapNashRootStack reward roots (profiles rank) := by
    intro rank
    exact exists_quittingCapNashRootStack reward (profiles rank) (rank + 1)
  choose roots hrootsLength hrootsNash using hrootChoice
  let tailDebt : ℕ → ℝ := fun rank ↦
    quittingTerminalDebtSum reward (profiles rank)
  let prefixDebt : ℕ → ℝ := fun rank ↦
    quittingTerminalDebtSum reward
      (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
  have htailDebt : Tendsto tailDebt atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
    have hpair : Tendsto (fun rank ↦
        quittingTerminalSemanticPair reward (profiles rank))
        atTop (nhds point.1) :=
      continuous_fst.tendsto point |>.comp hprofiles
    have hsum :=
      continuous_quittingTerminalSemanticDebtSum.tendsto point.1 |>.comp hpair
    change Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (profiles rank))) atTop
        (nhds (quittingTerminalSemanticDebtSum point.1)) at hsum
    rw [hdebt] at hsum
    simpa only [tailDebt, quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
      using hsum
  have hlower : ∀ rank,
      quittingTerminalDebtSumInf reward ≤ prefixDebt rank := by
    intro rank
    exact quittingTerminalDebtSumInf_le (reward := reward)
      (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
  have hupper : ∀ rank, prefixDebt rank ≤ tailDebt rank := by
    intro rank
    have htailNonneg : 0 ≤ tailDebt rank := by
      dsimp only [tailDebt, quittingTerminalDebtSum]
      exact Finset.sum_nonneg fun who _ ↦
        quittingTerminalDeviationDebt_nonneg reward (profiles rank) who
    rw [show prefixDebt rank =
        quittingCapNashStackContinueProduct (roots rank) * tailDebt rank by
      simpa only [prefixDebt, tailDebt] using
        quittingTerminalDebtSum_capNashRootStack_eq
          (reward := reward) (roots rank) (profiles rank)
            (hrootsNash rank)]
    exact mul_le_of_le_one_left htailNonneg
      (quittingCapNashStackContinueProduct_le_one (roots rank))
  have hprefixDebt : Tendsto prefixDebt atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
    have htailGap : Tendsto (fun rank ↦
        tailDebt rank - quittingTerminalDebtSumInf reward)
        atTop (nhds 0) := by
      simpa using htailDebt.sub_const (quittingTerminalDebtSumInf reward)
    have hprefixGap : Tendsto (fun rank ↦
        prefixDebt rank - quittingTerminalDebtSumInf reward)
        atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Eventually.of_forall fun rank ↦ sub_nonneg.mpr (hlower rank)
      · exact Eventually.of_forall fun rank ↦
          sub_le_sub_right (hupper rank) _
      · exact htailGap
    have hadd := hprefixGap.add_const (quittingTerminalDebtSumInf reward)
    simpa only [sub_add_cancel, zero_add] using hadd
  have hpointPositive : 0 < quittingTerminalSemanticDebtSum point.1 := by
    rw [hdebt]
    exact hinf
  have hproduct : Tendsto (fun rank ↦
      quittingCapNashStackContinueProduct (roots rank)) atTop (nhds 1) := by
    exact tendsto_capNashStackContinueProduct_one
        reward point profiles roots hpoint hminimum hpointPositive hprofiles
          hrootsNash (by
            simpa only [prefixDebt, prefixedProfile] using hprefixDebt)
  have hmass : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (profiles rank) (some terminal))
      atTop (nhds (point.2 (some terminal))) :=
    ((continuous_apply (some terminal)).comp continuous_snd).tendsto point |>.comp
      hprofiles
  have hlawFloor : ∀ rank, lambda ≤
      quittingTerminalOutcomeMass reward (profiles rank) (some terminal) := by
    intro rank
    exact (hmark rank).trans
      (quittingStageCoalitionMass_le_terminalOutcomeMass
        reward (profiles rank) (mark rank) terminal)
  have hterminalFloor : lambda ≤ point.2 (some terminal) := by
    apply ge_of_tendsto hmass
    exact Eventually.of_forall hlawFloor
  have hterminalPositive : 0 < point.2 (some terminal) :=
    hlambda.trans_le hterminalFloor
  have hwindowEventually : ∀ᶠ rank in atTop,
      point.2 (some terminal) / 2 <
        quittingTerminalOutcomeMass reward (profiles rank) (some terminal) :=
    hmass.eventually (Ioi_mem_nhds (by linarith))
  let rawCutoff : ℕ → ℕ := fun rank ↦
    if h : point.2 (some terminal) / 2 <
        quittingTerminalOutcomeMass reward (profiles rank) (some terminal) then
      Classical.choose
        (exists_finiteWindow_sum_stageCoalitionMass_gt
          (reward := reward) (profiles rank) terminal h)
    else 0
  let cutoff : ℕ → ℕ := fun rank ↦ max (rawCutoff rank) (mark rank + 1)
  have hwindow : ∀ᶠ rank in atTop,
      point.2 (some terminal) / 2 <
          ∑ time ∈ Finset.range (cutoff rank),
            quittingStageCoalitionMass reward (profiles rank) time terminal ∧
        mark rank < cutoff rank := by
    filter_upwards [hwindowEventually] with rank hrank
    have hraw : point.2 (some terminal) / 2 <
        ∑ time ∈ Finset.range (rawCutoff rank),
          quittingStageCoalitionMass reward (profiles rank) time terminal := by
      dsimp only [rawCutoff]
      rw [dif_pos hrank]
      exact Classical.choose_spec
        (exists_finiteWindow_sum_stageCoalitionMass_gt
          (reward := reward) (profiles rank) terminal hrank)
    have hsumLe :
        (∑ time ∈ Finset.range (rawCutoff rank),
            quittingStageCoalitionMass reward (profiles rank) time terminal) ≤
          ∑ time ∈ Finset.range (cutoff rank),
            quittingStageCoalitionMass reward (profiles rank) time terminal := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (le_max_left _ _)
      · intro time htime _
        exact quittingStageCoalitionMass_nonneg
          reward (profiles rank) time terminal
    refine ⟨hraw.trans_le hsumLe, ?_⟩
    dsimp only [cutoff]
    omega
  have hshifted : ∀ rank,
      quittingStageCoalitionMass reward
          (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
          (rank + 1 + mark rank) terminal =
        quittingCapNashStackContinueProduct (roots rank) *
          quittingStageCoalitionMass reward
            (profiles rank) (mark rank) terminal := by
    intro rank
    rw [← hrootsLength rank]
    exact quittingStageCoalitionMass_literalRootStack_add_length
      reward (roots rank) (profiles rank) (mark rank) terminal
  have hproductHalf : ∀ᶠ rank in atTop,
      1 / 2 < quittingCapNashStackContinueProduct (roots rank) :=
    hproduct.eventually (Ioi_mem_nhds (by norm_num))
  have hshiftedFloor : ∀ᶠ rank in atTop,
      lambda / 2 ≤ quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
        (rank + 1 + mark rank) terminal := by
    filter_upwards [hproductHalf] with rank hrank
    rw [hshifted rank]
    have hproductNonneg :=
      quittingCapNashStackContinueProduct_nonneg (roots rank)
    calc
      lambda / 2 ≤
          quittingCapNashStackContinueProduct (roots rank) * lambda := by
        nlinarith
      _ ≤ quittingCapNashStackContinueProduct (roots rank) *
          quittingStageCoalitionMass reward
            (profiles rank) (mark rank) terminal :=
        mul_le_mul_of_nonneg_left (hmark rank) hproductNonneg
  have hcausal : ∀ᶠ rank in atTop,
      point.2 (some terminal) / 2 <
          ∑ time ∈ Finset.range (cutoff rank),
            quittingStageCoalitionMass reward (profiles rank) time terminal ∧
        mark rank < cutoff rank ∧
        0 < quittingStageCoalitionMass reward
          (profiles rank) (mark rank) terminal ∧
        0 < quittingStageCoalitionMass reward
          (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
          (rank + 1 + mark rank) terminal := by
    filter_upwards [hwindow, hshiftedFloor] with rank hwindowRank hfloor
    have hlambdaHalf : 0 < lambda / 2 := half_pos hlambda
    exact ⟨hwindowRank.1, hwindowRank.2,
      hlambda.trans_le (hmark rank), hlambdaHalf.trans_le hfloor⟩
  exact ⟨{
    cutoff := cutoff
    roots := roots
    point_mem := hpoint
    profiles_tendsto := hprofiles
    minimum := hminimum
    debt_eq_inf := hdebt
    inf_pos := hinf
    lambda_pos := hlambda
    marked_mass_floor := hmark
    roots_length := hrootsLength
    roots_nash := hrootsNash
    prefix_debt_tendsto := by simpa only [prefixDebt] using hprefixDebt
    continueProduct_tendsto_one := hproduct
    shifted_mark_mass_eq := hshifted
    eventually_shifted_mark_mass_floor := hshiftedFloor
    causal := hcausal
  }⟩

/-! ## Supplied profiles with reselected finite-window marks -/

/-- A weaker source-faithful chronology which retains the supplied profile
family but selects a positive date from a finite terminal-mass window.

Unlike `QuittingSourceFaithfulMinimumCausalization`, this structure does not
claim a uniform per-stage mass floor or equality with any incoming dates. -/
structure QuittingSourceFaithfulMinimumCausalChronology
    (point : QuittingTerminalSemanticLawPoint ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) where
  cutoff : ℕ → ℕ
  mark : ℕ → ℕ
  roots : ℕ → List (ι → PMF Bool)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  profiles_tendsto : Tendsto (fun rank ↦
    (quittingTerminalSemanticPair reward (profiles rank),
      quittingTerminalOutcomeMass reward (profiles rank)))
    atTop (nhds point)
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum point.1 ≤
      quittingTerminalSemanticDebtSum candidate
  debt_eq_inf : quittingTerminalSemanticDebtSum point.1 =
    quittingTerminalDebtSumInf reward
  inf_pos : 0 < quittingTerminalDebtSumInf reward
  terminalMass_pos : 0 < point.2 (some terminal)
  roots_length : ∀ rank, (roots rank).length = rank + 1
  roots_nash : ∀ rank,
    IsQuittingCapNashRootStack reward (roots rank) (profiles rank)
  prefix_debt_tendsto : Tendsto (fun rank ↦
    quittingTerminalDebtSum reward
      (quittingLiteralRootStackProfile reward (roots rank) (profiles rank)))
    atTop (nhds (quittingTerminalDebtSumInf reward))
  continueProduct_tendsto_one : Tendsto (fun rank ↦
    quittingCapNashStackContinueProduct (roots rank)) atTop (nhds 1)
  causal : ∀ᶠ rank in atTop,
    point.2 (some terminal) / 2 <
        ∑ time ∈ Finset.range (cutoff rank),
          quittingStageCoalitionMass reward (profiles rank) time terminal ∧
      mark rank < cutoff rank ∧
      0 < quittingStageCoalitionMass reward
        (profiles rank) (mark rank) terminal ∧
      0 < quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
        (rank + 1 + mark rank) terminal

/-- A positive terminal coordinate along one supplied minimum-law realizing
profile family admits a causal chronology without replacing that family.
The marked dates are selected from finite windows and need not equal any
incoming date family. -/
theorem nonempty_sourceFaithfulMinimumCausalChronology
    (point : QuittingTerminalSemanticLawPoint ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hprofiles : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (profiles rank),
        quittingTerminalOutcomeMass reward (profiles rank)))
      atTop (nhds point))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdebt : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hmass : 0 < point.2 (some terminal)) :
    Nonempty (QuittingSourceFaithfulMinimumCausalChronology
      point terminal profiles) := by
  have hmassTendsto : Tendsto (fun rank ↦
      quittingTerminalOutcomeMass reward (profiles rank) (some terminal))
      atTop (nhds (point.2 (some terminal))) :=
    ((continuous_apply (some terminal)).comp continuous_snd).tendsto point |>.comp
      hprofiles
  have hpersistent : ∀ᶠ rank in atTop,
      point.2 (some terminal) / 2 <
        quittingTerminalOutcomeMass reward (profiles rank) (some terminal) :=
    hmassTendsto.eventually (Ioi_mem_nhds (by linarith))
  let cutoff : ℕ → ℕ := fun rank ↦
    if h : point.2 (some terminal) / 2 <
        quittingTerminalOutcomeMass reward (profiles rank) (some terminal) then
      Classical.choose
        (exists_finiteWindow_sum_stageCoalitionMass_gt
          (reward := reward) (profiles rank) terminal h)
    else 0
  have hwindow : ∀ᶠ rank in atTop,
      point.2 (some terminal) / 2 <
        ∑ time ∈ Finset.range (cutoff rank),
          quittingStageCoalitionMass reward (profiles rank) time terminal := by
    filter_upwards [hpersistent] with rank hrank
    dsimp only [cutoff]
    rw [dif_pos hrank]
    exact Classical.choose_spec
      (exists_finiteWindow_sum_stageCoalitionMass_gt
        (reward := reward) (profiles rank) terminal hrank)
  let mark : ℕ → ℕ := fun rank ↦
    if h : ∃ time < cutoff rank,
        0 < quittingStageCoalitionMass reward
          (profiles rank) time terminal then
      Classical.choose h
    else 0
  have hmark : ∀ᶠ rank in atTop,
      point.2 (some terminal) / 2 <
          ∑ time ∈ Finset.range (cutoff rank),
            quittingStageCoalitionMass reward (profiles rank) time terminal ∧
        mark rank < cutoff rank ∧
        0 < quittingStageCoalitionMass reward
          (profiles rank) (mark rank) terminal := by
    filter_upwards [hwindow] with rank hrank
    have hsumPos : 0 < ∑ time ∈ Finset.range (cutoff rank),
        quittingStageCoalitionMass reward
          (profiles rank) time terminal := by
      linarith
    have hnonneg : ∀ time ∈ Finset.range (cutoff rank),
        0 ≤ quittingStageCoalitionMass reward
          (profiles rank) time terminal := by
      intro time _
      exact quittingStageCoalitionMass_nonneg
        reward (profiles rank) time terminal
    obtain ⟨time, htime, htimePos⟩ :=
      (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsumPos
    have hexists : ∃ time < cutoff rank,
        0 < quittingStageCoalitionMass reward
          (profiles rank) time terminal :=
      ⟨time, Finset.mem_range.mp htime, htimePos⟩
    dsimp only [mark]
    rw [dif_pos hexists]
    exact ⟨hrank, (Classical.choose_spec hexists).1,
      (Classical.choose_spec hexists).2⟩
  have hrootChoice : ∀ rank : ℕ,
      ∃ roots : List (ι → PMF Bool),
        roots.length = rank + 1 ∧
          IsQuittingCapNashRootStack reward roots (profiles rank) := by
    intro rank
    exact exists_quittingCapNashRootStack reward (profiles rank) (rank + 1)
  choose roots hrootsLength hrootsNash using hrootChoice
  let tailDebt : ℕ → ℝ := fun rank ↦
    quittingTerminalDebtSum reward (profiles rank)
  let prefixDebt : ℕ → ℝ := fun rank ↦
    quittingTerminalDebtSum reward
      (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
  have htailDebt : Tendsto tailDebt atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
    have hpair : Tendsto (fun rank ↦
        quittingTerminalSemanticPair reward (profiles rank))
        atTop (nhds point.1) :=
      continuous_fst.tendsto point |>.comp hprofiles
    have hsum :=
      continuous_quittingTerminalSemanticDebtSum.tendsto point.1 |>.comp hpair
    change Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (profiles rank))) atTop
        (nhds (quittingTerminalSemanticDebtSum point.1)) at hsum
    rw [hdebt] at hsum
    simpa only [tailDebt, quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
      using hsum
  have hlower : ∀ rank,
      quittingTerminalDebtSumInf reward ≤ prefixDebt rank := by
    intro rank
    exact quittingTerminalDebtSumInf_le (reward := reward)
      (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
  have hupper : ∀ rank, prefixDebt rank ≤ tailDebt rank := by
    intro rank
    have htailNonneg : 0 ≤ tailDebt rank := by
      dsimp only [tailDebt, quittingTerminalDebtSum]
      exact Finset.sum_nonneg fun who _ ↦
        quittingTerminalDeviationDebt_nonneg reward (profiles rank) who
    rw [show prefixDebt rank =
        quittingCapNashStackContinueProduct (roots rank) * tailDebt rank by
      simpa only [prefixDebt, tailDebt] using
        quittingTerminalDebtSum_capNashRootStack_eq
          (reward := reward) (roots rank) (profiles rank)
            (hrootsNash rank)]
    exact mul_le_of_le_one_left htailNonneg
      (quittingCapNashStackContinueProduct_le_one (roots rank))
  have hprefixDebt : Tendsto prefixDebt atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
    have htailGap : Tendsto (fun rank ↦
        tailDebt rank - quittingTerminalDebtSumInf reward)
        atTop (nhds 0) := by
      simpa using htailDebt.sub_const (quittingTerminalDebtSumInf reward)
    have hprefixGap : Tendsto (fun rank ↦
        prefixDebt rank - quittingTerminalDebtSumInf reward)
        atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Eventually.of_forall fun rank ↦ sub_nonneg.mpr (hlower rank)
      · exact Eventually.of_forall fun rank ↦
          sub_le_sub_right (hupper rank) _
      · exact htailGap
    have hadd := hprefixGap.add_const (quittingTerminalDebtSumInf reward)
    simpa only [sub_add_cancel, zero_add] using hadd
  have hproduct : Tendsto (fun rank ↦
      quittingCapNashStackContinueProduct (roots rank)) atTop (nhds 1) := by
    have hpointPositive : 0 <
        quittingTerminalSemanticDebtSum point.1 := by
      rw [hdebt]
      exact hinf
    exact tendsto_capNashStackContinueProduct_one
      reward point profiles roots hpoint hminimum hpointPositive hprofiles
        hrootsNash (by
          simpa only [prefixDebt, prefixedProfile] using hprefixDebt)
  have hshifted : ∀ᶠ rank in atTop,
      0 < quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward (roots rank) (profiles rank))
        (rank + 1 + mark rank) terminal := by
    filter_upwards [hmark] with rank hrank
    rw [← hrootsLength rank,
      quittingStageCoalitionMass_literalRootStack_add_length]
    have htailDebtPos : 0 < quittingTerminalDebtSum reward (profiles rank) :=
      hinf.trans_le
        (quittingTerminalDebtSumInf_le (reward := reward) (profiles rank))
    have hproductLower := capNashStack_continueProduct_lowerBound
      (reward := reward) (roots rank) (profiles rank) hinf (hrootsNash rank)
    have hproductPos : 0 <
        quittingCapNashStackContinueProduct (roots rank) :=
      (div_pos hinf htailDebtPos).trans_le hproductLower
    exact mul_pos hproductPos hrank.2.2
  refine ⟨{
    cutoff := cutoff
    mark := mark
    roots := roots
    point_mem := hpoint
    profiles_tendsto := hprofiles
    minimum := hminimum
    debt_eq_inf := hdebt
    inf_pos := hinf
    terminalMass_pos := hmass
    roots_length := hrootsLength
    roots_nash := hrootsNash
    prefix_debt_tendsto := by simpa only [prefixDebt] using hprefixDebt
    continueProduct_tendsto_one := hproduct
    causal := ?_
  }⟩
  filter_upwards [hmark, hshifted] with rank hrank hshift
  exact ⟨hrank.1, hrank.2.1, hrank.2.2, hshift⟩

end GameTheory
