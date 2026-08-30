/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration
import UniformEquilibrium.Quitting.RewardBound

/-!
# Terminal-law erasure under the Never deviation

Replacing one player by the strategy which always Continues deletes that
player from every opponent stopping coalition.  This file records the exact
terminal-law moment exposed by that deviation and charges every path on which
the displayed sure opponent is not present to one explicit failure mass.

The estimate is for arbitrary behavioral profiles.  It does not replace the
full behavioral envelope by a stationary cap.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite terminal coalitions carrying one displayed anchor. -/
abbrev QuittingTerminalWithAnchor (anchor : ι) :=
  {terminal : {S : Finset ι // S.Nonempty} // anchor ∈ terminal.val}

/-- Terminal coalitions carrying `anchor` after `mover` has been erased. -/
abbrev QuittingTerminalErasureBase (mover anchor : ι) :=
  {terminal : {S : Finset ι // S.Nonempty} //
    anchor ∈ terminal.val ∧ mover ∉ terminal.val}

/-- A coalition carrying `anchor` is uniquely a mover-free coalition together
with the Boolean recording whether the mover belonged to the original one. -/
def quittingTerminalWithAnchorEquivErasurePair
    (mover anchor : ι) (hne : mover ≠ anchor) :
    QuittingTerminalWithAnchor anchor ≃
      Bool × QuittingTerminalErasureBase mover anchor where
  toFun terminal :=
    (decide (mover ∈ terminal.1.val),
      ⟨⟨terminal.1.val.erase mover,
          ⟨anchor, Finset.mem_erase.mpr ⟨hne.symm, terminal.2⟩⟩⟩,
        Finset.mem_erase.mpr ⟨hne.symm, terminal.2⟩,
        Finset.notMem_erase mover terminal.1.val⟩)
  invFun pair :=
    if pair.1 then
      ⟨quittingInsertTerminal mover pair.2.1, by
        simp [quittingInsertTerminal, pair.2.2.1]⟩
    else
      ⟨pair.2.1, pair.2.2.1⟩
  left_inv terminal := by
    apply Subtype.ext
    by_cases hmover : mover ∈ terminal.1.val
    · simp [hmover, quittingInsertTerminal, Finset.insert_erase]
    · simp [hmover, Finset.erase_eq_of_notMem]
  right_inv pair := by
    rcases pair with ⟨quit, terminal⟩
    cases quit <;> apply Prod.ext
    · simp [terminal.2.2]
    · apply Subtype.ext
      simp [terminal.2.2, Finset.erase_eq_of_notMem]
    · simp [quittingInsertTerminal]
    · apply Subtype.ext
      simp [quittingInsertTerminal, terminal.2.2]

/-- Complete failure mass for erasure through a displayed anchor: genuine
Never together with every finite coalition omitting the anchor. -/
def quittingTerminalErasureFailureMass
    (mass : QuittingTerminalOutcome ι → ℝ) (anchor : ι) : ℝ :=
  mass none +
    ∑ terminal ∈ Finset.univ.filter
        (fun terminal : {S : Finset ι // S.Nonempty} =>
          anchor ∉ terminal.val),
      mass (some terminal)

/-- Total finite terminal mass carried by coalitions containing `anchor`. -/
def quittingTerminalAnchorMass
    (mass : QuittingTerminalOutcome ι → ℝ) (anchor : ι) : ℝ :=
  ∑ terminal : QuittingTerminalWithAnchor anchor,
    mass (some terminal.1)

/-- The part of one terminal reward moment carried by coalitions containing
`anchor`. -/
def quittingTerminalAnchorRewardMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (who anchor : ι) : ℝ :=
  ∑ terminal : QuittingTerminalWithAnchor anchor,
    mass (some terminal.1) * reward terminal.1 who

/-- The finite payoff contribution of coalitions omitting `anchor`.
The Never atom has reward zero and is therefore not included in this sum. -/
def quittingTerminalErasureFailureRewardMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (who anchor : ι) : ℝ :=
  ∑ terminal ∈ Finset.univ.filter
      (fun terminal : {S : Finset ι // S.Nonempty} =>
        anchor ∉ terminal.val),
    mass (some terminal) * reward terminal who

/-- Reward moment obtained by deleting `mover` from every finite terminal
coalition carrying `anchor`.  The two displayed masses are exactly the two
preimages of one coalition under deletion. -/
def quittingTerminalErasureMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (mover anchor : ι) : ℝ :=
  ∑ terminal : QuittingTerminalErasureBase mover anchor,
    (mass (some terminal.1) +
        mass (some (quittingInsertTerminal mover terminal.1))) *
      reward terminal.1 mover

/-- The complete failure charge is a continuous coordinate functional of a
finite terminal law. -/
theorem continuous_quittingTerminalErasureFailureMass (anchor : ι) :
    Continuous (fun mass : QuittingTerminalOutcome ι → ℝ =>
      quittingTerminalErasureFailureMass mass anchor) := by
  unfold quittingTerminalErasureFailureMass
  fun_prop

/-- The erasure reward moment is a continuous finite linear functional of a
terminal law. -/
theorem continuous_quittingTerminalErasureMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mover anchor : ι) :
    Continuous (fun mass : QuittingTerminalOutcome ι → ℝ =>
      quittingTerminalErasureMoment reward mass mover anchor) := by
  unfold quittingTerminalErasureMoment
  fun_prop

/-- Reindex anchor-carrying coalitions by their mover-free image and the
Boolean recording mover membership. -/
theorem quittingTerminalAnchorMass_eq_sum_erasurePairs
    (mass : QuittingTerminalOutcome ι → ℝ)
    (mover anchor : ι) (hne : mover ≠ anchor) :
    quittingTerminalAnchorMass mass anchor =
      ∑ terminal : QuittingTerminalErasureBase mover anchor,
        (mass (some terminal.1) +
          mass (some (quittingInsertTerminal mover terminal.1))) := by
  let equivalence :=
    quittingTerminalWithAnchorEquivErasurePair mover anchor hne
  have hreindex := (equivalence.symm.sum_comp
    fun terminal : QuittingTerminalWithAnchor anchor =>
      mass (some terminal.1)).symm
  rw [quittingTerminalAnchorMass, hreindex, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro terminal _
  simp [equivalence, quittingTerminalWithAnchorEquivErasurePair]
  ring

/-- Anchor mass and its full explicit failure mass partition one complete
terminal law. -/
theorem quittingTerminalAnchorMass_add_failureMass
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (anchor : ι) :
    quittingTerminalAnchorMass mass anchor +
        quittingTerminalErasureFailureMass mass anchor = 1 := by
  have hanchor : quittingTerminalAnchorMass mass anchor =
      ∑ terminal ∈ Finset.univ.filter
          (fun terminal : {S : Finset ι // S.Nonempty} =>
            anchor ∈ terminal.val),
        mass (some terminal) := by
    unfold quittingTerminalAnchorMass
    symm
    exact Finset.sum_subtype _ (by simp) _
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset {S : Finset ι // S.Nonempty})
    (fun terminal => anchor ∈ terminal.val)
    (fun terminal => mass (some terminal))
  rw [hanchor, quittingTerminalErasureFailureMass]
  calc
    (∑ terminal ∈ Finset.univ.filter
          (fun terminal : {S : Finset ι // S.Nonempty} =>
            anchor ∈ terminal.val),
        mass (some terminal)) +
        (mass none +
          ∑ terminal ∈ Finset.univ.filter
              (fun terminal : {S : Finset ι // S.Nonempty} =>
                anchor ∉ terminal.val),
            mass (some terminal)) =
      mass none + ∑ terminal, mass (some terminal) := by
        rw [← hsplit]
        ring
    _ = ∑ outcome, mass outcome := by
      rw [Fintype.sum_option]
    _ = 1 := hmass.2

/-- The full terminal reward moment splits into the anchor-supported moment
and the finite failure contribution. -/
theorem quittingTerminalRewardMoment_eq_anchor_add_failure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (who anchor : ι) :
    quittingTerminalRewardMoment reward mass who =
      quittingTerminalAnchorRewardMoment reward mass who anchor +
        quittingTerminalErasureFailureRewardMoment reward mass who anchor := by
  have hanchor : quittingTerminalAnchorRewardMoment reward mass who anchor =
      ∑ terminal ∈ Finset.univ.filter
          (fun terminal : {S : Finset ι // S.Nonempty} =>
            anchor ∈ terminal.val),
        mass (some terminal) * reward terminal who := by
    unfold quittingTerminalAnchorRewardMoment
    symm
    exact Finset.sum_subtype _ (by simp) _
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset {S : Finset ι // S.Nonempty})
    (fun terminal => anchor ∈ terminal.val)
    (fun terminal => mass (some terminal) * reward terminal who)
  rw [quittingTerminalRewardMoment, Fintype.sum_option]
  simp only [quittingTerminalOutcomeReward]
  rw [hanchor, quittingTerminalErasureFailureRewardMoment, hsplit]
  simp

/-- Failure rewards are bounded below by the full explicit failure mass,
including the zero-reward Never atom. -/
theorem neg_mul_terminalErasureFailureMass_le_failureRewardMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (who anchor : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    -M * quittingTerminalErasureFailureMass mass anchor ≤
      quittingTerminalErasureFailureRewardMoment reward mass who anchor := by
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  let failures := Finset.univ.filter
    (fun terminal : {S : Finset ι // S.Nonempty} =>
      anchor ∉ terminal.val)
  have hfinite :
      -M * (∑ terminal ∈ failures, mass (some terminal)) ≤
        ∑ terminal ∈ failures,
          mass (some terminal) * reward terminal who := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro terminal hterminal
    have hmassNonneg := hmass.1 (some terminal)
    have hrewardLower : -M ≤ reward terminal who :=
      neg_le_of_abs_le (hreward terminal who)
    nlinarith
  have hneverNonneg := hmass.1 none
  calc
    -M * quittingTerminalErasureFailureMass mass anchor ≤
        -M * (∑ terminal ∈ failures, mass (some terminal)) := by
      unfold quittingTerminalErasureFailureMass
      dsimp only [failures]
      nlinarith
    _ ≤ quittingTerminalErasureFailureRewardMoment reward mass who anchor := by
      simpa [quittingTerminalErasureFailureRewardMoment, failures] using hfinite

/-- Deleting one player's action can only add mass to each opponent stopping
coalition.  The source pair consists of the coalition without the player and
the same coalition with that player inserted. -/
theorem quittingTerminalOutcomeMass_pair_le_update_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (terminal : {S : Finset ι // S.Nonempty})
    (hmover : mover ∉ terminal.val) :
    quittingTerminalOutcomeMass reward profile (some terminal) +
        quittingTerminalOutcomeMass reward profile
          (some (quittingInsertTerminal mover terminal)) ≤
      quittingTerminalOutcomeMass reward
        (Function.update profile mover
          (quittingPureTimeBehaviorStrategy reward mover none))
        (some terminal) := by
  change quittingAbsorbedMassLimit reward profile terminal +
      quittingAbsorbedMassLimit reward profile
        (quittingInsertTerminal mover terminal) ≤
    quittingAbsorbedMassLimit reward
      (Function.update profile mover
        (quittingPureTimeBehaviorStrategy reward mover none)) terminal
  have hfirstSummable :=
    (hasSum_quittingStageCoalitionMass reward profile terminal).summable
  have hsecondSummable :=
    (hasSum_quittingStageCoalitionMass reward profile
      (quittingInsertTerminal mover terminal)).summable
  rw [← tsum_quittingStageCoalitionMass reward profile terminal,
    ← tsum_quittingStageCoalitionMass reward profile
      (quittingInsertTerminal mover terminal),
    ← tsum_quittingStageCoalitionMass reward
      (Function.update profile mover
        (quittingPureTimeBehaviorStrategy reward mover none)) terminal,
    ← hfirstSummable.tsum_add hsecondSummable]
  apply Summable.tsum_le_tsum
  · intro time
    have hpair := opponentFactor_mul_survival_eq_stageMass_add_insertStageMass
      reward profile mover (profile mover) time terminal hmover
    have hdeleted := quittingStageCoalitionMass_update_eq_opponentFactor_mul
      reward profile mover
        (quittingPureTimeBehaviorStrategy reward mover none) time terminal
    simp only [Function.update_eq_self] at hpair
    rw [← hpair]
    rw [hdeleted]
    simp only [hmover, if_false,
      quittingBehaviorLiveHazard_pureTimeBehaviorStrategy]
    have hfactor := quittingStageCoalitionOpponentFactor_nonneg
      (quittingProfileLiveRoot reward profile) mover time terminal
    have hsurvival := quittingHazardSurvival_le_one
      (quittingBehaviorLiveHazard reward (profile mover)) time
    have hnever : quittingHazardSurvival (quittingPureTimeHazard none)
        (time + 1) = 1 := by
      simp [quittingHazardSurvival, Math.survivalProduct,
        quittingPureTimeHazard_none]
    rw [hnever]
    simpa using
      (mul_le_mul_of_nonneg_left hsurvival hfactor)
  · exact
      hfirstSummable.add hsecondSummable
  · exact (hasSum_quittingStageCoalitionMass reward
      (Function.update profile mover
        (quittingPureTimeBehaviorStrategy reward mover none)) terminal).summable

/-- After the Never deviation, anchor mass is exactly the sum over
mover-free anchor coalitions. -/
theorem quittingTerminalAnchorMass_update_never_eq_sum_erasureBases
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover anchor : ι) (hne : mover ≠ anchor) :
    quittingTerminalAnchorMass
        (quittingTerminalOutcomeMass reward
          (Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover none))) anchor =
      ∑ terminal : QuittingTerminalErasureBase mover anchor,
        quittingTerminalOutcomeMass reward
          (Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover none))
          (some terminal.1) := by
  rw [quittingTerminalAnchorMass_eq_sum_erasurePairs _ mover anchor hne]
  apply Finset.sum_congr rfl
  intro terminal _
  have hzero := quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
    reward profile mover (quittingInsertTerminal mover terminal.1) (by
      simp [quittingInsertTerminal])
  rw [hzero, add_zero]

/-- The anchor-supported reward moment of the Never deviation is likewise a
sum over mover-free anchor coalitions. -/
theorem quittingTerminalAnchorRewardMoment_update_never_eq_sum_erasureBases
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover anchor : ι) (hne : mover ≠ anchor) :
    quittingTerminalAnchorRewardMoment reward
        (quittingTerminalOutcomeMass reward
          (Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover none)))
        mover anchor =
      ∑ terminal : QuittingTerminalErasureBase mover anchor,
        quittingTerminalOutcomeMass reward
          (Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover none))
          (some terminal.1) * reward terminal.1 mover := by
  let equivalence :=
    quittingTerminalWithAnchorEquivErasurePair mover anchor hne
  have hreindex := (equivalence.symm.sum_comp
    fun terminal : QuittingTerminalWithAnchor anchor =>
      quittingTerminalOutcomeMass reward
          (Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover none))
          (some terminal.1) * reward terminal.1 mover).symm
  rw [quittingTerminalAnchorRewardMoment, hreindex,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hinsert : ∀ terminal : QuittingTerminalErasureBase mover anchor,
      quittingTerminalOutcomeMass reward
          (Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover none))
          (some (quittingInsertTerminal mover terminal.1)) = 0 := by
    intro terminal
    exact quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
      reward profile mover (quittingInsertTerminal mover terminal.1) (by
        simp [quittingInsertTerminal])
  simp [equivalence, quittingTerminalWithAnchorEquivErasurePair,
    hinsert]

/-- Signed erasure moment bound on one actual profile.  The loss term is
exactly the extra anchor mass created by deleting the mover. -/
theorem quittingTerminalErasureMoment_le_update_never_anchorMoment_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover anchor : ι) (hne : mover ≠ anchor) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalErasureMoment reward
        (quittingTerminalOutcomeMass reward profile) mover anchor ≤
      quittingTerminalAnchorRewardMoment reward
          (quittingTerminalOutcomeMass reward
            (Function.update profile mover
              (quittingPureTimeBehaviorStrategy reward mover none)))
          mover anchor +
        M * (quittingTerminalAnchorMass
            (quittingTerminalOutcomeMass reward
              (Function.update profile mover
                (quittingPureTimeBehaviorStrategy reward mover none))) anchor -
          quittingTerminalAnchorMass
            (quittingTerminalOutcomeMass reward profile) anchor) := by
  rw [quittingTerminalErasureMoment,
    quittingTerminalAnchorRewardMoment_update_never_eq_sum_erasureBases
      reward profile mover anchor hne,
    quittingTerminalAnchorMass_update_never_eq_sum_erasureBases
      reward profile mover anchor hne,
    quittingTerminalAnchorMass_eq_sum_erasurePairs
      (quittingTerminalOutcomeMass reward profile) mover anchor hne,
    mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro terminal _
  have hmass := quittingTerminalOutcomeMass_pair_le_update_never
    reward profile mover terminal.1 terminal.2.2
  have hrewardLower : -M ≤ reward terminal.1 mover :=
    neg_le_of_abs_le (hreward terminal.1 mover)
  nlinarith

/-- **Actual-profile erasure deviation estimate.**

The legal Never deviation realizes the displayed erasure moment up to exactly
one reward bound times the full failure mass: genuine Never plus all finite
coalitions omitting the anchor. -/
theorem quittingTerminalErasureMoment_sub_failure_le_update_never_payoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover anchor : ι) (hne : mover ≠ anchor) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalErasureMoment reward
          (quittingTerminalOutcomeMass reward profile) mover anchor -
        M * quittingTerminalErasureFailureMass
          (quittingTerminalOutcomeMass reward profile) anchor ≤
      quittingTerminalPayoff reward
        (Function.update profile mover
          (quittingPureTimeBehaviorStrategy reward mover none)) mover := by
  let deleted := Function.update profile mover
    (quittingPureTimeBehaviorStrategy reward mover none)
  let sourceMass := quittingTerminalOutcomeMass reward profile
  let deletedMass := quittingTerminalOutcomeMass reward deleted
  have hsourceSimplex : sourceMass ∈
      stdSimplex ℝ (QuittingTerminalOutcome ι) := by
    exact quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hdeletedSimplex : deletedMass ∈
      stdSimplex ℝ (QuittingTerminalOutcome ι) := by
    exact quittingTerminalOutcomeMass_mem_stdSimplex reward deleted
  have herasure :=
    quittingTerminalErasureMoment_le_update_never_anchorMoment_add
      reward profile mover anchor hne hreward
  have hfailure :=
    neg_mul_terminalErasureFailureMass_le_failureRewardMoment
      reward deletedMass hdeletedSimplex mover anchor hreward
  have hsourcePartition :=
    quittingTerminalAnchorMass_add_failureMass sourceMass
      hsourceSimplex anchor
  have hdeletedPartition :=
    quittingTerminalAnchorMass_add_failureMass deletedMass
      hdeletedSimplex anchor
  have haccount :
      M * (quittingTerminalAnchorMass deletedMass anchor -
          quittingTerminalAnchorMass sourceMass anchor) +
        M * quittingTerminalErasureFailureMass deletedMass anchor =
      M * quittingTerminalErasureFailureMass sourceMass anchor := by
    rw [show quittingTerminalErasureFailureMass deletedMass anchor =
        1 - quittingTerminalAnchorMass deletedMass anchor by linarith,
      show quittingTerminalErasureFailureMass sourceMass anchor =
        1 - quittingTerminalAnchorMass sourceMass anchor by linarith]
    ring
  have hpayoff : quittingTerminalPayoff reward deleted mover =
      quittingTerminalAnchorRewardMoment reward deletedMass mover anchor +
        quittingTerminalErasureFailureRewardMoment
          reward deletedMass mover anchor := by
    rw [← quittingTerminalRewardMoment_outcomeMass reward deleted]
    exact quittingTerminalRewardMoment_eq_anchor_add_failure
      reward deletedMass mover anchor
  dsimp only [deletedMass, sourceMass, deleted] at herasure hfailure haccount
  rw [hpayoff]
  nlinarith

/-- If the source law is entirely carried by coalitions containing the
anchor, deleting the mover transports every paired coalition coordinate
exactly.  Hence the erasure moment is the literal payoff of the Never
deviation, not merely a lower bound for it. -/
theorem quittingTerminalErasureMoment_eq_update_never_payoff_of_failure_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover anchor : ι) (hne : mover ≠ anchor)
    (hfailure : quittingTerminalErasureFailureMass
      (quittingTerminalOutcomeMass reward profile) anchor = 0) :
    quittingTerminalErasureMoment reward
        (quittingTerminalOutcomeMass reward profile) mover anchor =
      quittingTerminalPayoff reward
        (Function.update profile mover
          (quittingPureTimeBehaviorStrategy reward mover none)) mover := by
  let deleted := Function.update profile mover
    (quittingPureTimeBehaviorStrategy reward mover none)
  let sourceMass := quittingTerminalOutcomeMass reward profile
  let deletedMass := quittingTerminalOutcomeMass reward deleted
  let paired : QuittingTerminalErasureBase mover anchor → ℝ :=
    fun terminal => sourceMass (some terminal.1) +
      sourceMass (some (quittingInsertTerminal mover terminal.1))
  let deletedAt : QuittingTerminalErasureBase mover anchor → ℝ :=
    fun terminal => deletedMass (some terminal.1)
  have hsourceSimplex : sourceMass ∈
      stdSimplex ℝ (QuittingTerminalOutcome ι) :=
    quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hdeletedSimplex : deletedMass ∈
      stdSimplex ℝ (QuittingTerminalOutcome ι) :=
    quittingTerminalOutcomeMass_mem_stdSimplex reward deleted
  have hpair : ∀ terminal, paired terminal ≤ deletedAt terminal := by
    intro terminal
    exact quittingTerminalOutcomeMass_pair_le_update_never
      reward profile mover terminal.1 terminal.2.2
  have hsourcePartition := quittingTerminalAnchorMass_add_failureMass
    sourceMass hsourceSimplex anchor
  have hsourceAnchor : quittingTerminalAnchorMass sourceMass anchor = 1 := by
    linarith
  have hdeletedPartition := quittingTerminalAnchorMass_add_failureMass
    deletedMass hdeletedSimplex anchor
  have hdeletedFailureNonneg :
      0 ≤ quittingTerminalErasureFailureMass deletedMass anchor := by
    unfold quittingTerminalErasureFailureMass
    exact add_nonneg (hdeletedSimplex.1 none)
      (Finset.sum_nonneg fun terminal _ =>
        hdeletedSimplex.1 (some terminal))
  have hsourceSum : ∑ terminal, paired terminal = 1 := by
    rw [← hsourceAnchor,
      quittingTerminalAnchorMass_eq_sum_erasurePairs
        sourceMass mover anchor hne]
  have hdeletedSumLe : ∑ terminal, deletedAt terminal ≤ 1 := by
    rw [← quittingTerminalAnchorMass_update_never_eq_sum_erasureBases
      reward profile mover anchor hne]
    linarith
  have hsumLe : ∑ terminal, paired terminal ≤
      ∑ terminal, deletedAt terminal :=
    Finset.sum_le_sum fun terminal _ => hpair terminal
  have hsumEq : ∑ terminal, paired terminal =
      ∑ terminal, deletedAt terminal := by
    apply le_antisymm hsumLe
    rw [hsourceSum]
    exact hdeletedSumLe
  have hcoordinate : ∀ terminal, paired terminal = deletedAt terminal := by
    intro terminal
    exact (Finset.sum_eq_sum_iff_of_le
      (fun candidate _ => hpair candidate)).mp hsumEq terminal
        (Finset.mem_univ terminal)
  have hdeletedAnchor : quittingTerminalAnchorMass deletedMass anchor = 1 := by
    rw [quittingTerminalAnchorMass_update_never_eq_sum_erasureBases
      reward profile mover anchor hne]
    exact hsumEq.symm.trans hsourceSum
  have hdeletedFailure :
      quittingTerminalErasureFailureMass deletedMass anchor = 0 := by
    linarith
  have hfilteredNonneg : 0 ≤
      ∑ terminal ∈ Finset.univ.filter
          (fun terminal : {S : Finset ι // S.Nonempty} =>
            anchor ∉ terminal.val),
        deletedMass (some terminal) :=
    Finset.sum_nonneg fun terminal _ => hdeletedSimplex.1 (some terminal)
  have hfilteredZero :
      ∑ terminal ∈ Finset.univ.filter
          (fun terminal : {S : Finset ι // S.Nonempty} =>
            anchor ∉ terminal.val),
        deletedMass (some terminal) = 0 := by
    unfold quittingTerminalErasureFailureMass at hdeletedFailure
    nlinarith [hdeletedSimplex.1 none]
  have homit : ∀ terminal : {S : Finset ι // S.Nonempty},
      anchor ∉ terminal.val → deletedMass (some terminal) = 0 := by
    intro terminal hterminal
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun candidate _ => hdeletedSimplex.1 (some candidate))).mp
        hfilteredZero terminal (Finset.mem_filter.mpr
          ⟨Finset.mem_univ terminal, hterminal⟩)
  have hfailureReward :
      quittingTerminalErasureFailureRewardMoment
        reward deletedMass mover anchor = 0 := by
    unfold quittingTerminalErasureFailureRewardMoment
    apply Finset.sum_eq_zero
    intro terminal hterminal
    rw [homit terminal (Finset.mem_filter.mp hterminal).2, zero_mul]
  have hanchorMoment :
      quittingTerminalErasureMoment reward sourceMass mover anchor =
        quittingTerminalAnchorRewardMoment reward deletedMass mover anchor := by
    rw [quittingTerminalErasureMoment,
      quittingTerminalAnchorRewardMoment_update_never_eq_sum_erasureBases
        reward profile mover anchor hne]
    apply Finset.sum_congr rfl
    intro terminal _
    exact congrArg (fun value => value * reward terminal.1 mover)
      (hcoordinate terminal)
  rw [hanchorMoment]
  have hrewardMoment :
      quittingTerminalRewardMoment reward deletedMass mover =
        quittingTerminalAnchorRewardMoment reward deletedMass mover anchor := by
    rw [quittingTerminalRewardMoment_eq_anchor_add_failure,
      hfailureReward, add_zero]
  rw [← hrewardMoment]
  exact congrFun (quittingTerminalRewardMoment_outcomeMass reward deleted) mover

/-- The unrestricted behavioral envelope dominates the erasure moment with
the same sharp failure charge. -/
theorem quittingTerminalErasureMoment_sub_failure_le_envelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover anchor : ι) (hne : mover ≠ anchor) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalErasureMoment reward
          (quittingTerminalOutcomeMass reward profile) mover anchor -
        M * quittingTerminalErasureFailureMass
          (quittingTerminalOutcomeMass reward profile) anchor ≤
      quittingContinuationBestResponseValue reward profile mover := by
  exact (quittingTerminalErasureMoment_sub_failure_le_update_never_payoff
    reward profile mover anchor hne hreward).trans
      (quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile mover
          (quittingPureTimeBehaviorStrategy reward mover none))

end GameTheory
