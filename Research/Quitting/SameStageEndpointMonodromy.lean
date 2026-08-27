/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiveWeightedCollisionTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveMinimumUnitResetCycle
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction
import MathUE.FiniteBooleanEndpointOrbit

/-!
# Literal same-stage endpoint profiles

This Research module supplies the profile-level bridge needed before any
finite same-stage endpoint iteration can be stated.  The checked collision
transfer uses `quittingStagePureEndpointBehaviorDeviation`, which canonicalizes
off-path behavior.  Here we also expose a literal one-date override: it keeps
the complete source strategy at every date except the selected date.

The module includes a conditional finite dispatch/iteration interface.  It
does not assert a chronology upgrade, a residual contraction, or a uniform
equilibrium consumer.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal replacement of one behavior strategy at one date. -/
def quittingLiteralOneDateOverride
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (stage : ℕ) (action : Bool) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time history => if time = stage then PMF.pure action else strategy time history

/-- A profile obtained by applying a literal pure override to one player. -/
def quittingLiteralOneDateProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile who
    (quittingLiteralOneDateOverride (profile who) stage action)

/-- A profile whose stage root is a supplied pure Boolean root. -/
def quittingLiteralPureRootProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (root : ι → Bool) :
    (quittingGame reward).BehaviorProfile :=
  fun who => quittingLiteralOneDateOverride (profile who) stage (root who)

abbrev QuittingNonsingletonCoalition (ι : Type) [DecidableEq ι] :=
  MathUE.FiniteBooleanEndpointOrbit.NonsingletonCoalition ι

def quittingPureRootOfCoalition
    (coalition : Finset ι) : ι → Bool :=
  quittingCoalitionAction coalition

def quittingLiteralPureRootCoalitionProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (coalition : QuittingNonsingletonCoalition ι) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralPureRootProfile reward profile stage
    (quittingPureRootOfCoalition coalition.1)

def quittingNonsingletonCoalitionRouted
    (coalition : QuittingNonsingletonCoalition ι)
    (who : ι) (action : Bool) : Finset ι :=
  quittingPureEndpointRoutedCoalition coalition.1 who action

def quittingTerminalOfNonsingletonCoalition
    (coalition : QuittingNonsingletonCoalition ι) :
    {S : Finset ι // S.Nonempty} :=
  ⟨coalition.1, coalition.nonempty⟩

omit [Fintype ι] in
/-- A one-coordinate route from a nonsingleton coalition can be a singleton
only by making one member Continue from a two-player source. -/
theorem quittingPureEndpointRoutedCoalition_card_eq_one_of_nonsingleton
    (source : QuittingNonsingletonCoalition ι) (who : ι) (action : Bool)
    (hcard :
      (quittingPureEndpointRoutedCoalition source.1 who action).card = 1) :
    action = false ∧ source.1.card = 2 := by
  cases haction : action with
  | false =>
      refine ⟨rfl, ?_⟩
      have hcardErase : (source.1.erase who).card = 1 := by
        simpa [haction] using hcard
      by_cases hmem : who ∈ source.1
      · rw [Finset.card_erase_of_mem hmem] at hcardErase
        omega
      · rw [Finset.erase_eq_of_notMem hmem] at hcardErase
        have hnonsingleton := source.2
        omega
  | true =>
      have hcardInsert : (insert who source.1).card = 1 := by
        simpa [haction] using hcard
      have hle := Finset.card_le_card (Finset.subset_insert who source.1)
      have hnonsingleton := source.2
      omega

theorem quittingRootCoalitionMass_pureCoalitionAction_eq_one
    (coalition : Finset ι) :
    quittingRootCoalitionMass
        (fun who => PMF.pure (quittingCoalitionAction coalition who)) coalition = 1 := by
  unfold quittingRootCoalitionMass coalitionMass quittingRootQuitRates
  have hin : ∀ x ∈ coalition,
      (((fun who => PMF.pure (quittingCoalitionAction coalition who)) x) true).toReal = 1 := by
    intro x hx
    simp [quittingCoalitionAction, hx]
  have hout : ∀ x ∈ coalitionᶜ,
      1 - (((fun who => PMF.pure (quittingCoalitionAction coalition who)) x) true).toReal = 1 := by
    intro x hx
    have hnot : x ∉ coalition := by simpa using hx
    simp [quittingCoalitionAction, hnot]
  rw [Finset.prod_eq_one hin, Finset.prod_eq_one hout]
  norm_num

omit [DecidableEq ι] in
theorem quittingLiteralOneDateOverride_idem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (stage : ℕ) (action : Bool) :
    quittingLiteralOneDateOverride
        (quittingLiteralOneDateOverride strategy stage action) stage action =
      quittingLiteralOneDateOverride strategy stage action := by
  funext time history
  by_cases htime : time = stage
  · subst time
    simp [quittingLiteralOneDateOverride]
  · simp [quittingLiteralOneDateOverride, htime]

theorem quittingLiteralPureRootProfile_update_eq_routed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (coalition : Finset ι)
    (who : ι) (action : Bool)
    (target : Finset ι)
    (htarget : target =
      quittingPureEndpointRoutedCoalition coalition who action) :
    Function.update
        (quittingLiteralPureRootProfile reward profile stage
          (quittingCoalitionAction coalition))
        who
        (quittingLiteralOneDateOverride
          ((quittingLiteralPureRootProfile reward profile stage
            (quittingCoalitionAction coalition)) who)
          stage action) =
      quittingLiteralPureRootProfile reward profile stage
        (quittingCoalitionAction target) := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    have hroot : quittingCoalitionAction target who = action := by
      rw [htarget]
      rw [quittingCoalitionAction_routed]
      simp
    by_cases htime : time = stage
    · subst time
      simp [quittingLiteralPureRootProfile, quittingLiteralOneDateOverride,
        hroot]
    · simp [quittingLiteralPureRootProfile, quittingLiteralOneDateOverride,
        htime]
  · have hroot : quittingCoalitionAction target player =
        quittingCoalitionAction coalition player := by
      rw [htarget]
      rw [quittingCoalitionAction_routed]
      simp [hplayer]
    simp [quittingLiteralPureRootProfile, quittingLiteralOneDateOverride,
      hplayer, hroot]

/-- Updating one coordinate of a literal pure coalition root gives the
literal pure profile of its routed nonsingleton coalition. -/
theorem quittingLiteralPureRootCoalitionProfile_update_eq_routed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (coalition : QuittingNonsingletonCoalition ι)
    (who : ι) (action : Bool)
    (target : QuittingNonsingletonCoalition ι)
    (htarget : target.1 = quittingNonsingletonCoalitionRouted coalition who action) :
    Function.update
        (quittingLiteralPureRootCoalitionProfile reward profile stage coalition)
        who
        (quittingLiteralOneDateOverride
          ((quittingLiteralPureRootCoalitionProfile reward profile stage coalition) who)
          stage action) =
      quittingLiteralPureRootCoalitionProfile reward profile stage target := by
  simpa only [quittingLiteralPureRootCoalitionProfile,
    quittingPureRootOfCoalition, quittingNonsingletonCoalitionRouted] using
      quittingLiteralPureRootProfile_update_eq_routed reward profile stage
        coalition.1 who action target.1 htarget

omit [DecidableEq ι] in
@[simp] theorem quittingLiteralOneDateOverride_self
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (stage : ℕ) (action : Bool) :
    quittingLiteralOneDateOverride strategy stage action stage =
      fun _history => PMF.pure action := by
  funext history
  simp [quittingLiteralOneDateOverride]
  rfl

omit [DecidableEq ι] in
theorem quittingLiteralOneDateOverride_of_ne
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (stage time : ℕ) (action : Bool) (h : time ≠ stage) :
    quittingLiteralOneDateOverride strategy stage action time = strategy time := by
  funext history
  simp [quittingLiteralOneDateOverride, h]

theorem quittingProfileLiveRoot_literalOneDateProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingProfileLiveRoot reward
        (quittingLiteralOneDateProfile reward profile who stage action) stage =
      Function.update (quittingProfileLiveRoot reward profile stage) who
        (PMF.pure action) := by
  unfold quittingProfileLiveRoot quittingLiteralOneDateProfile
    quittingLiteralOneDateOverride
  funext player
  by_cases hplayer : player = who
  · subst player
    simp
    rfl
  · simp [Function.update_of_ne hplayer]

omit [DecidableEq ι] in
theorem quittingProfileLiveRoot_literalPureRootProfile_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (root : ι → Bool) :
    quittingProfileLiveRoot reward
        (quittingLiteralPureRootProfile reward profile stage root) stage =
      fun who => PMF.pure (root who) := by
  unfold quittingProfileLiveRoot quittingLiteralPureRootProfile
    quittingLiteralOneDateOverride
  funext who
  simp
  rfl

omit [DecidableEq ι] in
theorem quittingBehaviorLiveHazard_literalOneDateOverride
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (action : Bool) :
    quittingBehaviorLiveHazard reward
        (quittingLiteralOneDateOverride (profile who) stage action) =
      quittingStageDeviationHazard (quittingProfileLiveRoot reward profile)
        who stage (PMF.pure action)
        (fun offset =>
          quittingProfileLiveRoot reward profile (stage + 1 + offset) who) := by
  funext time
  unfold quittingBehaviorLiveHazard quittingLiteralOneDateOverride
  change (if time = stage then PMF.pure action else
    profile who time (quittingLiveHist reward time)) = _
  by_cases hlt : time < stage
  · rw [if_neg (ne_of_lt hlt)]
    rw [quittingStageDeviationHazard_of_lt
      (quittingProfileLiveRoot reward profile) who (PMF.pure action)
      (fun offset =>
        quittingProfileLiveRoot reward profile (stage + 1 + offset) who) hlt]
    rfl
  · by_cases heq : time = stage
    · subst time
      rw [quittingStageDeviationHazard_self]
      simp
    · have hstage : stage < time := lt_of_le_of_ne (Nat.le_of_not_gt hlt)
        (Ne.symm heq)
      rw [quittingStageDeviationHazard]
      simp only [if_neg hlt, if_neg heq]
      change profile who time (quittingLiveHist reward time) =
        profile who (stage + 1 + (time - (stage + 1)))
          (quittingLiveHist reward (stage + 1 + (time - (stage + 1))))
      rw [Nat.add_sub_of_le (Nat.succ_le_iff.mpr hstage)]

theorem quittingProfileLiveRoot_literalOneDateProfile_eq_rootSequenceUpdate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingProfileLiveRoot reward
        (quittingLiteralOneDateProfile reward profile who stage action) =
      quittingRootSequenceUpdate (quittingProfileLiveRoot reward profile)
        who (quittingStageDeviationHazard
          (quittingProfileLiveRoot reward profile) who stage (PMF.pure action)
          (fun offset =>
            quittingProfileLiveRoot reward profile (stage + 1 + offset) who)) := by
  unfold quittingLiteralOneDateProfile
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  rw [quittingBehaviorLiveHazard_literalOneDateOverride]

theorem quittingProfileLiveRoot_literalOneDateProfile_eq_canonical
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingProfileLiveRoot reward
        (quittingLiteralOneDateProfile reward profile who stage action) =
      quittingProfileLiveRoot reward
        (Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)) := by
  rw [quittingProfileLiveRoot_literalOneDateProfile_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation]

theorem quittingTerminalPayoff_literalOneDateProfile_eq_canonical
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingTerminalPayoff reward
        (quittingLiteralOneDateProfile reward profile who stage action) who =
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)) who := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_literalOneDateProfile_eq_canonical]

theorem quittingContinuationBestResponseValue_literalOneDateProfile_self_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingContinuationBestResponseValue reward
        (quittingLiteralOneDateProfile reward profile who stage action) who =
      quittingContinuationBestResponseValue reward profile who := by
  unfold quittingLiteralOneDateProfile
  exact quittingContinuationBestResponseValue_update_self
    reward profile who _

theorem quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralOneDateProfile reward profile who stage action)) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who -
        (quittingTerminalPayoff reward
          (quittingLiteralOneDateProfile reward profile who stage action) who -
          quittingTerminalPayoff reward profile who) := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
        (quittingLiteralOneDateProfile reward profile who stage action) who -
      quittingTerminalPayoff reward
        (quittingLiteralOneDateProfile reward profile who stage action) who =
    quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who -
        (quittingTerminalPayoff reward
          (quittingLiteralOneDateProfile reward profile who stage action) who -
          quittingTerminalPayoff reward profile who)
  rw [quittingContinuationBestResponseValue_literalOneDateProfile_self_eq]
  ring

theorem quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingTerminalPayoff reward
          (quittingLiteralOneDateProfile reward profile who stage action) who -
        quittingTerminalPayoff reward profile who =
      quittingLiveMass reward profile stage *
        (quittingRootSuccessorPayoff reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))).1
          (Function.update (quittingProfileLiveRoot reward profile stage) who
            (PMF.pure action)) who -
          quittingRootSuccessorPayoff reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who) := by
  rw [quittingTerminalPayoff_literalOneDateProfile_eq_canonical]
  exact quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul
    reward profile who stage action

theorem quittingTerminalPayoff_literalOneDateProfile_bestEndpoint_gain_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetProfile := quittingLiteralOneDateProfile reward profile who stage action
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    gain = quittingLiveMass reward profile stage *
      quittingRootCoordinateNashDefect reward tail.1 root who := by
  dsimp only
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let gain := quittingTerminalPayoff reward
      (quittingLiteralOneDateProfile reward profile who stage action) who -
    quittingTerminalPayoff reward profile who
  calc
    gain = quittingLiveMass reward profile stage *
        (quittingRootSuccessorPayoff reward tail.1
            (Function.update root who (PMF.pure action)) who -
          quittingRootSuccessorPayoff reward tail.1 root who) := by
      exact quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect
        reward profile who stage action
    _ = quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who := by
      rw [quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect]

theorem quittingTerminalSemanticDebt_literalOneDateProfile_bestEndpoint_eq_sub_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetProfile := quittingLiteralOneDateProfile reward profile who stage action
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain := by
  dsimp only
  exact quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain
    reward profile who stage _

theorem quittingLiveMass_literalOneDateProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingLiveMass reward
        (quittingLiteralOneDateProfile reward profile who stage action) stage =
      quittingLiveMass reward profile stage := by
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  apply quittingJointSurvivalWeight_congr
  intro time htime
  unfold quittingProfileLiveRoot quittingLiteralOneDateProfile
    quittingLiteralOneDateOverride
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [Nat.ne_of_lt htime]
  · simp [Function.update_of_ne hplayer]

theorem quittingProfileLiveRoot_literalOneDateProfile_tail_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage offset : ℕ) (action : Bool) :
    quittingProfileLiveRoot reward
        (quittingLiteralOneDateProfile reward profile who stage action)
        (stage + 1 + offset) =
      quittingProfileLiveRoot reward profile (stage + 1 + offset) := by
  unfold quittingProfileLiveRoot quittingLiteralOneDateProfile
    quittingLiteralOneDateOverride
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [show stage + 1 + offset ≠ stage by omega]
  · simp [Function.update_of_ne hplayer]

theorem quittingStageCoalitionMass_literalOneDateProfile_eq_canonical
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (action : Bool) :
    quittingStageCoalitionMass reward
        (quittingLiteralOneDateProfile reward profile who stage action)
        stage terminal =
      quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)) stage terminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalOneDateProfile_eq,
    quittingLiveMass_stagePureEndpoint_eq,
    quittingProfileLiveRoot_literalOneDateProfile_eq_canonical]

/-- The literal endpoint update has the same gain as the checked canonical
deviation, while retaining the source's complete strategy off the selected
date. -/
theorem quittingLiteralSameStage_bestEndpoint_gain_and_debt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetProfile := quittingLiteralOneDateProfile reward profile who stage action
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    gain = quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who ∧
      quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain := by
  dsimp only
  constructor
  · exact quittingTerminalPayoff_literalOneDateProfile_bestEndpoint_gain_eq
      reward profile who stage
  · exact quittingTerminalSemanticDebt_literalOneDateProfile_bestEndpoint_eq_sub_gain
      reward profile who stage

/-- One low-tail row dispatches to a literal same-stage endpoint update.  The
tail arm is discharged by the supplied strict low-tail inequality; the
remaining endpoint has the checked gain floor, exact mover-debt identity,
carrier membership, and no-loss routing. -/
theorem quittingLiteralSameStage_exists_strictGain_or_singletonRoute
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (lambda : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hcollision : 1 < terminal.val.card)
    (hmass : lambda ≤
      quittingStageCoalitionMass reward profile stage terminal)
    (hlowTail :
      quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2) :
    ∃ who,
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      let action := quittingRootBestEndpointAction reward tail.1 root who
      let targetProfile := quittingLiteralOneDateProfile reward profile who stage action
      let source := quittingTerminalSemanticPair reward profile
      let target := quittingTerminalSemanticPair reward targetProfile
      let gain := quittingTerminalPayoff reward targetProfile who -
        quittingTerminalPayoff reward profile who
      let routed := quittingPureEndpointRoutedCoalition terminal.val who action
      gain = quittingLiveMass reward profile stage *
          quittingRootCoordinateNashDefect reward tail.1 root who ∧
        0 < gain ∧
        lambda * quittingTerminalSemanticDebtSum minimum /
            (2 * (Fintype.card ι : ℝ)) ≤ gain ∧
        target ∈ quittingTerminalSemanticCarrier reward ∧
        quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebt source who - gain ∧
        (routed.card = 1 ∨ 1 < routed.card) ∧
        ∃ hrouted : routed.Nonempty,
          quittingStageCoalitionMass reward profile stage terminal ≤
            quittingStageCoalitionMass reward targetProfile stage
              ⟨routed, hrouted⟩ := by
  have hmassPos : 0 < quittingStageCoalitionMass reward profile stage terminal :=
    hlambda.trans_le hmass
  have hselected :=
    quittingLiveWeightedCollisionTransfer_tailEscape_or_exists_endpointGain
      reward minimum profile stage terminal hminimumCarrier hminimum
        hminimumDebt hcollision hmassPos
  dsimp only at hselected ⊢
  rcases hselected with htail | ⟨who, hgain, hgainPos, hgainFloor⟩
  · have hexcessNonneg := quittingSpineDebtExcess_nonneg_of_minimum
      reward profile minimum hminimum (stage + 1)
    have hliveNonneg := quittingLiveMass_nonneg reward profile stage
    have hliveLe := quittingLiveMass_le_one reward profile stage
    have htailLe : quittingLiveMass reward profile stage *
          quittingSpineDebtExcess reward profile
            (quittingTerminalSemanticDebtSum minimum) (stage + 1) ≤
        quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) := by
      nlinarith
    have hscale : lambda * quittingTerminalSemanticDebtSum minimum / 2 ≤
        quittingStageCoalitionMass reward profile stage terminal *
          quittingTerminalSemanticDebtSum minimum / 2 := by
      gcongr
    have : quittingLiveMass reward profile stage *
          quittingSpineDebtExcess reward profile
            (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        quittingStageCoalitionMass reward profile stage terminal *
          quittingTerminalSemanticDebtSum minimum / 2 := by
      exact htailLe.trans_lt (hlowTail.trans_le hscale)
    exact (False.elim ((not_lt_of_ge htail) this))
  · let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetProfile := quittingLiteralOneDateProfile reward profile who stage action
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    let routed := quittingPureEndpointRoutedCoalition terminal.val who action
    have hcanonicalRouting := quittingStageCoalitionMass_le_stagePureEndpointRouted
      reward profile who stage terminal action hcollision
    have htarget : target ∈ quittingTerminalSemanticCarrier reward := by
      exact quittingTerminalSemanticPair_mem_carrier reward targetProfile
    have hmover := quittingTerminalSemanticDebt_literalOneDateProfile_bestEndpoint_eq_sub_gain
      reward profile who stage
    have hgainLiteral := quittingTerminalPayoff_literalOneDateProfile_bestEndpoint_gain_eq
      reward profile who stage
    have hfloor : lambda * quittingTerminalSemanticDebtSum minimum /
          (2 * (Fintype.card ι : ℝ)) ≤ gain := by
      dsimp only [gain] at hgainFloor ⊢
      rw [← quittingTerminalPayoff_literalOneDateProfile_eq_canonical
        reward profile who stage] at hgainFloor
      have hmassScale := mul_le_mul_of_nonneg_right hmass
        (by positivity : 0 ≤ quittingTerminalSemanticDebtSum minimum)
      have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
      apply le_trans ?_ hgainFloor
      field_simp [ne_of_gt hcard]
      nlinarith
    have hrouted : ∃ hrouted : routed.Nonempty,
        quittingStageCoalitionMass reward profile stage terminal ≤
          quittingStageCoalitionMass reward targetProfile stage
            ⟨routed, hrouted⟩ := by
      obtain ⟨hrouted, hroute⟩ := hcanonicalRouting
      refine ⟨hrouted, ?_⟩
      rw [quittingStageCoalitionMass_literalOneDateProfile_eq_canonical]
      exact hroute
    have hcardCases : routed.card = 1 ∨ 1 < routed.card := by
      have hnonempty : 0 < routed.card := Finset.card_pos.mpr
        (Classical.choose hrouted)
      omega
    refine ⟨who, ?_⟩
    have hgainPosLiteral : 0 < gain := by
      dsimp only [gain]
      rw [quittingTerminalPayoff_literalOneDateProfile_eq_canonical]
      exact hgainPos
    refine ⟨?_, hgainPosLiteral, hfloor, htarget, ?_, hcardCases, hrouted⟩
    · exact hgainLiteral
    · exact hmover

/- The corresponding equality of complete shifted profiles is intentionally
not claimed: proving it requires a history-indexed shift congruence.  The
live-root tail equality below is the currently checked invariant. -/
omit [DecidableEq ι] in
theorem quittingLiteralPureRootProfile_eq_of_root_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (root₁ root₂ : ι → Bool) (hroot : root₁ = root₂) :
    quittingLiteralPureRootProfile reward profile stage root₁ =
      quittingLiteralPureRootProfile reward profile stage root₂ := by
  rw [hroot]

omit [DecidableEq ι] in
theorem quittingProfileLiveRoot_literalPureRootProfile_of_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage time : ℕ) (root : ι → Bool) (htime : time ≠ stage) :
    quittingProfileLiveRoot reward
        (quittingLiteralPureRootProfile reward profile stage root) time =
      quittingProfileLiveRoot reward profile time := by
  unfold quittingProfileLiveRoot quittingLiteralPureRootProfile
    quittingLiteralOneDateOverride
  funext who
  simp [htime]

theorem quittingTerminalSemanticPair_eq_of_liveRoot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile₁ profile₂ : (quittingGame reward).BehaviorProfile)
    (hroot : quittingProfileLiveRoot reward profile₁ =
      quittingProfileLiveRoot reward profile₂) :
    quittingTerminalSemanticPair reward profile₁ =
      quittingTerminalSemanticPair reward profile₂ := by
  unfold quittingTerminalSemanticPair
  apply Prod.ext
  · funext who
    change quittingTerminalPayoff reward profile₁ who =
      quittingTerminalPayoff reward profile₂ who
    rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
      quittingTerminalPayoff_eq_rootSequence_profileLiveRoot, hroot]
  · funext who
    change quittingContinuationBestResponseValue reward profile₁ who =
      quittingContinuationBestResponseValue reward profile₂ who
    rw [quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot,
      quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot,
      hroot]

omit [DecidableEq ι] in
theorem quittingLiteralPureRootProfile_tail_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (root : ι → Bool) (offset : ℕ) :
    quittingProfileLiveRoot reward
        (quittingLiteralPureRootProfile reward profile stage root)
        (stage + 1 + offset) =
      quittingProfileLiveRoot reward profile (stage + 1 + offset) := by
  apply quittingProfileLiveRoot_literalPureRootProfile_of_ne
  omega

omit [DecidableEq ι] in
theorem quittingProfileLiveRoot_spine_literalPureRoot_tail_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (root : ι → Bool) :
    quittingProfileLiveRoot reward
        (quittingAllContinueProfileSpine reward
          (quittingLiteralPureRootProfile reward profile stage root) (stage + 1)) =
      quittingProfileLiveRoot reward
        (quittingAllContinueProfileSpine reward profile (stage + 1)) := by
  funext offset player
  change (quittingAllContinueProfileSpine reward
      (quittingLiteralPureRootProfile reward profile stage root) (stage + 1)) player
        offset (quittingLiveHist reward offset) =
    (quittingAllContinueProfileSpine reward profile (stage + 1)) player offset
      (quittingLiveHist reward offset)
  rw [quittingAllContinueProfileSpine_apply_liveHist,
    quittingAllContinueProfileSpine_apply_liveHist]
  exact congrFun
    (quittingLiteralPureRootProfile_tail_eq reward profile stage root offset) player

theorem quittingTerminalSemanticPair_spine_literalPureRoot_tail_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (root : ι → Bool) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (quittingLiteralPureRootProfile reward profile stage root) (stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1)) := by
  exact quittingTerminalSemanticPair_eq_of_liveRoot_eq reward _ _
    (quittingProfileLiveRoot_spine_literalPureRoot_tail_eq reward profile stage root)

omit [DecidableEq ι] in
/-- Replacing only the selected date's root preserves the probability of
reaching that date. -/
theorem quittingLiveMass_literalPureRootProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (root : ι → Bool) :
    quittingLiveMass reward
        (quittingLiteralPureRootProfile reward profile stage root) stage =
      quittingLiveMass reward profile stage := by
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  apply quittingJointSurvivalWeight_congr
  intro time htime
  simpa only [Nat.zero_add] using
    (quittingProfileLiveRoot_literalPureRootProfile_of_ne
      reward profile stage time root (Nat.ne_of_lt htime))

theorem quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition ι) :
    quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage
        (quittingTerminalOfNonsingletonCoalition source) =
      quittingLiveMass reward profile stage := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  have hlive : quittingLiveMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage =
      quittingLiveMass reward profile stage :=
    quittingLiveMass_literalPureRootProfile_eq reward profile stage _
  rw [hlive]
  have hroot : quittingProfileLiveRoot reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage =
      fun who => PMF.pure (quittingCoalitionAction source.1 who) := by
    dsimp [quittingLiteralPureRootCoalitionProfile, quittingPureRootOfCoalition]
    exact quittingProfileLiveRoot_literalPureRootProfile_self reward profile stage _
  rw [hroot]
  change quittingLiveMass reward profile stage *
      quittingRootCoalitionMass
        (fun who => PMF.pure (quittingCoalitionAction source.1 who)) source.1 =
    quittingLiveMass reward profile stage
  rw [quittingRootCoalitionMass_pureCoalitionAction_eq_one]
  ring

def quittingSameStageCoalitionGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition ι)
    (who : ι) (action : Bool) : ℝ :=
  quittingTerminalPayoff reward
      (quittingLiteralOneDateProfile reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage source)
        who stage action) who -
    quittingTerminalPayoff reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage source) who

/-- A checked nonsingleton endpoint edge.  The certificate deliberately keeps
the source family and target family visible, including the exact mover debt
subtraction and routed stage-mass comparison. -/
structure QuittingSameStageEndpointEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (minimum : QuittingTerminalSemanticPair ι)
    (lambda : ℝ) (source target : QuittingNonsingletonCoalition ι) where
  who : ι
  action : Bool
  action_eq_best :
    action = quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine
          reward
          (quittingLiteralPureRootCoalitionProfile reward profile stage source)
          (stage + 1))).1
      (quittingProfileLiveRoot
        reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage) who
  target_eq_routed : target.1 =
    quittingPureEndpointRoutedCoalition source.1 who action
  gain_eq_live_defect :
    quittingSameStageCoalitionGain reward profile stage source who action =
      quittingLiveMass reward
          (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (quittingLiteralPureRootCoalitionProfile reward profile stage source)
              (stage + 1))).1
          (quittingProfileLiveRoot reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage)
          who
  gain_pos : 0 < quittingSameStageCoalitionGain reward profile stage source who action
  gain_floor :
    lambda * quittingTerminalSemanticDebtSum minimum /
          (2 * (Fintype.card ι : ℝ)) ≤
      quittingSameStageCoalitionGain reward profile stage source who action
  target_mem :
    quittingTerminalSemanticPair reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage target) ∈
      quittingTerminalSemanticCarrier reward
  mover_debt :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralPureRootCoalitionProfile reward profile stage target)) who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage source)) who -
        quittingSameStageCoalitionGain reward profile stage source who action
  stage_mass_le :
    quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage
        (quittingTerminalOfNonsingletonCoalition source) ≤
      quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage target) stage
        (quittingTerminalOfNonsingletonCoalition target)

theorem quittingLiteralSameStage_exists_singleton_or_endpointEdge
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition ι)
    (lambda : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hmass : lambda ≤ quittingStageCoalitionMass reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage
      (quittingTerminalOfNonsingletonCoalition source))
    (hlowTail : quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2) :
    (∃ (who : ι) (action : Bool) (singleton : {S : Finset ι // S.Nonempty}),
      singleton.val.card = 1 ∧
      singleton.val = quittingPureEndpointRoutedCoalition source.1 who action ∧
      quittingStageCoalitionMass reward
          (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage
          (quittingTerminalOfNonsingletonCoalition source) ≤
        quittingStageCoalitionMass reward
          (quittingLiteralOneDateProfile reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage source)
            who stage action) stage singleton) ∨
    ∃ target : QuittingNonsingletonCoalition ι,
      Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum lambda
        source target) := by
  let sourceProfile :=
    quittingLiteralPureRootCoalitionProfile reward profile stage source
  have hlowSource : quittingSpineDebtExcess reward sourceProfile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2 := by
    unfold quittingSpineDebtExcess
    dsimp [sourceProfile]
    change quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (quittingLiteralPureRootProfile reward profile stage
              (quittingPureRootOfCoalition source.1)) (stage + 1))) -
        quittingTerminalSemanticDebtSum minimum <
      lambda * quittingTerminalSemanticDebtSum minimum / 2
    rw [quittingTerminalSemanticPair_spine_literalPureRoot_tail_eq]
    exact hlowTail
  have hcollision : 1 < (source.1.card : ℕ) := source.2
  have hselected := quittingLiteralSameStage_exists_strictGain_or_singletonRoute
      reward minimum sourceProfile stage (quittingTerminalOfNonsingletonCoalition source)
      lambda hminimumCarrier hminimum hminimumDebt hlambda hcollision hmass hlowSource
  rcases hselected with ⟨who, hgain, hpos, hfloor, htarget, hdebt, hcases, hmassRoute⟩
  rcases hcases with hsingleton | hnonsingleton
  · obtain ⟨hrouted, hrouteMass⟩ := hmassRoute
    left
    refine ⟨who, quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward sourceProfile (stage + 1))).1
      (quittingProfileLiveRoot reward sourceProfile stage) who,
      ⟨quittingPureEndpointRoutedCoalition source.1 who
        (quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward sourceProfile (stage + 1))).1
          (quittingProfileLiveRoot reward sourceProfile stage) who), hrouted⟩,
      ?_, ?_, ?_⟩
    · exact hsingleton
    · rfl
    · exact hrouteMass
  · obtain ⟨hrouted, hrouteMass⟩ := hmassRoute
    let target : QuittingNonsingletonCoalition ι := ⟨_, hnonsingleton⟩
    have htargetEq : target.1 =
        quittingPureEndpointRoutedCoalition source.1 who
          (quittingRootBestEndpointAction reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward sourceProfile (stage + 1))).1
            (quittingProfileLiveRoot reward sourceProfile stage) who) := by
      rfl
    have hprofile :
        Function.update sourceProfile who
            (quittingLiteralOneDateOverride (sourceProfile who) stage
              (quittingRootBestEndpointAction reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward sourceProfile (stage + 1))).1
                (quittingProfileLiveRoot reward sourceProfile stage) who)) =
          quittingLiteralPureRootCoalitionProfile reward profile stage target := by
      exact quittingLiteralPureRootCoalitionProfile_update_eq_routed
        reward profile stage source who _ target htargetEq
    right
    refine ⟨target, ⟨{
      who := who
      action := quittingRootBestEndpointAction reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward sourceProfile (stage + 1))).1
        (quittingProfileLiveRoot reward sourceProfile stage) who
      action_eq_best := by rfl
      target_eq_routed := htargetEq
      gain_eq_live_defect := by
        simpa [quittingSameStageCoalitionGain, sourceProfile] using hgain
      gain_pos := by
        simpa [quittingSameStageCoalitionGain, sourceProfile] using hpos
      gain_floor := by
        simpa [quittingSameStageCoalitionGain, sourceProfile] using hfloor
      target_mem := by
        rw [← hprofile]
        simpa [quittingLiteralOneDateProfile, sourceProfile] using htarget
      mover_debt := by
        rw [← hprofile]
        simpa [quittingLiteralOneDateProfile, quittingSameStageCoalitionGain,
          sourceProfile] using hdebt
      stage_mass_le := by
        rw [← hprofile]
        have hterminal : quittingTerminalOfNonsingletonCoalition target =
            ⟨quittingPureEndpointRoutedCoalition source.1 who
              (quittingRootBestEndpointAction reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward sourceProfile
                    (stage + 1))).1
                (quittingProfileLiveRoot reward sourceProfile stage) who), hrouted⟩ := by
          apply Subtype.ext
          rfl
        rw [hterminal]
        simpa [quittingLiteralOneDateProfile,
          quittingTerminalOfNonsingletonCoalition, sourceProfile] using hrouteMass
    }⟩⟩

theorem quittingSameStage_minimalClosedSegment_of_serial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (minimum : QuittingTerminalSemanticPair ι)
    (lambda : ℝ) (start : QuittingNonsingletonCoalition ι)
    (hserial : ∀ source : QuittingNonsingletonCoalition ι,
      ∃ target : QuittingNonsingletonCoalition ι,
        Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum lambda
          source target)) :
    ∃ (orbit : ℕ → QuittingNonsingletonCoalition ι)
      (segment : MathUE.FiniteBooleanEndpointOrbit.MinimalClosedSegment orbit),
      orbit 0 = start ∧
      (∀ time, Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum
        lambda (orbit time) (orbit (time + 1)))) ∧
      segment.segment.period ≤
        2 ^ Fintype.card ι - Fintype.card ι - 1 ∧
      quittingLiteralPureRootCoalitionProfile reward profile stage
          (orbit (segment.segment.start + segment.segment.period)) =
        quittingLiteralPureRootCoalitionProfile reward profile stage
          (orbit segment.segment.start) := by
  classical
  let next : QuittingNonsingletonCoalition ι → QuittingNonsingletonCoalition ι :=
    fun source => Classical.choose (hserial source)
  have hnext : ∀ source : QuittingNonsingletonCoalition ι,
      Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum lambda
        source (next source)) := by
    intro source
    exact Classical.choose_spec (hserial source)
  let orbit : ℕ → QuittingNonsingletonCoalition ι :=
    fun time => Nat.rec start (fun _ source => next source) time
  have horbit_zero : orbit 0 = start := by
    rfl
  have horbit_step : ∀ time,
      Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum lambda
        (orbit time) (orbit (time + 1))) := by
    intro time
    change Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum lambda
      (orbit time) (next (orbit time)))
    exact hnext (orbit time)
  obtain ⟨segment⟩ :=
    MathUE.FiniteBooleanEndpointOrbit.exists_minimalClosedSegment orbit
  have hperiod : segment.segment.period ≤
      2 ^ Fintype.card ι - Fintype.card ι - 1 := by
    simpa [MathUE.FiniteBooleanEndpointOrbit.card_nonsingletonCoalition] using
      segment.segment.period_le_card
  have hroot :
      quittingPureRootOfCoalition
          (orbit (segment.segment.start + segment.segment.period)).1 =
        quittingPureRootOfCoalition (orbit segment.segment.start).1 := by
    exact congrArg quittingPureRootOfCoalition
      (congrArg Subtype.val segment.segment.closes)
  refine ⟨orbit, segment, horbit_zero, horbit_step, hperiod, ?_⟩
  exact quittingLiteralPureRootProfile_eq_of_root_eq reward profile stage _ _ hroot

def QuittingSameStageSingletonRoute
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition ι) : Prop :=
  ∃ (who : ι) (action : Bool) (singleton : {S : Finset ι // S.Nonempty}),
    singleton.val.card = 1 ∧
    singleton.val = quittingPureEndpointRoutedCoalition source.1 who action ∧
    quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage
        (quittingTerminalOfNonsingletonCoalition source) ≤
      quittingStageCoalitionMass reward
        (quittingLiteralOneDateProfile reward
          (quittingLiteralPureRootCoalitionProfile reward profile stage source)
          who stage action) stage singleton

/-- A two-player same-stage vertex already has a mass-preserving route to a
singleton, independently of minimum or gain data. -/
theorem quittingSameStageSingletonRoute_of_card_eq_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (source : QuittingNonsingletonCoalition ι)
    (hcard : source.1.card = 2) :
    QuittingSameStageSingletonRoute reward profile stage source := by
  have hcard_pos : 0 < source.1.card := by rw [hcard]; omega
  have hnonempty : source.1.Nonempty := Finset.card_pos.mp hcard_pos
  obtain ⟨who, hwho⟩ := hnonempty
  let routed := quittingPureEndpointRoutedCoalition source.1 who false
  have hrouted : routed.Nonempty :=
    quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
      source.1 who false source.2
  let singleton : {S : Finset ι // S.Nonempty} := ⟨routed, hrouted⟩
  refine ⟨who, false, singleton, ?_, rfl, ?_⟩
  · dsimp only [singleton, routed]
    rw [quittingPureEndpointRoutedCoalition_false,
      Finset.card_erase_of_mem hwho, hcard]
  · rw [quittingStageCoalitionMass_literalOneDateProfile_eq_canonical]
    obtain ⟨hrouted', hmass⟩ := quittingStageCoalitionMass_le_stagePureEndpointRouted
      reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage source)
      who stage (quittingTerminalOfNonsingletonCoalition source) false source.2
    simpa only [singleton, routed, quittingTerminalOfNonsingletonCoalition] using hmass

def QuittingSameStageEndpointDispatch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (minimum : QuittingTerminalSemanticPair ι)
    (lambda : ℝ) (source : QuittingNonsingletonCoalition ι) : Prop :=
  QuittingSameStageSingletonRoute reward profile stage source ∨
    ∃ target : QuittingNonsingletonCoalition ι,
      Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum lambda
        source target)

theorem quittingLiteralSameStage_dispatch
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition ι)
    (lambda : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hmass : lambda ≤ quittingStageCoalitionMass reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage source) stage
      (quittingTerminalOfNonsingletonCoalition source))
    (hlowTail : quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2) :
    QuittingSameStageEndpointDispatch reward profile stage minimum lambda source := by
  simpa [QuittingSameStageEndpointDispatch, QuittingSameStageSingletonRoute] using
    (quittingLiteralSameStage_exists_singleton_or_endpointEdge reward minimum profile
      stage source lambda hminimumCarrier hminimum hminimumDebt hlambda hmass hlowTail)

theorem exists_quittingSameStage_terminalRoute_or_closedSegment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (minimum : QuittingTerminalSemanticPair ι)
    (lambda : ℝ) (start : QuittingNonsingletonCoalition ι)
    (hdispatch : ∀ source : QuittingNonsingletonCoalition ι,
      QuittingSameStageEndpointDispatch reward profile stage minimum lambda source) :
    Nonempty (MathUE.FiniteBooleanEndpointOrbit.DispatchedOrbit
        (QuittingSameStageSingletonRoute reward profile stage)
        (fun source target => Nonempty
          (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
        start) ∨
      ∃ trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
          (QuittingSameStageSingletonRoute reward profile stage)
          (fun source target => Nonempty
            (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
          start,
        trace.segment.segment.period ≤
            2 ^ Fintype.card ι - Fintype.card ι - 1 ∧
        quittingLiteralPureRootCoalitionProfile reward profile stage
            (trace.orbit (trace.segment.segment.start + trace.segment.segment.period)) =
          quittingLiteralPureRootCoalitionProfile reward profile stage
            (trace.orbit trace.segment.segment.start) := by
  classical
  let terminal : QuittingNonsingletonCoalition ι → Prop :=
    QuittingSameStageSingletonRoute reward profile stage
  let edge : QuittingNonsingletonCoalition ι →
      QuittingNonsingletonCoalition ι → Prop := fun source target =>
    Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target)
  have hdispatch' : ∀ source, terminal source ∨ ∃ target, edge source target := by
    intro source
    simpa [terminal, edge, QuittingSameStageEndpointDispatch] using hdispatch source
  obtain htrace :=
    MathUE.FiniteBooleanEndpointOrbit.exists_dispatchedOrbit_terminal_or_closedSegment
      terminal edge hdispatch' start
  rcases htrace with hterminal | hclosed
  · exact Or.inl hterminal
  · obtain ⟨trace⟩ := hclosed
    have hperiod : trace.segment.segment.period ≤
        2 ^ Fintype.card ι - Fintype.card ι - 1 := by
      simpa [MathUE.FiniteBooleanEndpointOrbit.card_nonsingletonCoalition] using
        trace.segment.segment.period_le_card
    have hroot :
        quittingPureRootOfCoalition
            (trace.orbit (trace.segment.segment.start + trace.segment.segment.period)).1 =
          quittingPureRootOfCoalition (trace.orbit trace.segment.segment.start).1 := by
      exact congrArg quittingPureRootOfCoalition
        (congrArg Subtype.val trace.segment.segment.closes)
    right
    exact ⟨trace, hperiod,
      quittingLiteralPureRootProfile_eq_of_root_eq reward profile stage _ _ hroot⟩

theorem exists_quittingSameStage_terminalRoute_or_closedSegment_of_liveMass
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ) (start : QuittingNonsingletonCoalition ι)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hmass : lambda ≤ quittingLiveMass reward profile stage)
    (hlowTail : quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2) :
    Nonempty (MathUE.FiniteBooleanEndpointOrbit.DispatchedOrbit
        (QuittingSameStageSingletonRoute reward profile stage)
        (fun source target => Nonempty
          (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
        start) ∨
      ∃ trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
          (QuittingSameStageSingletonRoute reward profile stage)
          (fun source target => Nonempty
            (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
          start,
        trace.segment.segment.period ≤
            2 ^ Fintype.card ι - Fintype.card ι - 1 ∧
        quittingLiteralPureRootCoalitionProfile reward profile stage
            (trace.orbit (trace.segment.segment.start + trace.segment.segment.period)) =
          quittingLiteralPureRootCoalitionProfile reward profile stage
            (trace.orbit trace.segment.segment.start) := by
  have hdispatch : ∀ source : QuittingNonsingletonCoalition ι,
      QuittingSameStageEndpointDispatch reward profile stage minimum lambda source := by
    intro source
    apply quittingLiteralSameStage_dispatch reward minimum profile stage source lambda
      hminimumCarrier hminimum hminimumDebt hlambda
    rw [quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass]
    exact hmass
    exact hlowTail
  exact exists_quittingSameStage_terminalRoute_or_closedSegment reward profile stage
    minimum lambda start hdispatch

/-- A reached nonsingleton source row reduces to the common live-mass
dichotomy.  The resulting orbit is the canonical pure-root family over the
same base profile; this is not a checked `≤ n` preliminary best-update trace
from the original mixed row. -/
theorem exists_quittingSameStage_terminalRoute_or_closedSegment_of_sourceRow
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty}) (lambda : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hcollision : 1 < terminal.val.card)
    (hmass : lambda ≤ quittingStageCoalitionMass reward profile stage terminal)
    (hlowTail : quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2) :
    Nonempty (MathUE.FiniteBooleanEndpointOrbit.DispatchedOrbit
        (QuittingSameStageSingletonRoute reward profile stage)
        (fun source target => Nonempty
          (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
        ⟨terminal.val, hcollision⟩) ∨
      ∃ trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
          (QuittingSameStageSingletonRoute reward profile stage)
          (fun source target => Nonempty
            (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
          ⟨terminal.val, hcollision⟩,
        trace.segment.segment.period ≤
            2 ^ Fintype.card ι - Fintype.card ι - 1 ∧
        quittingLiteralPureRootCoalitionProfile reward profile stage
            (trace.orbit (trace.segment.segment.start + trace.segment.segment.period)) =
          quittingLiteralPureRootCoalitionProfile reward profile stage
            (trace.orbit trace.segment.segment.start) := by
  apply exists_quittingSameStage_terminalRoute_or_closedSegment_of_liveMass
    reward minimum profile stage lambda ⟨terminal.val, hcollision⟩
    hminimumCarrier hminimum hminimumDebt hlambda ?_ hlowTail
  exact le_trans hmass
    (quittingStageCoalitionMass_le_liveMass reward profile stage terminal)

theorem QuittingSameStageEndpointEdge.source_ne_target
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {source target : QuittingNonsingletonCoalition ι}
    (edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda source target) :
    source ≠ target := by
  intro hsame
  subst target
  have hprofile :
      Function.update
          (quittingLiteralPureRootCoalitionProfile reward profile stage source) edge.who
          (quittingLiteralOneDateOverride
            ((quittingLiteralPureRootCoalitionProfile reward profile stage source) edge.who)
            stage edge.action) =
        quittingLiteralPureRootCoalitionProfile reward profile stage source := by
    exact quittingLiteralPureRootCoalitionProfile_update_eq_routed reward profile stage
      source edge.who edge.action source edge.target_eq_routed
  have hgain :
      quittingSameStageCoalitionGain reward profile stage source edge.who edge.action = 0 := by
    unfold quittingSameStageCoalitionGain quittingLiteralOneDateProfile
    rw [hprofile]
    ring
  linarith [edge.gain_pos, hgain]

theorem QuittingSameStageEndpointEdge.target_eq_singlePlayer_toggle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {source target : QuittingNonsingletonCoalition ι}
    (edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda source target) :
    (source.1.erase edge.who = target.1 ∧ edge.action = false ∧
        edge.who ∈ source.1) ∨
      (insert edge.who source.1 = target.1 ∧ edge.action = true ∧
        edge.who ∉ source.1) := by
  rcases quittingPureEndpointRoutedCoalition_four_way source.1 edge.who edge.action with
    hsame | hdrop | hjoin | hsame
  · exfalso
    apply edge.source_ne_target
    apply Subtype.ext
    rw [edge.target_eq_routed]
    exact hsame.2.2.symm
  · exact Or.inl ⟨by simpa [hdrop.2.2] using edge.target_eq_routed.symm,
      hdrop.2.1, hdrop.1⟩
  · exact Or.inr ⟨by simpa [hjoin.2.2] using edge.target_eq_routed.symm,
      hjoin.2.1, hjoin.1⟩
  · exfalso
    apply edge.source_ne_target
    apply Subtype.ext
    rw [edge.target_eq_routed]
    exact hsame.2.2.symm

/-- A strict same-stage endpoint edge changes exactly the mover's Boolean
coalition membership. -/
theorem QuittingSameStageEndpointEdge.target_eq_toggle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {source target : QuittingNonsingletonCoalition ι}
    (edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda
      source target) :
    target.1 = quittingToggleCoalition source.1 edge.who := by
  rcases edge.target_eq_singlePlayer_toggle with hdrop | hjoin
  · rw [quittingToggleCoalition_of_mem hdrop.2.2]
    exact hdrop.1.symm
  · rw [quittingToggleCoalition_of_notMem hjoin.2.2]
    exact hjoin.1.symm

omit [Fintype ι] in
private theorem eq_of_toggle_toggle_eq_sameStage
    (coalition : Finset ι) (first second : ι)
    (hreturn : quittingToggleCoalition
      (quittingToggleCoalition coalition first) second = coalition) :
    second = first := by
  by_contra hne
  have hmembership := congrArg (fun target => first ∈ target) hreturn
  by_cases hfirst : first ∈ coalition
  · by_cases hsecond : second ∈ coalition
    · simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership
    · simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership
      exact hne hmembership.symm
  · by_cases hsecond : second ∈ coalition
    · simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership
      exact hne hmembership.symm
    · simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership

/-- Exact positive mover-debt subtraction forbids an immediate reverse
same-stage endpoint edge. -/
theorem QuittingSameStageEndpointEdge.not_reverse
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {source target : QuittingNonsingletonCoalition ι}
    (first : QuittingSameStageEndpointEdge reward profile stage minimum lambda
      source target)
    (second : QuittingSameStageEndpointEdge reward profile stage minimum lambda
      target source) : False := by
  have hreturn : quittingToggleCoalition
        (quittingToggleCoalition source.1 first.who) second.who = source.1 := by
    rw [← first.target_eq_toggle, ← second.target_eq_toggle]
  have hwho : second.who = first.who :=
    eq_of_toggle_toggle_eq_sameStage source.1 first.who second.who hreturn
  let sourceDebt := quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage source)) first.who
  let targetDebt := quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage target)) first.who
  have hfirstDebt : targetDebt = sourceDebt -
      quittingSameStageCoalitionGain reward profile stage source
        first.who first.action := by
    simpa [sourceDebt, targetDebt] using first.mover_debt
  have hsecondDebt : sourceDebt = targetDebt -
      quittingSameStageCoalitionGain reward profile stage target
        first.who second.action := by
    simpa [sourceDebt, targetDebt, hwho] using second.mover_debt
  have hsecondGain : 0 < quittingSameStageCoalitionGain reward profile stage
      target first.who second.action := by
    simpa [hwho] using second.gain_pos
  linarith [first.gain_pos, hsecondGain]

theorem dispatchedClosedSegment_period_ne_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) :
    trace.segment.segment.period ≠ 1 := by
  intro hperiod
  obtain ⟨edge⟩ := trace.offset_edge ⟨0, by omega⟩
  have hne := edge.source_ne_target
  apply hne
  simpa [hperiod] using trace.segment.segment.closes.symm

theorem dispatchedClosedSegment_period_two_or_more
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start) :
    2 ≤ trace.segment.segment.period := by
  have hpos := trace.segment.segment.period_pos
  have hne := dispatchedClosedSegment_period_ne_one trace
  omega

theorem dispatchedClosedSegment_stageMass_ge_initial
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (hinitial : lambda ≤ quittingStageCoalitionMass reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage
        (trace.orbit trace.segment.segment.start)) stage
      (quittingTerminalOfNonsingletonCoalition
        (trace.orbit trace.segment.segment.start))) :
    ∀ offset : Fin trace.segment.segment.period,
      lambda ≤ quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage
          (trace.orbit (trace.segment.segment.start + offset))) stage
        (quittingTerminalOfNonsingletonCoalition
          (trace.orbit (trace.segment.segment.start + offset))) := by
  intro offset
  have hmono : ∀ n : ℕ, n ≤ offset.val →
      lambda ≤ quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage
          (trace.orbit (trace.segment.segment.start + n))) stage
        (quittingTerminalOfNonsingletonCoalition
          (trace.orbit (trace.segment.segment.start + n))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero =>
        have hstart : trace.orbit (trace.segment.segment.start + 0) =
            trace.orbit trace.segment.segment.start := by simp
        rw [hstart]
        exact hinitial
      | succ n =>
        have hnlt : n < trace.segment.segment.period := by
          have hoffset := offset.isLt
          omega
        obtain ⟨edge⟩ := trace.offset_edge ⟨n, hnlt⟩
        have hmass := edge.stage_mass_le
        have hstep := ih n (by omega) (by omega)
        exact hstep.trans (by simpa [Nat.add_assoc] using hmass)
  simpa using hmono offset.val (by omega)

theorem dispatchedClosedSegment_offset_edge_certificate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    ∃ edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda
        (trace.orbit (trace.segment.segment.start + offset))
        (trace.orbit (trace.segment.segment.start + offset + 1)),
      0 < quittingSameStageCoalitionGain reward profile stage
          (trace.orbit (trace.segment.segment.start + offset)) edge.who edge.action ∧
        lambda * quittingTerminalSemanticDebtSum minimum /
              (2 * (Fintype.card ι : ℝ)) ≤
          quittingSameStageCoalitionGain reward profile stage
            (trace.orbit (trace.segment.segment.start + offset)) edge.who edge.action := by
  obtain ⟨edge⟩ := trace.offset_edge offset
  exact ⟨edge, edge.gain_pos, edge.gain_floor⟩

noncomputable def dispatchedClosedSegmentEdge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    QuittingSameStageEndpointEdge reward profile stage minimum lambda
      (trace.orbit (trace.segment.segment.start + offset))
      (trace.orbit (trace.segment.segment.start + offset + 1)) :=
  Classical.choice (trace.offset_edge offset)

theorem dispatchedClosedSegment_player_circulation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (player : ι) :
    let debtAt : ℕ → ℝ := fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralPureRootCoalitionProfile reward profile stage
            (trace.orbit (trace.segment.segment.start + n)))) player
    let moverAt : ℕ → Option ι := fun n =>
      if hn : n < trace.segment.segment.period then
        some (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).who
      else none
    let gainAt : ℕ → ℝ := fun n =>
      if hn : n < trace.segment.segment.period then
        quittingSameStageCoalitionGain reward profile stage
          (trace.orbit (trace.segment.segment.start + n))
          (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).who
          (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).action
      else 0
    ∑ n ∈ Finset.range trace.segment.segment.period,
        (if moverAt n = some player then gainAt n else 0) =
      ∑ n ∈ Finset.range trace.segment.segment.period,
        (if moverAt n ≠ some player then debtAt (n + 1) - debtAt n else 0) := by
  dsimp
  let debtAt : ℕ → ℝ := fun n =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage
          (trace.orbit (trace.segment.segment.start + n)))) player
  let moverAt : ℕ → Option ι := fun n =>
    if hn : n < trace.segment.segment.period then
      some (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).who
    else none
  let gainAt : ℕ → ℝ := fun n =>
    if hn : n < trace.segment.segment.period then
      quittingSameStageCoalitionGain reward profile stage
        (trace.orbit (trace.segment.segment.start + n))
        (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).who
        (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).action
    else 0
  have hzero : debtAt trace.segment.segment.period = debtAt 0 := by
    dsimp [debtAt]
    exact congrArg (fun s => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage s)) player)
      trace.segment.segment.closes
  have hsum : ∑ n ∈ Finset.range trace.segment.segment.period,
      (debtAt (n + 1) - debtAt n) = 0 := by
    rw [Finset.sum_range_sub, hzero]
    ring
  have hpoint : ∀ n, n < trace.segment.segment.period →
      debtAt (n + 1) - debtAt n =
        (if moverAt n = some player then -gainAt n else 0) +
          (if moverAt n ≠ some player then debtAt (n + 1) - debtAt n else 0) := by
    intro n hn
    by_cases hm : (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).who = player
    · simp [moverAt, gainAt, hn, hm]
      have hdebt : debtAt (n + 1) = debtAt n -
          quittingSameStageCoalitionGain reward profile stage
            (trace.orbit (trace.segment.segment.start + n))
            player
            (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).action := by
        simpa [debtAt, Nat.add_assoc, hm] using
          (dispatchedClosedSegmentEdge trace ⟨n, hn⟩).mover_debt
      rw [hdebt]
      ring
    · simp [moverAt, hn, hm]
  have hdecomp : ∑ n ∈ Finset.range trace.segment.segment.period,
      (debtAt (n + 1) - debtAt n) =
      ∑ n ∈ Finset.range trace.segment.segment.period,
        ((if moverAt n = some player then -gainAt n else 0) +
          (if moverAt n ≠ some player then debtAt (n + 1) - debtAt n else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n (Finset.mem_range.1 hn)
  rw [hdecomp, Finset.sum_add_distrib] at hsum
  have hneg : (∑ n ∈ Finset.range trace.segment.segment.period,
      if moverAt n = some player then -gainAt n else 0) =
      -∑ n ∈ Finset.range trace.segment.segment.period,
        if moverAt n = some player then gainAt n else 0 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : moverAt n = some player <;> simp [h]
  rw [hneg] at hsum
  linarith

theorem dispatchedClosedSegmentEdge_spec
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    Nonempty (QuittingSameStageEndpointEdge reward profile stage minimum lambda
      (trace.orbit (trace.segment.segment.start + offset))
      (trace.orbit (trace.segment.segment.start + offset + 1))) :=
  ⟨dispatchedClosedSegmentEdge trace offset⟩

theorem dispatchedClosedSegment_offset_edge_full_certificate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    ∃ edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda
        (trace.orbit (trace.segment.segment.start + offset))
        (trace.orbit (trace.segment.segment.start + offset + 1)),
      (trace.orbit (trace.segment.segment.start + offset + 1)).1 =
          quittingPureEndpointRoutedCoalition
            (trace.orbit (trace.segment.segment.start + offset)).1 edge.who edge.action ∧
        edge.action = quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (quittingLiteralPureRootCoalitionProfile reward profile stage
                (trace.orbit (trace.segment.segment.start + offset))) (stage + 1))).1
          (quittingProfileLiveRoot reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage
              (trace.orbit (trace.segment.segment.start + offset))) stage) edge.who ∧
        0 < quittingSameStageCoalitionGain reward profile stage
          (trace.orbit (trace.segment.segment.start + offset)) edge.who edge.action ∧
        lambda * quittingTerminalSemanticDebtSum minimum /
              (2 * (Fintype.card ι : ℝ)) ≤
          quittingSameStageCoalitionGain reward profile stage
            (trace.orbit (trace.segment.segment.start + offset)) edge.who edge.action ∧
        quittingTerminalSemanticPair reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage
              (trace.orbit (trace.segment.segment.start + offset + 1))) ∈
          quittingTerminalSemanticCarrier reward ∧
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingLiteralPureRootCoalitionProfile reward profile stage
                (trace.orbit (trace.segment.segment.start + offset + 1)))) edge.who =
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingLiteralPureRootCoalitionProfile reward profile stage
                (trace.orbit (trace.segment.segment.start + offset)))) edge.who -
            quittingSameStageCoalitionGain reward profile stage
              (trace.orbit (trace.segment.segment.start + offset)) edge.who edge.action ∧
        quittingStageCoalitionMass reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage
              (trace.orbit (trace.segment.segment.start + offset))) stage
            (quittingTerminalOfNonsingletonCoalition
              (trace.orbit (trace.segment.segment.start + offset))) ≤
          quittingStageCoalitionMass reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage
              (trace.orbit (trace.segment.segment.start + offset + 1))) stage
            (quittingTerminalOfNonsingletonCoalition
              (trace.orbit (trace.segment.segment.start + offset + 1))) := by
  let edge := dispatchedClosedSegmentEdge trace offset
  refine ⟨edge, ?_⟩
  exact ⟨edge.target_eq_routed, edge.action_eq_best, edge.gain_pos, edge.gain_floor,
    edge.target_mem, edge.mover_debt, edge.stage_mass_le⟩

theorem dispatchedClosedSegment_offset_literal_profile_update
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair ι} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition ι}
    (trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingSameStageEndpointEdge reward profile stage minimum lambda source target))
      start)
    (offset : Fin trace.segment.segment.period) :
    Function.update
        (quittingLiteralPureRootCoalitionProfile reward profile stage
          (trace.orbit (trace.segment.segment.start + offset)))
        (dispatchedClosedSegmentEdge trace offset).who
        (quittingLiteralOneDateOverride
          ((quittingLiteralPureRootCoalitionProfile reward profile stage
            (trace.orbit (trace.segment.segment.start + offset)))
            (dispatchedClosedSegmentEdge trace offset).who)
          stage (dispatchedClosedSegmentEdge trace offset).action) =
      quittingLiteralPureRootCoalitionProfile reward profile stage
        (trace.orbit (trace.segment.segment.start + offset + 1)) := by
  let edge := dispatchedClosedSegmentEdge trace offset
  exact quittingLiteralPureRootCoalitionProfile_update_eq_routed
    reward profile stage (trace.orbit (trace.segment.segment.start + offset))
    edge.who edge.action (trace.orbit (trace.segment.segment.start + offset + 1))
    edge.target_eq_routed

end GameTheory
