/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.AcyclicSoloPreemption
import UniformEquilibrium.Quitting.Classification.Existence.NoHarmSingletonGenerated
import UniformEquilibrium.Quitting.Classification.Existence.PrioritizedRefinedSourceBoundary
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.CompactQuantitativeAlternatives
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.CompactSpineSurvivalBoundary
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.PositiveRhoLandingCompactLimit
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding

/-!
# Prioritized attachment reduction

The punishment vector is a conditional reservation against every literal
root word.  A source row reached with one uniform positive probability is
therefore exact Nash against its punishment-floor lift in the limit.  This
consumes the finite sure-exit output of a positive-absorption attachment by
the instant-punishment compiler.  The infinite output passes through the
bounded support--Bellman split.  Under the four same-scale priority
negations, the entire attachment arm consequently reduces to the existing
positive-singleton-defect residual.

The resulting defect is not consumed here.  The nested infinite spine also
remains a compact source object rather than an executable chronology.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The min-max punishment vector is a conditional reservation against every
literal, possibly nonstationary, root word.  The securing reply is selected
from the unrestricted behavioral best-reply supremum; no attainment of that
supremum is assumed. -/
theorem isQuittingConditionalReservation_punishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) :
    IsQuittingConditionalReservation reward roots
      (fun who ↦ quittingPunishmentValue reward who) := by
  intro who start slack hslack
  let shifted : ℕ → ι → PMF Bool := fun time ↦ roots (start + time)
  let profile := quittingRootSequenceProfile reward shifted 0
  have hpunishment := quittingPunishmentValue_le reward who profile
  have hstrict : quittingPunishmentValue reward who - slack <
      quittingBestReplyValue reward profile who := by
    linarith
  letI : Nonempty ((quittingGame reward).BehaviorStrategy who) :=
    ⟨quittingAlwaysContinueStrategy reward who⟩
  obtain ⟨deviation, hdeviation⟩ :
      ∃ deviation : (quittingGame reward).BehaviorStrategy who,
        quittingPunishmentValue reward who - slack <
          quittingTerminalPayoff reward
            (Function.update profile who deviation) who := by
    exact exists_lt_of_lt_ciSup
      (f := fun deviation : (quittingGame reward).BehaviorStrategy who ↦
        quittingTerminalPayoff reward
          (Function.update profile who deviation) who)
      (b := quittingPunishmentValue reward who - slack)
      (by simpa only [quittingBestReplyValue] using hstrict)
  refine ⟨quittingBehaviorLiveHazard reward deviation, ?_⟩
  have hpayoff :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward profile who deviation
  rw [show quittingProfileLiveRoot reward profile = shifted by
    simpa only [profile] using
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero reward shifted]
    at hpayoff
  exact hdeviation.le.trans_eq hpayoff

/-- A uniformly reached limiting source row is exactly Nash against the
coordinatewise punishment-floor lift of its displayed successor value.  The
uniform reach floor makes the conditioned unrestricted source-Nash error
vanish along the retained subsequence. -/
theorem
    QuittingLowSurvivalPositiveRhoReachedRowLimit.isQuittingRootNash_punishmentFloorLift
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (row : QuittingLowSurvivalPositiveRhoReachedRowLimit base) :
    IsεQuittingRootNash reward
      (fun who ↦ max (row.nextValue who)
        (quittingPunishmentValue reward who))
      0 (quittingRootOfSimplex row.root) := by
  let sourceIndex : ℕ → ℕ := fun n ↦ base.index (row.subsequence n)
  let sourceAt := fun n ↦ landing.family.source (sourceIndex n)
  let stage : ℕ → ℕ := fun n ↦ (sourceAt n).crossingStage + row.offset
  let lifted : ℕ → Payoff ι := fun n ↦
    quittingLiftedContinuation reward (sourceAt n).roots
      (fun who ↦ quittingPunishmentValue reward who) (stage n + 1)
  let root : ℕ → QuittingRootSimplex ι := fun n ↦
    quittingSimplexOfRoot ((sourceAt n).roots (stage n))
  let error : ℕ → ℝ := fun n ↦
    landing.family.accuracy (sourceIndex n) /
      quittingJointSurvivalWeight (sourceAt n).roots 0 (stage n)
  have hindex : Tendsto sourceIndex atTop atTop :=
    base.index_tendsto_atTop.comp row.subsequence_strictMono.tendsto_atTop
  have haccuracy : Tendsto
      (fun n ↦ landing.family.accuracy (sourceIndex n)) atTop (nhds 0) :=
    landing.family.accuracy_tendsto_zero.comp hindex
  have herror : Tendsto error atTop (nhds 0) := by
    have hupper : Tendsto
        (fun n ↦ landing.family.accuracy (sourceIndex n) / row.reachFloor)
        atTop (nhds 0) := by
      simpa only [zero_div] using haccuracy.div_const row.reachFloor
    apply squeeze_zero' (g := fun n ↦
      landing.family.accuracy (sourceIndex n) / row.reachFloor)
    · apply Filter.Eventually.of_forall
      intro n
      exact div_nonneg
        (landing.family.accuracy_pos (sourceIndex n)).le
        (row.reachFloor_pos.trans (by
          simpa [sourceIndex, sourceAt, stage] using row.reached n)).le
    · apply Filter.Eventually.of_forall
      intro n
      exact div_le_div_of_nonneg_left
        (landing.family.accuracy_pos (sourceIndex n)).le
        row.reachFloor_pos
        (by simpa [sourceIndex, sourceAt, stage] using (row.reached n).le)
    · exact hupper
  have hlifted : Tendsto lifted atTop
      (nhds (fun who ↦ max (row.nextValue who)
        (quittingPunishmentValue reward who))) := by
    apply tendsto_pi_nhds.2
    intro who
    have htail := tendsto_pi_nhds.1 row.nextValue_tendsto who
    have hmax := htail.max
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦ quittingPunishmentValue reward who) atTop
        (nhds (quittingPunishmentValue reward who)))
    simpa [lifted, sourceAt, sourceIndex, stage, quittingLiftedContinuation,
      quittingRootSequenceTailVector, Nat.add_assoc] using hmax
  have hroot : Tendsto root atTop (nhds row.root) := by
    simpa [root, sourceAt, sourceIndex, stage] using row.root_tendsto
  have hendpoint : IsεQuittingRootEndpointNash reward
      (fun who ↦ max (row.nextValue who)
        (quittingPunishmentValue reward who))
      0 (quittingRootOfSimplex row.root) := by
    apply isεQuittingRootEndpointNash_of_tendsto reward error lifted root
      herror hlifted hroot
    apply Filter.Eventually.of_forall
    intro n
    have hsurvival : 0 < quittingJointSurvivalWeight
        (sourceAt n).roots 0 (stage n) :=
      row.reachFloor_pos.trans (by
        simpa [sourceAt, sourceIndex, stage] using row.reached n)
    simpa [error, lifted, root, sourceAt, sourceIndex, stage] using
      isεQuittingRootEndpointNash_quittingLiftedContinuation reward
        (sourceAt n).roots (sourceAt n).sourceNash
        (isQuittingConditionalReservation_punishmentValue reward
          (sourceAt n).roots)
        (stage n) hsurvival
  exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
    reward _ _ _).mp hendpoint

/-- Exact weighted endpoint complementarity recovers exact support-local
complementarity.  This converse is special to zero tolerance. -/
theorem isQuittingRootSupportApproxNash_zero_of_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hendpoint : IsεQuittingRootEndpointNash reward tail 0 root) :
    IsQuittingRootSupportApproxNash reward tail 0 root := by
  intro who
  constructor
  · intro hquit
    have hweighted := (hendpoint who).2
    nlinarith
  · intro hcontinue
    have hweighted := (hendpoint who).1
    nlinarith

/-- Under failure of the stationary and well-supported priority branches,
an infinite reached-row attachment spine contracts to the existing
positive-singleton-defect residual at the same tolerance. -/
theorem
    QuittingLowSurvivalPositiveRhoInfiniteExactSpine.nonempty_positiveSingletonDefect_of_priorities
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u delta : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    {seed : QuittingLowSurvivalPositiveRhoReachedRowLimit base}
    (spine : QuittingLowSurvivalPositiveRhoInfiniteExactSpine seed)
    (hdelta : 0 < delta)
    (hnotStationary : ¬QuittingStationaryεEquilibriumAt reward delta)
    (hnotWellSupported :
      ¬QuittingWellSupportedAbsorbingSequenceAt reward delta) :
    Nonempty
      (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta) := by
  let value : ℕ → Payoff ι := fun n ↦ (spine.row n).currentValue
  let roots : ℕ → ι → PMF Bool := fun n ↦
    quittingRootOfSimplex (spine.row n).root
  have hvalue : ∀ time who,
      |value time who| ≤ quittingRewardBound reward := by
    intro time who
    exact abs_le.mpr
      ⟨(spine.row time).currentValue_mem.1 who,
        (spine.row time).currentValue_mem.2 who⟩
  have hbellman : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) := by
    intro time
    exact (spine.edge time).1
  have hsupport : ∀ time,
      IsQuittingRootSupportApproxNash reward
        (value (time + 1)) delta (roots time) := by
    intro time
    have hexact : IsQuittingRootSupportApproxNash reward
        (value (time + 1)) 0 (roots time) :=
      isQuittingRootSupportApproxNash_zero_of_endpointNash reward _ _
        (spine.edge time).2
    exact hexact.mono hdelta.le
  rcases
      quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary
        reward value roots delta hvalue hbellman hsupport with
    hwellSupported | hboundary
  · exact False.elim (hnotWellSupported hwellSupported)
  · obtain ⟨boundary⟩ := hboundary
    rcases boundary.stationary_or_defect with hstationary | hdefect
    · exact False.elim (hnotStationary (hstationary delta hdelta))
    · exact hdefect

namespace QuittingPrioritizedRefinedSourceResidualAt

/-- A prioritized source witness whose corrected residual is explicitly in
the source-faithful all-Continue arm.  The package retains the same-scale
failure of every corrected pointwise branch. -/
structure AllContinueSourceAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (delta : ℝ) : Prop where
  source : Nonempty
    (QuittingLowSurvivalPositiveRhoAllContinueSourceResidual
      reward (1 / 2))
  not_stationary : ¬QuittingStationaryεEquilibriumAt reward delta
  not_instant : ¬QuittingInstantPunishmentεEquilibriumAt reward delta
  not_wellSupported : ¬QuittingWellSupportedAbsorbingSequenceAt reward delta
  not_generated :
    ¬QuittingStationarilyGeneratedApproximateEquilibriaAt reward delta

/-- Forgetting which corrected residual arm was selected recovers the ambient
prioritized source type. -/
theorem AllContinueSourceAt.toPrioritizedResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (source : AllContinueSourceAt reward delta) :
    QuittingPrioritizedRefinedSourceResidualAt reward delta := {
  residual := Or.inl source.source
  not_stationary := source.not_stationary
  not_instant := source.not_instant
  not_wellSupported := source.not_wellSupported
  not_generated := source.not_generated }

/-- A prioritized source witness whose corrected residual is explicitly in
the positive-singleton-defect arm.  Unlike the ambient prioritized residual
type, this package does not erase which arm was selected. -/
structure PositiveSingletonDefectAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (delta : ℝ) : Prop where
  defect : Nonempty
    (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta)
  not_stationary : ¬QuittingStationaryεEquilibriumAt reward delta
  not_instant : ¬QuittingInstantPunishmentεEquilibriumAt reward delta
  not_wellSupported : ¬QuittingWellSupportedAbsorbingSequenceAt reward delta
  not_generated :
    ¬QuittingStationarilyGeneratedApproximateEquilibriaAt reward delta

/-- Forgetting which corrected residual arm was selected recovers the ambient
prioritized source type. -/
theorem PositiveSingletonDefectAt.toPrioritizedResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (defect : PositiveSingletonDefectAt reward delta) :
    QuittingPrioritizedRefinedSourceResidualAt reward delta := {
  residual := Or.inr (Or.inr defect.defect)
  not_stationary := defect.not_stationary
  not_instant := defect.not_instant
  not_wellSupported := defect.not_wellSupported
  not_generated := defect.not_generated }

/-- Any fixed stationary branch contradicts either prioritized normal-form
arm at its retained positive scale. -/
theorem false_of_stationaryExistence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta)
    (hstationary : QuittingStationaryεEquilibriumExistence reward) : False :=
  residual.not_stationary (hstationary delta hdelta)

/-- Any fixed instant-punishment branch contradicts either prioritized
normal-form arm at its retained positive scale. -/
theorem false_of_instantExistence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta)
    (hinstant : QuittingInstantPunishmentεEquilibriumExistence reward) : False :=
  residual.not_instant (hinstant delta hdelta)

/-- Any fixed well-supported absorbing branch contradicts either prioritized
normal-form arm at its retained positive scale. -/
theorem false_of_wellSupportedExistence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta)
    (hwellSupported :
      QuittingWellSupportedAbsorbingSequenceExistence reward) : False :=
  residual.not_wellSupported (hwellSupported delta hdelta)

/-- A prioritized residual is incompatible with every literal fixed AGKRS
branch.  Therefore a branch consumer for either surviving normal-form arm
must eliminate that arm; it cannot consistently retain the source and merely
append a branch witness. -/
theorem not_stationary_or_instant_or_wellSupportedExistence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta) :
    ¬(QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward) := by
  rintro (hstationary | hinstant | hwellSupported)
  · exact residual.false_of_stationaryExistence hdelta hstationary
  · exact residual.false_of_instantExistence hdelta hinstant
  · exact residual.false_of_wellSupportedExistence hdelta hwellSupported

/-- At a prioritized scale, every positive-singleton owner is strictly
preempted by another player's solo row.  Positivity makes the owner
punishment-normal by testing the all-Continue stationary row.  If its own
singleton row weakly protected every outsider, it would generate Simon's
stationary-prefix branch and contradict the retained fourth priority
negation. -/
theorem exists_strict_solo_preemptor_of_singleton_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta) (owner : ι)
    (hsolo : 0 < quittingSoloReward reward owner owner) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other <
        quittingSoloReward reward other other := by
  by_contra hpreemptor
  have hnoHarm : ∀ other, other ≠ owner →
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other := by
    intro other hother
    exact le_of_not_gt fun hstrict ↦
      hpreemptor ⟨other, hother, hstrict⟩
  have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
    reward owner (quittingSoloStationaryRoot owner (PMF.pure false))
  rw [quittingStationaryUnilateralCap_solo_owner,
    max_eq_left hsolo.le] at hcap
  have hgenerated :=
    quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton
      reward owner hnoHarm hcap
  exact residual.not_generated (hgenerated delta hdelta)

/-- The prioritized all-Continue source arm retains an actual positive
singleton owner, and that owner is either punishment-abnormal or is strictly
preempted by another player's solo row. -/
theorem AllContinueSourceAt.exists_positiveSingleton_strictlyPreempted
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (source : AllContinueSourceAt reward delta) (hdelta : 0 < delta) :
    ∃ owner, 0 < quittingSoloReward reward owner owner ∧
      ∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSoloReward reward other other := by
  have hpositive : ∃ owner,
      0 < quittingSoloReward reward owner owner := by
    simpa [IsQuittingZeroSolo, quittingSoloReward,
      quittingSingletonTerminal, not_forall, not_le] using
      source.source.some.notZeroSolo
  obtain ⟨owner, howner⟩ := hpositive
  exact ⟨owner, howner,
    source.toPrioritizedResidual
      |>.exists_strict_solo_preemptor_of_singleton_pos
        hdelta owner howner⟩

/-- The selected positive singleton in the defect arm obeys the same exact
punishment-abnormal-or-preempted alternative. -/
theorem
    PositiveSingletonDefectAt.exists_selectedSingleton_strictlyPreempted
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (defect : PositiveSingletonDefectAt reward delta) (hdelta : 0 < delta) :
    ∃ other, other ≠ defect.defect.some.defect.who ∧
      quittingSoloReward reward defect.defect.some.defect.who other <
        quittingSoloReward reward other other :=
  defect.toPrioritizedResidual
    |>.exists_strict_solo_preemptor_of_singleton_pos
      hdelta defect.defect.some.defect.who
        defect.defect.some.defect.singleton_pos

/-- The complete prioritized positive-absorption attachment reduction.  A
finite sure-exit output contradicts the same-scale instant-punishment
priority after lifting its reached successor value to the punishment floor.
An infinite output contracts through the support--Bellman classification. -/
theorem positiveAbsorptionAttachment_to_positiveSingletonDefect
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta)
    (attachment :
      QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
        reward (1 / 2)) :
    Nonempty
      (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta) := by
  rcases finiteSureExitAttachment_or_exists_infiniteExactSpine
      attachment.consecutive with hfinite | hinfinite
  · obtain ⟨finite⟩ := hfinite
    let row := finite.terminal
    let tail : Payoff ι := fun who ↦
      max (row.nextValue who) (quittingPunishmentValue reward who)
    let root : ι → PMF Bool := quittingRootOfSimplex row.root
    have hnash : IsεQuittingRootNash reward tail 0 root := by
      simpa [tail, root] using
        row.isQuittingRootNash_punishmentFloorLift
    have hendpoint : IsεQuittingRootEndpointNash reward tail 0 root :=
      (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        reward tail 0 root).mpr hnash
    have hsupport : IsQuittingRootSupportApproxNash reward tail 0 root :=
      isQuittingRootSupportApproxNash_zero_of_endpointNash
        reward tail root hendpoint
    have hrational : QuittingSimonRationalPayoffAt reward 0 tail := by
      intro who
      simp [tail]
    obtain ⟨quitter, hquit⟩ := finite.sureExit
    obtain ⟨punishRow, hcap, hbehavior⟩ :=
      exists_oneStagePunishedProfile_of_rational_support_sureQuitter
        reward tail root quitter (η := 0) (δ := delta)
        (by norm_num) hdelta hrational hsupport hquit
    apply False.elim
    apply residual.not_instant
    refine ⟨quitter, root, punishRow, hquit, hcap, ?_⟩
    simpa using hbehavior
  · obtain ⟨spine⟩ := hinfinite
    exact spine.nonempty_positiveSingletonDefect_of_priorities hdelta
      residual.not_stationary residual.not_wellSupported

/-- The same-scale prioritized witness with the selected positive-singleton
defect exposed rather than hidden inside the ambient residual disjunction.
All four priority negations are copied from the source witness. -/
theorem prioritizedPositiveSingletonDefect_of_attachment
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta)
    (attachment :
      QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
        reward (1 / 2)) :
    PositiveSingletonDefectAt reward delta := by
  have hdefect :=
    residual.positiveAbsorptionAttachment_to_positiveSingletonDefect
      hdelta attachment
  exact {
    defect := hdefect
    not_stationary := residual.not_stationary
    not_instant := residual.not_instant
    not_wellSupported := residual.not_wellSupported
    not_generated := residual.not_generated }

/-- After prioritization, the corrected source residual has only the source-
faithful all-Continue arm or the positive-singleton-defect arm.  Both outputs
retain all four same-scale priority negations. -/
theorem allContinueSourceAt_or_positiveSingletonDefectAt
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta) :
    AllContinueSourceAt reward delta ∨
      PositiveSingletonDefectAt reward delta := by
  rcases residual.residual with hphantom | hattachment | hdefect
  · exact Or.inl {
      source := hphantom
      not_stationary := residual.not_stationary
      not_instant := residual.not_instant
      not_wellSupported := residual.not_wellSupported
      not_generated := residual.not_generated }
  · obtain ⟨attachment⟩ := hattachment
    exact Or.inr
      (residual.prioritizedPositiveSingletonDefect_of_attachment
        hdelta attachment)
  · exact Or.inr {
      defect := hdefect
      not_stationary := residual.not_stationary
      not_instant := residual.not_instant
      not_wellSupported := residual.not_wellSupported
      not_generated := residual.not_generated }

/-- Compatibility projection of
`allContinueSourceAt_or_positiveSingletonDefectAt` for callers which do not
need the retained priority provenance. -/
theorem sourcePhantom_or_positiveSingletonDefect
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta) :
    Nonempty
        (QuittingLowSurvivalPositiveRhoAllContinueSourceResidual
          reward (1 / 2)) ∨
      Nonempty
        (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta) := by
  rcases residual.allContinueSourceAt_or_positiveSingletonDefectAt hdelta with
    hsource | hdefect
  · exact Or.inl hsource.source
  · exact Or.inr hdefect.defect

/-- Every positive-scale prioritized residual forces a directed cycle in the
finite augmented solo-preemption graph.  Bottom points to a positive
singleton selected by either normal-form arm.  A negative singleton points
back to bottom, a positive singleton is strictly preempted, and a zero
singleton with no strict preemptor would be a normal no-harm owner and hence
would generate the excluded stationary-prefix branch. -/
theorem nonempty_augmentedSoloPreemptionCycle
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta) :
    Nonempty (QuittingAugmentedSoloPreemptionCycle reward) := by
  have hpositive : ∃ owner,
      0 < quittingSoloReward reward owner owner := by
    rcases residual.allContinueSourceAt_or_positiveSingletonDefectAt hdelta with
      hsource | hdefect
    · obtain ⟨owner, howner, _other, _hne, _hstrict⟩ :=
        hsource.exists_positiveSingleton_strictlyPreempted hdelta
      exact ⟨owner, howner⟩
    · exact ⟨hdefect.defect.some.defect.who,
        hdefect.defect.some.defect.singleton_pos⟩
  apply Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial
  intro source
  cases source with
  | none =>
      obtain ⟨owner, howner⟩ := hpositive
      exact ⟨some owner, by
        simpa only [QuittingAugmentedSoloPreemptionEdge] using howner⟩
  | some owner =>
      by_cases hnegative : quittingSoloReward reward owner owner < 0
      · exact ⟨none, by
          simpa only [QuittingAugmentedSoloPreemptionEdge] using hnegative⟩
      · by_cases hpositiveOwner :
            0 < quittingSoloReward reward owner owner
        · obtain ⟨other, hother, hstrict⟩ :=
            residual.exists_strict_solo_preemptor_of_singleton_pos
              hdelta owner hpositiveOwner
          exact ⟨some other, by
            simpa only [QuittingAugmentedSoloPreemptionEdge] using
              And.intro hother hstrict⟩
        · have hzero : quittingSoloReward reward owner owner = 0 := by
            exact le_antisymm (le_of_not_gt hpositiveOwner)
              (le_of_not_gt hnegative)
          by_cases hpreemptor : ∃ other, other ≠ owner ∧
              quittingSoloReward reward owner other <
                quittingSoloReward reward other other
          · obtain ⟨other, hother, hstrict⟩ := hpreemptor
            exact ⟨some other, by
              simpa only [QuittingAugmentedSoloPreemptionEdge] using
                And.intro hother hstrict⟩
          · have hnoHarm : ∀ other, other ≠ owner →
                quittingSoloReward reward other other ≤
                  quittingSoloReward reward owner other := by
              intro other hother
              exact le_of_not_gt fun hstrict ↦
                hpreemptor ⟨other, hother, hstrict⟩
            have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
              reward owner
                (quittingSoloStationaryRoot owner (PMF.pure false))
            rw [quittingStationaryUnilateralCap_solo_owner, hzero,
              max_self] at hcap
            have hnormal : quittingPunishmentValue reward owner ≤
                quittingSoloReward reward owner owner :=
              hcap.trans_eq hzero.symm
            have hgenerated :=
              quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton
                reward owner hnoHarm hnormal
            exact False.elim
              (residual.not_generated (hgenerated delta hdelta))

/-- Cofinal prioritized residuals have one exact global normal form.  Either
some positive scale retains a prioritized source-faithful all-Continue arm,
or positive-singleton defects occur cofinally toward zero with their scale
and all four priority negations retained. -/
theorem exists_allContinueSourceAt_or_cofinally_positiveSingletonDefectAt
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcofinal : ∀ target : ℝ, 0 < target →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ target ∧
        QuittingPrioritizedRefinedSourceResidualAt reward delta) :
    (∃ delta : ℝ, 0 < delta ∧ AllContinueSourceAt reward delta) ∨
      ∀ target : ℝ, 0 < target →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ target ∧
          PositiveSingletonDefectAt reward delta := by
  classical
  by_cases hsource : ∃ delta : ℝ,
      0 < delta ∧ AllContinueSourceAt reward delta
  · exact Or.inl hsource
  · right
    intro target htarget
    obtain ⟨delta, hdelta, hdeltaTarget, residual⟩ :=
      hcofinal target htarget
    rcases residual.allContinueSourceAt_or_positiveSingletonDefectAt hdelta with
      hsourceAt | hdefect
    · exact False.elim (hsource ⟨delta, hdelta, hsourceAt⟩)
    · exact ⟨delta, hdelta, hdeltaTarget, hdefect⟩

/-- A cofinal prioritized residual family is incompatible with every fixed
AGKRS branch.  The residual side of the corrected extraction must therefore
be eliminated, not decorated with a branch witness. -/
theorem cofinallyPrioritized_not_stationary_or_instant_or_wellSupported
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcofinal : ∀ target : ℝ, 0 < target →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ target ∧
        QuittingPrioritizedRefinedSourceResidualAt reward delta) :
    ¬(QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward) := by
  obtain ⟨delta, hdelta, _hdeltaOne, residual⟩ :=
    hcofinal 1 (by norm_num)
  exact residual.not_stationary_or_instant_or_wellSupportedExistence hdelta

/-- Cofinal prioritized residuals need no scale-indexed downstream consumer:
one selected positive scale already produces the table's augmented solo-
preemption cycle. -/
theorem nonempty_augmentedSoloPreemptionCycle_of_cofinallyPrioritized
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcofinal : ∀ target : ℝ, 0 < target →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ target ∧
        QuittingPrioritizedRefinedSourceResidualAt reward delta) :
    Nonempty (QuittingAugmentedSoloPreemptionCycle reward) := by
  obtain ⟨delta, hdelta, _hdeltaOne, residual⟩ :=
    hcofinal 1 (by norm_num)
  exact residual.nonempty_augmentedSoloPreemptionCycle hdelta

end QuittingPrioritizedRefinedSourceResidualAt
end GameTheory
