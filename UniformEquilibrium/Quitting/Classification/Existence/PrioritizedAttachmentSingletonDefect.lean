/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

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

/-- The same-scale prioritized witness with its corrected residual placed
literally in the positive-singleton-defect arm.  All four priority
negations are copied from the source witness. -/
theorem prioritizedPositiveSingletonDefect_of_attachment
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {delta : ℝ}
    (residual : QuittingPrioritizedRefinedSourceResidualAt reward delta)
    (hdelta : 0 < delta)
    (attachment :
      QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
        reward (1 / 2)) :
    QuittingPrioritizedRefinedSourceResidualAt reward delta := by
  have hdefect :=
    residual.positiveAbsorptionAttachment_to_positiveSingletonDefect
      hdelta attachment
  exact {
    residual := Or.inr (Or.inr hdefect)
    not_stationary := residual.not_stationary
    not_instant := residual.not_instant
    not_wellSupported := residual.not_wellSupported
    not_generated := residual.not_generated }

/-- After prioritization, the corrected source residual has only the source-
faithful all-Continue arm or the positive-singleton-defect arm.  This is a
normal-form reduction, not a consumer for either surviving arm. -/
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
  rcases residual.residual with hphantom | hattachment | hdefect
  · exact Or.inl hphantom
  · obtain ⟨attachment⟩ := hattachment
    exact Or.inr
      (residual.positiveAbsorptionAttachment_to_positiveSingletonDefect
        hdelta attachment)
  · exact Or.inr hdefect

end QuittingPrioritizedRefinedSourceResidualAt
end GameTheory
