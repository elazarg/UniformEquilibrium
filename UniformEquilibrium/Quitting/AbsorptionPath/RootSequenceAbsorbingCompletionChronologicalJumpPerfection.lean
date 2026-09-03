/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalRootSequenceTail
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionChronologicalSingletonDerivativeSupport
import UniformEquilibrium.Quitting.Bellman.Finite.EndpointNashClosed
import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow

/-!
# Exact perfection at chronological jump rows

At a nonterminal jump, the dominant finite stages retain both their product
roots and their post-stage continuation vectors.  The finite prefix payoff
identity identifies the limiting continuation with the absorption-path
payoff.  Reached-stage Nash then closes to exact endpoint Nash and hence exact
row perfection.

This module proves only the jump component of sequential perfection.  It does
not assert either continuous-clock clause or full sequential perfection.
-/

noncomputable section

namespace GameTheory

open Filter Finset Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

namespace ChronologicalLimit

/-- The chronological limit bundled with its four absorption-path axioms. -/
def absorptionPath (limit : diagonal.ChronologicalLimit) :
    QuittingAbsorptionPath.AbsorptionPath (ι := ι) :=
  ⟨limit.path, limit.isAbsorptionPath⟩

/-- A dominant jump-stage approximation together with one compactly
convergent subsequence of its post-stage continuation vectors. -/
structure ChronologicalJumpRootTailLimit
    (limit : diagonal.ChronologicalLimit) (time : ℝ) where
  approximation : limit.ChronologicalJumpStageLimit time
  tailRank : ℕ → ℕ
  tailRank_strictMono : StrictMono tailRank
  tail : QuittingAbsorptionPath.QuittingChronologicalTailBox reward
  tail_tendsto : Tendsto (fun index ↦
    quittingRootSequenceTailVector reward
      (diagonal.completedRoots
        (limit.subsequence (approximation.rank (tailRank index))))
      (approximation.stage (tailRank index) + 1)) atTop
    (nhds tail.1)

private def ChronologicalJumpStageLimit.tailPoint
    {limit : diagonal.ChronologicalLimit} {time : ℝ}
    (approximation : limit.ChronologicalJumpStageLimit time) (index : ℕ) :
    QuittingAbsorptionPath.QuittingChronologicalTailBox reward := by
  let roots := diagonal.completedRoots
    (limit.subsequence (approximation.rank index))
  let stage := approximation.stage index
  refine ⟨quittingRootSequenceTailVector reward roots (stage + 1), ?_⟩
  constructor <;> intro who
  · have h := abs_quittingRootSequenceTerminalValue_le reward roots who
      (stage + 1) (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
    exact neg_le_of_abs_le h
  · exact (abs_le.mp (abs_quittingRootSequenceTerminalValue_le reward roots who
      (stage + 1) (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward))).2

omit [Nonempty ι] in
/-- Every localized jump stage admits a compactly convergent post-stage tail
subsequence. -/
theorem nonempty_chronologicalJumpRootTailLimit
    (limit : diagonal.ChronologicalLimit) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathJumps limit.path) :
    Nonempty (limit.ChronologicalJumpRootTailLimit time) := by
  let approximation := Classical.choice
    (limit.nonempty_chronologicalJumpStageLimit htime)
  obtain ⟨tail, tailRank, hstrict, htendsto⟩ :=
    CompactSpace.tendsto_subseq approximation.tailPoint
  refine ⟨{
    approximation := approximation
    tailRank := tailRank
    tailRank_strictMono := hstrict
    tail := tail
    tail_tendsto := ?_
  }⟩
  have hvalue := continuous_subtype_val.continuousAt.tendsto.comp htendsto
  simpa [ChronologicalJumpStageLimit.tailPoint, Function.comp_def] using hvalue

/-- The compact post-stage continuation selected at a chronological jump is
the continuation payoff induced by the remaining absorption-path mass. -/
theorem ChronologicalJumpRootTailLimit.tail_eq_absorptionPathPayoff
    {limit : diagonal.ChronologicalLimit} {time : ℝ}
    (approximation : limit.ChronologicalJumpRootTailLimit time)
    (htime : time ∈ QuittingAbsorptionPath.pathJumps limit.path)
    (htotal : QuittingAbsorptionPath.pathTotal limit.path time < 1) :
    approximation.tail.1 =
      QuittingAbsorptionPath.absorptionPathPayoff reward limit.absorptionPath time := by
  classical
  let selected : ℕ → ℕ := fun index ↦
    approximation.approximation.rank (approximation.tailRank index)
  have hselected : StrictMono selected :=
    approximation.approximation.rank_strictMono.comp
      approximation.tailRank_strictMono
  let roots : ℕ → ℕ → ι → PMF Bool := fun index ↦
    diagonal.completedRoots (limit.subsequence (selected index))
  let stage : ℕ → ℕ := fun index ↦
    approximation.approximation.stage (approximation.tailRank index)
  have hterminal (who : ι) : Tendsto (fun index ↦
      quittingRootSequenceTerminalValue reward (roots index) who 0) atTop
      (nhds (limit.payoff who)) := by
    have h := limit.completedTerminalPayoff_tendsto.comp
      hselected.tendsto_atTop
    exact (tendsto_pi_nhds.mp h) who
  have hcumulative (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun index ↦
        QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
          (roots index) (stage index + 1) coalition) atTop
        (nhds (limit.path.value time coalition)) := by
    exact (approximation.approximation.postCumulativeMass_tendsto coalition).comp
      approximation.tailRank_strictMono.tendsto_atTop
  have hprefix (who : ι) : Tendsto (fun index ↦
      ∑ coalition,
        QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
            (roots index) (stage index + 1) coalition * reward coalition who)
      atTop (nhds (∑ coalition,
        limit.path.value time coalition * reward coalition who)) := by
    apply tendsto_finsetSum
    intro coalition _
    exact (hcumulative coalition).mul_const _
  have hclock : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (roots index) (stage index + 1)) atTop
      (nhds (QuittingAbsorptionPath.pathTotal limit.path time)) := by
    have hsum : Tendsto (fun index ↦
        ∑ coalition,
          QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
            (roots index) (stage index + 1) coalition) atTop
        (nhds (∑ coalition, limit.path.value time coalition)) := by
      apply tendsto_finsetSum
      intro coalition _
      exact hcumulative coalition
    simpa only [QuittingAbsorptionPath.sum_quittingRootSequenceCumulativeCoalitionMass,
      QuittingAbsorptionPath.pathTotal] using hsum
  have hsurvival : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index + 1)) atTop
      (nhds (1 - QuittingAbsorptionPath.pathTotal limit.path time)) := by
    convert tendsto_const_nhds.sub hclock using 1
    all_goals simp [QuittingAbsorptionPath.quittingRootSequenceClock]
  have htail (who : ι) : Tendsto (fun index ↦
      quittingRootSequenceTailVector reward (roots index) (stage index + 1) who)
      atTop (nhds (approximation.tail.1 who)) := by
    exact (tendsto_pi_nhds.mp approximation.tail_tendsto) who
  have hdecomposition (who : ι) : limit.payoff who =
      (∑ coalition, limit.path.value time coalition * reward coalition who) +
        (1 - QuittingAbsorptionPath.pathTotal limit.path time) *
          approximation.tail.1 who := by
    apply tendsto_nhds_unique (hterminal who)
    apply (hprefix who).add (hsurvival.mul (htail who)) |>.congr'
    filter_upwards [] with index
    exact
      QuittingAbsorptionPath.quittingRootSequenceTerminalValue_eq_prefixReward_add_survival_mul_tail
        reward (roots index) who (stage index + 1) |>.symm
  funext who
  have hendpoint : limit.payoff who =
      ∑ coalition, limit.path.value 1 coalition * reward coalition who := by
    rfl
  have hdenom : 0 < 1 - QuittingAbsorptionPath.pathTotal limit.path time :=
    sub_pos.mpr htotal
  rw [QuittingAbsorptionPath.absorptionPathPayoff, if_pos htime.1]
  change approximation.tail.1 who =
    (if QuittingAbsorptionPath.pathTotal limit.path time < 1 then
      fun who ↦ (∑ a, (limit.path.value 1 a - limit.path.value time a) *
        reward a who) / (1 - QuittingAbsorptionPath.pathTotal limit.path time)
    else 0) who
  rw [if_pos htotal]
  apply (eq_div_iff hdenom.ne').2
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  linarith [hdecomposition who, hendpoint]

/-- The limiting product row at a chronological jump is an exact endpoint
Nash row against its limiting post-stage continuation. -/
theorem ChronologicalJumpRootTailLimit.endpointNash
    {limit : diagonal.ChronologicalLimit} {time : ℝ}
    (approximation : limit.ChronologicalJumpRootTailLimit time)
    (htime : time ∈ QuittingAbsorptionPath.pathJumps limit.path)
    (htotal : QuittingAbsorptionPath.pathTotal limit.path time < 1) :
    IsεQuittingRootEndpointNash reward approximation.tail.1 0
      (quittingRootOfSimplex approximation.approximation.root) := by
  let selected : ℕ → ℕ := fun index ↦
    approximation.approximation.rank (approximation.tailRank index)
  have hselected : StrictMono selected :=
    approximation.approximation.rank_strictMono.comp
      approximation.tailRank_strictMono
  let roots : ℕ → ℕ → ι → PMF Bool := fun index ↦
    diagonal.completedRoots (limit.subsequence (selected index))
  let stage : ℕ → ℕ := fun index ↦
    approximation.approximation.stage (approximation.tailRank index)
  have htime_lt_one : time < 1 := lt_of_le_of_lt
    (limit.le_pathTotal time htime.1) htotal
  have hsurvival : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index)) atTop (nhds (1 - time)) := by
    have hclock := approximation.approximation.clock_tendsto.comp
      approximation.tailRank_strictMono.tendsto_atTop
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [roots, stage, selected, Function.comp_def,
      QuittingAbsorptionPath.quittingRootSequenceClock] using hone.sub hclock
  have hsurvival_pos : ∀ᶠ index in atTop,
      0 < QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index) :=
    hsurvival.eventually (Ioi_mem_nhds (sub_pos.mpr htime_lt_one))
  have herror : Tendsto (fun index ↦
      diagonal.completedError (limit.subsequence (selected index))) atTop
      (nhds 0) := by
    exact diagonal.completedError_tendsto_zero.comp
      (limit.subsequence_strictMono.comp hselected).tendsto_atTop
  have htolerance : Tendsto (fun index ↦
      diagonal.completedError (limit.subsequence (selected index)) /
        QuittingAbsorptionPath.quittingRootSequenceSurvival
          (roots index) (stage index)) atTop (nhds 0) := by
    change Tendsto
      ((fun index ↦ diagonal.completedError (limit.subsequence (selected index))) /
        fun index ↦ QuittingAbsorptionPath.quittingRootSequenceSurvival
          (roots index) (stage index)) atTop (nhds 0)
    simpa only [zero_div] using herror.div hsurvival
      (sub_ne_zero.mpr (ne_of_gt htime_lt_one))
  apply isεQuittingRootEndpointNash_of_tendsto reward
    (fun index ↦
      diagonal.completedError (limit.subsequence (selected index)) /
        QuittingAbsorptionPath.quittingRootSequenceSurvival
          (roots index) (stage index))
    (fun index ↦
      quittingRootSequenceTailVector reward (roots index) (stage index + 1))
    (fun index ↦ quittingSimplexOfRoot (roots index (stage index)))
    htolerance approximation.tail_tendsto
    (approximation.approximation.root_tendsto.comp
      approximation.tailRank_strictMono.tendsto_atTop)
  filter_upwards [hsurvival_pos] with index hpositive
  simpa only [QuittingAbsorptionPath.quittingRootSequenceSurvival,
    quittingRootOfSimplex_simplexOfRoot] using
    isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash
      reward (roots index)
      (diagonal.nash (limit.subsequence (selected index))) (stage index) hpositive

omit [Nonempty ι] in
/-- The dominant-stage root limit is the literal jump root selected by the
bundled absorption path. -/
theorem ChronologicalJumpRootTailLimit.root_eq_absorptionPathJumpRoot
    {limit : diagonal.ChronologicalLimit} {time : ℝ}
    (approximation : limit.ChronologicalJumpRootTailLimit time)
    (htime : time ∈ QuittingAbsorptionPath.pathJumps limit.path)
    (htotal : QuittingAbsorptionPath.pathTotal limit.path time < 1) :
    quittingRootOfSimplex approximation.approximation.root =
      QuittingAbsorptionPath.absorptionPathJumpRoot limit.absorptionPath time := by
  have htime_lt_one : time < 1 := lt_of_le_of_lt
    (limit.le_pathTotal time htime.1) htotal
  apply QuittingAbsorptionPath.AbsorptionPathJumpRelation.eq
    (path := limit.absorptionPath) (t := time)
  · intro coalition
    exact approximation.approximation.jump_relation htime_lt_one coalition
  · exact QuittingAbsorptionPath.absorptionPathJumpRoot_relation
      limit.absorptionPath htime

/-- The actual jump root selected by the chronological absorption path is an
exact endpoint-Nash row against its absorption-path continuation payoff. -/
theorem jumpEndpointNash
    (limit : diagonal.ChronologicalLimit) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathJumps limit.path)
    (htotal : QuittingAbsorptionPath.pathTotal limit.path time < 1) :
    IsεQuittingRootEndpointNash reward
      (QuittingAbsorptionPath.absorptionPathPayoff reward limit.absorptionPath time) 0
      (QuittingAbsorptionPath.absorptionPathJumpRoot limit.absorptionPath time) := by
  let approximation := Classical.choice
    (limit.nonempty_chronologicalJumpRootTailLimit htime)
  have hnash := approximation.endpointNash htime htotal
  rw [approximation.tail_eq_absorptionPathPayoff htime htotal,
    approximation.root_eq_absorptionPathJumpRoot htime htotal] at hnash
  exact hnash

/-- The chronological limit satisfies the jump-row component of exact
sequential perfection.  No continuous-clock clause is asserted here. -/
theorem jumpPerfect
    (limit : diagonal.ChronologicalLimit) :
    ∀ time ∈ QuittingAbsorptionPath.pathJumps limit.path,
      QuittingAbsorptionPath.pathTotal limit.path time < 1 →
        QuittingRowεPerfect reward
          (QuittingAbsorptionPath.absorptionPathPayoff
            reward limit.absorptionPath time)
          (QuittingAbsorptionPath.absorptionPathJumpRoot
            limit.absorptionPath time) 0 := by
  intro time htime htotal
  exact quittingRowεPerfect_of_isZeroEndpointNash
    (limit.jumpEndpointNash htime htotal) le_rfl

/-- Playerwise projection of the exact jump-row perfection component. -/
theorem jumpPlayerPerfect
    (limit : diagonal.ChronologicalLimit) (who : ι) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathJumps limit.path)
    (htotal : QuittingAbsorptionPath.pathTotal limit.path time < 1) :
    QuittingPlayerRowεPerfect reward
      (QuittingAbsorptionPath.absorptionPathPayoff reward limit.absorptionPath time)
      (QuittingAbsorptionPath.absorptionPathJumpRoot limit.absorptionPath time)
      who 0 :=
  limit.jumpPerfect time htime htotal who

end ChronologicalLimit

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory
