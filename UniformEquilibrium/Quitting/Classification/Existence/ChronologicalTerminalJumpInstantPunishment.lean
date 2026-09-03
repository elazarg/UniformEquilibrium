/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionChronologicalA3
import UniformEquilibrium.Quitting.Classification.InstantPunishmentEquivalence
import UniformEquilibrium.Quitting.Root.NearSureProfile

/-!
# Terminal chronological jumps produce instant punishment

A chronological jump whose post-jump path mass is one is approximated by
actual reached rows with positive pre-row reach and vanishing post-row reach.
The selected rows therefore have all-Continue mass tending to zero, while
restarting the source at those rows preserves vanishing full behavioral Nash
error.  The checked near-sure-to-sure perturbation and punishment adapter then
produce the literal instant-punishment branch.
-/

noncomputable section

namespace GameTheory

open Filter Finset Set StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

namespace ChronologicalLimit

omit [Nonempty ι] in
/-- The clock immediately after a selected dominant jump stage converges to
the total path mass after that jump. -/
theorem ChronologicalJumpStageLimit.postClock_tendsto_pathTotal
    {limit : diagonal.ChronologicalLimit} {time : ℝ}
    (approximation : limit.ChronologicalJumpStageLimit time) :
    Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceClock
        (diagonal.completedRoots
          (limit.subsequence (approximation.rank index)))
        (approximation.stage index + 1)) atTop
      (nhds (QuittingAbsorptionPath.pathTotal limit.path time)) := by
  have hsum : Tendsto (fun index ↦
      ∑ coalition,
        QuittingAbsorptionPath.quittingRootSequenceCumulativeCoalitionMass
          (diagonal.completedRoots
            (limit.subsequence (approximation.rank index)))
          (approximation.stage index + 1) coalition) atTop
      (nhds (∑ coalition, limit.path.value time coalition)) := by
    apply tendsto_finsetSum
    intro coalition _
    exact approximation.postCumulativeMass_tendsto coalition
  simpa only [
    QuittingAbsorptionPath.sum_quittingRootSequenceCumulativeCoalitionMass,
    QuittingAbsorptionPath.pathTotal] using hsum

omit [Nonempty ι] in
/-- At a terminal path jump, the actual selected dominant rows have
all-Continue probability tending to zero. -/
theorem ChronologicalJumpStageLimit.stageContinueMass_tendsto_zero_of_pathTotal_eq_one
    {limit : diagonal.ChronologicalLimit} {time : ℝ}
    (approximation : limit.ChronologicalJumpStageLimit time)
    (htime_lt_one : time < 1)
    (hterminal : QuittingAbsorptionPath.pathTotal limit.path time = 1) :
    Tendsto (fun index ↦
      quittingStationaryContinueMass
        (diagonal.completedRoots
          (limit.subsequence (approximation.rank index))
          (approximation.stage index))) atTop (nhds 0) := by
  let roots : ℕ → ℕ → ι → PMF Bool := fun index ↦
    diagonal.completedRoots
      (limit.subsequence (approximation.rank index))
  let stage : ℕ → ℕ := approximation.stage
  have hpreSurvival : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index)) atTop (nhds (1 - time)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [roots, stage,
      QuittingAbsorptionPath.quittingRootSequenceClock] using
        hone.sub approximation.clock_tendsto
  have hpostClock := approximation.postClock_tendsto_pathTotal
  rw [hterminal] at hpostClock
  have hpostSurvival : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index + 1)) atTop (nhds 0) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hdifference := hone.sub hpostClock
    simpa [roots, stage,
      QuittingAbsorptionPath.quittingRootSequenceClock] using hdifference
  have hratio : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceSurvival
          (roots index) (stage index + 1) /
        QuittingAbsorptionPath.quittingRootSequenceSurvival
          (roots index) (stage index)) atTop (nhds 0) := by
    have hquotient := hpostSurvival.div hpreSurvival
      (sub_ne_zero.mpr (ne_of_gt htime_lt_one))
    change Tendsto
      ((fun index ↦ QuittingAbsorptionPath.quittingRootSequenceSurvival
          (roots index) (stage index + 1)) /
        fun index ↦ QuittingAbsorptionPath.quittingRootSequenceSurvival
          (roots index) (stage index)) atTop (nhds 0)
    simpa only [zero_div] using hquotient
  have hprePositive : ∀ᶠ index in atTop,
      0 < QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index) :=
    hpreSurvival.eventually (Ioi_mem_nhds (sub_pos.mpr htime_lt_one))
  apply hratio.congr'
  filter_upwards [hprePositive] with index hpositive
  rw [QuittingAbsorptionPath.quittingRootSequenceSurvival_succ]
  change QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index) *
      quittingStationaryContinueMass (roots index (stage index)) /
        QuittingAbsorptionPath.quittingRootSequenceSurvival
          (roots index) (stage index) =
    quittingStationaryContinueMass (roots index (stage index))
  exact mul_div_cancel_left₀
    (quittingStationaryContinueMass (roots index (stage index)))
    hpositive.ne'

/-- A terminal jump of the actual chronological source path produces the
literal AKRS instant-punishment branch `S.2`. -/
theorem instantPunishmentEquilibriumExistence_of_terminalPathJump
    (limit : diagonal.ChronologicalLimit) {time : ℝ}
    (htime : time ∈ QuittingAbsorptionPath.pathJumps limit.path)
    (hterminal : QuittingAbsorptionPath.pathTotal limit.path time = 1) :
    QuittingInstantPunishmentεEquilibriumExistence reward := by
  have htime_ne_one : time ≠ 1 := by
    intro htimeOne
    subst time
    obtain ⟨coalition, hcoalition⟩ := htime.2
    exact hcoalition (limit.pathJump_one_eq_zero coalition)
  have htime_lt_one : time < 1 :=
    lt_of_le_of_ne htime.1.2 htime_ne_one
  let approximation := Classical.choice
    (limit.nonempty_chronologicalJumpStageLimit htime)
  let roots : ℕ → ℕ → ι → PMF Bool := fun index ↦
    diagonal.completedRoots
      (limit.subsequence (approximation.rank index))
  let stage : ℕ → ℕ := approximation.stage
  have hpreSurvival : Tendsto (fun index ↦
      QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index)) atTop (nhds (1 - time)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [roots, stage,
      QuittingAbsorptionPath.quittingRootSequenceClock] using
        hone.sub approximation.clock_tendsto
  have hcontinue : Tendsto (fun index ↦
      quittingStationaryContinueMass (roots index (stage index)))
      atTop (nhds 0) := by
    simpa only [roots, stage] using
      approximation.stageContinueMass_tendsto_zero_of_pathTotal_eq_one
        htime_lt_one hterminal
  have herror : Tendsto (fun index ↦
      diagonal.completedError
        (limit.subsequence (approximation.rank index))) atTop (nhds 0) :=
    diagonal.completedError_tendsto_zero.comp
      ((limit.subsequence_strictMono.comp approximation.rank_strictMono).tendsto_atTop)
  apply quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter
  intro ε hε
  let M := quittingRewardBound reward
  let rho := (1 - time) / 2
  let d := ε / (8 * (M + 1))
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith
  have hrhoLimit : rho < 1 - time := by
    dsimp only [rho]
    linarith
  have hd : 0 < d := by
    dsimp only [d, M]
    positivity
  have hdIdentity : 8 * (M + 1) * d = ε := by
    dsimp only [d]
    field_simp
  have hrounding : 4 * M * d < ε / 2 := by
    nlinarith
  have hreachEventually : ∀ᶠ index in atTop,
      rho ≤ QuittingAbsorptionPath.quittingRootSequenceSurvival
        (roots index) (stage index) := by
    filter_upwards [
      (tendsto_order.1 hpreSurvival).1 rho hrhoLimit] with index hreach
    exact hreach.le
  have hcontinueEventually : ∀ᶠ index in atTop,
      quittingStationaryContinueMass (roots index (stage index)) ≤
        d ^ Fintype.card ι := by
    have hthreshold : 0 < d ^ Fintype.card ι := pow_pos hd _
    filter_upwards [(tendsto_order.1 hcontinue).2 _ hthreshold] with index hmass
    exact hmass.le
  have herrorEventually : ∀ᶠ index in atTop,
      diagonal.completedError
          (limit.subsequence (approximation.rank index)) <
        rho * (ε / 2) :=
    (tendsto_order.1 herror).2 _ (mul_pos hrho (div_pos hε (by norm_num)))
  obtain ⟨index, hreach, hnear, herrorSmall⟩ :=
    (hreachEventually.and <|
      hcontinueEventually.and herrorEventually).exists
  have hcompletedErrorNonneg : 0 ≤ diagonal.completedError
      (limit.subsequence (approximation.rank index)) := by
    let who : ι := Classical.choice inferInstance
    have hnash := diagonal.nash
      (limit.subsequence (approximation.rank index)) who
      (fun offset ↦ roots index offset who)
    have hself : quittingRootSequenceHazardTerminalValue reward
        (roots index) who (fun offset ↦ roots index offset who) 0 =
      quittingRootSequenceTerminalValue reward (roots index) who 0 := by
      simpa using
        (quittingRootSequenceHazardTerminalValue_self_tail
          reward (roots index) who 0)
    rw [hself] at hnash
    linarith
  let shifted : ℕ → ι → PMF Bool := fun offset ↦
    roots index (stage index + offset)
  have hshiftedNash : IsεQuittingRootSequenceNash reward
      (diagonal.completedError
        (limit.subsequence (approximation.rank index)) / rho) shifted := by
    simpa only [shifted] using
      (isεQuittingRootSequenceNash_shift_of_survival_ge
        reward (roots index) hcompletedErrorNonneg hrho
        (diagonal.nash
          (limit.subsequence (approximation.rank index)))
        (stage index) hreach)
  have hshiftedProfileNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (diagonal.completedError
        (limit.subsequence (approximation.rank index)) / rho)
      (quittingRootThenContinuationProfile reward (shifted 0)
        (quittingRootSequenceProfile reward shifted 1)) := by
    have hbehavior :=
      (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
        (diagonal.completedError
          (limit.subsequence (approximation.rank index)) / rho)
        shifted).mp hshiftedNash
    rwa [quittingRootSequenceProfile_eq_rootThenContinuation] at hbehavior
  have hnearShifted : ((Math.PMFProduct.pmfPi (shifted 0))
      quittingAllContinueAction).toReal ≤ d ^ Fintype.card ι := by
    change ((Math.PMFProduct.pmfPi (roots index (stage index)))
      quittingAllContinueAction).toReal ≤ d ^ Fintype.card ι
    simpa only [quittingStationaryContinueMass] using hnear
  obtain ⟨sureRoot, hsureRoot, hsureNash⟩ :=
    exists_sureFirstProfile_of_allContinue_mass_le_pow
      reward (shifted 0) (quittingRootSequenceProfile reward shifted 1)
      hd (abs_reward_le_quittingRewardBound reward) hnearShifted
      hshiftedProfileNash
  obtain ⟨quitter, hquitter⟩ := hsureRoot
  refine ⟨quitter, sureRoot,
    quittingRootSequenceProfile reward shifted 1, hquitter, ?_⟩
  apply hsureNash.mono
  have hshiftedError : diagonal.completedError
        (limit.subsequence (approximation.rank index)) / rho < ε / 2 := by
    rw [div_lt_iff₀ hrho]
    nlinarith
  linarith

end ChronologicalLimit

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory
