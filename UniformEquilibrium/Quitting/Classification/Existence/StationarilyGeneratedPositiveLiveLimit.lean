/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedWitnessRegimes
import UniformEquilibrium.Quitting.Classification.Existence.WellSupportedAbsorbingSequence
import UniformEquilibrium.Quitting.Paths.JointSurvivalSelection

/-!
# Positive-live limits of stationary-prefix witnesses

When the repeated-prefix horizon tends to infinity and its one-stage live
mass has a positive limit, every fixed depth remains uniformly reachable.
The global Nash inequality can therefore be divided by that reach and passed
to a diagonal limit.  The limit retains:

* one limiting product root;
* a bounded Bellman continuation ray for that same root;
* exact endpoint Nash at every depth; and
* the actual punishment tail's limiting semantic pair and min-max cap.

If the limiting root absorbs with positive probability, bounded Bellman-path
uniqueness identifies the ray with the constant root sequence's actual tail.
That constant sequence is completely absorbing and gives branch `S.3`.
The sole remaining case is the all-Continue root.  Its forward continuation
ray is a phantom boundary value; the punishment cap survives separately at
the other, escaping end of the finite prefixes.  No relation between those
two ends is asserted.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The canonical compact cube containing every quitting terminal payoff. -/
def quittingStationaryPrefixValueCube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Set (Payoff ι) :=
  Set.Icc (fun _ => -quittingRewardBound reward)
    (fun _ => quittingRewardBound reward)

/-- The compact product carrier for a root, a forward continuation ray, and
the semantic pair of the punishment tail. -/
def quittingStationaryPrefixRayCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingRootSimplex ι ×
      ((ℕ → Payoff ι) × QuittingTerminalSemanticPair ι)) :=
  (Set.univ : Set (QuittingRootSimplex ι)) ×ˢ
    ({value | ∀ time, value time ∈ quittingStationaryPrefixValueCube reward} ×ˢ
      quittingTerminalSemanticCarrier reward)

/-- The root/ray/punishment carrier is compact. -/
theorem quittingStationaryPrefixRayCarrier_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingStationaryPrefixRayCarrier reward) := by
  apply isCompact_univ.prod
  apply (isCompact_pi_infinite fun _ => (isCompact_Icc :
    IsCompact (quittingStationaryPrefixValueCube reward))).prod
  exact quittingTerminalSemanticCarrier_isCompact reward

/-- The exact two-ended datum surviving from a positive-live,
divergent-horizon family.  The forward Bellman ray and the punishment-tail
semantic pair are retained as separate ends because their distance tends to
infinity. -/
structure QuittingPositiveLiveStationaryPrefixLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  punished : ι
  root : QuittingRootSimplex ι
  value : ℕ → Payoff ι
  punishmentTail : QuittingTerminalSemanticPair ι
  liveMass : ℝ
  liveMass_pos : 0 < liveMass
  liveMass_eq :
    quittingStationaryContinueMass (quittingRootOfSimplex root) = liveMass
  value_mem : ∀ time, value time ∈ quittingStationaryPrefixValueCube reward
  policy : ∀ time, value time = quittingRootSuccessorPayoff reward
    (value (time + 1)) (quittingRootOfSimplex root)
  endpointNash : ∀ time, IsεQuittingRootEndpointNash reward
    (value (time + 1)) 0 (quittingRootOfSimplex root)
  punishmentTail_mem : punishmentTail ∈ quittingTerminalSemanticCarrier reward
  punishmentCap : punishmentTail.2 punished ≤
    quittingPunishmentValue reward punished

/-- The root sequence represented by one selected family member. -/
def quittingStationaryPrefixFamilyPlan
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward) (index : ℕ) :
    ℕ → ι → PMF Bool :=
  quittingStationaryPrefixThenRoots (family.root index) (family.horizon index)
    (family.punishment index)

/-- The actual terminal continuation vector at every depth of one selected
stationary-prefix witness. -/
def quittingStationaryPrefixFamilyValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward) (index time : ℕ) :
    Payoff ι :=
  quittingRootSequenceTailVector reward
    (quittingStationaryPrefixFamilyPlan family index) time

/-- The compact datum attached to one selected stationary-prefix witness. -/
def quittingStationaryPrefixFamilyRayData
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward) (index : ℕ) :
    QuittingRootSimplex ι ×
      ((ℕ → Payoff ι) × QuittingTerminalSemanticPair ι) :=
  (quittingSimplexOfRoot (family.root index),
    (quittingStationaryPrefixFamilyValue family index,
      quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward (family.punishment index) 0)))

/-- Every selected witness datum belongs to the compact ray carrier. -/
theorem quittingStationaryPrefixFamilyRayData_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward) (index : ℕ) :
    quittingStationaryPrefixFamilyRayData family index ∈
      quittingStationaryPrefixRayCarrier reward := by
  refine ⟨Set.mem_univ _, ?_, subset_closure ⟨_, rfl⟩⟩
  intro time
  exact quittingTerminalPayoff_mem_rewardCube reward
    (quittingRootSequenceProfile reward
      (quittingStationaryPrefixFamilyPlan family index) time)

/-- Before the declared horizon, the selected plan is the repeated root. -/
theorem quittingStationaryPrefixFamilyPlan_eq_root
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward) (index time : ℕ)
    (htime : time ≤ family.horizon index) :
    quittingStationaryPrefixFamilyPlan family index time = family.root index :=
  quittingStationaryPrefixThenRoots_of_le _ _ _ htime

/-- Survival through a fixed part of the repeated prefix is the corresponding
power of its one-stage live mass. -/
theorem quittingJointSurvivalWeight_stationaryPrefixFamilyPlan
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward) (index time : ℕ)
    (htime : time ≤ family.horizon index + 1) :
    quittingJointSurvivalWeight
        (quittingStationaryPrefixFamilyPlan family index) 0 time =
      quittingStationaryContinueMass (family.root index) ^ time := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simp only [zero_add]
  calc
    (∏ offset ∈ Finset.range time,
        quittingStationaryContinueMass
          (quittingStationaryPrefixFamilyPlan family index offset)) =
        ∏ _offset ∈ Finset.range time,
          quittingStationaryContinueMass (family.root index) := by
      apply Finset.prod_congr rfl
      intro offset hoffset
      rw [quittingStationaryPrefixFamilyPlan_eq_root]
      exact Nat.lt_succ_iff.mp ((Finset.mem_range.mp hoffset).trans_le htime)
    _ = quittingStationaryContinueMass (family.root index) ^ time := by simp

/-- A positive-live, divergent-horizon selected family has a structured
two-ended limit whose recorded live mass is the selected source limit.  Exact
local endpoint Nash is obtained by dividing the global Nash error by the
positive reach of each fixed depth. -/
theorem exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (punished : ι) (liveLimit : ℝ)
    (hsubsequence : StrictMono subsequence)
    (hpunished : ∀ n, family.punished (subsequence n) = punished)
    (hlivePositive : 0 < liveLimit)
    (hlive : Tendsto
      (fun n => quittingStationaryContinueMass (family.root (subsequence n)))
      atTop (nhds liveLimit))
    (hhorizon : Tendsto (fun n => family.horizon (subsequence n)) atTop atTop) :
    ∃ limit : QuittingPositiveLiveStationaryPrefixLimit reward,
      limit.liveMass = liveLimit := by
  let data : ℕ → QuittingRootSimplex ι ×
      ((ℕ → Payoff ι) × QuittingTerminalSemanticPair ι) := fun n =>
    quittingStationaryPrefixFamilyRayData family (subsequence n)
  have hdata : ∀ n, data n ∈ quittingStationaryPrefixRayCarrier reward := by
    intro n
    exact quittingStationaryPrefixFamilyRayData_mem family (subsequence n)
  obtain ⟨limit, hlimitMem, limitSubsequence, hlimitSubsequence, hlimit⟩ :=
    (quittingStationaryPrefixRayCarrier_isCompact reward).tendsto_subseq hdata
  have hselected : StrictMono (subsequence ∘ limitSubsequence) :=
    hsubsequence.comp hlimitSubsequence
  have hroot : Tendsto
      (fun n => quittingSimplexOfRoot
        (family.root (subsequence (limitSubsequence n)))) atTop
      (nhds limit.1) := by
    exact (continuous_fst.tendsto limit).comp hlimit
  have hvalue : ∀ time, Tendsto
      (fun n => quittingStationaryPrefixFamilyValue family
        (subsequence (limitSubsequence n)) time) atTop
      (nhds (limit.2.1 time)) := by
    intro time
    exact ((continuous_apply time).tendsto limit.2.1).comp
      ((continuous_fst.tendsto limit.2).comp
        ((continuous_snd.tendsto limit).comp hlimit))
  have hpunishmentTail : Tendsto
      (fun n => quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (family.punishment (subsequence (limitSubsequence n))) 0)) atTop
      (nhds limit.2.2) := by
    exact (continuous_snd.tendsto limit.2).comp
      ((continuous_snd.tendsto limit).comp hlimit)
  have hliveSelected : Tendsto
      (fun n => quittingStationaryContinueMass
        (family.root (subsequence (limitSubsequence n)))) atTop
      (nhds liveLimit) :=
    hlive.comp hlimitSubsequence.tendsto_atTop
  have hliveRoot : quittingStationaryContinueMass
      (quittingRootOfSimplex limit.1) = liveLimit := by
    exact tendsto_nhds_unique
      ((continuous_quittingStationaryContinueMass_simplex.tendsto
        limit.1).comp hroot)
      (by
        have heq :
            (fun n => quittingStationaryContinueMass (quittingRootOfSimplex
              (quittingSimplexOfRoot
                (family.root (subsequence (limitSubsequence n)))))) =
              fun n => quittingStationaryContinueMass
                (family.root (subsequence (limitSubsequence n))) := by
          funext n
          rw [quittingRootOfSimplex_simplexOfRoot]
        change Tendsto
          (fun n => quittingStationaryContinueMass (quittingRootOfSimplex
            (quittingSimplexOfRoot
              (family.root (subsequence (limitSubsequence n))))))
          atTop (nhds liveLimit)
        rw [heq]
        exact hliveSelected)
  have hpolicy : ∀ time, limit.2.1 time =
      quittingRootSuccessorPayoff reward (limit.2.1 (time + 1))
        (quittingRootOfSimplex limit.1) := by
    intro time
    have hhorizonEventually : ∀ᶠ n in atTop,
        time ≤ family.horizon (subsequence (limitSubsequence n)) :=
      (hhorizon.comp hlimitSubsequence.tendsto_atTop).eventually_ge_atTop time
    have hleft := hvalue time
    have hright : Tendsto
        (fun n => quittingRootSuccessorPayoff reward
          (quittingStationaryPrefixFamilyValue family
            (subsequence (limitSubsequence n)) (time + 1))
          (family.root (subsequence (limitSubsequence n)))) atTop
        (nhds (quittingRootSuccessorPayoff reward (limit.2.1 (time + 1))
          (quittingRootOfSimplex limit.1))) := by
      have hpair : Tendsto
          (fun n =>
            (quittingStationaryPrefixFamilyValue family
                (subsequence (limitSubsequence n)) (time + 1),
              quittingSimplexOfRoot
                (family.root (subsequence (limitSubsequence n))))) atTop
          (nhds (limit.2.1 (time + 1), limit.1)) :=
        (hvalue (time + 1)).prodMk_nhds hroot
      have ht := (continuous_quittingRootSuccessorPayoff_simplex reward).tendsto
        (limit.2.1 (time + 1), limit.1) |>.comp hpair
      change Tendsto
        (fun n => quittingRootSuccessorPayoff reward
          (quittingStationaryPrefixFamilyValue family
            (subsequence (limitSubsequence n)) (time + 1))
          (quittingRootOfSimplex (quittingSimplexOfRoot
            (family.root (subsequence (limitSubsequence n)))))) atTop _ at ht
      simpa only [quittingRootOfSimplex_simplexOfRoot] using ht
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [hhorizonEventually] with n hn
    funext who
    symm
    change quittingRootSequenceTerminalValue reward
        (quittingStationaryPrefixFamilyPlan family
          (subsequence (limitSubsequence n))) who time = _
    simpa [quittingStationaryPrefixFamilyValue,
      quittingStationaryPrefixFamilyPlan_eq_root family _ time hn] using
      (quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector reward
        (quittingStationaryPrefixFamilyPlan family
          (subsequence (limitSubsequence n))) who time)
  have hendpoint : ∀ time, IsεQuittingRootEndpointNash reward
      (limit.2.1 (time + 1)) 0 (quittingRootOfSimplex limit.1) := by
    intro time
    let reach : ℕ → ℝ := fun n => quittingJointSurvivalWeight
      (quittingStationaryPrefixFamilyPlan family
        (subsequence (limitSubsequence n))) 0 time
    have hhorizonEventually : ∀ᶠ n in atTop,
        time ≤ family.horizon (subsequence (limitSubsequence n)) :=
      (hhorizon.comp hlimitSubsequence.tendsto_atTop).eventually_ge_atTop time
    have hreach : Tendsto reach atTop (nhds (liveLimit ^ time)) := by
      apply (hliveSelected.pow time).congr'
      filter_upwards [hhorizonEventually] with n hn
      exact (quittingJointSurvivalWeight_stationaryPrefixFamilyPlan
        family _ time (hn.trans (Nat.le_add_right _ 1))).symm
    have hreachPositive : 0 < liveLimit ^ time := pow_pos hlivePositive time
    have hreachEventually : ∀ᶠ n in atTop, 0 < reach n :=
      hreach.eventually (Ioi_mem_nhds hreachPositive)
    let tolerance : ℕ → ℝ := fun n =>
      2 * family.error (subsequence (limitSubsequence n)) / reach n
    have htolerance : Tendsto tolerance atTop (nhds 0) := by
      have herror : Tendsto
          (fun n => 2 * family.error (subsequence (limitSubsequence n)))
          atTop (nhds 0) := by
        simpa only [Function.comp_apply, mul_zero] using
          (tendsto_const_nhds.mul
            (family.error_tendsto_zero.comp hselected.tendsto_atTop) :
              Tendsto
                (fun n => (2 : ℝ) *
                  (family.error ∘ subsequence ∘ limitSubsequence) n)
                atTop (nhds ((2 : ℝ) * 0)))
      have hquotient := herror.div hreach (ne_of_gt hreachPositive)
      change Tendsto
        ((fun n => 2 * family.error (subsequence (limitSubsequence n))) /
          reach) atTop (nhds 0)
      simpa only [zero_div] using hquotient
    apply isεQuittingRootEndpointNash_of_tendsto reward tolerance
      (fun n => quittingStationaryPrefixFamilyValue family
        (subsequence (limitSubsequence n)) (time + 1))
      (fun n => quittingSimplexOfRoot
        (family.root (subsequence (limitSubsequence n))))
      htolerance (hvalue (time + 1)) hroot
    filter_upwards [hhorizonEventually, hreachEventually] with n hn hreachN
    have hnash := isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash
      reward (quittingStationaryPrefixFamilyPlan family
        (subsequence (limitSubsequence n)))
      (family.nash (subsequence (limitSubsequence n))) time hreachN
    rw [quittingStationaryPrefixFamilyPlan_eq_root family _ time (by omega)] at hnash
    simpa [tolerance, reach, quittingStationaryPrefixFamilyValue] using hnash
  have hpunishmentCap : limit.2.2.2 punished ≤
      quittingPunishmentValue reward punished := by
    have hleft : Tendsto
        (fun n => (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward
            (family.punishment (subsequence (limitSubsequence n))) 0)).2
              punished) atTop (nhds (limit.2.2.2 punished)) :=
      ((continuous_apply punished).comp continuous_snd).tendsto limit.2.2 |>.comp
        hpunishmentTail
    have hright : Tendsto
        (fun n => quittingPunishmentValue reward punished +
          family.error (subsequence (limitSubsequence n))) atTop
        (nhds (quittingPunishmentValue reward punished)) := by
      simpa using tendsto_const_nhds.add
        (family.error_tendsto_zero.comp hselected.tendsto_atTop)
    apply le_of_tendsto_of_tendsto hleft hright
    apply Filter.Eventually.of_forall
    intro n
    change quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward
          (family.punishment (subsequence (limitSubsequence n))) 0) punished ≤ _
    rw [quittingContinuationBestResponseValue_eq_bestReplyValue]
    simpa [hpunished (limitSubsequence n)] using
      (isQuittingRootSequencePunishmentWithin_iff_bestReplyValue reward
        (family.punished (subsequence (limitSubsequence n)))
        (family.error (subsequence (limitSubsequence n)))
        (family.punishment (subsequence (limitSubsequence n)))).mp
          (family.punishmentWithin (subsequence (limitSubsequence n)))
  exact ⟨{
    punished := punished
    root := limit.1
    value := limit.2.1
    punishmentTail := limit.2.2
    liveMass := liveLimit
    liveMass_pos := hlivePositive
    liveMass_eq := hliveRoot
    value_mem := hlimitMem.2.1
    policy := hpolicy
    endpointNash := hendpoint
    punishmentTail_mem := hlimitMem.2.2
    punishmentCap := hpunishmentCap
  }, rfl⟩

/-- Target-free projection of
`exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq`. -/
theorem exists_quittingPositiveLiveStationaryPrefixLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (punished : ι) (liveLimit : ℝ)
    (hsubsequence : StrictMono subsequence)
    (hpunished : ∀ n, family.punished (subsequence n) = punished)
    (hlivePositive : 0 < liveLimit)
    (hlive : Tendsto
      (fun n => quittingStationaryContinueMass (family.root (subsequence n)))
      atTop (nhds liveLimit))
    (hhorizon : Tendsto (fun n => family.horizon (subsequence n)) atTop atTop) :
    Nonempty (QuittingPositiveLiveStationaryPrefixLimit reward) := by
  obtain ⟨limit, _⟩ :=
    exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq
      family subsequence punished liveLimit hsubsequence hpunished
        hlivePositive hlive hhorizon
  exact ⟨limit⟩

/-! ## Decoding the limiting root -/

/-- The constant root sequence selected by a positive-live limit. -/
def QuittingPositiveLiveStationaryPrefixLimit.constantRoots
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (limit : QuittingPositiveLiveStationaryPrefixLimit reward) :
    ℕ → ι → PMF Bool :=
  fun _ => quittingRootOfSimplex limit.root

/-- If the limiting root has positive absorption, its bounded Bellman ray is
the actual continuation-value ray of the constant root sequence. -/
theorem QuittingPositiveLiveStationaryPrefixLimit.value_eq_constantRoots
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (limit : QuittingPositiveLiveStationaryPrefixLimit reward)
    (habsorbs : limit.liveMass < 1) (time : ℕ) :
    limit.value time = fun who => quittingRootSequenceTerminalValue reward
      limit.constantRoots who time := by
  let charge := 1 - limit.liveMass
  have hcharge : 0 < charge := sub_pos.mpr habsorbs
  apply eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_absorption_lower
    reward limit.constantRoots limit.value hcharge
  · intro stage
    unfold quittingRootAbsorptionMass
    change charge ≤ 1 - quittingStationaryContinueMass
      (quittingRootOfSimplex limit.root)
    rw [limit.liveMass_eq]
  · exact abs_reward_le_quittingRewardBound reward
  · intro stage who
    exact abs_le.mpr
      ⟨(limit.value_mem stage).1 who, (limit.value_mem stage).2 who⟩
  · exact limit.policy

/-- A positive-absorption limiting root gives a completely absorbing constant
root sequence with exact support-local optimality. -/
theorem QuittingPositiveLiveStationaryPrefixLimit.wellSupported_of_lt_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (limit : QuittingPositiveLiveStationaryPrefixLimit reward)
    (habsorbs : limit.liveMass < 1) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  let roots := limit.constantRoots
  have hcomplete : IsCompletelyAbsorbing roots := by
    have hlive0 : 0 ≤ limit.liveMass := limit.liveMass_pos.le
    have heq : quittingSurvivalPrefix roots = fun horizon => limit.liveMass ^ horizon := by
      funext horizon
      unfold quittingSurvivalPrefix roots
      simp only [QuittingPositiveLiveStationaryPrefixLimit.constantRoots,
        Finset.prod_const, Finset.card_range]
      rw [limit.liveMass_eq]
    unfold IsCompletelyAbsorbing
    rw [heq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hlive0 habsorbs
  have hexact : IsQuittingRootSequenceSupportApproxNash reward roots 0 := by
    intro time
    have htail : quittingRootSequenceTailVector reward roots (time + 1) =
        limit.value (time + 1) := by
      funext who
      exact (congrFun (limit.value_eq_constantRoots habsorbs (time + 1)) who).symm
    rw [htail]
    intro who
    have hendpoint := limit.endpointNash time who
    simp only [neg_zero] at hendpoint
    constructor
    · intro hquit
      change 0 < ((quittingRootOfSimplex limit.root who) true).toReal at hquit
      change -0 ≤ quittingRootEndpointDifference reward
        (limit.value (time + 1)) (quittingRootOfSimplex limit.root) who
      nlinarith [hendpoint.2]
    · intro hcontinue
      change 0 < ((quittingRootOfSimplex limit.root who) false).toReal at hcontinue
      change quittingRootEndpointDifference reward
        (limit.value (time + 1)) (quittingRootOfSimplex limit.root) who ≤ 0
      nlinarith [hendpoint.1]
  intro error herror
  exact ⟨roots, hcomplete, hexact.mono herror.le⟩

/-- The exact residual at unit limiting live mass.  The forward root is pure
Continue and its bounded Bellman continuation ray is constant.  The actual
punishment-tail semantic pair and cap remain present in `limit`, but the
finite prefixes supply no closed bridge between the two ends. -/
def IsQuittingAllContinuePhantomStationaryPrefixLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (limit : QuittingPositiveLiveStationaryPrefixLimit reward) : Prop :=
  limit.liveMass = 1 ∧
    quittingRootOfSimplex limit.root =
      (quittingAllContinueRoot : ι → PMF Bool) ∧
    ∀ time, limit.value time = limit.value 0

/-- Unit live mass forces the precise all-Continue phantom-boundary
residual. -/
theorem QuittingPositiveLiveStationaryPrefixLimit.isAllContinuePhantom_of_eq_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (limit : QuittingPositiveLiveStationaryPrefixLimit reward)
    (hlive : limit.liveMass = 1) :
    IsQuittingAllContinuePhantomStationaryPrefixLimit limit := by
  have hrootMass : quittingStationaryContinueMass
      (quittingRootOfSimplex limit.root) = 1 := limit.liveMass_eq.trans hlive
  have hroot : quittingRootOfSimplex limit.root =
      (quittingAllContinueRoot : ι → PMF Bool) := by
    funext who
    simpa [quittingAllContinueRoot] using
      (eq_pure_false_of_quittingStationaryContinueMass_eq_one hrootMass who)
  refine ⟨hlive, hroot, ?_⟩
  intro time
  induction time with
  | zero => rfl
  | succ time ih =>
      have hstep := limit.policy time
      rw [hroot, quittingRootSuccessorPayoff_allContinueRoot_eq] at hstep
      exact hstep.symm.trans ih

/-- Every positive-live stationary-prefix limit either produces branch `S.3`
or is exactly the all-Continue phantom-boundary residual.  This is the
strongest closed dichotomy available from the forward fixed-depth data while
retaining the punishment tail at the escaping end. -/
theorem QuittingPositiveLiveStationaryPrefixLimit.wellSupported_or_phantom
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (limit : QuittingPositiveLiveStationaryPrefixLimit reward) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      IsQuittingAllContinuePhantomStationaryPrefixLimit limit := by
  rcases lt_or_eq_of_le (quittingStationaryContinueMass_le_one
    (quittingRootOfSimplex limit.root)) with habsorbs | hlive
  · exact Or.inl (limit.wellSupported_of_lt_one
      (by rwa [limit.liveMass_eq] at habsorbs))
  · exact Or.inr (limit.isAllContinuePhantom_of_eq_one
      (by rwa [limit.liveMass_eq] at hlive))

/-- The phantom continuation vector dominates every singleton quitting
reward.  This is exactly what survives from local Nash at the all-Continue
face; it does not identify the phantom vector with the literal all-Continue
terminal payoff `0`. -/
theorem QuittingPositiveLiveStationaryPrefixLimit.singleton_le_value_zero_of_phantom
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (limit : QuittingPositiveLiveStationaryPrefixLimit reward)
    (hphantom : IsQuittingAllContinuePhantomStationaryPrefixLimit limit)
    (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ limit.value 0 who := by
  have hendpoint := (limit.endpointNash 0 who).1
  rw [hphantom.2.1, quittingRootEndpointDifference_allContinueRoot,
    hphantom.2.2 1] at hendpoint
  simpa [quittingAllContinueRoot] using hendpoint

/-- The positive-live, divergent-horizon regime has one exact outcome: a
well-supported completely absorbing sequence, or a structured all-Continue
phantom limit retaining the actual punishment-tail cap. -/
theorem wellSupported_or_exists_allContinuePhantom_of_stationaryPrefix_family
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (punished : ι) (liveLimit : ℝ)
    (hsubsequence : StrictMono subsequence)
    (hpunished : ∀ n, family.punished (subsequence n) = punished)
    (hlivePositive : 0 < liveLimit)
    (hlive : Tendsto
      (fun n => quittingStationaryContinueMass (family.root (subsequence n)))
      atTop (nhds liveLimit))
    (hhorizon : Tendsto (fun n => family.horizon (subsequence n)) atTop atTop) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      ∃ limit : QuittingPositiveLiveStationaryPrefixLimit reward,
        IsQuittingAllContinuePhantomStationaryPrefixLimit limit := by
  let limit := Classical.choice
    (exists_quittingPositiveLiveStationaryPrefixLimit family subsequence
      punished liveLimit hsubsequence hpunished hlivePositive hlive hhorizon)
  rcases limit.wellSupported_or_phantom with hwellSupported | hphantom
  · exact Or.inl hwellSupported
  · exact Or.inr ⟨limit, hphantom⟩

/-! ## The escaping endpoint is realizable but not anchored -/

/-- The retained punishment endpoint is not merely a formal closure point:
it is the limit of actual behavioral terminal semantic pairs, and its
best-response coordinate keeps the exact punishment cap. -/
theorem QuittingPositiveLiveStationaryPrefixLimit.exists_punishmentTail_realizers
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (limit : QuittingPositiveLiveStationaryPrefixLimit reward) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (nhds limit.punishmentTail) ∧
      limit.punishmentTail.2 limit.punished ≤
        quittingPunishmentValue reward limit.punished := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward
      limit.punishmentTail limit.punishmentTail_mem
  exact ⟨profiles, hprofiles, limit.punishmentCap⟩

namespace StationaryPrefixEndpointDecouplingRegression

/-- The one-player unit quitting table used to separate the two retained
endpoints. -/
def reward : {S : Finset PUnit // S.Nonempty} → Payoff PUnit :=
  fun _ _ => 1

private theorem terminal_unique
    (first second : {S : Finset PUnit // S.Nonempty}) : first = second := by
  apply Subtype.ext
  ext player
  constructor
  · intro _
    obtain ⟨witness, hwitness⟩ := second.property
    simpa [Subsingleton.elim witness player] using hwitness
  · intro _
    obtain ⟨witness, hwitness⟩ := first.property
    simpa [Subsingleton.elim witness player] using hwitness

/-- The canonical bound of the one-player unit table is exactly one. -/
theorem rewardBound_eq_one : quittingRewardBound reward = 1 := by
  unfold quittingRewardBound
  simp only [reward, abs_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_punit, Nat.cast_one, mul_one]
  have hcard : Fintype.card {S : Finset PUnit // S.Nonempty} = 1 :=
    Fintype.card_eq_one_iff.mpr
      ⟨⟨{PUnit.unit}, Finset.singleton_nonempty PUnit.unit⟩,
        fun terminal => terminal_unique terminal _⟩
  exact_mod_cast hcard

/-- In the one-player unit table the exact punishment value is one. -/
theorem punishmentValue_eq_one :
    quittingPunishmentValue reward PUnit.unit = 1 := by
  apply le_antisymm
  · have hupper := quittingPunishmentValue_le_max_solo reward PUnit.unit
    simpa [reward, QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty]
      using hupper
  · unfold quittingPunishmentValue
    letI : Nonempty (quittingGame reward).BehaviorProfile :=
      ⟨quittingAlwaysContinueProfile reward⟩
    apply le_ciInf
    intro profile
    unfold quittingBestReplyValue
    let deviation : (quittingGame reward).BehaviorStrategy PUnit.unit :=
      quittingPureTimeBehaviorStrategy reward PUnit.unit (some 0)
    have hreply := le_ciSup
      (bddAbove_range_quittingTerminalPayoff_update reward profile PUnit.unit)
      deviation
    have hvalue : quittingTerminalPayoff reward
        (Function.update profile PUnit.unit deviation) PUnit.unit = 1 := by
      rw [show deviation = quittingPureTimeBehaviorStrategy reward
        PUnit.unit (some 0) by rfl,
        quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
      unfold quittingStationaryFixedOpponentsQuitValue
        quittingFixedOpponentsQuitValue
      have hroot : Function.update
          (quittingProfileLiveRoot reward profile 0) PUnit.unit (PMF.pure true) =
          QuittingSureSetOwnerRepair.quittingPureSetRoot {PUnit.unit} := by
        funext player
        cases player
        simp [QuittingSureSetOwnerRepair.quittingPureSetRoot,
          QuittingSureSetOwnerRepair.quittingSetAction]
      rw [hroot,
        QuittingSureSetOwnerRepair.quittingRootAbsorbingContribution_pureSetRoot]
      simp [reward,
        QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty]
    rw [hvalue] at hreply
    exact hreply

/-- The exact all-Continue punishment endpoint.  Its prescribed value is
zero, while its best-response envelope is capped by the unit punishment
value. -/
def punishmentTail : QuittingTerminalSemanticPair PUnit :=
  quittingTerminalSemanticPair reward (quittingAlwaysContinueProfile reward)

/-- The forward phantom value is the constant unit payoff. -/
def value : ℕ → Payoff PUnit := fun _ _ => 1

/-- The all-Continue phantom datum with its actual all-Continue punishment
endpoint. -/
def limit : QuittingPositiveLiveStationaryPrefixLimit reward where
  punished := PUnit.unit
  root := quittingSimplexOfRoot
    (quittingAllContinueRoot : PUnit → PMF Bool)
  value := value
  punishmentTail := punishmentTail
  liveMass := 1
  liveMass_pos := by norm_num
  liveMass_eq := by
    rw [quittingRootOfSimplex_simplexOfRoot,
      quittingStationaryContinueMass_eq_prod_continueProbability]
    simp [quittingAllContinueRoot]
  value_mem := by
    intro time
    constructor <;> intro who
    · have hbound := abs_reward_le_quittingRewardBound reward
        ⟨{PUnit.unit}, Finset.singleton_nonempty PUnit.unit⟩ PUnit.unit
      simpa [value, reward] using (neg_le_of_abs_le hbound)
    · have hbound := abs_reward_le_quittingRewardBound reward
        ⟨{PUnit.unit}, Finset.singleton_nonempty PUnit.unit⟩ PUnit.unit
      simpa [value, reward] using (le_of_abs_le hbound)
  policy := by
    intro time
    rw [quittingRootOfSimplex_simplexOfRoot,
      quittingRootSuccessorPayoff_allContinueRoot_eq]
    rfl
  endpointNash := by
    intro time
    rw [quittingRootOfSimplex_simplexOfRoot]
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (value (time + 1)) quittingAllContinueRoot).2
    apply quittingAllContinueRoot_isZeroNash_of_singleton_le
    intro who
    simp [reward, value]
  punishmentTail_mem := by
    exact subset_closure ⟨quittingAlwaysContinueProfile reward, rfl⟩
  punishmentCap := by
    change quittingContinuationBestResponseValue reward
      (quittingAlwaysContinueProfile reward) PUnit.unit ≤ _
    rw [quittingContinuationBestResponseValue_eq_bestReplyValue,
      punishmentValue_eq_one]
    apply quittingBestReplyValue_le
    intro deviation
    exact (le_of_abs_le (abs_quittingTerminalPayoff_le reward _ PUnit.unit
      (abs_reward_le_quittingRewardBound reward))).trans
        (le_of_eq rewardBound_eq_one)

/-- The regression is genuinely in the phantom residual. -/
theorem limit_isPhantom :
    IsQuittingAllContinuePhantomStationaryPrefixLimit limit := by
  apply limit.isAllContinuePhantom_of_eq_one
  rfl

/-- The forward phantom value and the prescribed punishment endpoint are
different, even though the latter is an actual semantic pair and satisfies
the exact punishment cap. -/
theorem forward_value_ne_punishment_prescribed :
    limit.value 0 ≠ limit.punishmentTail.1 := by
  intro heq
  have hcoordinate := congrFun heq PUnit.unit
  change (1 : ℝ) = quittingTerminalPayoff reward
    (quittingAlwaysContinueProfile reward) PUnit.unit at hcoordinate
  rw [quittingTerminalPayoff_quittingAlwaysContinue] at hcoordinate
  norm_num at hcoordinate

end StationaryPrefixEndpointDecouplingRegression

end GameTheory
