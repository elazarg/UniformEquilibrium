/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CounterexampleAtomEndpointRisePassport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetFaceReprojection
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCommonSuffixCurvatureRegression
import UniformEquilibrium.Quitting.RewardBound

/-!
# Endpoint return versus reset-face separation

This experiment compactifies the actual fixed-label atom endpoints.  For the
rectangle branch, the observer response already has vanishing own debt, so
its cluster lies on an exact reset face and feeds the existing reset-face
return/all-Continue-cap consumer.

For the prescribed branch, the mover endpoint need not lie on that face.
Its limiting mover debt is exactly

`d_p(base) + tangent(p,p)`,

which the current half-best-response construction bounds only between zero
and `d_p(base) / 2`.  Thus endpoint separation has a named consumer exactly
when this residual vanishes.  A strictly positive residual is the sharp
missing premise: surface tension and reprojection are face theorems, and the
common-suffix curvature regression forbids replacing face membership by
small debt-height excess alone.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- On the mover coordinate, the normalized stopping-law direction is
exactly the full endpoint debt change. -/
theorem stoppingLawNormalizedDebtDirection_self_eq_endpointDebtChange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hlambda : 0 < lambda) :
    quittingStoppingLawNormalizedDebtDirection reward profile mover target
        lambda hlambda0 hlambda1 mover =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) mover -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover := by
  have hself := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
    reward profile mover (profile mover) target lambda hlambda0 hlambda1
  rw [Function.update_eq_self] at hself
  unfold quittingStoppingLawNormalizedDebtDirection
    quittingStoppingLawResetProfile quittingTerminalSemanticDebtChange
  rw [hself]
  field_simp
  ring

/-- The named semantic consumer supplied by an exact reset point: minimize
on the same reset face.  The result either returns to the global minimum
fiber or is an off-minimum point whose only exact cap--Nash root is
all-Continue. -/
def HasQuittingResetFaceReturnOrAllContinueSeparation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι) (owner : ι) : Prop :=
  ∃ returned : QuittingTerminalSemanticPair ι,
    returned ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt returned owner = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned ∧
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum target ∧
      (quittingTerminalSemanticDebtSum returned =
          quittingTerminalSemanticDebtSum source ∨
        quittingTerminalSemanticDebtSum source <
          quittingTerminalSemanticDebtSum returned) ∧
      IsεQuittingRootNash reward returned.2 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot returned =
        returned ∧
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.2 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool)

/-- Adapter from the production reset-face selector to the focused consumer
used below. -/
theorem hasQuittingResetFaceReturnOrAllContinueSeparation_of_reset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι) (owner : ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0) :
    HasQuittingResetFaceReturnOrAllContinueSeparation reward source target
      owner := by
  obtain ⟨M, hM, hreward⟩ :=
    exists_quittingRewardBound reward
  obtain ⟨returned, hreturned, hreturnedReset, hsourceLe, hreturnedLe,
      _htransferIdentity, _htransfer, hfiber, hnash, hfixed, hallRoots⟩ :=
    exists_resetFace_minimizer_with_unique_allContinue_capNash
      (reward := reward) source target owner hM hreward hminimum
        hsourcePositive htarget hreset
  exact ⟨returned, hreturned, hreturnedReset, hsourceLe, hreturnedLe,
    hfiber, hnash, hfixed, hallRoots⟩

/-! ## Prescribed endpoint cluster -/

/-- Compact limit of the actual prescribed mover endpoints, retaining the
fixed mover, observer, charge, terminal label, and rank subsequence through
the underlying sequence. -/
structure QuittingPrescribedAtomEndpointCluster
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawPrescribedAtomEndpointRiseSequence packet)
    where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  cluster : QuittingTerminalSemanticPair ι
  cluster_mem : cluster ∈ quittingTerminalSemanticCarrier reward
  endpoint_tendsto : Tendsto (fun n =>
    let profile := frontier.profiles
      (frontier.subseq (sequence.rank (subseq n)))
    quittingTerminalSemanticPair reward
      (Function.update profile packet.chronology.mover.1
        (frontier.bestResponse packet.chronology.mover
          (frontier.subseq (sequence.rank (subseq n))))))
    atTop (nhds cluster)
  observer_rise : packet.chronology.charge ≤
    quittingTerminalSemanticDebt cluster packet.chronology.observer -
      quittingTerminalSemanticDebt frontier.base packet.chronology.observer
  mover_debt_eq : quittingTerminalSemanticDebt cluster
      packet.chronology.mover.1 =
    quittingTerminalSemanticDebt frontier.base packet.chronology.mover.1 +
      frontier.tangent packet.chronology.mover
        packet.chronology.mover.1
  mover_debt_nonneg : 0 ≤ quittingTerminalSemanticDebt cluster
    packet.chronology.mover.1
  mover_debt_le_half : quittingTerminalSemanticDebt cluster
      packet.chronology.mover.1 ≤
    quittingTerminalSemanticDebt frontier.base
      packet.chronology.mover.1 / 2
  fiber_or_separated :
    quittingTerminalSemanticDebtSum cluster =
        quittingTerminalSemanticDebtSum frontier.base ∨
      quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum cluster

/-- Extract the endpoint cluster and identify its exact residual mover debt.
The fixed atom and exact stack remain available at every `sequence.rank
(cluster.subseq n)`. -/
theorem QuittingStoppingLawPrescribedAtomEndpointRiseSequence.nonempty_endpointCluster
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawPrescribedAtomEndpointRiseSequence packet) :
    Nonempty (QuittingPrescribedAtomEndpointCluster sequence) := by
  let endpoint : ℕ → QuittingTerminalSemanticPair ι := fun n =>
    let profile := frontier.profiles (frontier.subseq (sequence.rank n))
    quittingTerminalSemanticPair reward
      (Function.update profile packet.chronology.mover.1
        (frontier.bestResponse packet.chronology.mover
          (frontier.subseq (sequence.rank n))))
  have hendpointMem : ∀ n,
      endpoint n ∈ quittingTerminalSemanticCarrier reward := by
    intro n
    exact quittingTerminalSemanticPair_mem_carrier reward _
  obtain ⟨cluster, hcluster, subseq, hsubseq, hendpoint⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)).tendsto_subseq hendpointMem
  have hsource : Tendsto (fun n => quittingTerminalSemanticPair reward
      (frontier.profiles
        (frontier.subseq (sequence.rank (subseq n))))) atTop
      (nhds frontier.base) := by
    exact frontier.profiles_tendsto.comp
      ((frontier.subseq_strictMono.comp
        (sequence.rank_strictMono.comp hsubseq)).tendsto_atTop)
  have hobserverEndpoint :=
    (continuous_quittingTerminalSemanticDebt packet.chronology.observer).tendsto
      cluster |>.comp hendpoint
  have hobserverSource :=
    (continuous_quittingTerminalSemanticDebt packet.chronology.observer).tendsto
      frontier.base |>.comp hsource
  have hobserverDifference : Tendsto (fun n =>
      quittingTerminalSemanticDebt (endpoint (subseq n))
          packet.chronology.observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles
              (frontier.subseq (sequence.rank (subseq n)))))
          packet.chronology.observer) atTop
      (nhds (quittingTerminalSemanticDebt cluster
          packet.chronology.observer -
        quittingTerminalSemanticDebt frontier.base
          packet.chronology.observer)) :=
    hobserverEndpoint.sub hobserverSource
  have hobserverRise : packet.chronology.charge ≤
      quittingTerminalSemanticDebt cluster packet.chronology.observer -
        quittingTerminalSemanticDebt frontier.base
          packet.chronology.observer := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hobserverDifference
    exact Eventually.of_forall fun n => by
      simpa only [endpoint] using sequence.endpointDebtRise (subseq n)
  let direction : ℕ → ℝ := fun n =>
    quittingStoppingLawNormalizedDebtDirection reward
      (frontier.profiles (frontier.subseq (sequence.rank n)))
      packet.chronology.mover.1
      (frontier.bestResponse packet.chronology.mover
        (frontier.subseq (sequence.rank n)))
      (frontier.lambda (frontier.subseq (sequence.rank n)))
      (frontier.lambda_pos
        (frontier.subseq (sequence.rank n))).le
      (frontier.lambda_le_one
        (frontier.subseq (sequence.rank n)))
      packet.chronology.mover.1
  have hdirection : Tendsto (fun n => direction (subseq n)) atTop
      (nhds (frontier.tangent packet.chronology.mover
        packet.chronology.mover.1)) := by
    exact (frontier.tangent_tendsto packet.chronology.mover
      packet.chronology.mover.1).comp
        (sequence.rank_strictMono.comp hsubseq).tendsto_atTop
  have hsourceMover :=
    (continuous_quittingTerminalSemanticDebt
      packet.chronology.mover.1).tendsto frontier.base |>.comp hsource
  have hendpointMover :=
    (continuous_quittingTerminalSemanticDebt
      packet.chronology.mover.1).tendsto cluster |>.comp hendpoint
  have hendpointMover' : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (endpoint (subseq n)) packet.chronology.mover.1) atTop
      (nhds (quittingTerminalSemanticDebt frontier.base
          packet.chronology.mover.1 +
        frontier.tangent packet.chronology.mover
          packet.chronology.mover.1)) := by
    have hsum := hsourceMover.add hdirection
    apply hsum.congr'
    apply Eventually.of_forall
    intro n
    change quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles
              (frontier.subseq (sequence.rank (subseq n)))))
          packet.chronology.mover.1 + direction (subseq n) =
        quittingTerminalSemanticDebt (endpoint (subseq n))
          packet.chronology.mover.1
    dsimp only [direction, endpoint]
    rw [stoppingLawNormalizedDebtDirection_self_eq_endpointDebtChange]
    · ring
    · exact frontier.lambda_pos
        (frontier.subseq (sequence.rank (subseq n)))
  have hmoverEq : quittingTerminalSemanticDebt cluster
      packet.chronology.mover.1 =
      quittingTerminalSemanticDebt frontier.base
          packet.chronology.mover.1 +
        frontier.tangent packet.chronology.mover
          packet.chronology.mover.1 :=
    tendsto_nhds_unique hendpointMover hendpointMover'
  have hmoverNonneg : 0 ≤ quittingTerminalSemanticDebt cluster
      packet.chronology.mover.1 :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hcluster _
  have hmoverLe : quittingTerminalSemanticDebt cluster
        packet.chronology.mover.1 ≤
      quittingTerminalSemanticDebt frontier.base
        packet.chronology.mover.1 / 2 := by
    have hdiag := frontier.tangent_diagonal packet.chronology.mover
    rw [hmoverEq]
    linarith
  have hbaseLe := frontier.base_minimum cluster hcluster
  have hfiber := hbaseLe.eq_or_lt.imp Eq.symm id
  exact ⟨⟨subseq, hsubseq, cluster, hcluster, hendpoint, hobserverRise,
    hmoverEq, hmoverNonneg, hmoverLe, hfiber⟩⟩

/-- The prescribed endpoint has an exhaustive return/separation verdict.
If its limiting mover debt vanishes, the existing reset-face consumer
applies.  Otherwise the strictly positive residual is exactly why neither
surface tension nor reset reprojection is available. -/
theorem QuittingPrescribedAtomEndpointCluster.return_or_resetFaceConsumer_or_positiveResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    {sequence : QuittingStoppingLawPrescribedAtomEndpointRiseSequence packet}
    (cluster : QuittingPrescribedAtomEndpointCluster sequence) :
    quittingTerminalSemanticDebtSum cluster.cluster =
        quittingTerminalSemanticDebtSum frontier.base ∨
      quittingTerminalSemanticDebtSum frontier.base <
          quittingTerminalSemanticDebtSum cluster.cluster ∧
        (HasQuittingResetFaceReturnOrAllContinueSeparation reward
            frontier.base cluster.cluster packet.chronology.mover.1 ∨
          0 < quittingTerminalSemanticDebt cluster.cluster
            packet.chronology.mover.1) := by
  rcases cluster.fiber_or_separated with hreturn | hseparated
  · exact Or.inl hreturn
  · right
    refine ⟨hseparated, ?_⟩
    by_cases hreset : quittingTerminalSemanticDebt cluster.cluster
        packet.chronology.mover.1 = 0
    · left
      exact hasQuittingResetFaceReturnOrAllContinueSeparation_of_reset
        reward frontier.base cluster.cluster packet.chronology.mover.1
        frontier.base_minimum
        frontier.base_positive cluster.cluster_mem hreset
    · exact Or.inr (lt_of_le_of_ne cluster.mover_debt_nonneg
        (Ne.symm hreset))

/-! ## Rectangle double-endpoint cluster -/

/-- Literal double endpoint from the enriched rectangle sequence. -/
def quittingRectangleDoubleEndpointProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  let profile := frontier.profiles (frontier.subseq (sequence.rank n))
  Function.update
    (Function.update profile packet.chronology.mover.1
      (frontier.bestResponse packet.chronology.mover
        (frontier.subseq (sequence.rank n))))
    packet.chronology.observer
    (quittingPureTimeBehaviorStrategy reward packet.chronology.observer
      (sequence.quitTime n))

/-- The optional rectangle response compactifies to an exact observer-reset
point, with all fixed labels and atom bounds retained along the selected
subsequence. -/
structure QuittingRectangleDoubleEndpointCluster
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet) where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  cluster : QuittingTerminalSemanticPair ι
  cluster_mem : cluster ∈ quittingTerminalSemanticCarrier reward
  endpoint_tendsto : Tendsto (fun n =>
    quittingTerminalSemanticPair reward
      (quittingRectangleDoubleEndpointProfile sequence (subseq n)))
    atTop (nhds cluster)
  observer_reset : quittingTerminalSemanticDebt cluster
    packet.chronology.observer = 0
  fiber_or_separated :
    quittingTerminalSemanticDebtSum cluster =
        quittingTerminalSemanticDebtSum frontier.base ∨
      quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum cluster

/-- Extract the exact double-endpoint reset cluster. -/
theorem QuittingStoppingLawRectangleEndpointRiseSequence.nonempty_doubleEndpointCluster
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet) :
    Nonempty (QuittingRectangleDoubleEndpointCluster sequence) := by
  let endpoint : ℕ → QuittingTerminalSemanticPair ι := fun n =>
    quittingTerminalSemanticPair reward
      (quittingRectangleDoubleEndpointProfile sequence n)
  have hendpointMem : ∀ n,
      endpoint n ∈ quittingTerminalSemanticCarrier reward := by
    intro n
    exact quittingTerminalSemanticPair_mem_carrier reward _
  obtain ⟨cluster, hcluster, subseq, hsubseq, hendpoint⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)).tendsto_subseq hendpointMem
  have hdebtCluster :=
    (continuous_quittingTerminalSemanticDebt
      packet.chronology.observer).tendsto cluster |>.comp hendpoint
  have hdebtZero := sequence.observer_debt_tendsto_zero.comp
    hsubseq.tendsto_atTop
  change Tendsto (fun n => quittingTerminalSemanticDebt
      (endpoint (subseq n)) packet.chronology.observer) atTop (nhds 0) at hdebtZero
  have hreset : quittingTerminalSemanticDebt cluster
      packet.chronology.observer = 0 := by
    change Tendsto (fun n => quittingTerminalSemanticDebt
      (endpoint (subseq n)) packet.chronology.observer) atTop
      (nhds (quittingTerminalSemanticDebt cluster
        packet.chronology.observer)) at hdebtCluster
    exact tendsto_nhds_unique hdebtCluster hdebtZero
  have hbaseLe := frontier.base_minimum cluster hcluster
  have hfiber := hbaseLe.eq_or_lt.imp Eq.symm id
  exact ⟨⟨subseq, hsubseq, cluster, hcluster, hendpoint, hreset, hfiber⟩⟩

/-- Unlike the prescribed endpoint, every double-endpoint cluster feeds the
named reset-face return/all-Continue separation consumer unconditionally. -/
theorem QuittingRectangleDoubleEndpointCluster.has_resetFaceConsumer
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    {sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet}
    (cluster : QuittingRectangleDoubleEndpointCluster sequence) :
    HasQuittingResetFaceReturnOrAllContinueSeparation reward frontier.base
      cluster.cluster packet.chronology.observer :=
  hasQuittingResetFaceReturnOrAllContinueSeparation_of_reset reward
    frontier.base cluster.cluster packet.chronology.observer
    frontier.base_minimum
    frontier.base_positive cluster.cluster_mem cluster.observer_reset

end GameTheory
