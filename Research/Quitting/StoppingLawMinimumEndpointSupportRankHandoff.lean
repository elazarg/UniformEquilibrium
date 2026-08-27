/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.PositiveMinimumDebtTangentFamily
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawDebtConvexity

/-!
# Support-rank handoff from a minimum stopping-law endpoint

Two actual profile sequences which differ only in one player's complete
strategy provide an actual half stopping-law mixture at every index.  If the
source debts converge to a positive global minimum, the source mover debt has
a positive limit, and the endpoint kills that debt, joint compactness gives
an exact dichotomy.  An off-minimum endpoint is retained as such.  A minimum
endpoint instead has a half-mixture minimum whose debt support is the union
of the endpoint supports, and hence strictly contains the killed endpoint's
support.  The existing tangent-family extractor and re-extractor consume this
fresh comparison.

This is a one-time handoff relative to the new half-mixture parent.  It does
not assert a renewable rank decrease from the incoming source.
-/

noncomputable section

namespace GameTheory

open Filter Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal half mixture of the two complete stopping laws of `mover`.
The endpoint profiles are required to have the same opponents only when this
profile is compared with them. -/
def quittingHalfStoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) (mover : ι) :
    (quittingGame reward).BehaviorProfile :=
  Function.update source mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (source mover) (target mover) (1 / 2 : ℝ) (by norm_num) (by norm_num))

theorem update_source_with_target_mover_eq_target
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) (mover : ι)
    (hopponents : ∀ other, other ≠ mover → target other = source other) :
    Function.update source mover (target mover) = target := by
  funext other
  by_cases hother : other = mover
  · subst other
    simp
  · rw [Function.update_of_ne hother]
    exact (hopponents other hother).symm

/-- Coordinatewise debt convexity of the actual half profile. -/
theorem quittingTerminalSemanticDebt_halfStoppingLawProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) (mover observer : ι)
    (hopponents : ∀ other, other ≠ mover → target other = source other) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingHalfStoppingLawProfile reward source target mover)) observer ≤
      (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward source) observer +
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward target) observer) / 2 := by
  have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward source mover observer (source mover) (target mover)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)
  rw [Function.update_eq_self,
    update_source_with_target_mover_eq_target reward source target mover
      hopponents]
    at hconvex
  unfold quittingHalfStoppingLawProfile
  convert hconvex using 1
  ring

/-- A same-minimum endpoint, its exact union-support half parent, and the
checked one-time tangent-family re-extraction from that parent. -/
structure QuittingMinimumEndpointSupportRankHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (sourceProfiles targetProfiles : ℕ →
      (quittingGame reward).BehaviorProfile)
    (mover : ι) where
  sourceCluster : QuittingTerminalSemanticPair ι
  endpointCluster : QuittingTerminalSemanticPair ι
  halfCluster : QuittingTerminalSemanticPair ι
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  source_tendsto : Tendsto (fun rank ↦
    quittingTerminalSemanticPair reward (sourceProfiles (subsequence rank)))
      atTop (nhds sourceCluster)
  endpoint_tendsto : Tendsto (fun rank ↦
    quittingTerminalSemanticPair reward (targetProfiles (subsequence rank)))
      atTop (nhds endpointCluster)
  half_tendsto : Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
    (quittingHalfStoppingLawProfile reward
      (sourceProfiles (subsequence rank))
      (targetProfiles (subsequence rank)) mover)) atTop (nhds halfCluster)
  source_mem : sourceCluster ∈ quittingTerminalSemanticCarrier reward
  endpoint_mem : endpointCluster ∈ quittingTerminalSemanticCarrier reward
  half_mem : halfCluster ∈ quittingTerminalSemanticCarrier reward
  source_debtSum_eq_minimum : quittingTerminalSemanticDebtSum sourceCluster =
    quittingTerminalSemanticDebtSum minimum
  endpoint_debtSum_eq_minimum : quittingTerminalSemanticDebtSum endpointCluster =
    quittingTerminalSemanticDebtSum minimum
  half_debtSum_eq_minimum : quittingTerminalSemanticDebtSum halfCluster =
    quittingTerminalSemanticDebtSum minimum
  half_debt_eq_average : ∀ who,
    quittingTerminalSemanticDebt halfCluster who =
      (quittingTerminalSemanticDebt sourceCluster who +
        quittingTerminalSemanticDebt endpointCluster who) / 2
  half_support_eq_union : quittingPositiveDebtSupport halfCluster =
    quittingPositiveDebtSupport sourceCluster ∪
      quittingPositiveDebtSupport endpointCluster
  source_moverDebt_pos : 0 < quittingTerminalSemanticDebt sourceCluster mover
  endpoint_moverDebt_eq_zero :
    quittingTerminalSemanticDebt endpointCluster mover = 0
  endpoint_support_ssubset_half :
    quittingPositiveDebtSupport endpointCluster ⊂
      quittingPositiveDebtSupport halfCluster
  parentFamily : QuittingPositiveMinimumDebtTangentFamily reward
  parentFamily_base_eq : parentFamily.base = halfCluster
  nextFamily : QuittingPositiveMinimumDebtTangentFamily reward
  nextFamily_base_eq : nextFamily.base = endpointCluster
  next_support_ssubset_parent :
    nextFamily.positiveDebtSupport ⊂ parentFamily.positiveDebtSupport

/-- The alternative in which the selected endpoint cluster remains strictly
above the positive global minimum. -/
structure QuittingMinimumEndpointDebtAscent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (sourceProfiles targetProfiles : ℕ →
      (quittingGame reward).BehaviorProfile)
    (mover : ι) where
  sourceCluster : QuittingTerminalSemanticPair ι
  endpointCluster : QuittingTerminalSemanticPair ι
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  source_tendsto : Tendsto (fun rank ↦
    quittingTerminalSemanticPair reward (sourceProfiles (subsequence rank)))
      atTop (nhds sourceCluster)
  endpoint_tendsto : Tendsto (fun rank ↦
    quittingTerminalSemanticPair reward (targetProfiles (subsequence rank)))
      atTop (nhds endpointCluster)
  source_mem : sourceCluster ∈ quittingTerminalSemanticCarrier reward
  endpoint_mem : endpointCluster ∈ quittingTerminalSemanticCarrier reward
  source_debtSum_eq_minimum : quittingTerminalSemanticDebtSum sourceCluster =
    quittingTerminalSemanticDebtSum minimum
  endpoint_debtSum_gt_minimum : quittingTerminalSemanticDebtSum minimum <
    quittingTerminalSemanticDebtSum endpointCluster
  source_moverDebt_pos : 0 < quittingTerminalSemanticDebt sourceCluster mover
  endpoint_moverDebt_eq_zero :
    quittingTerminalSemanticDebt endpointCluster mover = 0

/-- Joint compactification of the source, endpoint, and literal half-mixture
sequences.  Equality at the endpoint is consumed by the fresh half-parent
support rank; strict endpoint debt ascent is returned unchanged. -/
theorem exists_minimumEndpointSupportRankHandoff_or_debtAscent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (sourceProfiles targetProfiles : ℕ →
      (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (hopponents : ∀ index other, other ≠ mover →
      targetProfiles index other = sourceProfiles index other)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsourceDebtSum : Tendsto (fun index ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (sourceProfiles index))) atTop
        (nhds (quittingTerminalSemanticDebtSum minimum)))
    (sourceMoverLimit : ℝ) (hsourceMoverLimit : 0 < sourceMoverLimit)
    (hsourceMover : Tendsto (fun index ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sourceProfiles index)) mover)
        atTop (nhds sourceMoverLimit))
    (htargetMover : ∀ index, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (targetProfiles index)) mover = 0) :
    Nonempty (QuittingMinimumEndpointSupportRankHandoff reward minimum
        sourceProfiles targetProfiles mover) ∨
      Nonempty (QuittingMinimumEndpointDebtAscent reward minimum
        sourceProfiles targetProfiles mover) := by
  let halfProfiles : ℕ → (quittingGame reward).BehaviorProfile := fun index ↦
    quittingHalfStoppingLawProfile reward (sourceProfiles index)
      (targetProfiles index) mover
  have hsourceMem : ∀ index, quittingTerminalSemanticPair reward
      (sourceProfiles index) ∈ quittingTerminalSemanticCarrier reward :=
    fun index ↦ quittingTerminalSemanticPair_mem_carrier reward _
  obtain ⟨sourceCluster, hsourceMem', first, hfirst, hsourceLimit⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq
      hsourceMem
  have htargetMem : ∀ rank, quittingTerminalSemanticPair reward
      (targetProfiles (first rank)) ∈ quittingTerminalSemanticCarrier reward :=
    fun rank ↦ quittingTerminalSemanticPair_mem_carrier reward _
  obtain ⟨endpointCluster, hendpointMem, second, hsecond, htargetLimit⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq
      htargetMem
  have hhalfMem : ∀ rank, quittingTerminalSemanticPair reward
      (halfProfiles (first (second rank))) ∈
        quittingTerminalSemanticCarrier reward :=
    fun rank ↦ quittingTerminalSemanticPair_mem_carrier reward _
  obtain ⟨halfCluster, hhalfMem', third, hthird, hhalfLimit⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq hhalfMem
  let subsequence : ℕ → ℕ := fun rank ↦ first (second (third rank))
  have hsubsequence : StrictMono subsequence :=
    hfirst.comp (hsecond.comp hthird)
  have hsourceLimit' : Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (sourceProfiles (subsequence rank))) atTop (nhds sourceCluster) := by
    exact hsourceLimit.comp (hsecond.comp hthird).tendsto_atTop
  have htargetLimit' : Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (targetProfiles (subsequence rank))) atTop (nhds endpointCluster) := by
    exact htargetLimit.comp hthird.tendsto_atTop
  have hhalfLimit' : Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (halfProfiles (subsequence rank))) atTop (nhds halfCluster) := by
    simpa only [subsequence, Function.comp_def] using hhalfLimit
  have hsourceSumEq : quittingTerminalSemanticDebtSum sourceCluster =
      quittingTerminalSemanticDebtSum minimum := by
    have hleft :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        hsourceLimit'
    have hright := hsourceDebtSum.comp hsubsequence.tendsto_atTop
    exact tendsto_nhds_unique hleft hright
  have hsourceMoverEq :
      quittingTerminalSemanticDebt sourceCluster mover = sourceMoverLimit := by
    have hleft := (continuous_quittingTerminalSemanticDebt mover).tendsto
      sourceCluster |>.comp hsourceLimit'
    have hright := hsourceMover.comp hsubsequence.tendsto_atTop
    exact tendsto_nhds_unique hleft hright
  have hendpointMoverEq :
      quittingTerminalSemanticDebt endpointCluster mover = 0 := by
    have hleft := (continuous_quittingTerminalSemanticDebt mover).tendsto
      endpointCluster |>.comp htargetLimit'
    have hright : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    have heq : (fun rank ↦ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (targetProfiles (subsequence rank))) mover) = fun _ ↦ 0 := by
      funext rank
      exact htargetMover (subsequence rank)
    have hleft' : Tendsto (fun rank ↦ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (targetProfiles (subsequence rank))) mover) atTop
        (nhds (quittingTerminalSemanticDebt endpointCluster mover)) := by
      simpa only [Function.comp_def] using hleft
    rw [heq] at hleft'
    exact tendsto_nhds_unique hleft' hright
  have hsourceMoverPos :
      0 < quittingTerminalSemanticDebt sourceCluster mover := by
    rw [hsourceMoverEq]
    exact hsourceMoverLimit
  have hminimumEndpoint := hminimum endpointCluster hendpointMem
  rcases hminimumEndpoint.eq_or_lt with hequal | hstrict
  · left
    have hendpointSumEq : quittingTerminalSemanticDebtSum endpointCluster =
        quittingTerminalSemanticDebtSum minimum := hequal.symm
    have hcoordinateLe : ∀ who,
        quittingTerminalSemanticDebt halfCluster who ≤
          (quittingTerminalSemanticDebt sourceCluster who +
            quittingTerminalSemanticDebt endpointCluster who) / 2 := by
      intro who
      have hhalfCoordinate :=
        (continuous_quittingTerminalSemanticDebt who).tendsto halfCluster
          |>.comp hhalfLimit'
      have hsourceCoordinate :=
        (continuous_quittingTerminalSemanticDebt who).tendsto sourceCluster
          |>.comp hsourceLimit'
      have htargetCoordinate :=
        (continuous_quittingTerminalSemanticDebt who).tendsto endpointCluster
          |>.comp htargetLimit'
      have hright := (hsourceCoordinate.add htargetCoordinate).div_const 2
      apply le_of_tendsto_of_tendsto hhalfCoordinate hright
      exact Filter.Eventually.of_forall fun rank ↦ by
        simpa only [Function.comp_def, halfProfiles] using
          quittingTerminalSemanticDebt_halfStoppingLawProfile_le reward
            (sourceProfiles (subsequence rank))
            (targetProfiles (subsequence rank)) mover who
            (hopponents (subsequence rank))
    have hhalfSumLe : quittingTerminalSemanticDebtSum halfCluster ≤
        quittingTerminalSemanticDebtSum minimum := by
      unfold quittingTerminalSemanticDebtSum
      calc
        ∑ who, quittingTerminalSemanticDebt halfCluster who ≤
            ∑ who, (quittingTerminalSemanticDebt sourceCluster who +
              quittingTerminalSemanticDebt endpointCluster who) / 2 :=
          Finset.sum_le_sum fun who _ ↦ hcoordinateLe who
        _ = (quittingTerminalSemanticDebtSum sourceCluster +
            quittingTerminalSemanticDebtSum endpointCluster) / 2 := by
          unfold quittingTerminalSemanticDebtSum
          rw [← Finset.sum_add_distrib, Finset.sum_div]
        _ = quittingTerminalSemanticDebtSum minimum := by
          rw [hsourceSumEq, hendpointSumEq]
          ring
    have hhalfSumEq : quittingTerminalSemanticDebtSum halfCluster =
        quittingTerminalSemanticDebtSum minimum :=
      le_antisymm hhalfSumLe (hminimum halfCluster hhalfMem')
    let gap : ι → ℝ := fun who ↦
      (quittingTerminalSemanticDebt sourceCluster who +
          quittingTerminalSemanticDebt endpointCluster who) / 2 -
        quittingTerminalSemanticDebt halfCluster who
    have hgapNonneg : ∀ who, 0 ≤ gap who := fun who ↦ by
      dsimp only [gap]
      linarith [hcoordinateLe who]
    have hgapSum : ∑ who, gap who = 0 := by
      dsimp only [gap]
      rw [Finset.sum_sub_distrib, ← Finset.sum_div,
        Finset.sum_add_distrib]
      change (quittingTerminalSemanticDebtSum sourceCluster +
          quittingTerminalSemanticDebtSum endpointCluster) / 2 -
        quittingTerminalSemanticDebtSum halfCluster = 0
      rw [hsourceSumEq, hendpointSumEq, hhalfSumEq]
      ring
    have hcoordinateEq : ∀ who,
        quittingTerminalSemanticDebt halfCluster who =
          (quittingTerminalSemanticDebt sourceCluster who +
            quittingTerminalSemanticDebt endpointCluster who) / 2 := by
      intro who
      have hrest : 0 ≤ ∑ other ∈ Finset.univ.erase who, gap other :=
        Finset.sum_nonneg fun other _ ↦ hgapNonneg other
      have hsplit := Finset.sum_erase_add Finset.univ gap
        (Finset.mem_univ who)
      rw [hgapSum] at hsplit
      have hgapZero : gap who = 0 := by
        linarith [hgapNonneg who, hrest]
      dsimp only [gap] at hgapZero
      linarith
    have hsupportEq : quittingPositiveDebtSupport halfCluster =
        quittingPositiveDebtSupport sourceCluster ∪
          quittingPositiveDebtSupport endpointCluster := by
      ext who
      simp only [quittingPositiveDebtSupport, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_union]
      rw [hcoordinateEq who]
      have hsourceNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hsourceMem' who
      have htargetNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hendpointMem who
      constructor
      · intro hpositive
        by_contra hneither
        push Not at hneither
        rcases hneither with ⟨hsourceNot, htargetNot⟩
        linarith
      · rintro (hsourcePositive | htargetPositive) <;> linarith
    have hsupportStrict : quittingPositiveDebtSupport endpointCluster ⊂
        quittingPositiveDebtSupport halfCluster := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · rw [hsupportEq]
        exact Finset.subset_union_right
      · intro heq
        have hmoverHalf : mover ∈ quittingPositiveDebtSupport halfCluster := by
          rw [hsupportEq]
          exact Finset.mem_union_left _
            ((mem_quittingPositiveDebtSupport_iff sourceCluster mover).2
              hsourceMoverPos)
        have hmoverEndpoint : mover ∈
            quittingPositiveDebtSupport endpointCluster := by
          rw [heq]
          exact hmoverHalf
        have hmoverPositive :=
          (mem_quittingPositiveDebtSupport_iff endpointCluster mover).1
            hmoverEndpoint
        rw [hendpointMoverEq] at hmoverPositive
        exact (lt_irrefl 0) hmoverPositive
    have hhalfMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum halfCluster ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      rw [hhalfSumEq]
      exact hminimum candidate hcandidate
    have hhalfPositive : 0 < quittingTerminalSemanticDebtSum halfCluster := by
      rw [hhalfSumEq]
      exact hminimumPos
    obtain ⟨parentFamily, hparentBase⟩ :=
      exists_positiveMinimumDebtTangentFamily_of_pair halfCluster hhalfMem'
        hhalfMinimum hhalfPositive
    have hendpointFiber : quittingTerminalSemanticDebtSum endpointCluster =
        quittingTerminalSemanticDebtSum parentFamily.base := by
      rw [hparentBase, hendpointSumEq, hhalfSumEq]
    have hendpointSubset : ∀ who,
        0 < quittingTerminalSemanticDebt endpointCluster who →
          who ∈ parentFamily.positiveDebtSupport := by
      intro who hpositive
      rw [QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport,
        hparentBase]
      exact hsupportStrict.subset
        ((mem_quittingPositiveDebtSupport_iff endpointCluster who).2 hpositive)
    have hvanished : ∃ who ∈ parentFamily.positiveDebtSupport,
        quittingTerminalSemanticDebt endpointCluster who = 0 := by
      refine ⟨mover, ?_, hendpointMoverEq⟩
      rw [QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport,
        hparentBase]
      exact (mem_quittingPositiveDebtSupport_iff halfCluster mover).2 (by
        rw [hcoordinateEq mover, hendpointMoverEq]
        linarith)
    obtain ⟨nextFamily, hnextBase, hnextSupport⟩ :=
      parentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished
        endpointCluster hendpointMem hendpointFiber hendpointSubset hvanished
    exact ⟨{
      sourceCluster := sourceCluster
      endpointCluster := endpointCluster
      halfCluster := halfCluster
      subsequence := subsequence
      subsequence_strictMono := hsubsequence
      source_tendsto := hsourceLimit'
      endpoint_tendsto := htargetLimit'
      half_tendsto := by simpa only [halfProfiles] using hhalfLimit'
      source_mem := hsourceMem'
      endpoint_mem := hendpointMem
      half_mem := hhalfMem'
      source_debtSum_eq_minimum := hsourceSumEq
      endpoint_debtSum_eq_minimum := hendpointSumEq
      half_debtSum_eq_minimum := hhalfSumEq
      half_debt_eq_average := hcoordinateEq
      half_support_eq_union := hsupportEq
      source_moverDebt_pos := hsourceMoverPos
      endpoint_moverDebt_eq_zero := hendpointMoverEq
      endpoint_support_ssubset_half := hsupportStrict
      parentFamily := parentFamily
      parentFamily_base_eq := hparentBase
      nextFamily := nextFamily
      nextFamily_base_eq := hnextBase
      next_support_ssubset_parent := hnextSupport
    }⟩
  · right
    exact ⟨{
      sourceCluster := sourceCluster
      endpointCluster := endpointCluster
      subsequence := subsequence
      subsequence_strictMono := hsubsequence
      source_tendsto := hsourceLimit'
      endpoint_tendsto := htargetLimit'
      source_mem := hsourceMem'
      endpoint_mem := hendpointMem
      source_debtSum_eq_minimum := hsourceSumEq
      endpoint_debtSum_gt_minimum := hstrict
      source_moverDebt_pos := hsourceMoverPos
      endpoint_moverDebt_eq_zero := hendpointMoverEq
    }⟩

end GameTheory
