/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ReturnedBlockTangentGap
import UniformEquilibrium.Quitting.Classification.LCP.PrincipalRootRestriction

/-!
# Restricting returned product blocks to a principal player subset

This file restricts a finite returned product block to a finite subset of its
players.  The structural restriction is unconditional.  Exact semantic
comparison with the ambient block requires every omitted marginal to be pure
Continue and is developed below.
-/

noncomputable section

namespace GameTheory
namespace QuittingReturnedProductBlock

open Math.PMFProduct QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Restrict every phase root and payoff annotation to a finite player
subset. -/
def principalRestriction (block : QuittingReturnedProductBlock ι)
    (players : Finset ι) : QuittingReturnedProductBlock players where
  extraPhases := block.extraPhases
  root phase who := block.root phase who.1
  value phase who := block.value phase who.1

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem principalRestriction_extraPhases
    (block : QuittingReturnedProductBlock ι) (players : Finset ι) :
    (block.principalRestriction players).extraPhases = block.extraPhases :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem principalRestriction_root
    (block : QuittingReturnedProductBlock ι) (players : Finset ι)
    (phase : Fin (block.extraPhases + 1)) (who : players) :
    (block.principalRestriction players).root phase who =
      block.root phase who.1 :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem principalRestriction_value
    (block : QuittingReturnedProductBlock ι) (players : Finset ι)
    (phase : Fin (block.extraPhases + 1)) (who : players) :
    (block.principalRestriction players).value phase who =
      block.value phase who.1 :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem principalRestriction_next
    (block : QuittingReturnedProductBlock ι) (players : Finset ι)
    (phase : Fin (block.extraPhases + 1)) :
    (block.principalRestriction players).next phase = block.next phase :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem principalRestriction_hazard
    (block : QuittingReturnedProductBlock ι) (players : Finset ι)
    (phase : Fin (block.extraPhases + 1)) (who : players) :
    (block.principalRestriction players).hazard phase who =
      block.hazard phase who.1 :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem principalRestriction_phaseHazard
    (block : QuittingReturnedProductBlock ι) (players : Finset ι)
    (phase : Fin (block.extraPhases + 1)) :
    (block.principalRestriction players).phaseHazard phase =
      ∑ who ∈ players, block.hazard phase who := by
  change (∑ who : players, block.hazard phase who.1) = _
  rw [Finset.sum_subtype players (fun _ => Iff.rfl)]

omit [DecidableEq ι] in
/-- Deleting zero-hazard coordinates preserves each phase's total hazard. -/
theorem principalRestriction_phaseHazard_eq
    (block : QuittingReturnedProductBlock ι) (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0)
    (phase : Fin (block.extraPhases + 1)) :
    (block.principalRestriction players).phaseHazard phase =
      block.phaseHazard phase := by
  rw [principalRestriction_phaseHazard]
  unfold phaseHazard
  exact Finset.sum_subset (Finset.subset_univ players)
    (fun who _ hwho => hoff phase who hwho)

omit [DecidableEq ι] in
/-- Deleting zero-hazard coordinates preserves total accumulated hazard. -/
theorem principalRestriction_totalHazard_eq
    (block : QuittingReturnedProductBlock ι) (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0) :
    (block.principalRestriction players).totalHazard = block.totalHazard := by
  unfold totalHazard
  apply Finset.sum_congr rfl
  intro phase _
  exact block.principalRestriction_phaseHazard_eq players hoff phase

omit [Fintype ι] [DecidableEq ι] in
/-- A Boolean marginal with zero Quit hazard is exactly pure Continue. -/
theorem root_eq_pureContinue_of_hazard_eq_zero
    (block : QuittingReturnedProductBlock ι)
    (phase : Fin (block.extraPhases + 1)) (who : ι)
    (hzero : block.hazard phase who = 0) :
    block.root phase who = PMF.pure false := by
  have hquitReal : (block.root phase who true).toReal = 0 := hzero
  have hquit : block.root phase who true = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hquitReal with hzero' | htop
    · exact hzero'
    · exact absurd htop (PMF.apply_ne_top (block.root phase who) true)
  have htotal : block.root phase who true + block.root phase who false = 1 := by
    simpa only [tsum_fintype, Fintype.sum_bool] using
      (block.root phase who).tsum_coe
  have hcontinue : block.root phase who false = 1 := by
    rw [hquit, zero_add] at htotal
    exact htotal
  ext action
  cases action <;> simp [hquit, hcontinue]

omit [Fintype ι] [DecidableEq ι] in
/-- Zero hazards off a subset mean that every omitted marginal is literally
pure Continue, phase by phase. -/
theorem root_eq_pureContinue_off_principal
    (block : QuittingReturnedProductBlock ι) (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0)
    (phase : Fin (block.extraPhases + 1)) {who : ι}
    (hwho : who ∉ players) :
    block.root phase who = PMF.pure false :=
  block.root_eq_pureContinue_of_hazard_eq_zero phase who
    (hoff phase who hwho)

/-- The prescribed successor payoff on a retained coordinate is exactly the
ambient successor payoff when every omitted marginal has zero hazard. -/
theorem principalRestriction_successorPayoff_eq
    (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0)
    (phase : Fin (block.extraPhases + 1)) (who : players) :
    quittingRootSuccessorPayoff (quittingPrincipalReward reward players)
        ((block.principalRestriction players).value
          ((block.principalRestriction players).next phase))
        ((block.principalRestriction players).root phase) who =
      quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who.1 := by
  have hpure : ∀ outside, outside ∉ players →
      block.root phase outside = PMF.pure false := by
    intro outside houtside
    exact block.root_eq_pureContinue_off_principal players hoff phase houtside
  change quittingRootSuccessorPayoff (quittingPrincipalReward reward players)
      (fun principalWho => block.value (block.next phase) principalWho.1)
      (fun principalWho => block.root phase principalWho.1) who = _
  symm
  have h := quittingRootSuccessorPayoff_principal reward
    (block.value (block.next phase)) (block.root phase) players hpure who
  change quittingRootSuccessorPayoff reward
      (block.value (block.next phase)) (block.root phase) who.1 =
    quittingRootSuccessorPayoff (quittingPrincipalReward reward players)
      (fun principalWho => block.value (block.next phase) principalWho.1)
      (fun principalWho => block.root phase principalWho.1) who at h
  exact h

/-- The pure-Quit minus pure-Continue payoff on a retained coordinate is
exactly the ambient endpoint difference. -/
theorem principalRestriction_endpointDifference_eq
    (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0)
    (phase : Fin (block.extraPhases + 1)) (who : players) :
    quittingRootEndpointDifference (quittingPrincipalReward reward players)
        ((block.principalRestriction players).value
          ((block.principalRestriction players).next phase))
        ((block.principalRestriction players).root phase) who =
      quittingRootEndpointDifference reward
        (block.value (block.next phase)) (block.root phase) who.1 := by
  have hpure : ∀ outside, outside ∉ players →
      block.root phase outside = PMF.pure false := by
    intro outside houtside
    exact block.root_eq_pureContinue_off_principal players hoff phase houtside
  change quittingRootEndpointDifference (quittingPrincipalReward reward players)
      (fun principalWho => block.value (block.next phase) principalWho.1)
      (fun principalWho => block.root phase principalWho.1) who = _
  symm
  have h := quittingRootEndpointDifference_principal reward
    (block.value (block.next phase)) (block.root phase) players hpure who
  change quittingRootEndpointDifference reward
      (block.value (block.next phase)) (block.root phase) who.1 =
    quittingRootEndpointDifference (quittingPrincipalReward reward players)
      (fun principalWho => block.value (block.next phase) principalWho.1)
      (fun principalWho => block.root phase principalWho.1) who at h
  exact h

/-- Aggregate absolute Bellman residual over retained payoff coordinates. -/
def principalBellmanError (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) : ℝ :=
  ∑ phase : Fin (block.extraPhases + 1), ∑ who ∈ players,
    |block.value phase who -
      quittingRootSuccessorPayoff reward (block.value (block.next phase))
        (block.root phase) who|

/-- Aggregate exact endpoint regret over retained payoff coordinates. -/
def principalEndpointRegret (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) : ℝ :=
  ∑ phase : Fin (block.extraPhases + 1), ∑ who ∈ players,
    (max 0 ((block.root phase who false).toReal *
      quittingRootEndpointDifference reward
        (block.value (block.next phase)) (block.root phase) who) +
    max 0 (-(block.root phase who true).toReal *
      quittingRootEndpointDifference reward
        (block.value (block.next phase)) (block.root phase) who))

/-- The restricted block's Bellman error is exactly the ambient Bellman error
summed over retained coordinates. -/
theorem principalRestriction_bellmanError_eq
    (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0) :
    (block.principalRestriction players).bellmanError
        (quittingPrincipalReward reward players) =
      block.principalBellmanError reward players := by
  unfold bellmanError principalBellmanError
  change (∑ phase : Fin (block.extraPhases + 1), ∑ who : players,
      |block.value phase who.1 -
        quittingRootSuccessorPayoff (quittingPrincipalReward reward players)
          (fun principalWho =>
            block.value (block.next phase) principalWho.1)
          (fun principalWho => block.root phase principalWho.1) who|) = _
  apply Finset.sum_congr rfl
  intro phase _
  rw [Finset.sum_subtype players (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro who _
  have h := block.principalRestriction_successorPayoff_eq
    reward players hoff phase who
  change quittingRootSuccessorPayoff (quittingPrincipalReward reward players)
      (fun principalWho => block.value (block.next phase) principalWho.1)
      (fun principalWho => block.root phase principalWho.1) who =
    quittingRootSuccessorPayoff reward (block.value (block.next phase))
      (block.root phase) who.1 at h
  rw [h]

/-- The restricted block's endpoint regret is exactly the ambient endpoint
regret summed over retained coordinates. -/
theorem principalRestriction_endpointRegret_eq
    (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0) :
    (block.principalRestriction players).endpointRegret
        (quittingPrincipalReward reward players) =
      block.principalEndpointRegret reward players := by
  unfold endpointRegret principalEndpointRegret
  change (∑ phase : Fin (block.extraPhases + 1), ∑ who : players,
      (max 0 ((block.root phase who.1 false).toReal *
        quittingRootEndpointDifference (quittingPrincipalReward reward players)
          (fun principalWho =>
            block.value (block.next phase) principalWho.1)
          (fun principalWho => block.root phase principalWho.1) who) +
      max 0 (-(block.root phase who.1 true).toReal *
        quittingRootEndpointDifference (quittingPrincipalReward reward players)
          (fun principalWho =>
            block.value (block.next phase) principalWho.1)
          (fun principalWho => block.root phase principalWho.1) who))) = _
  apply Finset.sum_congr rfl
  intro phase _
  rw [Finset.sum_subtype players (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro who _
  have h := block.principalRestriction_endpointDifference_eq
    reward players hoff phase who
  change quittingRootEndpointDifference (quittingPrincipalReward reward players)
      (fun principalWho => block.value (block.next phase) principalWho.1)
      (fun principalWho => block.root phase principalWho.1) who =
    quittingRootEndpointDifference reward (block.value (block.next phase))
      (block.root phase) who.1 at h
  rw [h]

omit [DecidableEq ι] in
/-- Retained-coordinate Bellman error is bounded by the ambient aggregate
Bellman error. -/
theorem principalBellmanError_le
    (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    block.principalBellmanError reward players ≤ block.bellmanError reward := by
  unfold principalBellmanError bellmanError
  apply Finset.sum_le_sum
  intro phase _
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ players)
    (fun who _ _ => abs_nonneg (block.value phase who -
      quittingRootSuccessorPayoff reward (block.value (block.next phase))
        (block.root phase) who))

/-- Retained-coordinate endpoint regret is bounded by the ambient aggregate
endpoint regret. -/
theorem principalEndpointRegret_le
    (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    block.principalEndpointRegret reward players ≤
      block.endpointRegret reward := by
  unfold principalEndpointRegret endpointRegret
  apply Finset.sum_le_sum
  intro phase _
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ players)
    (fun who _ _ => add_nonneg (le_max_left _ _) (le_max_left _ _))

/-- Deleting zero-hazard coordinates cannot increase aggregate Bellman
error. -/
theorem principalRestriction_bellmanError_le
    (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0) :
    (block.principalRestriction players).bellmanError
        (quittingPrincipalReward reward players) ≤
      block.bellmanError reward := by
  rw [block.principalRestriction_bellmanError_eq reward players hoff]
  exact block.principalBellmanError_le reward players

/-- Deleting zero-hazard coordinates cannot increase aggregate endpoint
regret. -/
theorem principalRestriction_endpointRegret_le
    (block : QuittingReturnedProductBlock ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (hoff : ∀ phase who, who ∉ players → block.hazard phase who = 0) :
    (block.principalRestriction players).endpointRegret
        (quittingPrincipalReward reward players) ≤
      block.endpointRegret reward := by
  rw [block.principalRestriction_endpointRegret_eq reward players hoff]
  exact block.principalEndpointRegret_le reward players

end QuittingReturnedProductBlock

namespace QuittingLCPClassification

open Filter QuittingReturnedProductBlock

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Vanishing returned blocks whose hazards are supported on a fixed nonempty
player subset expose a homogeneous simplex solution of that subset's
principal normalized matrix.  The blocks themselves remain ambient: only the
zero-hazard coordinates are deleted before applying the restricted theorem. -/
theorem hasHomogeneousSimplexSolution_principal_of_vanishing_ambientReturnedBlocks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) (hplayers : players.Nonempty)
    (blocks : ℕ → QuittingReturnedProductBlock ι) {K : ℝ}
    (hoff : ∀ n phase who, who ∉ players →
      (blocks n).hazard phase who = 0)
    (hvalue : ∀ n phase who, who ∈ players →
      |(blocks n).value phase who| ≤ K)
    (hpositive : ∀ n, 0 < (blocks n).totalHazard)
    (hvanish : Tendsto (fun n => (blocks n).totalHazard) atTop (nhds 0))
    (hbellman : Tendsto (fun n =>
      (blocks n).bellmanError reward / (blocks n).totalHazard)
        atTop (nhds 0))
    (hendpoint : Tendsto (fun n =>
      (blocks n).endpointRegret reward / (blocks n).totalHazard)
        atTop (nhds 0)) :
    HasHomogeneousSimplexSolution
      (principalMatrix (normalizedSoloMatrix reward) players) := by
  let restricted : ℕ → QuittingReturnedProductBlock players :=
    fun n => (blocks n).principalRestriction players
  apply hasHomogeneousSimplexSolution_principal_of_vanishing_returnedBlocks
    reward players hplayers restricted
  · intro n phase who
    exact hvalue n phase who.1 who.2
  · intro n
    rw [show (restricted n).totalHazard = (blocks n).totalHazard by
      exact (blocks n).principalRestriction_totalHazard_eq players (hoff n)]
    exact hpositive n
  · apply hvanish.congr'
    exact Filter.Eventually.of_forall fun n =>
      ((blocks n).principalRestriction_totalHazard_eq players (hoff n)).symm
  · exact squeeze_zero
      (f := fun n => (restricted n).bellmanError
        (quittingPrincipalReward reward players) / (restricted n).totalHazard)
      (g := fun n => (blocks n).bellmanError reward / (blocks n).totalHazard)
      (fun n => div_nonneg ((restricted n).bellmanError_nonneg _)
        (by
          rw [(blocks n).principalRestriction_totalHazard_eq players (hoff n)]
          exact (hpositive n).le))
      (fun n => by
        rw [(blocks n).principalRestriction_totalHazard_eq players (hoff n)]
        exact div_le_div_of_nonneg_right
          ((blocks n).principalRestriction_bellmanError_le reward players (hoff n))
          (hpositive n).le)
      hbellman
  · exact squeeze_zero
      (f := fun n => (restricted n).endpointRegret
        (quittingPrincipalReward reward players) / (restricted n).totalHazard)
      (g := fun n => (blocks n).endpointRegret reward / (blocks n).totalHazard)
      (fun n => div_nonneg ((restricted n).endpointRegret_nonneg _)
        (by
          rw [(blocks n).principalRestriction_totalHazard_eq players (hoff n)]
          exact (hpositive n).le))
      (fun n => by
        rw [(blocks n).principalRestriction_totalHazard_eq players (hoff n)]
        exact div_le_div_of_nonneg_right
          ((blocks n).principalRestriction_endpointRegret_le reward players (hoff n))
          (hpositive n).le)
      hendpoint

/-- A nonhomogeneous principal normalized matrix gives a uniform relative
error gap for ambient returned blocks supported on that principal subset. -/
theorem exists_pos_ambientReturnedBlock_relativeError_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) (hplayers : players.Nonempty) {K : ℝ}
    (hno : ¬HasHomogeneousSimplexSolution
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    ∃ δ > 0, ∃ c > 0, ∀ block : QuittingReturnedProductBlock ι,
      (∀ phase who, who ∈ players → |block.value phase who| ≤ K) →
      (∀ phase who, who ∉ players → block.hazard phase who = 0) →
      0 < block.totalHazard → block.totalHazard ≤ δ →
      c * block.totalHazard ≤
        block.bellmanError reward + block.endpointRegret reward := by
  obtain ⟨δ, hδ, c, hc, hgap⟩ :=
    exists_pos_principalReturnedBlock_relativeError_gap
      reward players hplayers (K := K) hno
  refine ⟨δ, hδ, c, hc, ?_⟩
  intro block hvalue hoff hpositive hsmall
  have hrestricted := hgap (block.principalRestriction players)
    (fun phase who => hvalue phase who.1 who.2)
    (by rwa [block.principalRestriction_totalHazard_eq players hoff])
    (by rwa [block.principalRestriction_totalHazard_eq players hoff])
  rw [block.principalRestriction_totalHazard_eq players hoff] at hrestricted
  calc
    c * block.totalHazard ≤
        (block.principalRestriction players).bellmanError
            (quittingPrincipalReward reward players) +
          (block.principalRestriction players).endpointRegret
            (quittingPrincipalReward reward players) := hrestricted
    _ ≤ block.bellmanError reward + block.endpointRegret reward :=
      add_le_add
        (block.principalRestriction_bellmanError_le reward players hoff)
        (block.principalRestriction_endpointRegret_le reward players hoff)

/-- On `ResidualHardClass`, ambient returned blocks supported on the recursive
normal core have a uniform positive relative-error gap. -/
theorem ResidualHardClass.exists_pos_ambientNormalCoreReturnedBlock_relativeError_gap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hard : ResidualHardClass reward) {K : ℝ} :
    ∃ δ > 0, ∃ c > 0, ∀ block : QuittingReturnedProductBlock ι,
      (∀ phase who, who ∈ normalCore (normalizedSoloMatrix reward) →
        |block.value phase who| ≤ K) →
      (∀ phase who, who ∉ normalCore (normalizedSoloMatrix reward) →
        block.hazard phase who = 0) →
      0 < block.totalHazard → block.totalHazard ≤ δ →
      c * block.totalHazard ≤
        block.bellmanError reward + block.endpointRegret reward := by
  apply exists_pos_ambientReturnedBlock_relativeError_gap reward
    (normalCore (normalizedSoloMatrix reward)) hard.normal_nonempty
  simpa only [normalizedNormalPlayerMatrix, normalPlayerMatrix] using
    hard.no_homogeneous

end QuittingLCPClassification
end GameTheory
