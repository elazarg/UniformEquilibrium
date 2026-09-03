/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.UnboundedInverseIterate
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile
import UniformEquilibrium.Quitting.Punishment.CompletedCycle
import UniformEquilibrium.Quitting.Terminal.PassivePlayerPaddingPeriodRetraction

/-!
# Retracting passive-padding block certificates

An admissible exact absorbing finite block certificate for a one-passive-player
padding with a valid old-player upper endpoint cannot use the passive player
as an independent clock. Starting the induced cyclic profile at any phase, exact terminal Nash
and the passive player's Never deviation force fresh-only absorption to have
zero mass.  The old rows therefore retain the Bellman recursion,
complementarity, and absorption of the padded block.  Projecting the displayed
values gives a bounded completely absorbing inverse iterate of the old game.

The sure-Quit face of an old row is included.  There the Continue inequality
is vacuous, while the Quit inequality is retained because the supplied upper
endpoint dominates the projected tail value.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct StochasticGame
open scoped Topology

variable {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-! ## One-sided terminal bounds -/

omit [DecidableEq I] in
/-- A one-sided terminal-reward bound controls the one-stage absorbing
contribution after multiplying by the absorption probability. -/
theorem quittingRootAbsorbingContribution_le_absorption_mul
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (root : I → PMF Bool) (who : I) (upper : ℝ)
    (hreward : ∀ terminal, reward terminal who ≤ upper) :
    quittingRootAbsorbingContribution reward root who ≤
      upper * quittingRootAbsorptionMass root := by
  let bound : (I → Bool) → ℝ := fun action ↦
    if (quittingQuitters action).Nonempty then upper else 0
  have hpoint : ∀ action : I → Bool,
      quittingRootPayoff reward (0 : Payoff I) action who ≤ bound action := by
    intro action
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp only [quittingRootPayoff, dif_pos hquit, bound, if_pos hquit]
      exact hreward _
    · simp only [quittingRootPayoff, dif_neg hquit, Pi.zero_apply,
        bound, if_neg hquit, le_refl]
  have hexpect : quittingRootAbsorbingContribution reward root who ≤
      expect (pmfPi root) bound := by
    exact expect_mono _ _ _ hpoint
  have hbound : expect (pmfPi root) bound =
      upper * quittingRootAbsorptionMass root := by
    unfold bound
    rw [show (fun action : I → Bool ↦
        if (quittingQuitters action).Nonempty then upper else 0) =
      fun action ↦ upper *
        (if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) by
          funext action
          split <;> simp_all]
    rw [expect_const_mul, expect_quittingNonemptyIndicator_eq_absorptionMass]
  simpa [quittingRootAbsorbingContribution, quittingRootExpectedPayoff,
    hbound] using hexpect

omit [DecidableEq I] in
/-- If joint survival vanishes, a coordinatewise terminal-reward upper bound
also bounds the corresponding root-sequence terminal value. -/
theorem quittingRootSequenceTerminalValue_le_of_tendsto_zero
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (roots : ℕ → I → PMF Bool) (who : I) (start : ℕ) (upper : ℝ)
    (hreward : ∀ terminal, reward terminal who ≤ upper)
    (hsurvival : Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0)) :
    quittingRootSequenceTerminalValue reward roots who start ≤ upper := by
  rw [quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  have hsummable :=
    summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
      reward roots who start
  have hpartial : ∀ fuel, (∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight roots start offset *
        quittingRootAbsorbingContribution reward (roots (start + offset)) who) ≤
      upper * (1 - quittingJointSurvivalWeight roots start fuel) := by
    intro fuel
    calc
      _ ≤ ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start offset *
            (upper * (1 - quittingStationaryContinueMass
              (roots (start + offset)))) := by
        apply Finset.sum_le_sum
        intro offset _
        apply mul_le_mul_of_nonneg_left _
          (quittingJointSurvivalWeight_nonneg roots start offset)
        simpa [quittingRootAbsorptionMass] using
          (quittingRootAbsorbingContribution_le_absorption_mul
            reward (roots (start + offset)) who upper hreward)
      _ = upper * (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start offset *
            (1 - quittingStationaryContinueMass
              (roots (start + offset)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        ring
      _ = upper * (1 - quittingJointSurvivalWeight roots start fuel) := by
        rw [sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
  have hright : Tendsto (fun fuel ↦
      upper * (1 - quittingJointSurvivalWeight roots start fuel)) atTop
      (nhds upper) := by
    have hone : Tendsto (fun fuel : ℕ ↦
        (1 : ℝ) - quittingJointSurvivalWeight roots start fuel) atTop
        (nhds 1) := by
      simpa using tendsto_const_nhds.sub hsurvival
    simpa using hone.const_mul upper
  apply le_of_tendsto_of_tendsto' hsummable.hasSum.tendsto_sum_nat hright
  exact hpartial

omit [Fintype J] in
/-- Every padded terminal reward of an old player is at most the supplied
upper endpoint. -/
theorem quittingPassivePaddingReward_old_le_upper
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (hupper : ∀ terminal old, reward terminal old ≤ upper old)
    (terminal : {S : Finset (I ⊕ J) // S.Nonempty}) (old : I) :
    quittingPassivePaddingReward (J := J) reward upper penalty terminal (.inl old) ≤
      upper old := by
  unfold quittingPassivePaddingReward
  split
  next hold => exact hupper _ old
  next => exact le_rfl

/-- Exact terminal Nash in an arbitrary passive padding forces the total
fresh-only absorption mass to vanish.  Unlike the quantitative canonical
retraction, this zero-error statement does not use extremality of `upper`. -/
theorem quittingPassivePaddingFreshOnlyMass_eq_zero_of_isZeroAsymptoticNash
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) {penalty : ℝ} (hpenalty : 0 < penalty)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty))
      |>.IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward upper penalty))
        0 profile) :
    quittingPassivePaddingFreshOnlyMass
        (quittingProfileLiveRoot
          (quittingPassivePaddingReward (J := J) reward upper penalty)
          profile) 0 = 0 := by
  let paddedReward := quittingPassivePaddingReward (J := J) reward upper penalty
  let mass := quittingPassivePaddingFreshOnlyMass
    (quittingProfileLiveRoot paddedReward profile) 0
  have hnever : ∀ fresh : J,
      -quittingTerminalPayoff paddedReward profile (.inr fresh) ≤ 0 := by
    intro fresh
    let never := quittingPureTimeBehaviorStrategy paddedReward (.inr fresh) none
    have hstep := hnash (.inr fresh) never
    have hzero := quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero
      (J := J) reward upper penalty profile fresh
    dsimp only [never, paddedReward] at hstep hzero
    rw [hzero] at hstep
    linarith
  have hsumUpper :
      (∑ fresh : J, -quittingTerminalPayoff paddedReward profile (.inr fresh)) ≤ 0 := by
    simpa using Finset.sum_le_sum (fun fresh _ ↦ hnever fresh)
  have haggregate := sum_quittingTerminalPayoff_passivePadding_fresh_le
    (J := J) reward upper hpenalty.le profile
  have hmassScaled : penalty * mass ≤
      ∑ fresh : J, -quittingTerminalPayoff paddedReward profile (.inr fresh) := by
    dsimp only [paddedReward, mass] at haggregate ⊢
    rw [Finset.sum_neg_distrib]
    linarith
  have hmassNonpos : mass ≤ 0 := by
    nlinarith [hmassScaled.trans hsumUpper]
  exact le_antisymm hmassNonpos
    (quittingPassivePaddingFreshOnlyMass_nonneg
      (quittingProfileLiveRoot paddedReward profile) 0)

/-! ## One-root identities -/

omit [Fintype I] [Fintype J] in
/-- Updating an old coordinate of a sum-indexed root acts only on the old
root. -/
theorem update_sumElim_inl
    (old : I → PMF Bool) (fresh : J → PMF Bool) (who : I)
    (replacement : PMF Bool) :
    Function.update (Sum.elim old fresh) (.inl who) replacement =
      Sum.elim (Function.update old who replacement) fresh := by
  funext player
  cases player with
  | inl other =>
      by_cases hother : other = who
      · subst other; simp
      · simp [Function.update_of_ne hother, Function.update_of_ne (Sum.inl_injective.ne hother)]
  | inr other => simp

/-- Exact endpoint-difference decomposition for an old player.  The only
padding correction is the fresh absorption probability, weighted by the
probability that every old opponent Continues. -/
theorem quittingRootEndpointDifference_passivePadding_old
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (old : I → PMF Bool) (fresh : J → PMF Bool)
    (tail : Payoff (I ⊕ J)) (who : I) :
    quittingRootEndpointDifference reward (fun old ↦ tail (.inl old)) old who =
      quittingRootEndpointDifference
          (quittingPassivePaddingReward (J := J) reward upper penalty)
          tail (Sum.elim old fresh) (.inl who) +
        quittingStationaryContinueMass
            (Function.update old who (PMF.pure false)) *
          quittingRootAbsorptionMass fresh * (upper who - tail (.inl who)) := by
  rw [quittingRootEndpointDifference, quittingRootEndpointDifference]
  unfold quittingRootQuitPayoff quittingRootContinuePayoff
  rw [update_sumElim_inl, update_sumElim_inl]
  simp_rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  rw [quittingRootAbsorbingContribution_passivePadding_old,
    quittingRootAbsorbingContribution_passivePadding_old,
    quittingStationaryContinueMass_sumElim,
    quittingStationaryContinueMass_sumElim,
    quittingStationaryContinueMass_update_pure_true_eq_zero]
  unfold quittingRootAbsorptionMass
  ring

/-! ## The projected cyclic certificate -/

variable [Nonempty I]

/-- Canonical one-passive-player padding of an old reward table. -/
abbrev quittingOnePassivePlayerPaddingReward
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ) :=
  quittingPassivePaddingReward (J := PUnit) reward
    (quittingPassivePaddingUpperEndpoint reward) penalty

/-- Old part of a padded finite block cycle. -/
def quittingPassivePaddingProjectedBlockCycle {m : ℕ}
    (hazard : Fin (m + 1) → I ⊕ PUnit → ℝ)
    (h0 : ∀ k player, 0 ≤ hazard k player)
    (h1 : ∀ k player, hazard k player ≤ 1) :
    Fin (m + 1) → I → PMF Bool :=
  fun stage old ↦ quittingBlockCycle hazard h0 h1 stage (.inl old)

/-- Old coordinates of the displayed cyclic values. -/
def quittingPassivePaddingProjectedBlockValue {m : ℕ}
    (U : Fin (m + 2) → Payoff (I ⊕ PUnit)) :
    Fin (m + 1) → Payoff I :=
  fun stage old ↦ U (Fin.castSucc stage) (.inl old)

omit [Nonempty I] in
/-- At every phase of an exact admissible padded block, the unconditional
phase-zero mass of fresh-only absorption is zero. -/
theorem quittingPassivePaddingBlock_freshOnlyStageMass_eq_zero {m : ℕ}
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    {hazard : Fin (m + 1) → I ⊕ PUnit → ℝ}
    {U : Fin (m + 2) → Payoff (I ⊕ PUnit)}
    (hcert : IsQuittingBlockCertificate
      (quittingPassivePaddingReward (J := PUnit) reward upper penalty) hazard U)
    (phase : Fin (m + 1)) :
    let block := quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U
    let profile := quittingCyclicContinuationBlockProfile
      (quittingPassivePaddingReward (J := PUnit) reward upper penalty) m block phase
    quittingPassivePaddingFreshOnlyStageMass
      (quittingProfileLiveRoot
        (quittingPassivePaddingReward (J := PUnit) reward upper penalty) profile) 0 0 = 0 := by
  let paddedReward := quittingPassivePaddingReward (J := PUnit) reward upper penalty
  let block := quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U
  let profile := quittingCyclicContinuationBlockProfile paddedReward m block phase
  have hblock : IsQuittingCyclicContinuationBlock paddedReward (U 0) (m + 1) block :=
    isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate hcert
  have hadmissible : IsQuittingCycleAdmissible paddedReward
      (quittingCyclicContinuationBlockCycle m block) :=
    isQuittingCycleAdmissible_of_isQuittingBlockCertificate hcert
  have hnash : (quittingGame paddedReward).IsεAsymptoticNash
      (quittingTerminalPayoff paddedReward) 0 profile :=
    isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile
      paddedReward (U 0) m block hblock hadmissible phase
  have hmass : quittingPassivePaddingFreshOnlyMass
      (quittingProfileLiveRoot paddedReward profile) 0 = 0 := by
    exact quittingPassivePaddingFreshOnlyMass_eq_zero_of_isZeroAsymptoticNash
      (J := PUnit) reward upper hpenalty profile hnash
  have hstageLe : quittingPassivePaddingFreshOnlyStageMass
      (quittingProfileLiveRoot paddedReward profile) 0 0 ≤
      quittingPassivePaddingFreshOnlyMass
        (quittingProfileLiveRoot paddedReward profile) 0 := by
    unfold quittingPassivePaddingFreshOnlyMass
    have hsummable := summable_quittingPassivePaddingFreshOnlyStageMass
      (quittingProfileLiveRoot paddedReward profile) 0
    simpa using hsummable.sum_le_tsum ({0} : Finset ℕ)
      (fun offset _ ↦ quittingPassivePaddingFreshOnlyStageMass_nonneg
        (quittingProfileLiveRoot paddedReward profile) 0 offset)
  dsimp only [paddedReward, block, profile] at hmass hstageLe ⊢
  rw [hmass] at hstageLe
  exact le_antisymm hstageLe
    (quittingPassivePaddingFreshOnlyStageMass_nonneg _ 0 0)

omit [Nonempty I] in
/-- Root-level form of the preceding vanishing statement: at every padded
block phase, old all-Continue mass times passive-player absorption is zero. -/
theorem quittingPassivePaddingBlock_oldContinue_mul_freshAbsorption_eq_zero
    {m : ℕ}
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    {hazard : Fin (m + 1) → I ⊕ PUnit → ℝ}
    {U : Fin (m + 2) → Payoff (I ⊕ PUnit)}
    (hcert : IsQuittingBlockCertificate
      (quittingPassivePaddingReward (J := PUnit) reward upper penalty) hazard U)
    (phase : Fin (m + 1)) :
    let paddedRoot := quittingBlockCycle hazard hcert.hazard_nonneg
      hcert.hazard_le_one phase
    quittingStationaryContinueMass
        (fun old ↦ paddedRoot (.inl old)) *
      quittingRootAbsorptionMass (fun fresh ↦ paddedRoot (.inr fresh)) = 0 := by
  have hzero := quittingPassivePaddingBlock_freshOnlyStageMass_eq_zero
    reward upper hpenalty hcert phase
  let block := quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U
  let cycle := quittingBlockCycle hazard hcert.hazard_nonneg hcert.hazard_le_one
  dsimp only at hzero
  rw [quittingCyclicContinuationBlockProfile,
    quittingProfileLiveRoot_cyclicBehaviorProfile] at hzero
  rw [show quittingCyclicContinuationBlockCycle m block = cycle by
    exact quittingCyclicContinuationBlockCycle_quittingBlockPath
      hcert.hazard_nonneg hcert.hazard_le_one U] at hzero
  unfold quittingPassivePaddingFreshOnlyStageMass at hzero
  simp only [quittingJointSurvivalWeight, quittingFiniteContinueWeight,
    Nat.zero_add, one_mul] at hzero
  change quittingStationaryContinueMass
      (fun old ↦ quittingCyclicRootSequence cycle phase 0 (.inl old)) *
    quittingRootAbsorptionMass
      (fun fresh ↦ quittingCyclicRootSequence cycle phase 0 (.inr fresh)) = 0 at hzero
  rw [quittingCyclicRootSequence_zero] at hzero
  exact hzero

omit [Nonempty I] in
/-- Every old displayed value of a padded block is at most its supplied old
upper endpoint. -/
theorem quittingPassivePaddingProjectedBlockValue_le_upper {m : ℕ}
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ)
    (hupper : ∀ terminal old, reward terminal old ≤ upper old)
    {penalty : ℝ}
    {hazard : Fin (m + 1) → I ⊕ PUnit → ℝ}
    {U : Fin (m + 2) → Payoff (I ⊕ PUnit)}
    (hcert : IsQuittingBlockCertificate
      (quittingPassivePaddingReward (J := PUnit) reward upper penalty) hazard U)
    (phase : Fin (m + 1)) (old : I) :
    quittingPassivePaddingProjectedBlockValue U phase old ≤
      upper old := by
  let paddedReward := quittingPassivePaddingReward (J := PUnit) reward upper penalty
  let block := quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U
  let cycle := quittingCyclicContinuationBlockCycle m block
  let value := quittingCyclicContinuationBlockValue m block
  let profile := quittingCyclicBehaviorProfile paddedReward cycle phase
  have hblock : IsQuittingCyclicContinuationBlock paddedReward (U 0) (m + 1) block :=
    isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate hcert
  have hcycle : (∏ stage : Fin (m + 1),
      quittingStationaryContinueMass (cycle stage)) < 1 :=
    quittingCyclicContinuationBlock_prod_continueMass_lt_one
      paddedReward (U 0) m block hblock
  have hvalue : value = quittingCyclicTerminalValue paddedReward cycle :=
    eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
      paddedReward cycle value
      (quittingCyclicContinuationBlock_policy paddedReward (U 0) m block hblock)
      hcycle
  have hterminal : quittingPassivePaddingProjectedBlockValue U phase old =
      quittingRootSequenceTerminalValue paddedReward
        (quittingCyclicRootSequence cycle phase) (.inl old) 0 := by
    change value phase (.inl old) = _
    rw [hvalue]
    change quittingTerminalPayoff paddedReward profile (.inl old) = _
    rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
      quittingProfileLiveRoot_cyclicBehaviorProfile]
  rw [hterminal]
  apply quittingRootSequenceTerminalValue_le_of_tendsto_zero
  · intro terminal
    exact quittingPassivePaddingReward_old_le_upper reward
      upper penalty hupper terminal old
  · exact tendsto_zero_quittingJointSurvivalWeight_cyclicRootSequence
      cycle phase hcycle

omit [Nonempty I] in
/-- Every phase of the projected old block is an exact inverse-iterate step.
The proof retains both endpoint inequalities, including old players who Quit
surely at the phase. -/
theorem isQuittingRootSuccessorCertificate_projectedPassivePaddingBlockPhase
    {m : ℕ}
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ)
    (hupper : ∀ terminal old, reward terminal old ≤ upper old)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    {hazard : Fin (m + 1) → I ⊕ PUnit → ℝ}
    {U : Fin (m + 2) → Payoff (I ⊕ PUnit)}
    (hcert : IsQuittingBlockCertificate
      (quittingPassivePaddingReward (J := PUnit) reward upper penalty) hazard U)
    (phase : Fin (m + 1)) :
    IsεQuittingRootSuccessorCertificate reward 0
      (quittingPassivePaddingProjectedBlockCycle hazard
        hcert.hazard_nonneg hcert.hazard_le_one phase)
      (quittingPassivePaddingProjectedBlockValue U phase)
      (quittingPassivePaddingProjectedBlockValue U
        (finRotate (m + 1) phase)) := by
  let paddedReward := quittingPassivePaddingReward (J := PUnit) reward upper penalty
  let block := quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U
  let paddedCycle := quittingCyclicContinuationBlockCycle m block
  let paddedValue := quittingCyclicContinuationBlockValue m block
  let oldRoot : I → PMF Bool := fun old ↦ paddedCycle phase (.inl old)
  let freshRoot : PUnit → PMF Bool := fun fresh ↦ paddedCycle phase (.inr fresh)
  let oldTail : Payoff I := fun old ↦
    paddedValue (finRotate (m + 1) phase) (.inl old)
  have hblock : IsQuittingCyclicContinuationBlock paddedReward (U 0) (m + 1) block :=
    isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate hcert
  have hpaddedPolicy :=
    quittingCyclicContinuationBlock_policy paddedReward (U 0) m block hblock phase
  have hpaddedNash : IsεQuittingRootEndpointNash paddedReward
      (paddedValue (finRotate (m + 1) phase)) 0 (paddedCycle phase) := by
    rw [isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    exact quittingCyclicContinuationBlock_rootNash
      paddedReward (U 0) m block hblock phase
  have hroot : paddedCycle phase = Sum.elim oldRoot freshRoot := by
    funext player
    cases player <;> rfl
  have hcycle : paddedCycle = quittingBlockCycle hazard
      hcert.hazard_nonneg hcert.hazard_le_one := by
    exact quittingCyclicContinuationBlockCycle_quittingBlockPath
      hcert.hazard_nonneg hcert.hazard_le_one U
  have holdRootEq : quittingPassivePaddingProjectedBlockCycle hazard
      hcert.hazard_nonneg hcert.hazard_le_one phase = oldRoot := by
    funext old
    exact congrFun (congrFun hcycle phase) (.inl old) |>.symm
  have holdTailEq : quittingPassivePaddingProjectedBlockValue U
      (finRotate (m + 1) phase) = oldTail := by
    rfl
  have hstage : quittingStationaryContinueMass oldRoot *
      quittingRootAbsorptionMass freshRoot = 0 := by
    simpa [oldRoot, freshRoot, hcycle] using
      (quittingPassivePaddingBlock_oldContinue_mul_freshAbsorption_eq_zero
        reward upper hpenalty hcert phase)
  have htailUpper : ∀ old, oldTail old ≤ upper old := by
    intro old
    exact quittingPassivePaddingProjectedBlockValue_le_upper
      reward upper hupper hcert (finRotate (m + 1) phase) old
  have holdMass : ∀ old,
      quittingStationaryContinueMass oldRoot =
        (oldRoot old false).toReal *
          quittingStationaryContinueMass
            (Function.update oldRoot old (PMF.pure false)) := by
    intro old
    have hmass := quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul
      oldRoot old
    unfold quittingRootAbsorptionMass at hmass
    change 1 - quittingStationaryContinueMass oldRoot =
      1 - (oldRoot old false).toReal *
        quittingStationaryContinueMass
          (Function.update oldRoot old (PMF.pure false)) at hmass
    linarith
  have hpolicy : quittingPassivePaddingProjectedBlockValue U phase =
      quittingRootSuccessorPayoff reward
        (quittingPassivePaddingProjectedBlockValue U
          (finRotate (m + 1) phase))
        (quittingPassivePaddingProjectedBlockCycle hazard
          hcert.hazard_nonneg hcert.hazard_le_one phase) := by
    rw [holdRootEq, holdTailEq]
    funext old
    have hpadded := congrFun hpaddedPolicy (.inl old)
    change paddedValue phase (.inl old) =
      quittingRootSuccessorPayoff reward oldTail oldRoot old
    rw [quittingRootSuccessorPayoff,
      quittingRootExpectedPayoff_eq_absorbingContribution_add]
    change paddedValue phase (.inl old) =
      quittingRootSuccessorPayoff paddedReward
        (paddedValue (finRotate (m + 1) phase)) (paddedCycle phase) (.inl old)
      at hpadded
    rw [hroot, quittingRootSuccessorPayoff,
      quittingRootExpectedPayoff_eq_absorbingContribution_add,
      quittingRootAbsorbingContribution_passivePadding_old,
      quittingStationaryContinueMass_sumElim] at hpadded
    change paddedValue phase (.inl old) = _ at hpadded
    unfold quittingRootAbsorptionMass at hstage
    rw [hpadded]
    unfold quittingRootAbsorptionMass
    have hfreshPart : quittingStationaryContinueMass oldRoot *
        (1 - quittingStationaryContinueMass freshRoot) *
          upper old = 0 := by
      rw [hstage, zero_mul]
    have hsurvival : quittingStationaryContinueMass oldRoot *
        quittingStationaryContinueMass freshRoot =
          quittingStationaryContinueMass oldRoot := by
      nlinarith [hstage]
    rw [hfreshPart, add_zero, hsurvival]
  refine ⟨hpolicy, ?_⟩
  rw [holdRootEq, holdTailEq]
  intro old
  have hpad := hpaddedNash (.inl old)
  rw [hroot] at hpad
  have hpadOld : (oldRoot old false).toReal *
        quittingRootEndpointDifference paddedReward
          (paddedValue (finRotate (m + 1) phase))
          (Sum.elim oldRoot freshRoot) (.inl old) ≤ 0 ∧
      0 ≤ (oldRoot old true).toReal *
        quittingRootEndpointDifference paddedReward
          (paddedValue (finRotate (m + 1) phase))
          (Sum.elim oldRoot freshRoot) (.inl old) := by
    simpa using hpad
  have hgap := quittingRootEndpointDifference_passivePadding_old
    reward upper penalty oldRoot freshRoot
    (paddedValue (finRotate (m + 1) phase)) old
  change quittingRootEndpointDifference reward oldTail oldRoot old = _ at hgap
  have hcorrection : 0 ≤
      quittingStationaryContinueMass
          (Function.update oldRoot old (PMF.pure false)) *
        quittingRootAbsorptionMass freshRoot *
          (upper old - oldTail old) := by
    exact mul_nonneg
      (mul_nonneg (quittingStationaryContinueMass_nonneg _)
        (quittingRootAbsorptionMass_nonneg _))
      (sub_nonneg.mpr (htailUpper old))
  have hcontinueCorrection : (oldRoot old false).toReal *
      (quittingStationaryContinueMass
          (Function.update oldRoot old (PMF.pure false)) *
        quittingRootAbsorptionMass freshRoot *
          (upper old - oldTail old)) = 0 := by
    calc
      _ = ((oldRoot old false).toReal *
          quittingStationaryContinueMass
            (Function.update oldRoot old (PMF.pure false))) *
        quittingRootAbsorptionMass freshRoot *
          (upper old - oldTail old) := by ring
      _ = quittingStationaryContinueMass oldRoot *
          quittingRootAbsorptionMass freshRoot *
            (upper old - oldTail old) := by
        rw [← holdMass old]
      _ = 0 := by rw [hstage, zero_mul]
  constructor
  · rw [hgap, mul_add, hcontinueCorrection]
    simpa using hpadOld.1
  · simp only [neg_zero]
    rw [hgap, mul_add]
    exact add_nonneg hpadOld.2
      (mul_nonneg ENNReal.toReal_nonneg hcorrection)

omit [Nonempty I] in
/-- The projected old cycle retains the padded cycle's joint contraction. -/
theorem prod_projectedPassivePaddingBlockCycle_lt_one {m : ℕ}
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    {hazard : Fin (m + 1) → I ⊕ PUnit → ℝ}
    {U : Fin (m + 2) → Payoff (I ⊕ PUnit)}
    (hcert : IsQuittingBlockCertificate
      (quittingPassivePaddingReward (J := PUnit) reward upper penalty) hazard U) :
    (∏ phase : Fin (m + 1), quittingStationaryContinueMass
      (quittingPassivePaddingProjectedBlockCycle hazard
        hcert.hazard_nonneg hcert.hazard_le_one phase)) < 1 := by
  let paddedReward := quittingPassivePaddingReward (J := PUnit) reward upper penalty
  let block := quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U
  let paddedCycle := quittingCyclicContinuationBlockCycle m block
  have hblock : IsQuittingCyclicContinuationBlock paddedReward (U 0) (m + 1) block :=
    isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate hcert
  have hpadded : (∏ phase : Fin (m + 1),
      quittingStationaryContinueMass (paddedCycle phase)) < 1 :=
    quittingCyclicContinuationBlock_prod_continueMass_lt_one
      paddedReward (U 0) m block hblock
  have hcycle : paddedCycle = quittingBlockCycle hazard
      hcert.hazard_nonneg hcert.hazard_le_one := by
    exact quittingCyclicContinuationBlockCycle_quittingBlockPath
      hcert.hazard_nonneg hcert.hazard_le_one U
  have hphase : ∀ phase : Fin (m + 1),
      quittingStationaryContinueMass
          (quittingPassivePaddingProjectedBlockCycle hazard
            hcert.hazard_nonneg hcert.hazard_le_one phase) =
        quittingStationaryContinueMass (paddedCycle phase) := by
    intro phase
    let oldRoot : I → PMF Bool := fun old ↦ paddedCycle phase (.inl old)
    let freshRoot : PUnit → PMF Bool := fun fresh ↦ paddedCycle phase (.inr fresh)
    have hroot : paddedCycle phase = Sum.elim oldRoot freshRoot := by
      funext player
      cases player <;> rfl
    have hstage : quittingStationaryContinueMass oldRoot *
        quittingRootAbsorptionMass freshRoot = 0 := by
      simpa [oldRoot, freshRoot, hcycle] using
        (quittingPassivePaddingBlock_oldContinue_mul_freshAbsorption_eq_zero
          reward upper hpenalty hcert phase)
    have hsurvival : quittingStationaryContinueMass oldRoot *
        quittingStationaryContinueMass freshRoot =
          quittingStationaryContinueMass oldRoot := by
      unfold quittingRootAbsorptionMass at hstage
      nlinarith
    have holdRoot : quittingPassivePaddingProjectedBlockCycle hazard
        hcert.hazard_nonneg hcert.hazard_le_one phase = oldRoot := by
      funext old
      exact congrFun (congrFun hcycle phase) (.inl old) |>.symm
    rw [holdRoot]
    rw [hroot, quittingStationaryContinueMass_sumElim, hsurvival]
  rw [Finset.prod_congr rfl (fun phase _ ↦ hphase phase)]
  exact hpadded

omit [DecidableEq I] [Nonempty I] in
/-- A contracting finite cycle, read forever, is a completely absorbing
inverse-iterate row sequence. -/
theorem isCompletelyAbsorbing_quittingCyclicRootSequence {K : ℕ}
    (cycle : Fin K → I → PMF Bool) (phase : Fin K)
    (hcycle : (∏ stage : Fin K,
      quittingStationaryContinueMass (cycle stage)) < 1) :
    IsCompletelyAbsorbing (quittingCyclicRootSequence cycle phase) := by
  have hjoint := tendsto_zero_quittingJointSurvivalWeight_cyclicRootSequence
    cycle phase hcycle
  unfold IsCompletelyAbsorbing
  apply hjoint.congr'
  filter_upwards with fuel
  rw [quittingJointSurvivalWeight_eq_prod]
  simp [quittingSurvivalPrefix]

omit [Nonempty I] in
/-- **Passive-padding block-certificate retraction.** Every exact bounded,
absorbing, admissible finite block certificate for a valid one-passive-player
padding produces a bounded completely absorbing inverse iterate of the old
game. -/
theorem exists_boundedCompletelyAbsorbingInverseIterate_of_onePassivePlayerBlockCertificate
    {m : ℕ}
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ)
    (hupper : ∀ terminal old, reward terminal old ≤ upper old)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    {hazard : Fin (m + 1) → I ⊕ PUnit → ℝ}
    {U : Fin (m + 2) → Payoff (I ⊕ PUnit)}
    (hcert : IsQuittingBlockCertificate
      (quittingPassivePaddingReward (J := PUnit) reward upper penalty) hazard U) :
    ∃ (rows : ℕ → I → PMF Bool) (values : ℕ → Payoff I) (M : ℝ),
      (∀ time old, |values time old| ≤ M) ∧
        IsQuittingInverseIterate reward rows values ∧
        IsCompletelyAbsorbing rows := by
  let cycle := quittingPassivePaddingProjectedBlockCycle hazard
    hcert.hazard_nonneg hcert.hazard_le_one
  let phase : Fin (m + 1) := 0
  let rows := quittingCyclicRootSequence cycle phase
  let values : ℕ → Payoff I := fun time ↦
    quittingPassivePaddingProjectedBlockValue U
      (quittingCyclicOrbit phase time)
  let M := quittingRewardBound
    (quittingPassivePaddingReward (J := PUnit) reward upper penalty)
  refine ⟨rows, values, M, ?_, ?_, ?_⟩
  · intro time old
    exact hcert.box (Fin.castSucc (quittingCyclicOrbit phase time)) (.inl old)
  · intro time
    have hphase :=
      isQuittingRootSuccessorCertificate_projectedPassivePaddingBlockPhase
        reward upper hupper hpenalty hcert (quittingCyclicOrbit phase time)
    simpa [rows, values, cycle, quittingCyclicRootSequence,
      quittingCyclicOrbit_succ] using hphase
  · apply isCompletelyAbsorbing_quittingCyclicRootSequence
    exact prod_projectedPassivePaddingBlockCycle_lt_one
      reward upper hpenalty hcert

omit [Nonempty I] in
/-- A bounded inverse-iterate no-go for the old game rules out every finite
admissible exact block certificate in any valid one-passive-player padding. -/
theorem no_onePassivePlayerBlockCertificate_of_noBoundedCompletelyAbsorbingInverseIterate
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (hno : NoBoundedCompletelyAbsorbingInverseIterate reward)
    (upper : I → ℝ)
    (hupper : ∀ terminal old, reward terminal old ≤ upper old)
    {penalty : ℝ} (hpenalty : 0 < penalty) :
    ¬ ∃ (m : ℕ) (hazard : Fin (m + 1) → I ⊕ PUnit → ℝ)
        (U : Fin (m + 2) → Payoff (I ⊕ PUnit)),
      IsQuittingBlockCertificate
        (quittingPassivePaddingReward (J := PUnit) reward upper penalty) hazard U := by
  rintro ⟨m, hazard, U, hcert⟩
  exact hno
    (exists_boundedCompletelyAbsorbingInverseIterate_of_onePassivePlayerBlockCertificate
      reward upper hupper hpenalty hcert)

end GameTheory
