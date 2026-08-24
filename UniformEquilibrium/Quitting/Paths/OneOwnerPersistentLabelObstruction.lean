/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import MathUE.SequenceVariation
import Mathlib.Analysis.PSeries

/-!
# One-owner obstruction to two persistent exact-spine labels

This module formalizes a bounded-potential obstruction for one explicit
finite quitting reward.  Every outsider's marginal Quit stream is summable
on every canonical exact Nash--Bellman spine.  Thus no such spine carries two
distinct persistent labels, even though the reward admits exact local roots
with two active outsider labels.

This refutes only an unconditional exact-spine selector.  It does not refute
a selector restricted to a no-uniform-equilibrium or positive-debt branch.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open Filter
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The owner gets zero when it quits and minus one when only outsiders quit.
An outsider gets minus one exactly when it joins the owner. -/
def oneOwnerHazardObstructionReward
    (owner : ι) (terminal : {S : Finset ι // S.Nonempty}) : Payoff ι :=
  fun who =>
    if who = owner then
      if owner ∈ terminal.1 then 0 else -1
    else if owner ∈ terminal.1 ∧ who ∈ terminal.1 then -1 else 0

omit [Fintype ι] in
@[simp] theorem oneOwnerHazardObstructionReward_owner
    (owner : ι) (terminal : {S : Finset ι // S.Nonempty}) :
    oneOwnerHazardObstructionReward owner terminal owner =
      if owner ∈ terminal.1 then 0 else -1 := by
  simp [oneOwnerHazardObstructionReward]

omit [Fintype ι] in
@[simp] theorem oneOwnerHazardObstructionReward_outsider
    (owner who : ι) (hne : who ≠ owner)
    (terminal : {S : Finset ι // S.Nonempty}) :
    oneOwnerHazardObstructionReward owner terminal who =
      if owner ∈ terminal.1 ∧ who ∈ terminal.1 then -1 else 0 := by
  simp [oneOwnerHazardObstructionReward, hne]

omit [Fintype ι] in
theorem abs_oneOwnerHazardObstructionReward_le_one
    (owner : ι) (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |oneOwnerHazardObstructionReward owner terminal who| ≤ 1 := by
  simp only [oneOwnerHazardObstructionReward]
  split <;> split <;> norm_num

@[simp] theorem quittingRootQuitPayoff_oneOwnerHazardObstruction
    (owner : ι) (tail : Payoff ι) (root : ι → PMF Bool) :
    quittingRootQuitPayoff (oneOwnerHazardObstructionReward owner)
        tail root owner = 0 := by
  classical
  unfold quittingRootQuitPayoff
  rw [quittingRootExpectedPayoff_eq_sum_coalitionMass]
  apply Finset.sum_eq_zero
  intro coalition _
  by_cases howner : owner ∈ coalition
  · have hnonempty : coalition.Nonempty := ⟨owner, howner⟩
    simp [quittingStageCoalitionPayoff, hnonempty, howner]
  · have hmass : coalitionMass
        (hazardOfRoot (Function.update root owner (PMF.pure true)))
        coalition = 0 := by
      unfold coalitionMass hazardOfRoot
      have hzero :
          ∏ i ∈ coalitionᶜ,
              (1 - (Function.update root owner (PMF.pure true) i true).toReal) = 0 := by
        apply Finset.prod_eq_zero
        · simpa [Finset.mem_compl] using howner
        · simp
      rw [hzero, mul_zero]
    rw [hmass, zero_mul]

/-- The owner's immediate reward after it is forced to Continue is minus the
probability that at least one outsider Quits. -/
theorem quittingRootDeletedContinueReward_oneOwnerHazardObstruction
    (owner : ι) (root : ι → PMF Bool) :
    quittingRootDeletedContinueReward
        (oneOwnerHazardObstructionReward owner) root owner =
      -quittingRootOpponentAbsorptionMass root owner := by
  classical
  unfold quittingRootDeletedContinueReward quittingRootAbsorbingContribution
  rw [quittingRootExpectedPayoff_eq_sum_coalitionMass]
  have htotal := sum_coalitionMass_nonempty
    (hazardOfRoot (Function.update root owner (PMF.pure false)))
  have hcontinue : continueMass
      (hazardOfRoot (Function.update root owner (PMF.pure false))) =
        quittingRootOpponentContinueMass root owner := by
    unfold continueMass hazardOfRoot quittingRootOpponentContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_congr rfl
    intro who _
    have hsum := pmf_toReal_sum_one
      (Function.update root owner (PMF.pure false) who)
    rw [Fintype.sum_bool] at hsum
    linarith
  have habs :
      ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          coalitionMass
            (hazardOfRoot (Function.update root owner (PMF.pure false)))
            coalition = quittingRootOpponentAbsorptionMass root owner := by
    rw [htotal, hcontinue,
      quittingRootOpponentContinueMass_eq_one_sub_absorptionMass]
    ring
  calc
    (∑ coalition : Finset ι,
        coalitionMass
            (hazardOfRoot (Function.update root owner (PMF.pure false)))
            coalition *
          quittingStageCoalitionPayoff
            (oneOwnerHazardObstructionReward owner) 0 coalition owner) =
      ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          coalitionMass
              (hazardOfRoot (Function.update root owner (PMF.pure false)))
              coalition *
            quittingStageCoalitionPayoff
              (oneOwnerHazardObstructionReward owner) 0 coalition owner := by
        symm
        apply Finset.sum_erase
        simp [quittingStageCoalitionPayoff]
    _ = ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
        -coalitionMass
          (hazardOfRoot (Function.update root owner (PMF.pure false)))
          coalition := by
        apply Finset.sum_congr rfl
        intro coalition hcoalition
        have hne : coalition ≠ ∅ := Finset.ne_of_mem_erase hcoalition
        have hnonempty : coalition.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
        by_cases howner : owner ∈ coalition
        · have hmass : coalitionMass
              (hazardOfRoot (Function.update root owner (PMF.pure false)))
              coalition = 0 := by
            unfold coalitionMass hazardOfRoot
            have hzero :
                ∏ i ∈ coalition,
                    (Function.update root owner (PMF.pure false) i true).toReal = 0 := by
              apply Finset.prod_eq_zero howner
              simp
            rw [hzero, zero_mul]
          simp [hmass]
        · have hpayoff :
              quittingStageCoalitionPayoff
                  (oneOwnerHazardObstructionReward owner) 0 coalition owner = -1 := by
            simp [quittingStageCoalitionPayoff, hnonempty, howner]
          rw [hpayoff]
          ring
    _ = -quittingRootOpponentAbsorptionMass root owner := by
      rw [Finset.sum_neg_distrib, habs]

theorem quittingRootContinuePayoff_oneOwnerHazardObstruction
    (owner : ι) (tail : Payoff ι) (root : ι → PMF Bool) :
    quittingRootContinuePayoff (oneOwnerHazardObstructionReward owner)
        tail root owner =
      quittingRootOpponentContinueMass root owner * tail owner -
        quittingRootOpponentAbsorptionMass root owner := by
  rw [quittingRootContinuePayoff_eq_deleted,
    quittingRootDeletedContinueReward_oneOwnerHazardObstruction]
  unfold quittingRootDeletedContinueMass quittingRootOpponentContinueMass
  ring

private theorem coalitionMass_hazardOfRoot_eq_zero_of_pure_true_not_mem
    (root : ι → PMF Bool) {owner : ι} (hroot : root owner = PMF.pure true)
    {coalition : Finset ι} (howner : owner ∉ coalition) :
    coalitionMass (hazardOfRoot root) coalition = 0 := by
  unfold coalitionMass hazardOfRoot
  have hzero :
      ∏ i ∈ coalitionᶜ, (1 - (root i true).toReal) = 0 := by
    apply Finset.prod_eq_zero
    · simpa [Finset.mem_compl] using howner
    · rw [hroot]
      simp
  rw [hzero, mul_zero]

private theorem coalitionMass_hazardOfRoot_eq_zero_of_pure_false_mem
    (root : ι → PMF Bool) {owner : ι} (hroot : root owner = PMF.pure false)
    {coalition : Finset ι} (howner : owner ∈ coalition) :
    coalitionMass (hazardOfRoot root) coalition = 0 := by
  unfold coalitionMass hazardOfRoot
  have hzero : ∏ i ∈ coalition, (root i true).toReal = 0 := by
    apply Finset.prod_eq_zero howner
    rw [hroot]
    simp
  rw [hzero, zero_mul]

theorem quittingRootQuitPayoff_outsider_oneOwnerHazardObstruction_of_owner_sureQuit
    (owner who : ι) (hne : who ≠ owner) (tail : Payoff ι)
    (root : ι → PMF Bool) (howner : (root owner true).toReal = 1) :
    quittingRootQuitPayoff (oneOwnerHazardObstructionReward owner)
        tail root who = -1 := by
  classical
  have hrootOwner : root owner = PMF.pure true :=
    Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ howner
  unfold quittingRootQuitPayoff
  rw [quittingRootExpectedPayoff_eq_sum_coalitionMass]
  have htotal := sum_coalitionMass
    (hazardOfRoot (Function.update root who (PMF.pure true)))
  calc
    (∑ coalition : Finset ι,
        coalitionMass
            (hazardOfRoot (Function.update root who (PMF.pure true))) coalition *
          quittingStageCoalitionPayoff
            (oneOwnerHazardObstructionReward owner) tail coalition who) =
      ∑ coalition : Finset ι,
        -coalitionMass
          (hazardOfRoot (Function.update root who (PMF.pure true))) coalition := by
        apply Finset.sum_congr rfl
        intro coalition _
        by_cases ho : owner ∈ coalition
        · by_cases hw : who ∈ coalition
          · have hnonempty : coalition.Nonempty := ⟨owner, ho⟩
            have hpayoff : quittingStageCoalitionPayoff
                (oneOwnerHazardObstructionReward owner) tail coalition who = -1 := by
              simp [quittingStageCoalitionPayoff, hnonempty, hne, ho, hw]
            rw [hpayoff]
            ring
          · have hmass : coalitionMass
                (hazardOfRoot (Function.update root who (PMF.pure true)))
                coalition = 0 := by
              apply coalitionMass_hazardOfRoot_eq_zero_of_pure_true_not_mem
                (owner := who)
              · simp
              · exact hw
            simp [hmass]
        · have hmass : coalitionMass
              (hazardOfRoot (Function.update root who (PMF.pure true)))
              coalition = 0 := by
            apply coalitionMass_hazardOfRoot_eq_zero_of_pure_true_not_mem
              (owner := owner)
            · simpa [Function.update_of_ne hne.symm] using hrootOwner
            · exact ho
          simp [hmass]
    _ = -1 := by rw [Finset.sum_neg_distrib, htotal]

theorem quittingRootContinuePayoff_outsider_oneOwnerHazardObstruction_of_owner_sureQuit
    (owner who : ι) (hne : who ≠ owner) (tail : Payoff ι)
    (root : ι → PMF Bool) (howner : (root owner true).toReal = 1) :
    quittingRootContinuePayoff (oneOwnerHazardObstructionReward owner)
        tail root who = 0 := by
  classical
  have hrootOwner : root owner = PMF.pure true :=
    Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ howner
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_sum_coalitionMass]
  apply Finset.sum_eq_zero
  intro coalition _
  by_cases ho : owner ∈ coalition
  · by_cases hw : who ∈ coalition
    · have hmass : coalitionMass
          (hazardOfRoot (Function.update root who (PMF.pure false))) coalition = 0 := by
        apply coalitionMass_hazardOfRoot_eq_zero_of_pure_false_mem
          (owner := who)
        · simp
        · exact hw
      simp [hmass]
    · have hnonempty : coalition.Nonempty := ⟨owner, ho⟩
      simp [quittingStageCoalitionPayoff, hnonempty, hne, ho, hw]
  · have hmass : coalitionMass
        (hazardOfRoot (Function.update root who (PMF.pure false))) coalition = 0 := by
      apply coalitionMass_hazardOfRoot_eq_zero_of_pure_true_not_mem
        (owner := owner)
      · simpa [Function.update_of_ne hne.symm] using hrootOwner
      · exact ho
    simp [hmass]

/-- The deleted-owner clock charge is paid by the increase of the owner's
Bellman value at every exact root. -/
theorem ownerDeletedCharge_le_value_succ_sub_value_of_exactRoot
    (owner : ι) (current tail : Payoff ι) (root : ι → PMF Bool)
    (hbellman : current = quittingRootSuccessorPayoff
      (oneOwnerHazardObstructionReward owner) tail root)
    (hnash : IsεQuittingRootNash
      (oneOwnerHazardObstructionReward owner) tail 0 root)
    (htail : 0 ≤ tail owner) :
    quittingRootOpponentAbsorptionMass root owner ≤
      tail owner - current owner := by
  classical
  let quitMass := (root owner true).toReal
  let continueMass := (root owner false).toReal
  let opponentCharge := quittingRootOpponentAbsorptionMass root owner
  have hsum : continueMass + quitMass = 1 := by
    exact quittingRoot_continueProbability_add_quitProbability root owner
  have hquitNonneg : 0 ≤ quitMass := ENNReal.toReal_nonneg
  have hcontinueNonneg : 0 ≤ continueMass := ENNReal.toReal_nonneg
  have hquitLeOne : quitMass ≤ 1 := by linarith
  have hendpoint : IsεQuittingRootEndpointNash
      (oneOwnerHazardObstructionReward owner) tail 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      (oneOwnerHazardObstructionReward owner) tail root).2 hnash
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    (oneOwnerHazardObstructionReward owner) tail root owner
  have hcurrent := congrFun hbellman owner
  have hcontinue := quittingRootContinuePayoff_oneOwnerHazardObstruction
    owner tail root
  have hopponentNonneg : 0 ≤ opponentCharge :=
    quittingRootOpponentAbsorptionMass_nonneg root owner
  have hopponentContinue :=
    quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root owner
  by_cases hquitZero : quitMass = 0
  · have hcontinueOne : continueMass = 1 := by linarith
    have hcontinueEndpoint := (hendpoint owner).1
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_oneOwnerHazardObstruction] at hcontinueEndpoint
    have hcontinuePayoff : 0 ≤ quittingRootContinuePayoff
        (oneOwnerHazardObstructionReward owner) tail root owner := by
      nlinarith
    have hcurrentEq : current owner = quittingRootContinuePayoff
        (oneOwnerHazardObstructionReward owner) tail root owner := by
      rw [hcurrent, hmix,
        quittingRootQuitPayoff_oneOwnerHazardObstruction]
      nlinarith
    rw [hcurrentEq, hcontinue, hopponentContinue]
    nlinarith [mul_nonneg hopponentNonneg htail]
  · by_cases hquitOne : quitMass = 1
    · have hcontinueZero : continueMass = 0 := by linarith
      have houtsiderZero : ∀ who, who ≠ owner →
          quittingMarginalQuitHazard (fun _ => root) who 0 = 0 := by
        intro who hne
        have hwho := (hendpoint who).2
        rw [quittingRootEndpointDifference,
          quittingRootQuitPayoff_outsider_oneOwnerHazardObstruction_of_owner_sureQuit
            owner who hne tail root hquitOne,
          quittingRootContinuePayoff_outsider_oneOwnerHazardObstruction_of_owner_sureQuit
            owner who hne tail root hquitOne] at hwho
        norm_num at hwho
        have hnonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
        change (root who true).toReal = 0
        nlinarith
      have hopponentZero : opponentCharge = 0 := by
        apply le_antisymm
        · calc
            opponentCharge = quittingOpponentClockCharge (fun _ => root) owner 0 := rfl
            _ ≤ ∑ who ∈ Finset.univ.erase owner,
                quittingMarginalQuitHazard (fun _ => root) who 0 :=
              quittingOpponentClockCharge_le_sum_marginalQuitHazard
                (fun _ => root) owner 0
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro who hwho
              exact houtsiderZero who (Finset.ne_of_mem_erase hwho)
        · exact hopponentNonneg
      have hcurrentZero : current owner = 0 := by
        change (root owner true).toReal = 1 at hquitOne
        change (root owner false).toReal = 0 at hcontinueZero
        rw [hcurrent, hmix,
          quittingRootQuitPayoff_oneOwnerHazardObstruction,
          hquitOne, hcontinueZero]
        ring
      change quittingRootOpponentAbsorptionMass root owner = 0 at hopponentZero
      rw [hopponentZero, hcurrentZero]
      simpa using htail
    · have hquitPos : 0 < quitMass := lt_of_le_of_ne hquitNonneg (Ne.symm hquitZero)
      have hcontinuePos : 0 < continueMass := by
        have : quitMass < 1 := lt_of_le_of_ne hquitLeOne hquitOne
        linarith
      have hcontinueSide := (hendpoint owner).1
      have hquitSide := (hendpoint owner).2
      rw [quittingRootEndpointDifference,
        quittingRootQuitPayoff_oneOwnerHazardObstruction] at hcontinueSide hquitSide
      have hcontinueZero : quittingRootContinuePayoff
          (oneOwnerHazardObstructionReward owner) tail root owner = 0 := by
        nlinarith
      have hcurrentZero : current owner = 0 := by
        rw [hcurrent, hmix,
          quittingRootQuitPayoff_oneOwnerHazardObstruction, hcontinueZero]
        ring
      rw [hcontinue, hopponentContinue] at hcontinueZero
      rw [hcurrentZero]
      nlinarith [mul_nonneg hopponentNonneg htail]

theorem ownerValue_nonneg_of_exactSpine
    (owner : ι) (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner) value roots) (time : ℕ) :
    0 ≤ value time owner := by
  calc
    (0 : ℝ) = quittingRootQuitPayoff
        (oneOwnerHazardObstructionReward owner)
        (value (time + 1)) (roots time) owner := by simp
    _ ≤ quittingRootSuccessorPayoff
        (oneOwnerHazardObstructionReward owner)
        (value (time + 1)) (roots time) owner :=
      quittingRootQuitPayoff_le_successor_of_isZeroNash
        (oneOwnerHazardObstructionReward owner)
        (value (time + 1)) (roots time) owner (hspine.2.2 time)
    _ = value time owner := (congrFun (hspine.2.1 time) owner).symm

theorem ownerDeletedCharge_le_value_succ_sub_value_of_exactSpine
    (owner : ι) (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner) value roots) (time : ℕ) :
    quittingOpponentClockCharge roots owner time ≤
      value (time + 1) owner - value time owner := by
  exact ownerDeletedCharge_le_value_succ_sub_value_of_exactRoot
    owner (value time) (value (time + 1)) (roots time)
    (hspine.2.1 time) (hspine.2.2 time)
    (ownerValue_nonneg_of_exactSpine owner value roots hspine (time + 1))

/-- Every outsider clock is summable on every bounded exact spine for the
one-owner reward. -/
theorem summable_ownerDeletedClock_of_exactSpine
    (owner : ι) (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner) value roots) :
    Summable (quittingOpponentClockCharge roots owner) := by
  apply summable_of_sum_range_le
    (quittingOpponentClockCharge_nonneg roots owner)
  intro horizon
  calc
    (∑ time ∈ Finset.range horizon,
        quittingOpponentClockCharge roots owner time) ≤
      ∑ time ∈ Finset.range horizon,
        (value (time + 1) owner - value time owner) := by
      apply Finset.sum_le_sum
      intro time _
      exact ownerDeletedCharge_le_value_succ_sub_value_of_exactSpine
        owner value roots hspine time
    _ = value horizon owner - value 0 owner := by
      have htelescope := Math.sum_range_sub_succ
        (fun time => value time owner) horizon
      calc
        (∑ time ∈ Finset.range horizon,
            (value (time + 1) owner - value time owner)) =
          -(∑ time ∈ Finset.range horizon,
              (value time owner - value (time + 1) owner)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro time _
            ring
        _ = value horizon owner - value 0 owner := by
          rw [htelescope]
          ring
    _ ≤ 2 * quittingRewardBound (oneOwnerHazardObstructionReward owner) := by
      have hfinal := abs_le.mp (hspine.1 horizon owner)
      have hinitial := abs_le.mp (hspine.1 0 owner)
      linarith

/-- Under the unit value bound used in the ordinary statement of the
counterexample, every initial deleted-owner partial sum is at most one. -/
theorem sum_range_ownerDeletedClock_le_one_of_exactSpine
    (owner : ι) (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner) value roots)
    (hunit : ∀ time, |value time owner| ≤ 1) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
      quittingOpponentClockCharge roots owner time) ≤ 1 := by
  calc
    (∑ time ∈ Finset.range horizon,
        quittingOpponentClockCharge roots owner time) ≤
      ∑ time ∈ Finset.range horizon,
        (value (time + 1) owner - value time owner) := by
      apply Finset.sum_le_sum
      intro time _
      exact ownerDeletedCharge_le_value_succ_sub_value_of_exactSpine
        owner value roots hspine time
    _ = value horizon owner - value 0 owner := by
      have htelescope := Math.sum_range_sub_succ
        (fun time => value time owner) horizon
      calc
        (∑ time ∈ Finset.range horizon,
            (value (time + 1) owner - value time owner)) =
          -(∑ time ∈ Finset.range horizon,
              (value time owner - value (time + 1) owner)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro time _
            ring
        _ = value horizon owner - value 0 owner := by
          rw [htelescope]
          ring
    _ ≤ 1 := by
      have hfinal := (abs_le.mp (hunit horizon)).2
      have hinitial := ownerValue_nonneg_of_exactSpine owner value roots hspine 0
      linarith

theorem summable_marginalQuitHazard_outsider_of_exactSpine
    (owner : ι) (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner) value roots)
    (who : ι) (hne : who ≠ owner) :
    Summable (quittingMarginalQuitHazard roots who) := by
  exact (summable_ownerDeletedClock_of_exactSpine owner value roots hspine).of_nonneg_of_le
    (quittingMarginalQuitHazard_nonneg roots who)
    (quittingMarginalQuitHazard_le_opponentClockCharge roots hne)

/-- Principal negative result: no canonical exact spine for this reward has
two distinct persistent marginal labels. -/
theorem not_hasTwoPersistentQuittingMarginals_oneOwnerReward
    (owner : ι) (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner) value roots) :
    ¬HasTwoPersistentQuittingMarginals roots := by
  rintro ⟨first, second, hne, hfirst, hsecond⟩
  by_cases hfirstOwner : first = owner
  · apply hsecond
    exact summable_marginalQuitHazard_outsider_of_exactSpine
      owner value roots hspine second (by simpa [hfirstOwner] using hne.symm)
  · apply hfirst
    exact summable_marginalQuitHazard_outsider_of_exactSpine
      owner value roots hspine first hfirstOwner

theorem not_consecutiveBlock_summableError_twoLabelTransport_oneOwnerReward
    (owner : ι) (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner) value roots)
    (length : ℕ → ℕ) (nominal : ℕ → ι → ℝ)
    {first second : ι} (hne : first ≠ second)
    (hnominal : ∀ time who, 0 ≤ nominal time who)
    (hfirst : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time first)))
    (hsecond : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time second))) :
    ¬(Summable (consecutiveBlockSum length (fun time =>
        |quittingMarginalQuitHazard roots first time - nominal time first|)) ∧
      Summable (consecutiveBlockSum length (fun time =>
        |quittingMarginalQuitHazard roots second time - nominal time second|))) := by
  rintro ⟨hfirstError, hsecondError⟩
  exact not_hasTwoPersistentQuittingMarginals_oneOwnerReward
    owner value roots hspine
    (hasTwoPersistentQuittingMarginals_of_consecutiveBlock_summableError
      roots length nominal hne hnominal hfirst hsecond hfirstError hsecondError)

theorem not_consecutiveBlock_fixedFraction_twoLabelTransport_oneOwnerReward
    (owner : ι) (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner) value roots)
    (length : ℕ → ℕ) (nominal : ℕ → ι → ℝ)
    {first second : ι} (hne : first ≠ second) {theta : ℝ}
    (htheta : 0 < theta) (hnominal : ∀ time who, 0 ≤ nominal time who)
    (hfirst : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time first)))
    (hsecond : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time second))) :
    ¬((∀ time, theta * nominal time first ≤
        quittingMarginalQuitHazard roots first time) ∧
      (∀ time, theta * nominal time second ≤
        quittingMarginalQuitHazard roots second time)) := by
  rintro ⟨hfirstRetain, hsecondRetain⟩
  exact not_hasTwoPersistentQuittingMarginals_oneOwnerReward
    owner value roots hspine
    (hasTwoPersistentQuittingMarginals_of_consecutiveBlock_fixedFraction
      roots length nominal hne htheta hnominal hfirstRetain hsecondRetain
      hfirst hsecond)

/-! ## Immediate-exit boundary spine -/

/-- The owner quits surely and every outsider continues surely. -/
def oneOwnerImmediateExitRoot (owner : ι) (who : ι) : PMF Bool :=
  if who = owner then PMF.pure true else PMF.pure false

omit [Fintype ι] in
@[simp] theorem oneOwnerImmediateExitRoot_owner (owner : ι) :
    oneOwnerImmediateExitRoot owner owner = PMF.pure true := by
  simp [oneOwnerImmediateExitRoot]

omit [Fintype ι] in
@[simp] theorem oneOwnerImmediateExitRoot_outsider
    (owner who : ι) (hne : who ≠ owner) :
    oneOwnerImmediateExitRoot owner who = PMF.pure false := by
  simp [oneOwnerImmediateExitRoot, hne]

@[simp] theorem quittingRootOpponentAbsorptionMass_oneOwnerImmediateExitRoot_owner
    (owner : ι) :
    quittingRootOpponentAbsorptionMass (oneOwnerImmediateExitRoot owner) owner = 0 := by
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  have hproduct :
      (∏ who ∈ Finset.univ.erase owner,
          (1 - (oneOwnerImmediateExitRoot owner who true).toReal)) = 1 := by
    apply Finset.prod_eq_one
    intro who hwho
    have hne := Finset.ne_of_mem_erase hwho
    simp [oneOwnerImmediateExitRoot, hne]
  rw [hproduct]
  ring

theorem isZeroQuittingRootNash_oneOwnerImmediateExitRoot (owner : ι) :
    IsεQuittingRootNash (oneOwnerHazardObstructionReward owner) 0 0
      (oneOwnerImmediateExitRoot owner) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  by_cases hwho : who = owner
  · subst who
    have hcontinue := quittingRootContinuePayoff_oneOwnerHazardObstruction
      owner 0 (oneOwnerImmediateExitRoot owner)
    rw [quittingRootOpponentAbsorptionMass_oneOwnerImmediateExitRoot_owner] at hcontinue
    simp only [Pi.zero_apply, mul_zero, sub_zero] at hcontinue
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_oneOwnerHazardObstruction, hcontinue]
    simp
  · have howner :
        ((oneOwnerImmediateExitRoot owner owner) true).toReal = 1 := by simp
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_outsider_oneOwnerHazardObstruction_of_owner_sureQuit
        owner who hwho 0 (oneOwnerImmediateExitRoot owner) howner,
      quittingRootContinuePayoff_outsider_oneOwnerHazardObstruction_of_owner_sureQuit
        owner who hwho 0 (oneOwnerImmediateExitRoot owner) howner]
    simp [oneOwnerImmediateExitRoot, hwho]

theorem quittingRootSuccessorPayoff_oneOwnerImmediateExitRoot (owner : ι) :
    quittingRootSuccessorPayoff (oneOwnerHazardObstructionReward owner) 0
      (oneOwnerImmediateExitRoot owner) = 0 := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  by_cases hwho : who = owner
  · subst who
    rw [quittingRootQuitPayoff_oneOwnerHazardObstruction]
    simp [oneOwnerImmediateExitRoot]
  · have howner :
        ((oneOwnerImmediateExitRoot owner owner) true).toReal = 1 := by simp
    rw [quittingRootQuitPayoff_outsider_oneOwnerHazardObstruction_of_owner_sureQuit
        owner who hwho 0 (oneOwnerImmediateExitRoot owner) howner,
      quittingRootContinuePayoff_outsider_oneOwnerHazardObstruction_of_owner_sureQuit
        owner who hwho 0 (oneOwnerImmediateExitRoot owner) howner]
    simp [oneOwnerImmediateExitRoot, hwho]

/-- The obstruction is nonvacuous: the table has a bounded stationary exact
Nash--Bellman spine with immediate owner exit. -/
theorem isCanonicalExactQuittingNashBellmanSpine_oneOwnerImmediateExit
    (owner : ι) :
    IsCanonicalExactQuittingNashBellmanSpine
      (oneOwnerHazardObstructionReward owner)
      (fun _ => 0) (fun _ => oneOwnerImmediateExitRoot owner) := by
  refine ⟨?_, ?_, ?_⟩
  · intro time who
    simpa using quittingRewardBound_nonneg
      (oneOwnerHazardObstructionReward owner)
  · intro time
    simpa using (quittingRootSuccessorPayoff_oneOwnerImmediateExitRoot owner).symm
  · intro time
    exact isZeroQuittingRootNash_oneOwnerImmediateExitRoot owner

theorem zero_isUniformEquilibriumPayoff_oneOwnerHazardObstruction
    (owner : ι) :
    (quittingGame (oneOwnerHazardObstructionReward owner)).IsUniformEquilibriumPayoff
      none 0 := by
  apply isUniformEquilibriumPayoff_of_stationaryEndpointCertificate
    (oneOwnerHazardObstructionReward owner)
    (oneOwnerImmediateExitRoot owner) 0
  · rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    have hzero :
        ∏ who, (oneOwnerImmediateExitRoot owner who false).toReal = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ owner)
      simp
    rw [hzero]
    norm_num
  · simpa using (quittingRootSuccessorPayoff_oneOwnerImmediateExitRoot owner).symm
  · exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      (oneOwnerHazardObstructionReward owner) 0
      (oneOwnerImmediateExitRoot owner)).2
      (isZeroQuittingRootNash_oneOwnerImmediateExitRoot owner)
  · intro who hmass
    by_cases hwho : who = owner
    · subst who
      simp [oneOwnerHazardObstructionReward, quittingSingletonTerminal]
    · have hle := quittingRootOpponentContinueMass_le_continueProbability_of_ne
          (oneOwnerImmediateExitRoot owner) (Ne.symm hwho)
      change quittingStationaryFixedOpponentsContinueMass
          (oneOwnerImmediateExitRoot owner) who ≤
        (oneOwnerImmediateExitRoot owner owner false).toReal at hle
      rw [hmass] at hle
      simp [oneOwnerImmediateExitRoot] at hle
      linarith

private theorem quittingRootExpectedPayoff_outsider_eq_zero_of_owner_sureContinue
    (owner who : ι) (hne : who ≠ owner) (tail : Payoff ι)
    (htail : tail who = 0) (root : ι → PMF Bool)
    (howner : root owner = PMF.pure false) :
    quittingRootExpectedPayoff (oneOwnerHazardObstructionReward owner)
      tail root who = 0 := by
  classical
  rw [quittingRootExpectedPayoff_eq_sum_coalitionMass]
  apply Finset.sum_eq_zero
  intro coalition _
  by_cases ho : owner ∈ coalition
  · have hmass : coalitionMass (hazardOfRoot root) coalition = 0 :=
      coalitionMass_hazardOfRoot_eq_zero_of_pure_false_mem root howner ho
    simp [hmass]
  · by_cases hnonempty : coalition.Nonempty
    · simp [quittingStageCoalitionPayoff, hnonempty,
        oneOwnerHazardObstructionReward, hne, ho]
    · have hempty : coalition = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
      subst coalition
      simp [quittingStageCoalitionPayoff, htail]

theorem quittingRootQuitPayoff_outsider_oneOwnerHazardObstruction_of_owner_sureContinue
    (owner who : ι) (hne : who ≠ owner) (tail : Payoff ι)
    (htail : tail who = 0) (root : ι → PMF Bool)
    (howner : root owner = PMF.pure false) :
    quittingRootQuitPayoff (oneOwnerHazardObstructionReward owner)
      tail root who = 0 := by
  unfold quittingRootQuitPayoff
  apply quittingRootExpectedPayoff_outsider_eq_zero_of_owner_sureContinue
    owner who hne tail htail
  simpa [Function.update_of_ne hne.symm] using howner

theorem quittingRootContinuePayoff_outsider_oneOwnerHazardObstruction_of_owner_sureContinue
    (owner who : ι) (hne : who ≠ owner) (tail : Payoff ι)
    (htail : tail who = 0) (root : ι → PMF Bool)
    (howner : root owner = PMF.pure false) :
    quittingRootContinuePayoff (oneOwnerHazardObstructionReward owner)
      tail root who = 0 := by
  unfold quittingRootContinuePayoff
  apply quittingRootExpectedPayoff_outsider_eq_zero_of_owner_sureContinue
    owner who hne tail htail
  simpa [Function.update_of_ne hne.symm] using howner

/-! ## Four-player local packet boundary -/

namespace OneOwnerFourPlayerPacket

abbrev Player := Fin 4

def owner : Player := 0
def first : Player := 1
def second : Player := 2
def dormant : Player := 3

def hazard (s : ℝ) (who : Player) : ℝ :=
  if who = first ∨ who = second then s else 0

theorem hazard_nonneg {s : ℝ} (hs : 0 ≤ s) (who : Player) :
    0 ≤ hazard s who := by
  simp only [hazard]
  split <;> positivity

theorem hazard_le_one {s : ℝ} (hs : s ≤ 1) (who : Player) :
    hazard s who ≤ 1 := by
  simp only [hazard]
  split <;> linarith

def root (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Player → PMF Bool :=
  rootOfHazard (hazard s) (hazard_nonneg hs0) (hazard_le_one hs1)

def absorption (s : ℝ) : ℝ := 2 * s - s ^ 2

def successor (s : ℝ) : Payoff Player :=
  fun who => if who = owner then absorption s / (1 - absorption s) else 0

@[simp] theorem hazard_owner (s : ℝ) : hazard s owner = 0 := by
  simp [hazard, owner, first, second, Fin.ext_iff]

@[simp] theorem hazard_first (s : ℝ) : hazard s first = s := by
  simp [hazard]

@[simp] theorem hazard_second (s : ℝ) : hazard s second = s := by
  simp [hazard]

@[simp] theorem hazard_dormant (s : ℝ) : hazard s dormant = 0 := by
  simp [hazard, dormant, first, second, Fin.ext_iff]

@[simp] theorem root_owner {s : ℝ} {hs0 : 0 ≤ s} {hs1 : s ≤ 1} :
    root s hs0 hs1 owner = PMF.pure false := by
  unfold root rootOfHazard
  apply quittingHazardCoin_eq_pure_false_of_quitMass_zero
  simp

@[simp] theorem root_quitProbability
    {s : ℝ} {hs0 : 0 ≤ s} {hs1 : s ≤ 1} (who : Player) :
    ((root s hs0 hs1 who) true).toReal = hazard s who := by
  change hazardOfRoot (root s hs0 hs1) who = hazard s who
  exact congrFun (hazardOfRoot_rootOfHazard
    (hazard s) (hazard_nonneg hs0) (hazard_le_one hs1)) who

@[simp] theorem root_continueProbability
    {s : ℝ} {hs0 : 0 ≤ s} {hs1 : s ≤ 1} (who : Player) :
    ((root s hs0 hs1 who) false).toReal = 1 - hazard s who := by
  have hsum := pmf_toReal_sum_one (root s hs0 hs1 who)
  rw [Fintype.sum_bool, root_quitProbability] at hsum
  linarith

private theorem player_univ : (Finset.univ : Finset Player) = {0, 1, 2, 3} := by
  decide

private theorem player_erase_owner :
    (Finset.univ : Finset Player).erase owner = {1, 2, 3} := by
  decide

private theorem player_erase_first :
    (Finset.univ : Finset Player).erase first = {0, 2, 3} := by
  decide

private theorem player_erase_second :
    (Finset.univ : Finset Player).erase second = {0, 1, 3} := by
  decide

private theorem player_erase_dormant :
    (Finset.univ : Finset Player).erase dormant = {0, 1, 2} := by
  decide

/-- The packet's one-stage absorption probability is `2s-s²`. -/
theorem quittingRootAbsorptionMass_root
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    quittingRootAbsorptionMass (root s hs0 hs1) = absorption s := by
  unfold quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, player_univ]
  simp +decide [hazard, absorption, first, second, Finset.prod_insert]
  ring

/-- Deleting the owner leaves both active outsider hazards. -/
theorem quittingRootOpponentAbsorptionMass_owner
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    quittingRootOpponentAbsorptionMass (root s hs0 hs1) owner = absorption s := by
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  rw [player_erase_owner]
  simp +decide [hazard, absorption, first, second, Finset.prod_insert]
  ring

/-- Deleting the first active outsider leaves the second hazard. -/
theorem quittingRootOpponentAbsorptionMass_first
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    quittingRootOpponentAbsorptionMass (root s hs0 hs1) first = s := by
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  rw [player_erase_first]
  simp +decide [hazard, first, second, Finset.prod_insert]

/-- Deleting the second active outsider leaves the first hazard. -/
theorem quittingRootOpponentAbsorptionMass_second
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    quittingRootOpponentAbsorptionMass (root s hs0 hs1) second = s := by
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  rw [player_erase_second]
  simp +decide [hazard, first, second, Finset.prod_insert]

/-- Deleting the dormant player leaves both active hazards. -/
theorem quittingRootOpponentAbsorptionMass_dormant
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    quittingRootOpponentAbsorptionMass (root s hs0 hs1) dormant = absorption s := by
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  rw [player_erase_dormant]
  simp +decide [hazard, absorption, first, second, Finset.prod_insert]
  ring

theorem absorption_lt_one {s : ℝ} (hs1 : s < 1) : absorption s < 1 := by
  have hsquare : 0 < (1 - s) ^ 2 := sq_pos_of_pos (sub_pos.mpr hs1)
  simp only [absorption]
  nlinarith

theorem absorption_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ absorption s := by
  simp only [absorption]
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]

@[simp] theorem successor_owner (s : ℝ) :
    successor s owner = absorption s / (1 - absorption s) := by
  simp [successor]

@[simp] theorem successor_outsider (s : ℝ) {who : Player} (hne : who ≠ owner) :
    successor s who = 0 := by
  simp [successor, hne]

/-- With the displayed successor value, the owner's Continue endpoint is
exactly zero. -/
theorem quittingRootContinuePayoff_owner
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    quittingRootContinuePayoff (oneOwnerHazardObstructionReward owner)
      (successor s) (root s hs0 hs1.le) owner = 0 := by
  rw [quittingRootContinuePayoff_oneOwnerHazardObstruction,
    quittingRootOpponentContinueMass_eq_one_sub_absorptionMass,
    quittingRootOpponentAbsorptionMass_owner, successor_owner]
  have hne : 1 - absorption s ≠ 0 := ne_of_gt (sub_pos.mpr (absorption_lt_one hs1))
  field_simp
  ring

@[simp] theorem quittingRootQuitPayoff_owner
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    quittingRootQuitPayoff (oneOwnerHazardObstructionReward owner)
      (successor s) (root s hs0 hs1.le) owner = 0 := by
  exact quittingRootQuitPayoff_oneOwnerHazardObstruction owner _ _

theorem quittingRootQuitPayoff_outsider
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {who : Player}
    (hne : who ≠ owner) :
    quittingRootQuitPayoff (oneOwnerHazardObstructionReward owner)
      (successor s) (root s hs0 hs1.le) who = 0 := by
  apply quittingRootQuitPayoff_outsider_oneOwnerHazardObstruction_of_owner_sureContinue
    owner who hne (successor s)
  · exact successor_outsider s hne
  · exact root_owner

theorem quittingRootContinuePayoff_outsider
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {who : Player}
    (hne : who ≠ owner) :
    quittingRootContinuePayoff (oneOwnerHazardObstructionReward owner)
      (successor s) (root s hs0 hs1.le) who = 0 := by
  apply quittingRootContinuePayoff_outsider_oneOwnerHazardObstruction_of_owner_sureContinue
    owner who hne (successor s)
  · exact successor_outsider s hne
  · exact root_owner

/-- Every pure endpoint has payoff zero, so the packet root is exact Nash. -/
theorem isZeroQuittingRootNash_root
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    IsεQuittingRootNash (oneOwnerHazardObstructionReward owner)
      (successor s) 0 (root s hs0 hs1.le) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  by_cases hwho : who = owner
  · subst who
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_owner hs0 hs1,
      quittingRootContinuePayoff_owner hs0 hs1]
    simp
  · rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_outsider hs0 hs1 hwho,
      quittingRootContinuePayoff_outsider hs0 hs1 hwho]
    simp

/-- The predecessor generated by the packet root and displayed successor is
the zero payoff vector. -/
theorem quittingRootSuccessorPayoff_root
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    quittingRootSuccessorPayoff (oneOwnerHazardObstructionReward owner)
      (successor s) (root s hs0 hs1.le) = 0 := by
  funext who
  simp only [Pi.zero_apply]
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  by_cases hwho : who = owner
  · subst who
    rw [quittingRootQuitPayoff_owner hs0 hs1,
      quittingRootContinuePayoff_owner hs0 hs1]
    ring
  · rw [quittingRootQuitPayoff_outsider hs0 hs1 hwho,
      quittingRootContinuePayoff_outsider hs0 hs1 hwho]
    ring

/-- The zero predecessor, packet root, and displayed successor form one exact
Nash--Bellman edge. -/
theorem exactNashBellmanEdge
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (0 : Payoff Player) =
        quittingRootSuccessorPayoff (oneOwnerHazardObstructionReward owner)
          (successor s) (root s hs0 hs1.le) ∧
      IsεQuittingRootNash (oneOwnerHazardObstructionReward owner)
        (successor s) 0 (root s hs0 hs1.le) := by
  exact ⟨(quittingRootSuccessorPayoff_root hs0 hs1).symm,
    isZeroQuittingRootNash_root hs0 hs1⟩

/-! ### Rational vanishing packet family -/

/-- The packet scale `1/(n+4)`. -/
def rationalScale (n : ℕ) : ℝ := 1 / (n + 4 : ℕ)

theorem rationalScale_pos (n : ℕ) : 0 < rationalScale n := by
  unfold rationalScale
  apply one_div_pos.mpr
  exact_mod_cast (show 0 < n + 4 by omega)

theorem rationalScale_le_quarter (n : ℕ) : rationalScale n ≤ (1 : ℝ) / 4 := by
  have hn : (0 : ℝ) < (n + 4 : ℕ) := by
    exact_mod_cast (show 0 < n + 4 by omega)
  rw [rationalScale, div_le_div_iff₀ hn (by norm_num)]
  norm_num

theorem rationalScale_lt_one (n : ℕ) : rationalScale n < 1 := by
  exact lt_of_le_of_lt (rationalScale_le_quarter n) (by norm_num)

theorem rationalScale_tendsto_zero :
    Tendsto rationalScale atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat 3).2
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun n : ℕ => 1 / (((n + 4 : ℕ) : ℝ))) atTop (𝓝 0)
  convert h using 1
  funext n
  congr 1
  push_cast
  ring

theorem not_summable_rationalScale : ¬Summable rationalScale := by
  have h := mt (_root_.summable_nat_add_iff 4).1
    Real.not_summable_one_div_natCast
  change ¬Summable (fun n : ℕ => 1 / ((n + 4 : ℕ) : ℝ))
  simpa only [Nat.cast_add, Nat.cast_ofNat, one_div] using h

def rationalRoot (n : ℕ) : Player → PMF Bool :=
  root (rationalScale n) (rationalScale_pos n).le (rationalScale_lt_one n).le

def rationalSuccessor (n : ℕ) : Payoff Player := successor (rationalScale n)

@[simp] theorem rationalRoot_marginalQuitHazard (n : ℕ) (who : Player) :
    quittingMarginalQuitHazard rationalRoot who n = hazard (rationalScale n) who := by
  change ((rationalRoot n who) true).toReal = _
  exact root_quitProbability who

@[simp] theorem rationalRoot_first_hazard (n : ℕ) :
    quittingMarginalQuitHazard rationalRoot first n = rationalScale n := by
  rw [rationalRoot_marginalQuitHazard, hazard_first]

@[simp] theorem rationalRoot_second_hazard (n : ℕ) :
    quittingMarginalQuitHazard rationalRoot second n = rationalScale n := by
  rw [rationalRoot_marginalQuitHazard, hazard_second]

/-- Both fixed active labels have divergent total marginal hazard. -/
theorem not_summable_rationalRoot_first :
    ¬Summable (quittingMarginalQuitHazard rationalRoot first) := by
  rw [show quittingMarginalQuitHazard rationalRoot first = rationalScale by
    funext n
    exact rationalRoot_first_hazard n]
  exact not_summable_rationalScale

theorem not_summable_rationalRoot_second :
    ¬Summable (quittingMarginalQuitHazard rationalRoot second) := by
  rw [show quittingMarginalQuitHazard rationalRoot second = rationalScale by
    funext n
    exact rationalRoot_second_hazard n]
  exact not_summable_rationalScale

/-- Every player's marginal hazard is bounded by the common scale, and hence
all packet hazards vanish. -/
theorem rationalRoot_hazard_le_scale (n : ℕ) (who : Player) :
    quittingMarginalQuitHazard rationalRoot who n ≤ rationalScale n := by
  rw [rationalRoot_marginalQuitHazard]
  simp only [hazard]
  split <;> linarith [rationalScale_pos n]

theorem rationalRoot_hazard_tendsto_zero (who : Player) :
    Tendsto (quittingMarginalQuitHazard rationalRoot who) atTop (𝓝 0) := by
  rw [show quittingMarginalQuitHazard rationalRoot who =
      fun n => hazard (rationalScale n) who by
    funext n
    exact rationalRoot_marginalQuitHazard n who]
  simp only [hazard]
  split
  · exact rationalScale_tendsto_zero
  · exact tendsto_const_nhds

theorem absorption_pos_of_pos_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    0 < absorption s := by
  have hfactor : 0 < 2 - s := lt_of_lt_of_le (by norm_num) (sub_le_sub_left hs1 2)
  rw [absorption]
  nlinarith [mul_pos hs0 hfactor]

theorem scale_le_absorption {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ≤ absorption s := by
  rw [absorption]
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]

theorem rationalRoot_absorption_pos (n : ℕ) :
    0 < quittingRootAbsorptionMass (rationalRoot n) := by
  simpa only [rationalRoot] using
    (show 0 < quittingRootAbsorptionMass
        (root (rationalScale n) (rationalScale_pos n).le
          (rationalScale_lt_one n).le) by
      rw [quittingRootAbsorptionMass_root]
      exact absorption_pos_of_pos_le_one
        (rationalScale_pos n) (rationalScale_lt_one n).le)

private theorem player_cases (who : Player) :
    who = owner ∨ who = first ∨ who = second ∨ who = dormant := by
  fin_cases who <;> simp [owner, first, second, dormant, Fin.ext_iff]

/-- Every one-player-deleted clock retains at least the scale and is
therefore positive at every packet. -/
theorem rationalScale_le_deletedCharge (n : ℕ) (who : Player) :
    rationalScale n ≤ quittingRootOpponentAbsorptionMass (rationalRoot n) who := by
  rcases player_cases who with howner | hfirst | hsecond | hdormant
  · subst who
    rw [rationalRoot, quittingRootOpponentAbsorptionMass_owner]
    exact scale_le_absorption (rationalScale_pos n).le (rationalScale_lt_one n).le
  · subst who
    rw [rationalRoot, quittingRootOpponentAbsorptionMass_first]
  · subst who
    rw [rationalRoot, quittingRootOpponentAbsorptionMass_second]
  · subst who
    rw [rationalRoot, quittingRootOpponentAbsorptionMass_dormant]
    exact scale_le_absorption (rationalScale_pos n).le (rationalScale_lt_one n).le

theorem rationalRoot_deletedCharge_pos (n : ℕ) (who : Player) :
    0 < quittingRootOpponentAbsorptionMass (rationalRoot n) who :=
  lt_of_lt_of_le (rationalScale_pos n) (rationalScale_le_deletedCharge n who)

/-- Every member of the rational family is an exact zero-predecessor
Nash--Bellman edge. -/
theorem rationalExactNashBellmanEdge (n : ℕ) :
    (0 : Payoff Player) =
        quittingRootSuccessorPayoff (oneOwnerHazardObstructionReward owner)
          (rationalSuccessor n) (rationalRoot n) ∧
      IsεQuittingRootNash (oneOwnerHazardObstructionReward owner)
        (rationalSuccessor n) 0 (rationalRoot n) := by
  exact exactNashBellmanEdge (rationalScale_pos n).le (rationalScale_lt_one n)

theorem absorption_rationalScale_le_seven_sixteenths (n : ℕ) :
    absorption (rationalScale n) ≤ (7 : ℝ) / 16 := by
  have hs0 := (rationalScale_pos n).le
  have hs4 := rationalScale_le_quarter n
  have hleft : 0 ≤ (1 : ℝ) / 4 - rationalScale n := sub_nonneg.mpr hs4
  have hright : 0 ≤ (7 : ℝ) / 4 - rationalScale n := by linarith
  have hproduct : 0 ≤ ((1 : ℝ) / 4 - rationalScale n) *
      ((7 : ℝ) / 4 - rationalScale n) := mul_nonneg hleft hright
  rw [absorption]
  nlinarith

theorem rationalSuccessor_owner_nonneg (n : ℕ) :
    0 ≤ rationalSuccessor n owner := by
  rw [rationalSuccessor, successor_owner]
  exact div_nonneg
    (absorption_nonneg (rationalScale_pos n).le (rationalScale_lt_one n).le)
    (sub_nonneg.mpr (absorption_lt_one (rationalScale_lt_one n)).le)

theorem rationalSuccessor_owner_le_seven_ninths (n : ℕ) :
    rationalSuccessor n owner ≤ (7 : ℝ) / 9 := by
  rw [rationalSuccessor, successor_owner]
  rw [div_le_iff₀ (sub_pos.mpr (absorption_lt_one (rationalScale_lt_one n)))]
  have hbound := absorption_rationalScale_le_seven_sixteenths n
  nlinarith

/-- The local successors stay strictly inside the unit payoff box. -/
theorem abs_rationalSuccessor_lt_one (n : ℕ) (who : Player) :
    |rationalSuccessor n who| < 1 := by
  by_cases hwho : who = owner
  · subst who
    rw [abs_of_nonneg (rationalSuccessor_owner_nonneg n)]
    exact lt_of_le_of_lt (rationalSuccessor_owner_le_seven_ninths n) (by norm_num)
  · rw [rationalSuccessor, successor_outsider _ hwho, abs_zero]
    norm_num

theorem absorption_rationalScale_tendsto_zero :
    Tendsto (fun n => absorption (rationalScale n)) atTop (𝓝 0) := by
  simpa [absorption] using
    (rationalScale_tendsto_zero.const_mul 2).sub (rationalScale_tendsto_zero.pow 2)

/-- The displayed successor vectors converge pointwise to zero. -/
theorem rationalSuccessor_tendsto_zero (who : Player) :
    Tendsto (fun n => rationalSuccessor n who) atTop (𝓝 0) := by
  by_cases hwho : who = owner
  · subst who
    simp only [rationalSuccessor, successor_owner]
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hdenominator :
        Tendsto (fun n => 1 - absorption (rationalScale n)) atTop (𝓝 (1 : ℝ)) :=
      by simpa using hone.sub absorption_rationalScale_tendsto_zero
    have hdiv := absorption_rationalScale_tendsto_zero.div
      hdenominator (by norm_num : (1 : ℝ) ≠ 0)
    convert hdiv using 1
    · funext n
      rfl
    · norm_num
  · have heq : (fun n => rationalSuccessor n who) = fun _ => (0 : ℝ) := by
      funext n
      exact successor_outsider (rationalScale n) hwho
    rw [heq]
    exact tendsto_const_nhds

end OneOwnerFourPlayerPacket

end GameTheory
