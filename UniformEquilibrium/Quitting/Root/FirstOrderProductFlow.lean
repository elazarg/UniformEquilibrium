/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.SmallHazardExpectation
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockTangentObstruction

/-!
# First-order product flow at a quitting root

This file gives the literal first-order singleton and collision matrices of a
finite product quitting root.  The exact product formulas differ from their
linearizations by a uniform quadratic remainder.  The statements concern one
supplied root and tail only; they make no Nash, cap, or convergence claim.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The terminal coalition in which the displayed pair quits. -/
def quittingPairTerminal (who owner : ι) :
    {S : Finset ι // S.Nonempty} :=
  ⟨{who, owner}, by simp⟩

/-- The first-order change in player `who`'s terminal payoff when `who` is
added to `owner`'s singleton exit.  The diagonal entry is definitionally
zero. -/
def quittingCollisionMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  if _ : who = owner then 0 else
    reward (quittingPairTerminal who owner) who -
      reward (quittingSingletonTerminal owner) who

/-- The first-order pure-Quit row: adding `owner` to `who`'s own singleton
exit. -/
def quittingPairJoinMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  reward (quittingPairTerminal who owner) who -
    reward (quittingSingletonTerminal who) who

omit [Fintype ι] in
@[simp]
theorem quittingCollisionMatrix_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingCollisionMatrix reward who who = 0 := by
  simp [quittingCollisionMatrix]

omit [Fintype ι] in
@[simp]
theorem quittingPairJoinMatrix_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPairJoinMatrix reward who who = 0 := by
  have hterminal :
      quittingPairTerminal who who = quittingSingletonTerminal who := by
    apply Subtype.ext
    simp [quittingPairTerminal, quittingSingletonTerminal]
  rw [quittingPairJoinMatrix, hterminal]
  ring

/-- Reward table seen after `who` has already committed to Quit: every
subsequent quitter coalition is enlarged by `who`. -/
def quittingPureQuitLiftReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (terminal : {S : Finset ι // S.Nonempty}) : Payoff ι :=
  reward ⟨insert who terminal.val, Finset.insert_nonempty who _⟩

omit [Fintype ι] in
@[simp]
theorem quittingPureQuitLiftReward_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) :
    quittingPureQuitLiftReward reward who (quittingSingletonTerminal owner) =
      reward (quittingPairTerminal who owner) := by
  unfold quittingPureQuitLiftReward quittingSingletonTerminal
    quittingPairTerminal
  apply congrArg reward
  apply Subtype.ext
  simp [Finset.pair_comm]

omit [Fintype ι] [DecidableEq ι] in
private theorem quittingSoloReward_eq_singletonTerminal'
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) :
    quittingSoloReward reward owner who =
      reward (quittingSingletonTerminal owner) who := by
  unfold quittingSoloReward quittingSingletonTerminal
  apply congrArg (fun terminal ↦ reward terminal who)
  apply Subtype.ext
  rfl

private theorem quittingRootQuitPayoff_eq_liftedSuccessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward tail root who =
      quittingRootSuccessorPayoff (quittingPureQuitLiftReward reward who)
        (quittingSoloReward reward who)
        (Function.update root who (PMF.pure false)) who := by
  unfold quittingRootQuitPayoff quittingRootSuccessorPayoff
    quittingRootExpectedPayoff
  rw [KernelGame.expect_pmfPi_update_pure,
    KernelGame.expect_pmfPi_update_pure]
  apply congrArg (expect (pmfPi root))
  funext action
  unfold quittingRootPayoff
  have hquitters :
      quittingQuitters (Function.update action who true) =
        insert who (quittingQuitters (Function.update action who false)) := by
    ext owner
    by_cases howner : owner = who
    · subst owner
      simp [quittingQuitters]
    · simp [quittingQuitters, Function.update, howner]
  have hleft :
      (quittingQuitters (Function.update action who true)).Nonempty := by
    rw [hquitters]
    exact Finset.insert_nonempty _ _
  rw [dif_pos hleft]
  by_cases hright :
      (quittingQuitters (Function.update action who false)).Nonempty
  · rw [dif_pos hright]
    change reward _ who = reward _ who
    apply congrArg (fun terminal ↦ reward terminal who)
    apply Subtype.ext
    exact hquitters
  · rw [dif_neg hright]
    change reward _ who = quittingSoloReward reward who who
    unfold quittingSoloReward
    apply congrArg (fun terminal ↦ reward terminal who)
    apply Subtype.ext
    exact hquitters.trans (by
      rw [Finset.not_nonempty_iff_eq_empty.mp hright]
      simp)

/-- The successor update has normalized-singleton first-order flow plus the
moving-tail baseline, with a uniform quadratic product remainder. -/
theorem
    abs_quittingRootSuccessorPayoff_sub_tail_sub_normalizedSoloFlow_sub_baseline_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : |tail who| ≤ M) :
    |quittingRootSuccessorPayoff reward tail root who - tail who -
        ∑ owner, quittingRootQuitRates root owner *
          normalizedSoloMatrix reward who owner -
        (∑ owner, quittingRootQuitRates root owner) *
          (quittingSoloReward reward who who - tail who)| ≤
      2 * M * (∑ owner, quittingRootQuitRates root owner) ^ 2 := by
  have hlinear :
      (∑ owner, quittingRootQuitRates root owner *
          (reward (quittingSingletonTerminal owner) who - tail who)) =
        (∑ owner, quittingRootQuitRates root owner *
          normalizedSoloMatrix reward who owner) +
        (∑ owner, quittingRootQuitRates root owner) *
          (quittingSoloReward reward who who - tail who) := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro owner _
    rw [normalizedSoloMatrix_eq_soloReward_sub,
      quittingSoloReward_eq_singletonTerminal']
    ring
  rw [show
      quittingRootSuccessorPayoff reward tail root who - tail who -
            ∑ owner, quittingRootQuitRates root owner *
              normalizedSoloMatrix reward who owner -
          (∑ owner, quittingRootQuitRates root owner) *
            (quittingSoloReward reward who who - tail who) =
        quittingRootSuccessorPayoff reward tail root who - tail who -
          ((∑ owner, quittingRootQuitRates root owner *
            normalizedSoloMatrix reward who owner) +
          (∑ owner, quittingRootQuitRates root owner) *
            (quittingSoloReward reward who who - tail who)) by ring,
    ← hlinear]
  exact
    abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le
      reward tail root who hreward htail

/-- After omitting the moving-tail baseline, the normalized-singleton flow
has only a linear tail mismatch and the quadratic product remainder. -/
theorem abs_quittingRootSuccessorPayoff_sub_tail_sub_normalizedSoloFlow_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : |tail who| ≤ M) :
    |quittingRootSuccessorPayoff reward tail root who - tail who -
        ∑ owner, quittingRootQuitRates root owner *
          normalizedSoloMatrix reward who owner| ≤
      (∑ owner, quittingRootQuitRates root owner) *
          |tail who - quittingSoloReward reward who who| +
        2 * M * (∑ owner, quittingRootQuitRates root owner) ^ 2 := by
  let total := ∑ owner, quittingRootQuitRates root owner
  let baseline := quittingSoloReward reward who who - tail who
  let residual := quittingRootSuccessorPayoff reward tail root who - tail who -
    ∑ owner, quittingRootQuitRates root owner *
      normalizedSoloMatrix reward who owner
  have htotal : 0 ≤ total :=
    Finset.sum_nonneg fun owner _ ↦ ENNReal.toReal_nonneg
  have hbound :=
    abs_quittingRootSuccessorPayoff_sub_tail_sub_normalizedSoloFlow_sub_baseline_le
      reward tail root who hreward htail
  change |residual| ≤ total * |tail who - quittingSoloReward reward who who| + _
  change |residual - total * baseline| ≤ _ at hbound
  calc
    |residual| = |(residual - total * baseline) + total * baseline| := by ring_nf
    _ ≤ |residual - total * baseline| + |total * baseline| := abs_add_le _ _
    _ ≤ 2 * M * total ^ 2 + total * |baseline| := by
      exact add_le_add hbound (by rw [abs_mul, abs_of_nonneg htotal])
    _ = total * |tail who - quittingSoloReward reward who who| +
        2 * M * total ^ 2 := by
      rw [show |baseline| =
          |tail who - quittingSoloReward reward who who| by
        dsimp only [baseline]
        rw [abs_sub_comm]]
      ring

/-- The pure-Quit endpoint has the pair-join first-order flow, with a
quadratic remainder in the original root's total Quit hazard. -/
theorem abs_quittingRootQuitPayoff_sub_solo_sub_pairJoinFlow_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootQuitPayoff reward tail root who -
        quittingSoloReward reward who who -
        ∑ owner, quittingRootQuitRates root owner *
          quittingPairJoinMatrix reward who owner| ≤
      2 * M * (∑ owner, quittingRootQuitRates root owner) ^ 2 := by
  let forced := Function.update root who (PMF.pure false)
  have hbound :=
    abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le
      (quittingPureQuitLiftReward reward who)
      (quittingSoloReward reward who) forced who
      (fun terminal player ↦ hreward
        ⟨insert who terminal.val, Finset.insert_nonempty who _⟩ player)
      (by
        rw [quittingSoloReward_eq_singletonTerminal']
        exact hreward (quittingSingletonTerminal who) who)
  have hflow :
      (∑ owner, quittingRootQuitRates forced owner *
        (quittingPureQuitLiftReward reward who
            (quittingSingletonTerminal owner) who -
          quittingSoloReward reward who who)) =
        ∑ owner, quittingRootQuitRates root owner *
          quittingPairJoinMatrix reward who owner := by
    apply Finset.sum_congr rfl
    intro owner _
    by_cases howner : owner = who
    · subst owner
      simp [forced, quittingRootQuitRates]
    · simp [forced, quittingRootQuitRates, howner,
        quittingPairJoinMatrix, quittingPureQuitLiftReward_singleton,
        quittingSoloReward_eq_singletonTerminal']
  have hforcedTotal :
      (∑ owner, quittingRootQuitRates forced owner) ≤
        ∑ owner, quittingRootQuitRates root owner := by
    apply Finset.sum_le_sum
    intro owner _
    by_cases howner : owner = who
    · subst owner
      simp [forced, quittingRootQuitRates, ENNReal.toReal_nonneg]
    · simp [forced, quittingRootQuitRates, howner]
  have hforcedNonneg : 0 ≤ ∑ owner, quittingRootQuitRates forced owner :=
    Finset.sum_nonneg fun owner _ ↦ ENNReal.toReal_nonneg
  have htotalNonneg : 0 ≤ ∑ owner, quittingRootQuitRates root owner :=
    Finset.sum_nonneg fun owner _ ↦ ENNReal.toReal_nonneg
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  rw [← quittingRootQuitPayoff_eq_liftedSuccessor reward tail root who,
    hflow] at hbound
  have hsquare :
      (∑ owner, quittingRootQuitRates forced owner) ^ 2 ≤
        (∑ owner, quittingRootQuitRates root owner) ^ 2 := by
    nlinarith
  exact hbound.trans
    (mul_le_mul_of_nonneg_left hsquare (mul_nonneg (by norm_num) hM))

/-- The pure-action endpoint difference has collision-matrix first-order
flow.  Omitting the small damping of the singleton-versus-tail baseline costs
one linear tail-mismatch term; all remaining product error is quadratic. -/
theorem abs_quittingRootEndpointDifference_sub_solo_sub_tail_sub_collisionFlow_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : |tail who| ≤ M) :
    |quittingRootEndpointDifference reward tail root who -
        (quittingSoloReward reward who who - tail who) -
        ∑ owner, quittingRootQuitRates root owner *
          quittingCollisionMatrix reward who owner| ≤
      (∑ owner, quittingRootQuitRates root owner) *
          |tail who - quittingSoloReward reward who who| +
        4 * M * (∑ owner, quittingRootQuitRates root owner) ^ 2 := by
  let forced := Function.update root who (PMF.pure false)
  let total := ∑ owner, quittingRootQuitRates root owner
  let opponentTotal := ∑ owner, quittingRootQuitRates forced owner
  let baseline := quittingSoloReward reward who who - tail who
  let pairFlow := ∑ owner, quittingRootQuitRates root owner *
    quittingPairJoinMatrix reward who owner
  let continueFlow := ∑ owner, quittingRootQuitRates forced owner *
    (reward (quittingSingletonTerminal owner) who - tail who)
  let collisionFlow := ∑ owner, quittingRootQuitRates root owner *
    quittingCollisionMatrix reward who owner
  have htotalNonneg : 0 ≤ total :=
    Finset.sum_nonneg fun owner _ ↦ ENNReal.toReal_nonneg
  have hopponentNonneg : 0 ≤ opponentTotal :=
    Finset.sum_nonneg fun owner _ ↦ ENNReal.toReal_nonneg
  have hopponent_le : opponentTotal ≤ total := by
    apply Finset.sum_le_sum
    intro owner _
    by_cases howner : owner = who
    · subst owner
      simp [forced, quittingRootQuitRates, ENNReal.toReal_nonneg]
    · simp [forced, quittingRootQuitRates, howner]
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hQ :
      |quittingRootQuitPayoff reward tail root who -
          quittingSoloReward reward who who - pairFlow| ≤
        2 * M * total ^ 2 := by
    exact abs_quittingRootQuitPayoff_sub_solo_sub_pairJoinFlow_le
      reward tail root who hreward
  have hCraw :=
    abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le
      reward tail forced who hreward htail
  have hC :
      |quittingRootContinuePayoff reward tail root who - tail who -
          continueFlow| ≤
        2 * M * total ^ 2 := by
    have hsquare : opponentTotal ^ 2 ≤ total ^ 2 := by
      nlinarith
    have hscale : 2 * M * opponentTotal ^ 2 ≤ 2 * M * total ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (mul_nonneg (by norm_num) hM)
    change
      |quittingRootSuccessorPayoff reward tail forced who - tail who -
          continueFlow| ≤ 2 * M * opponentTotal ^ 2 at hCraw
    have hcontinueDef : quittingRootContinuePayoff reward tail root who =
        quittingRootSuccessorPayoff reward tail forced who := rfl
    rw [hcontinueDef]
    exact hCraw.trans hscale
  have hpairFlow : pairFlow =
      ∑ owner, quittingRootQuitRates forced owner *
        quittingPairJoinMatrix reward who owner := by
    apply Finset.sum_congr rfl
    intro owner _
    by_cases howner : owner = who
    · subst owner
      simp [forced, quittingRootQuitRates]
    · simp [forced, quittingRootQuitRates, howner]
  have hcollisionFlow : collisionFlow =
      ∑ owner, quittingRootQuitRates forced owner *
        quittingCollisionMatrix reward who owner := by
    apply Finset.sum_congr rfl
    intro owner _
    by_cases howner : owner = who
    · subst owner
      simp [forced, quittingRootQuitRates]
    · simp [forced, quittingRootQuitRates, howner]
  have hrow (owner : ι) :
      quittingPairJoinMatrix reward who owner -
          (reward (quittingSingletonTerminal owner) who - tail who) =
        quittingCollisionMatrix reward who owner - baseline := by
    by_cases howner : who = owner
    · subst owner
      simp [baseline, quittingSoloReward_eq_singletonTerminal']
    · simp [quittingPairJoinMatrix, quittingCollisionMatrix, howner,
        baseline, quittingSoloReward_eq_singletonTerminal']
      ring
  have hflow : pairFlow - continueFlow =
      collisionFlow - opponentTotal * baseline := by
    rw [hpairFlow, hcollisionFlow]
    change
      (∑ owner, quittingRootQuitRates forced owner *
          quittingPairJoinMatrix reward who owner) -
          (∑ owner, quittingRootQuitRates forced owner *
            (reward (quittingSingletonTerminal owner) who - tail who)) =
        (∑ owner, quittingRootQuitRates forced owner *
          quittingCollisionMatrix reward who owner) -
          opponentTotal * baseline
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro owner _
    linear_combination quittingRootQuitRates forced owner * hrow owner
  let endpointCore :=
    quittingRootEndpointDifference reward tail root who - baseline -
      collisionFlow + opponentTotal * baseline
  have hcoreEq : endpointCore =
      (quittingRootQuitPayoff reward tail root who -
          quittingSoloReward reward who who - pairFlow) -
        (quittingRootContinuePayoff reward tail root who - tail who -
          continueFlow) := by
    unfold endpointCore quittingRootEndpointDifference
    linear_combination hflow
  have hcore : |endpointCore| ≤ 4 * M * total ^ 2 := by
    rw [hcoreEq]
    calc
      |_ - _| ≤
          |quittingRootQuitPayoff reward tail root who -
            quittingSoloReward reward who who - pairFlow| +
          |quittingRootContinuePayoff reward tail root who - tail who -
            continueFlow| := abs_sub _ _
      _ ≤ 2 * M * total ^ 2 + 2 * M * total ^ 2 := add_le_add hQ hC
      _ = 4 * M * total ^ 2 := by ring
  change
    |quittingRootEndpointDifference reward tail root who - baseline -
        collisionFlow| ≤
      total * |tail who - quittingSoloReward reward who who| +
        4 * M * total ^ 2
  calc
    |quittingRootEndpointDifference reward tail root who - baseline -
        collisionFlow| = |endpointCore - opponentTotal * baseline| := by
      unfold endpointCore
      ring_nf
    _ ≤ |endpointCore| + |opponentTotal * baseline| := abs_sub _ _
    _ ≤ 4 * M * total ^ 2 + total * |baseline| := by
      apply add_le_add hcore
      rw [abs_mul, abs_of_nonneg hopponentNonneg]
      exact mul_le_mul_of_nonneg_right hopponent_le (abs_nonneg baseline)
    _ = total * |tail who - quittingSoloReward reward who who| +
        4 * M * total ^ 2 := by
      rw [show |baseline| =
          |tail who - quittingSoloReward reward who who| by
        dsimp only [baseline]
        rw [abs_sub_comm]]
      ring

end GameTheory
