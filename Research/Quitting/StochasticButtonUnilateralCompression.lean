/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.StochasticButtonCompression
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Paths.OpponentClockDichotomy

/-!
# Player-deleted stochastic-button compression

The joint absorption clock used by `QuittingStochasticButtonCompression` is
changed by a unilateral deviation.  For a fixed player `who`, the correct
deviation-invariant clock deletes that player's button and records only the
probability that at least one opponent quits.

This file proves the missing uniform estimate.  On rows where the opponent
charge is at most `threshold`, an arbitrary time-varying hazard chosen by
`who` can overlap opponent absorption with total probability at most
`threshold`.  The proof uses the deviator's own first-quit mass as a
subprobability measure; it does not count the number of diffuse rows.

Together with the earlier diffuse-collision theorem applied to the deleted
roots, this gives a finite atom/diffuse/tail certificate that is uniform over
the deviator:

* only finitely many large opponent packets are retained;
* collisions among opponents on all diffuse rows cost `O(threshold)`;
* overlap of any deviation with diffuse opponent absorption costs at most
  `threshold`; and
* the remaining opponent-survival tail is exponentially small.

This is still a probability-law compression theorem, not an equivalence
theorem for quitting games.  In particular, no continuation payoff or
punishment-floor transport is asserted here.
-/

noncomputable section

namespace Research.QuittingStochasticButtonUnilateralCompression

open GameTheory Filter Math.Probability
open scoped BigOperators

open Research.QuittingStochasticButtonCompression

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Delete `who` from every row.  This is the root sequence of the fixed
opponents when the distinguished player always continues. -/
def playerDeletedRoots
    (roots : ℕ → ι → PMF Bool) (who : ι) : ℕ → ι → PMF Bool :=
  quittingRootSequenceUpdate roots who (fun _ => PMF.pure false)

/-- Cumulative effectiveness of the player-deleted (opponent-only) clock. -/
def cumulativeOpponentEffectiveness
    (roots : ℕ → ι → PMF Bool) (who : ι) (horizon : ℕ) : ℝ :=
  cumulativeEffectiveness (playerDeletedRoots roots who) horizon

/-- Large packets for the player-deleted clock. -/
def atomicOpponentButtonTimes
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (horizon : ℕ) (threshold : ℝ) : Finset ℕ :=
  atomicButtonTimes (playerDeletedRoots roots who) horizon threshold

/-- Collision mass internal to the opponents, weighted by opponent-only
survival and restricted to diffuse opponent rows. -/
def diffuseInternalOpponentCollisionMass
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (horizon : ℕ) (threshold : ℝ) : ℝ :=
  diffuseCollisionMass
    (playerDeletedRoots roots who) horizon threshold

/-- Survival-weighted mass with which the distinguished player's supplied
hazard quits.  This is a subprobability mass even when the hazard varies
arbitrarily with time. -/
def weightedOwnQuitMass
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    quittingSurvivalPrefix
        (quittingRootSequenceUpdate roots who hazard) time *
      (hazard time true).toReal

/-- Probability ledger for simultaneous quitting by `who` and at least one
opponent on rows diffuse for the fixed opponent clock.  Conditional on
reaching a row, independence makes the overlap factor exactly
`ownQuitProbability * opponentAbsorptionProbability`. -/
def unilateralDiffuseOverlapMass
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) (threshold : ℝ) : ℝ :=
  ∑ time ∈ (Finset.range horizon).filter
      (fun time =>
        quittingOpponentClockCharge roots who time ≤ threshold),
    quittingSurvivalPrefix
        (quittingRootSequenceUpdate roots who hazard) time *
      (hazard time true).toReal *
      quittingOpponentClockCharge roots who time

@[simp] theorem buttonEffectiveness_playerDeletedRoots
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    buttonEffectiveness (playerDeletedRoots roots who) time =
      quittingOpponentClockCharge roots who time := by
  rfl

/-- Updating `who` does not change the player-deleted clock. -/
theorem opponentClockCharge_rootSequenceUpdate
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    quittingOpponentClockCharge
        (quittingRootSequenceUpdate roots who hazard) who time =
      quittingOpponentClockCharge roots who time := by
  classical
  unfold quittingOpponentClockCharge quittingRootOpponentAbsorptionMass
    quittingRootSequenceUpdate
  rw [Function.update_idem]

/-- Exact one-row collision split after changing one player's button.  A
collision either already occurs among the opponents while `who` continues,
or `who` quits together with at least one opponent. -/
theorem quittingRootCollisionMass_update_decomposition
    (root : ι → PMF Bool) (who : ι) (own : PMF Bool) :
    quittingRootCollisionMass (Function.update root who own) =
      (own false).toReal *
          quittingRootCollisionMass
            (Function.update root who (PMF.pure false)) +
        (own true).toReal *
          quittingRootOpponentAbsorptionMass root who := by
  classical
  let x : ι → ℝ :=
    quittingRootQuitRates (Function.update root who own)
  let opponents : Finset ι := Finset.univ.erase who
  have hwho : who ∉ opponents := by simp [opponents]
  have huniv : insert who opponents = (Finset.univ : Finset ι) := by
    exact Finset.insert_erase (Finset.mem_univ who)
  have hfull :
      quittingRootCollisionMass (Function.update root who own) =
        Math.PMFProduct.collisionMassFormulaOn x Finset.univ := by
    unfold quittingRootCollisionMass
    rw [Math.PMFProduct.collisionMass_eq_one_sub_continueMass_sub_singletonMass]
    rfl
  have hdeleted :
      quittingRootCollisionMass
          (Function.update root who (PMF.pure false)) =
        Math.PMFProduct.collisionMassFormulaOn x opponents := by
    unfold quittingRootCollisionMass
    rw [Math.PMFProduct.collisionMass_eq_one_sub_continueMass_sub_singletonMass]
    change Math.PMFProduct.collisionMassFormulaOn
        (quittingRootQuitRates
          (Function.update root who (PMF.pure false))) Finset.univ =
      Math.PMFProduct.collisionMassFormulaOn x opponents
    rw [← huniv,
      Math.PMFProduct.collisionMassFormulaOn_insert _ hwho]
    simp only [quittingRootQuitRates, Function.update_self, PMF.pure_apply,
      Bool.true_eq_false, ↓reduceIte, ENNReal.toReal_zero, sub_zero, one_mul,
      zero_mul, add_zero]
    let y : ι → ℝ :=
      quittingRootQuitRates
        (Function.update root who (PMF.pure false))
    have hxy : ∀ player ∈ opponents, y player = x player := by
      intro player hplayer
      have hne : player ≠ who := Finset.ne_of_mem_erase hplayer
      simp [x, y, quittingRootQuitRates, Function.update_of_ne hne]
    have hprod :
        (∏ player ∈ opponents, (1 - y player)) =
          ∏ player ∈ opponents, (1 - x player) := by
      apply Finset.prod_congr rfl
      intro player hplayer
      rw [hxy player hplayer]
    have hsingle :
        (∑ player ∈ opponents,
            y player * ∏ other ∈ opponents.erase player, (1 - y other)) =
          ∑ player ∈ opponents,
            x player * ∏ other ∈ opponents.erase player, (1 - x other) := by
      apply Finset.sum_congr rfl
      intro player hplayer
      rw [hxy player hplayer]
      congr 1
      apply Finset.prod_congr rfl
      intro other hother
      rw [hxy other (Finset.mem_of_mem_erase hother)]
    change Math.PMFProduct.collisionMassFormulaOn y opponents =
      Math.PMFProduct.collisionMassFormulaOn x opponents
    unfold Math.PMFProduct.collisionMassFormulaOn
    rw [hprod, hsingle]
  have hopponent :
      1 - ∏ player ∈ opponents, (1 - x player) =
        quittingRootOpponentAbsorptionMass root who := by
    have hprod :
        (∏ player ∈ opponents, (1 - x player)) =
          Math.PMFProduct.continueMass
            (quittingRootQuitRates
              (Function.update root who (PMF.pure false))) := by
      unfold Math.PMFProduct.continueMass
      rw [← huniv, Finset.prod_insert hwho]
      have hzero : quittingRootQuitRates
          (Function.update root who (PMF.pure false)) who = 0 := by
        simp [quittingRootQuitRates]
      rw [hzero, sub_zero, one_mul]
      apply Finset.prod_congr rfl
      intro player hplayer
      have hne : player ≠ who := Finset.ne_of_mem_erase hplayer
      simp [x, quittingRootQuitRates, Function.update_of_ne hne]
    rw [hprod, continueMass_quittingRootQuitRates]
    rfl
  rw [hfull, ← huniv,
    Math.PMFProduct.collisionMassFormulaOn_insert _ hwho,
    ← hdeleted, hopponent]
  dsimp [x]
  simp only [quittingRootQuitRates, Function.update_self]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (Function.update root who own) who
  simp only [Function.update_self] at hsum
  change (1 - (own true).toReal) *
      quittingRootCollisionMass
        (Function.update root who (PMF.pure false)) +
      (own true).toReal * quittingRootOpponentAbsorptionMass root who = _
  rw [show 1 - (own true).toReal = (own false).toReal by linarith]

/-- The distinguished player's marginal quit probability is bounded by the
updated row's total absorption probability. -/
theorem ownHazard_le_updatedEffectiveness
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    (hazard time true).toReal ≤
      buttonEffectiveness
        (quittingRootSequenceUpdate roots who hazard) time := by
  classical
  simpa [buttonEffectiveness, quittingRootSequenceUpdate] using
    (quittingRoot_quitProbability_le_absorptionMass
      ((quittingRootSequenceUpdate roots who hazard) time) who)

/-- At every time, survival under an arbitrary update is dominated by
survival after deleting the updated player. -/
theorem survivalPrefix_rootSequenceUpdate_le_playerDeleted
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) :
    quittingSurvivalPrefix
        (quittingRootSequenceUpdate roots who hazard) horizon ≤
      quittingSurvivalPrefix (playerDeletedRoots roots who) horizon := by
  unfold quittingSurvivalPrefix
  apply Finset.prod_le_prod
  · intro time _
    exact quittingStationaryContinueMass_nonneg
      ((quittingRootSequenceUpdate roots who hazard) time)
  · intro time _
    have hdom := quittingStationaryContinueMass_le_update_pure_false
      ((quittingRootSequenceUpdate roots who hazard) time) who
    simpa [playerDeletedRoots, quittingRootSequenceUpdate,
      Function.update_idem] using hdom

/-- A player's survival-weighted first-quit ledger is a subledger of total
absorption and hence has mass at most the absorbed mass of the window. -/
theorem weightedOwnQuitMass_le_absorbedMass
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) :
    weightedOwnQuitMass roots who hazard horizon ≤
      1 - quittingSurvivalPrefix
        (quittingRootSequenceUpdate roots who hazard) horizon := by
  calc
    weightedOwnQuitMass roots who hazard horizon ≤
        weightedEffectiveness
          (quittingRootSequenceUpdate roots who hazard) horizon := by
      unfold weightedOwnQuitMass weightedEffectiveness
      apply Finset.sum_le_sum
      intro time _
      exact mul_le_mul_of_nonneg_left
        (ownHazard_le_updatedEffectiveness roots who hazard time)
        (quittingSurvivalPrefix_nonneg
          (quittingRootSequenceUpdate roots who hazard) time)
    _ = 1 - quittingSurvivalPrefix
        (quittingRootSequenceUpdate roots who hazard) horizon :=
      weightedEffectiveness_eq_one_sub_survival _ _

theorem weightedOwnQuitMass_le_one
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) :
    weightedOwnQuitMass roots who hazard horizon ≤ 1 := by
  have hmain := weightedOwnQuitMass_le_absorbedMass
    roots who hazard horizon
  have hsurvival := quittingSurvivalPrefix_nonneg
    (quittingRootSequenceUpdate roots who hazard) horizon
  linarith

/-- **Deviation-uniform diffuse-overlap estimate.**  No matter how the
distinguished player's hazard varies, its total overlap with opponent
absorption on rows of opponent charge at most `threshold` is bounded by
`threshold` times its own first-quit mass. -/
theorem unilateralDiffuseOverlapMass_le_threshold_mul_ownQuitMass
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) :
    unilateralDiffuseOverlapMass roots who hazard horizon threshold ≤
      threshold * weightedOwnQuitMass roots who hazard horizon := by
  let diffuseTimes := (Finset.range horizon).filter
    (fun time => quittingOpponentClockCharge roots who time ≤ threshold)
  have hrow : ∀ time ∈ diffuseTimes,
      quittingSurvivalPrefix
            (quittingRootSequenceUpdate roots who hazard) time *
          (hazard time true).toReal *
          quittingOpponentClockCharge roots who time ≤
        threshold *
          (quittingSurvivalPrefix
            (quittingRootSequenceUpdate roots who hazard) time *
            (hazard time true).toReal) := by
    intro time htime
    have hcharge : quittingOpponentClockCharge roots who time ≤ threshold :=
      (Finset.mem_filter.mp htime).2
    have hbase : 0 ≤
        quittingSurvivalPrefix
            (quittingRootSequenceUpdate roots who hazard) time *
          (hazard time true).toReal :=
      mul_nonneg
        (quittingSurvivalPrefix_nonneg
          (quittingRootSequenceUpdate roots who hazard) time)
        ENNReal.toReal_nonneg
    nlinarith
  calc
    unilateralDiffuseOverlapMass roots who hazard horizon threshold =
        ∑ time ∈ diffuseTimes,
          quittingSurvivalPrefix
              (quittingRootSequenceUpdate roots who hazard) time *
            (hazard time true).toReal *
            quittingOpponentClockCharge roots who time := by rfl
    _ ≤ ∑ time ∈ diffuseTimes,
        threshold *
          (quittingSurvivalPrefix
            (quittingRootSequenceUpdate roots who hazard) time *
            (hazard time true).toReal) :=
      Finset.sum_le_sum hrow
    _ ≤ ∑ time ∈ Finset.range horizon,
        threshold *
          (quittingSurvivalPrefix
            (quittingRootSequenceUpdate roots who hazard) time *
            (hazard time true).toReal) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro time _ _
        exact mul_nonneg hthreshold <|
          mul_nonneg
            (quittingSurvivalPrefix_nonneg
              (quittingRootSequenceUpdate roots who hazard) time)
            ENNReal.toReal_nonneg
    _ = threshold * weightedOwnQuitMass roots who hazard horizon := by
      unfold weightedOwnQuitMass
      rw [Finset.mul_sum]

/-- In particular the diffuse overlap is at most `threshold`, uniformly over
all deviations and all finite horizons. -/
theorem unilateralDiffuseOverlapMass_le_threshold
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) :
    unilateralDiffuseOverlapMass roots who hazard horizon threshold ≤
      threshold := by
  exact (unilateralDiffuseOverlapMass_le_threshold_mul_ownQuitMass
    roots who hazard horizon hthreshold).trans <| by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (weightedOwnQuitMass_le_one roots who hazard horizon) hthreshold

/-- Literal survival-weighted mass of rows with at least two quitters after
the unilateral update, restricted by the fixed player-deleted clock. -/
def unilateralDiffuseCollisionMass
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) (threshold : ℝ) : ℝ :=
  ∑ time ∈ (Finset.range horizon).filter
      (fun time =>
        quittingOpponentClockCharge roots who time ≤ threshold),
    quittingSurvivalPrefix
        (quittingRootSequenceUpdate roots who hazard) time *
      quittingRootCollisionMass
        ((quittingRootSequenceUpdate roots who hazard) time)

/-- The literal collision ledger is bounded by the sum of the two transparent
ledgers: collisions internal to the fixed opponents, and overlap between the
deviator and at least one opponent. -/
theorem unilateralDiffuseCollisionMass_le_internal_add_overlap
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) (threshold : ℝ) :
    unilateralDiffuseCollisionMass roots who hazard horizon threshold ≤
      diffuseInternalOpponentCollisionMass roots who horizon threshold +
        unilateralDiffuseOverlapMass roots who hazard horizon threshold := by
  let diffuseTimes := (Finset.range horizon).filter
    (fun time => quittingOpponentClockCharge roots who time ≤ threshold)
  have hrow : ∀ time ∈ diffuseTimes,
      quittingSurvivalPrefix
            (quittingRootSequenceUpdate roots who hazard) time *
          quittingRootCollisionMass
            ((quittingRootSequenceUpdate roots who hazard) time) ≤
        quittingSurvivalPrefix (playerDeletedRoots roots who) time *
            quittingRootCollisionMass
              ((playerDeletedRoots roots who) time) +
          quittingSurvivalPrefix
              (quittingRootSequenceUpdate roots who hazard) time *
            (hazard time true).toReal *
            quittingOpponentClockCharge roots who time := by
    intro time _htime
    have hsurvival0 := quittingSurvivalPrefix_nonneg
      (quittingRootSequenceUpdate roots who hazard) time
    have hsurvivalDom :=
      survivalPrefix_rootSequenceUpdate_le_playerDeleted
        roots who hazard time
    have hcollision0 := quittingRootCollisionMass_nonneg
      ((playerDeletedRoots roots who) time)
    have hcontinue0 : 0 ≤ (hazard time false).toReal := ENNReal.toReal_nonneg
    have hcontinue1 : (hazard time false).toReal ≤ 1 := by
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (hazard time) false)
    have hinternal :
        quittingSurvivalPrefix
              (quittingRootSequenceUpdate roots who hazard) time *
            (hazard time false).toReal *
            quittingRootCollisionMass
              ((playerDeletedRoots roots who) time) ≤
          quittingSurvivalPrefix (playerDeletedRoots roots who) time *
            quittingRootCollisionMass
              ((playerDeletedRoots roots who) time) := by
      calc
        quittingSurvivalPrefix
              (quittingRootSequenceUpdate roots who hazard) time *
            (hazard time false).toReal *
            quittingRootCollisionMass
              ((playerDeletedRoots roots who) time) ≤
            quittingSurvivalPrefix
                (quittingRootSequenceUpdate roots who hazard) time * 1 *
              quittingRootCollisionMass
                ((playerDeletedRoots roots who) time) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcontinue1 hsurvival0) hcollision0
        _ = quittingSurvivalPrefix
              (quittingRootSequenceUpdate roots who hazard) time *
            quittingRootCollisionMass
              ((playerDeletedRoots roots who) time) := by ring
        _ ≤ quittingSurvivalPrefix (playerDeletedRoots roots who) time *
            quittingRootCollisionMass
              ((playerDeletedRoots roots who) time) :=
          mul_le_mul_of_nonneg_right hsurvivalDom hcollision0
    rw [show quittingRootCollisionMass
        ((quittingRootSequenceUpdate roots who hazard) time) =
          quittingRootCollisionMass
            (Function.update (roots time) who (hazard time)) by rfl]
    rw [quittingRootCollisionMass_update_decomposition
      (roots time) who (hazard time)]
    change quittingSurvivalPrefix
          (quittingRootSequenceUpdate roots who hazard) time *
        ((hazard time false).toReal *
            quittingRootCollisionMass
              ((playerDeletedRoots roots who) time) +
          (hazard time true).toReal *
            quittingOpponentClockCharge roots who time) ≤ _
    nlinarith
  calc
    unilateralDiffuseCollisionMass roots who hazard horizon threshold =
        ∑ time ∈ diffuseTimes,
          quittingSurvivalPrefix
              (quittingRootSequenceUpdate roots who hazard) time *
            quittingRootCollisionMass
              ((quittingRootSequenceUpdate roots who hazard) time) := by rfl
    _ ≤ ∑ time ∈ diffuseTimes,
        (quittingSurvivalPrefix (playerDeletedRoots roots who) time *
            quittingRootCollisionMass
              ((playerDeletedRoots roots who) time) +
          quittingSurvivalPrefix
              (quittingRootSequenceUpdate roots who hazard) time *
            (hazard time true).toReal *
            quittingOpponentClockCharge roots who time) :=
      Finset.sum_le_sum hrow
    _ = diffuseInternalOpponentCollisionMass roots who horizon threshold +
        unilateralDiffuseOverlapMass roots who hazard horizon threshold := by
      unfold diffuseInternalOpponentCollisionMass diffuseCollisionMass
        unilateralDiffuseOverlapMass
      rw [Finset.sum_add_distrib]
      congr 1

/-- **Literal deviation-uniform collision estimate.**  On rows diffuse for
the opponent clock, the probability of at least two quitters is at most
`(choose (card ι) 2 + 1) * threshold`, uniformly over every hazard of the
distinguished player. -/
theorem unilateralDiffuseCollisionMass_le_threshold
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) :
    unilateralDiffuseCollisionMass roots who hazard horizon threshold ≤
      ((Fintype.card ι).choose 2 + 1) * threshold := by
  calc
    unilateralDiffuseCollisionMass roots who hazard horizon threshold ≤
        diffuseInternalOpponentCollisionMass roots who horizon threshold +
          unilateralDiffuseOverlapMass roots who hazard horizon threshold :=
      unilateralDiffuseCollisionMass_le_internal_add_overlap
        roots who hazard horizon threshold
    _ ≤ (Fintype.card ι).choose 2 * threshold + threshold := by
      exact add_le_add
        (diffuseCollisionMass_le_threshold
          (playerDeletedRoots roots who) horizon hthreshold)
        (unilateralDiffuseOverlapMass_le_threshold
          roots who hazard horizon hthreshold)
    _ = ((Fintype.card ι).choose 2 + 1) * threshold := by ring

/-- **Player-deleted finite compression certificate.**  A bounded window of
the opponent clock has finitely many large packets, small internal-opponent
collision mass, an exponentially small opponent tail, and—uniformly for the
supplied arbitrary deviation hazard—small deviator/opponent overlap on the
diffuse rows. -/
theorem unilateral_atom_diffuse_tail_certificate
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (horizon : ℕ)
    {threshold level : ℝ} (hthreshold : 0 ≤ threshold)
    (hlower : level ≤ cumulativeOpponentEffectiveness roots who horizon)
    (hupper : cumulativeOpponentEffectiveness roots who horizon ≤ level + 1) :
    (atomicOpponentButtonTimes roots who horizon threshold).card * threshold ≤
        level + 1 ∧
      diffuseInternalOpponentCollisionMass roots who horizon threshold ≤
        (Fintype.card ι).choose 2 * threshold ∧
      quittingSurvivalPrefix (playerDeletedRoots roots who) horizon ≤
        Real.exp (-level) ∧
      unilateralDiffuseOverlapMass roots who hazard horizon threshold ≤
        threshold ∧
      unilateralDiffuseCollisionMass roots who hazard horizon threshold ≤
        ((Fintype.card ι).choose 2 + 1) * threshold := by
  have hjoint := stochasticButton_atom_diffuse_tail_certificate
    (playerDeletedRoots roots who) horizon hthreshold hlower hupper
  exact ⟨hjoint.1, hjoint.2.1, hjoint.2.2,
    unilateralDiffuseOverlapMass_le_threshold
      roots who hazard horizon hthreshold,
    unilateralDiffuseCollisionMass_le_threshold
      roots who hazard horizon hthreshold⟩

/-- **Finite reduction chosen before the deviation.**  If the fixed
opponent clock is nonsummable, then one finite horizon and one finite set of
large opponent packets work simultaneously for every possible hazard of the
distinguished player.  All literal collision mass on the remaining diffuse
rows is `O(threshold)`, and every updated survival tail is dominated by the
displayed exponentially small opponent tail. -/
theorem exists_unilateral_atom_diffuse_tail_certificate_of_not_summable
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {threshold level : ℝ} (hthreshold : 0 ≤ threshold)
    (hlevel : 0 < level)
    (hnotSummable :
      ¬Summable (quittingOpponentClockCharge roots who)) :
    ∃ horizon,
      (atomicOpponentButtonTimes roots who horizon threshold).card *
          threshold ≤ level + 1 ∧
        diffuseInternalOpponentCollisionMass roots who horizon threshold ≤
          (Fintype.card ι).choose 2 * threshold ∧
        quittingSurvivalPrefix (playerDeletedRoots roots who) horizon ≤
          Real.exp (-level) ∧
        ∀ hazard : ℕ → PMF Bool,
          unilateralDiffuseOverlapMass
              roots who hazard horizon threshold ≤ threshold ∧
            unilateralDiffuseCollisionMass
                roots who hazard horizon threshold ≤
              ((Fintype.card ι).choose 2 + 1) * threshold := by
  have hdeleted :
      ¬Summable
        (buttonEffectiveness (playerDeletedRoots roots who)) := by
    intro hsummable
    apply hnotSummable
    have heq : buttonEffectiveness (playerDeletedRoots roots who) =
        quittingOpponentClockCharge roots who := by
      funext time
      exact buttonEffectiveness_playerDeletedRoots roots who time
    rw [← heq]
    exact hsummable
  obtain ⟨horizon, hatoms, hinternal, htail⟩ :=
    exists_stochasticButton_atom_diffuse_tail_certificate_of_not_summable
      (playerDeletedRoots roots who) hthreshold hlevel hdeleted
  refine ⟨horizon, hatoms, hinternal, htail, ?_⟩
  intro hazard
  exact ⟨
    unilateralDiffuseOverlapMass_le_threshold
      roots who hazard horizon hthreshold,
    unilateralDiffuseCollisionMass_le_threshold
      roots who hazard horizon hthreshold⟩

/-- The same strategic bound applies directly to every behavioral deviation
on the canonical live path of a quitting-game profile. -/
theorem behaviorDeviation_diffuseOverlap_le_threshold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    unilateralDiffuseOverlapMass
        (quittingProfileLiveRoot reward profile) who
        (quittingBehaviorLiveHazard reward deviation) horizon threshold ≤
      threshold :=
  unilateralDiffuseOverlapMass_le_threshold _ _ _ _ hthreshold


end Research.QuittingStochasticButtonUnilateralCompression
