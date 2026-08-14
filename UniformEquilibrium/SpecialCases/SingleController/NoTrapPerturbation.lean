/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.SpecialCases.SingleController.Basic
import MathUE.LinearProgramming.ClosedTrapPerturbation

/-!
# The Vrieze adapter for closed-trap perturbations

This module is the game-specific adapter between the generic finite
closed-region perturbation in `MathUE` and Vrieze's sign-split standard-form
LP.  Given a nonempty state region that is closed under positive controller
transitions and carries zero dual occupation, strong complementarity gives a
common positive bias slack there.  Decoding the primal point, bumping its gain
on the region, and re-encoding it produces a feasible point with strictly
smaller minimization objective.

The dependent Vrieze row and column types, PMF decoding, and sign-split
encoding remain here deliberately; they are not part of the game-independent
perturbation statement.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability
open Math.LinearProgramming

variable {G : StochasticGame Bool} [Finite G.State]
  [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

/-- A nonempty positively closed zero-occupation region yields a strictly
better feasible Vrieze primal point. -/
theorem exists_vriezePrimalFeasible_strictImprovement_of_closedZeroOccupation
    {controller : Bool}
    {q : VriezeCol G controller → ℝ}
    {w : VriezeRow G controller → ℝ}
    (hstrong : IsStrongComplementaryPair
      (G.vriezeA controller) (G.vriezeB controller)
        (G.vriezeC controller) q w)
    (region : G.State → Prop) (hregion : ∃ state, region state)
    (hclosed : ∀ {source destination : G.State}
      (action : G.Act controller), region source →
        0 < G.transProb controller source action destination →
          region destination)
    (hdualZ_zero : ∀ state, region state → ∀ action,
      G.vriezeDualZ controller w state action = 0) :
    ∃ candidate : VriezeCol G controller → ℝ,
      MinPrimalFeasible
          (G.vriezeA controller) (G.vriezeB controller) candidate ∧
        minPrimalValue (G.vriezeC controller) candidate <
          minPrimalValue (G.vriezeC controller) q := by
  classical
  let indicator : G.State → ℝ :=
    ClosedTrapPerturbation.indicator region
  let biasSlack : G.State × G.Act controller → ℝ := fun pair ↦
    minPrimalSlack (G.vriezeA controller) (G.vriezeB controller) q
      (Sum.inr (Sum.inl pair))
  let guardedSlack : G.State × G.Act controller → ℝ := fun pair ↦
    if region pair.1 then biasSlack pair else 1
  obtain ⟨regionState, hregionState⟩ := hregion
  let witnessPair : G.State × G.Act controller :=
    (regionState, Classical.choice (inferInstance : Nonempty (G.Act controller)))
  letI : Nonempty (G.State × G.Act controller) := ⟨witnessPair⟩
  have hguardedSlack_pos : ∀ pair : G.State × G.Act controller,
      0 < guardedSlack pair := by
    intro pair
    by_cases hpair : region pair.1
    · dsimp only [guardedSlack]
      rw [if_pos hpair]
      exact
        (hstrong.minPrimalSlack_pos_iff_dual_eq_zero
          (Sum.inr (Sum.inl pair))).2
          (hdualZ_zero pair.1 hpair pair.2)
    · simp [guardedSlack, hpair]
  obtain ⟨ε, hεpos, hεle⟩ :=
    ClosedTrapPerturbation.exists_uniformPositiveLowerBound
      guardedSlack hguardedSlack_pos
  have hε_le_slack : ∀ state, region state → ∀ action,
      ε ≤ biasSlack (state, action) := by
    intro state hstate action
    have hle := hεle (state, action)
    simpa only [guardedSlack, if_pos hstate] using hle
  let decodedX : G.State → PMF (G.Act (!controller)) :=
    G.vriezeDecodeX controller q
  let decodedG : G.State → ℝ := G.vriezeDecodeG controller q
  let decodedV : G.State → ℝ := G.vriezeDecodeV controller q
  have hdecodeXVal_isProb : ∀ state : G.State,
      (∀ action, 0 ≤ G.vriezeDecodeXVal controller q state action) ∧
        (∑ action, G.vriezeDecodeXVal controller q state action) = 1 := by
    intro state
    refine ⟨fun action ↦ hstrong.1.1 (Sum.inl (state, action)), ?_⟩
    have hpos := hstrong.1.2
      (Sum.inr (Sum.inr (Sum.inl state)))
    have hneg := hstrong.1.2
      (Sum.inr (Sum.inr (Sum.inr state)))
    rw [(G.rowEval_vriezeA_simplex controller q state).1] at hpos
    rw [(G.rowEval_vriezeA_simplex controller q state).2] at hneg
    simp only [vriezeB] at hpos hneg
    linarith
  have hdecodedX_toReal : ∀ (state : G.State)
      (action : G.Act (!controller)),
      ((decodedX state) action).toReal =
        G.vriezeDecodeXVal controller q state action := by
    intro state action
    dsimp only [decodedX]
    exact G.vriezeDecodeX_apply_toReal controller q state
      (hdecodeXVal_isProb state).1 (hdecodeXVal_isProb state).2 action
  have htransProb_nonneg : ∀ source (action : G.Act controller) destination,
      0 ≤ G.transProb controller source action destination := by
    intro source action destination
    exact ENNReal.toReal_nonneg
  have htransProb_sum : ∀ source (action : G.Act controller),
      (∑ destination, G.transProb controller source action destination) = 1 := by
    intro source action
    simpa [transProb] using
      pmf_toReal_sum_one
        (G.transition source (G.jointOfControllerAct controller action))
  have hgain : ∀ (state : G.State) (action : G.Act controller),
      decodedG state ≤
        ∑ destination,
          G.transProb controller state action destination * decodedG destination := by
    intro state action
    have hrow := hstrong.1.2 (Sum.inl (state, action))
    rw [G.rowEval_vriezeA_gain] at hrow
    simp only [vriezeB] at hrow
    dsimp only [decodedG]
    linarith
  let improvedG : G.State → ℝ := fun state ↦
    decodedG state + ε * indicator state
  have hgain_improved : ∀ (state : G.State) (action : G.Act controller),
      improvedG state ≤
        ∑ destination,
          G.transProb controller state action destination *
            improvedG destination := by
    have himproved :=
      ClosedTrapPerturbation.add_indicator_preserves_gain
        (G.transProb controller) region decodedG hεpos.le
        htransProb_nonneg htransProb_sum hclosed hgain
    simpa only [improvedG, indicator] using himproved
  let biasRhs : G.State → G.Act controller → ℝ :=
    fun state action ↦
      (∑ opponentAction,
        ((decodedX state) opponentAction).toReal *
          G.rewardVal controller state opponentAction action) +
        ∑ destination,
          G.transProb controller state action destination *
            decodedV destination
  have hbias : ∀ (state : G.State) (action : G.Act controller),
      decodedG state + decodedV state ≤ biasRhs state action := by
    intro state action
    have hrow := hstrong.1.2
      (Sum.inr (Sum.inl (state, action)))
    rw [G.rowEval_vriezeA_bias] at hrow
    simp only [vriezeB] at hrow
    simp_rw [← hdecodedX_toReal] at hrow
    dsimp only [biasRhs, decodedG, decodedV]
    linarith
  have hslack_eq : ∀ (state : G.State) (action : G.Act controller),
      biasSlack (state, action) =
        biasRhs state action - (decodedG state + decodedV state) := by
    intro state action
    dsimp only [biasSlack]
    rw [minPrimalSlack, G.rowEval_vriezeA_bias]
    simp only [vriezeB, sub_zero]
    simp_rw [← hdecodedX_toReal]
    dsimp only [biasRhs, decodedG, decodedV]
    ring
  have hbias_improved : ∀ (state : G.State) (action : G.Act controller),
      improvedG state + decodedV state ≤ biasRhs state action := by
    have himproved :=
      ClosedTrapPerturbation.add_indicator_le_of_region_le_slack
        region
        (fun state _ ↦ decodedG state + decodedV state)
        biasRhs hbias
        (fun state hstate action ↦ by
          rw [← hslack_eq]
          exact hε_le_slack state hstate action)
    intro state action
    have hrow := himproved state action
    dsimp only [improvedG, indicator] at hrow ⊢
    linarith
  let improvedPoint : VriezeCol G controller → ℝ :=
    G.vriezeEncode controller decodedX improvedG decodedV
  have himproved_feasible :
      MinPrimalFeasible
        (G.vriezeA controller) (G.vriezeB controller) improvedPoint := by
    refine ⟨?_, ?_⟩
    · rintro (⟨state, action⟩ | state | state | state | state) <;>
        simp [improvedPoint, vriezeEncode, ENNReal.toReal_nonneg]
    · rintro (⟨state, action⟩ | ⟨state, action⟩ | state | state)
      · dsimp only [improvedPoint]
        rw [G.rowEval_vriezeA_vriezeEncode_gain]
        change (0 : ℝ) ≤ _
        linarith [hgain_improved state action]
      · dsimp only [improvedPoint]
        rw [G.rowEval_vriezeA_vriezeEncode_bias]
        change (0 : ℝ) ≤ _
        dsimp only [biasRhs] at hbias_improved
        linarith [hbias_improved state action]
      · change (1 : ℝ) ≤ rowEval
          (G.vriezeA controller) improvedPoint
            (Sum.inr (Sum.inr (Sum.inl state)))
        rw [(G.rowEval_vriezeA_simplex controller improvedPoint state).1]
        dsimp only [improvedPoint]
        simp only [G.vriezeDecodeXVal_vriezeEncode]
        exact le_of_eq (pmf_toReal_sum_one (decodedX state)).symm
      · change (-1 : ℝ) ≤ rowEval
          (G.vriezeA controller) improvedPoint
            (Sum.inr (Sum.inr (Sum.inr state)))
        rw [(G.rowEval_vriezeA_simplex controller improvedPoint state).2]
        dsimp only [improvedPoint]
        simp only [G.vriezeDecodeXVal_vriezeEncode]
        rw [pmf_toReal_sum_one (decodedX state)]
  have hsum_gain_lt :
      (∑ state, decodedG state) < ∑ state, improvedG state := by
    simpa only [improvedG, indicator] using
      ClosedTrapPerturbation.sum_lt_sum_add_indicator
        region decodedG hεpos ⟨regionState, hregionState⟩
  have himproved_value_lt :
      minPrimalValue (G.vriezeC controller) improvedPoint <
        minPrimalValue (G.vriezeC controller) q := by
    rw [G.minPrimalValue_vriezeC_eq,
      G.minPrimalValue_vriezeC_eq]
    simp only [improvedPoint, G.vriezeDecodeG_vriezeEncode]
    exact neg_lt_neg hsum_gain_lt
  exact ⟨improvedPoint, himproved_feasible, himproved_value_lt⟩

end StochasticGame
end GameTheory
