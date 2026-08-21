/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.CollisionMass
import MathUE.Probability.WeightedCollisionConcentration
import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Collision concentration along finite quitting windows

This module connects the independent-product collision estimate to quitting
roots.  `quittingRootCollisionMass` is the exact one-stage probability of a
quitter set containing at least two players, expressed through the existing
`quittingRootCoalitionMass` semantics.

For a finite survival-weighted window whose one-stage absorption is at most
`rho`, conditional collision mass is at most

`choose (card ι) 2 * rho`.

The theorem separates the zero-absorption case, where collision mass is also
zero and no quotient is formed.  A companion estimate transfers this bound
to any bounded payoff decomposition into singleton and collision parts.

The root-level interface also characterizes zero collision as having at most
one positive Quit marginal and bounds collision by every player's
opponent-absorption event. These facts support rank reduction without counting
coalitions individually.
-/

noncomputable section

namespace GameTheory

open Filter Math.PMFProduct Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One-stage probability of simultaneous quitting by at least two players. -/
def quittingRootCollisionMass (root : ι → PMF Bool) : ℝ :=
  collisionMass (quittingRootQuitRates root)

/-- Collision mass is exactly the sum of the existing product-law coalition
masses over quitter sets of cardinality at least two. -/
theorem quittingRootCollisionMass_eq_sum_coalitionMass
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root =
      ∑ coalition ∈ Finset.univ.filter
          (fun coalition : Finset ι => 2 ≤ coalition.card),
        quittingRootCoalitionMass root coalition := by
  rfl

/-- Collision is contained in every player's opponent-absorption event. -/
theorem quittingRootCollisionMass_le_opponentAbsorptionMass
    (root : ι → PMF Bool) (owner : ι) :
    quittingRootCollisionMass root ≤
      quittingRootOpponentAbsorptionMass root owner := by
  let rate : ι → ℝ := quittingRootQuitRates root
  have hrate0 : ∀ who, 0 ≤ rate who := fun _ => ENNReal.toReal_nonneg
  have hrate1 : ∀ who, rate who ≤ 1 := fun who =>
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  let others : Finset ι := Finset.univ.erase owner
  have hownerNot : owner ∉ others := by simp [others]
  have huniv : (Finset.univ : Finset ι) = insert owner others :=
    (Finset.insert_erase (Finset.mem_univ owner)).symm
  have hcollisionRest0 : 0 ≤ collisionMassFormulaOn rate others :=
    collisionMassFormulaOn_nonneg rate others
      (fun who _ => hrate0 who) (fun who _ => hrate1 who)
  have habsorptionRest0 :
      0 ≤ 1 - ∏ who ∈ others, (1 - rate who) := by
    exact sub_nonneg.mpr (Finset.prod_le_one
      (fun who _ => sub_nonneg.mpr (hrate1 who))
      (fun who _ => by linarith [hrate0 who]))
  have hcollisionRestLe : collisionMassFormulaOn rate others ≤
      1 - ∏ who ∈ others, (1 - rate who) := by
    unfold collisionMassFormulaOn
    have hsingle0 : 0 ≤ ∑ who ∈ others,
        rate who * ∏ other ∈ others.erase who, (1 - rate other) :=
      Finset.sum_nonneg fun who _ => mul_nonneg (hrate0 who)
        (Finset.prod_nonneg fun other _ =>
          sub_nonneg.mpr (hrate1 other))
    linarith
  have hformula : collisionMass rate =
      (1 - rate owner) * collisionMassFormulaOn rate others +
        rate owner * (1 - ∏ who ∈ others, (1 - rate who)) := by
    rw [collisionMass_eq_one_sub_continueMass_sub_singletonMass]
    change collisionMassFormulaOn rate Finset.univ = _
    rw [huniv, collisionMassFormulaOn_insert rate hownerNot]
  have hbound : collisionMass rate ≤
      1 - ∏ who ∈ others, (1 - rate who) := by
    rw [hformula]
    calc
      (1 - rate owner) * collisionMassFormulaOn rate others +
            rate owner * (1 - ∏ who ∈ others, (1 - rate who)) ≤
          (1 - rate owner) *
              (1 - ∏ who ∈ others, (1 - rate who)) +
            rate owner * (1 - ∏ who ∈ others, (1 - rate who)) := by
        gcongr
        exact sub_nonneg.mpr (hrate1 owner)
      _ = 1 - ∏ who ∈ others, (1 - rate who) := by ring
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  simpa only [quittingRootCollisionMass, rate, others,
    quittingRootQuitRates] using hbound

/-- Collision mass times a nonnegative coordinate sum is bounded by the sum
of opponent-absorption charges. -/
theorem quittingRootCollisionMass_mul_sum_le_sum_opponentAbsorptionMass_mul
    (root : ι → PMF Bool) (weight : ι → ℝ)
    (hweight : ∀ who, 0 ≤ weight who) :
    quittingRootCollisionMass root * (∑ who, weight who) ≤
      ∑ who,
        quittingRootOpponentAbsorptionMass root who * weight who := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun who _ =>
    mul_le_mul_of_nonneg_right
      (quittingRootCollisionMass_le_opponentAbsorptionMass root who)
      (hweight who)

/-- Two distinct positive Quit marginals force positive collision mass. -/
theorem quittingRootCollisionMass_pos_of_two_quitProbability_pos
    (root : ι → PMF Bool) {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < (root first true).toReal)
    (hsecond : 0 < (root second true).toReal) :
    0 < quittingRootCollisionMass root := by
  apply collisionMass_pos_of_two_pos
    (quittingRootQuitRates root)
  · exact fun _ => ENNReal.toReal_nonneg
  · exact fun who =>
      ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  · exact hne
  · exact hfirst
  · exact hsecond

/-- Positive collision mass exposes two distinct positive Quit marginals. -/
theorem exists_two_quitProbability_pos_of_quittingRootCollisionMass_pos
    (root : ι → PMF Bool) (hcollision : 0 < quittingRootCollisionMass root) :
    ∃ first second, first ≠ second ∧
      0 < (root first true).toReal ∧ 0 < (root second true).toReal := by
  exact exists_two_pos_of_collisionMass_pos
    (quittingRootQuitRates root)
    (fun _ => ENNReal.toReal_nonneg)
    (fun who =>
      ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true))
    hcollision

/-- Collision mass is positive exactly when two distinct players have
positive Quit probability. -/
theorem quittingRootCollisionMass_pos_iff_exists_two_quitProbability_pos
    (root : ι → PMF Bool) :
    0 < quittingRootCollisionMass root ↔
      ∃ first second, first ≠ second ∧
        0 < (root first true).toReal ∧ 0 < (root second true).toReal := by
  constructor
  · exact exists_two_quitProbability_pos_of_quittingRootCollisionMass_pos root
  · rintro ⟨first, second, hne, hfirst, hsecond⟩
    exact quittingRootCollisionMass_pos_of_two_quitProbability_pos
      root hne hfirst hsecond

/-- Collision mass vanishes exactly when at most one player has positive Quit
probability. -/
theorem quittingRootCollisionMass_eq_zero_iff_atMostOne_quitProbability_pos
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root = 0 ↔
      ∀ first second,
        0 < (root first true).toReal →
        0 < (root second true).toReal → first = second := by
  exact collisionMass_eq_zero_iff_atMostOne_pos
    (quittingRootQuitRates root)
    (fun _ => ENNReal.toReal_nonneg)
    (fun who =>
      ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true))

omit [DecidableEq ι] in
/-- The all-continue mass computed from quit rates agrees with the quitting
root's stationary all-Continue probability. -/
theorem continueMass_quittingRootQuitRates (root : ι → PMF Bool) :
    continueMass (quittingRootQuitRates root) =
      quittingStationaryContinueMass root := by
  classical
  rw [continueMass, quittingStationaryContinueMass_eq_prod_continueProbability]
  congr 1
  funext who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  change 1 - (root who true).toReal = (root who false).toReal
  linarith

omit [DecidableEq ι] in
/-- Root absorption is nonnegative. -/
theorem quittingRootAbsorptionMass_nonneg
    (root : ι → PMF Bool) :
    0 ≤ quittingRootAbsorptionMass root := by
  exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one root)

/-- Root collision mass is nonnegative. -/
theorem quittingRootCollisionMass_nonneg
    (root : ι → PMF Bool) :
    0 ≤ quittingRootCollisionMass root := by
  apply collisionMass_nonneg
  · exact fun _ => ENNReal.toReal_nonneg
  · exact fun who => by
      unfold quittingRootQuitRates
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (root who) true)

/-- Collision mass is no greater than total absorption mass. -/
theorem quittingRootCollisionMass_le_absorptionMass
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root ≤ quittingRootAbsorptionMass root := by
  rw [quittingRootCollisionMass,
    collisionMass_eq_one_sub_continueMass_sub_singletonMass,
    continueMass_quittingRootQuitRates, quittingRootAbsorptionMass]
  apply sub_le_self
  exact Finset.sum_nonneg fun owner _ ↦
    mul_nonneg ENNReal.toReal_nonneg
      (Finset.prod_nonneg fun other _ ↦ by
        have hle : ((root other) true).toReal ≤ 1 := by
          simpa using ENNReal.toReal_mono ENNReal.one_ne_top
            (PMF.coe_le_one (root other) true)
        unfold quittingRootQuitRates
        linarith)

/-- Sharp intermediate pair-union bound for a quitting root. -/
theorem quittingRootCollisionMass_le_pairMulSum
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root ≤
      Math.pairMulSum (quittingRootQuitRates root) Finset.univ := by
  apply collisionMass_le_pairMulSum
  · exact fun _ => ENNReal.toReal_nonneg
  · exact fun who => by
      unfold quittingRootQuitRates
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (root who) true)

/-- Stagewise product-law collision estimate.  The constant is the number of
unordered pairs of players. -/
theorem quittingRootCollisionMass_le_choose_card_mul_absorption_sq
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root ≤
      (Fintype.card ι).choose 2 * quittingRootAbsorptionMass root ^ 2 := by
  have h := collisionMass_le_choose_card_mul_absorption_sq
    (quittingRootQuitRates root)
    (fun _ => ENNReal.toReal_nonneg)
    (fun who => by
      unfold quittingRootQuitRates
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (root who) true))
  rw [continueMass_quittingRootQuitRates] at h
  simpa [quittingRootCollisionMass, quittingRootAbsorptionMass] using h

/-! ## Infinite survival-weighted collision mass -/

/-- The total probability of first-stage absorption by two or more players
along a root sequence. -/
def quittingRootSequenceCollisionMass
    (roots : ℕ → ι → PMF Bool) (start : ℕ) : ℝ :=
  ∑' offset : ℕ, quittingJointSurvivalWeight roots start offset *
    quittingRootCollisionMass (roots (start + offset))

/-- Infinite survival-weighted collision mass is nonnegative. -/
theorem quittingRootSequenceCollisionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    0 ≤ quittingRootSequenceCollisionMass roots start := by
  exact tsum_nonneg fun offset => mul_nonneg
    (quittingJointSurvivalWeight_nonneg roots start offset)
    (quittingRootCollisionMass_nonneg _)

/-- Survival-weighted collision probabilities are summable. -/
theorem summable_quittingJointSurvivalWeight_mul_quittingRootCollisionMass
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    Summable (fun offset : ℕ ↦
      quittingJointSurvivalWeight roots start offset *
        quittingRootCollisionMass (roots (start + offset))) := by
  apply summable_of_sum_range_le (c := 1)
  · intro offset
    exact mul_nonneg
      (quittingJointSurvivalWeight_nonneg roots start offset)
      (quittingRootCollisionMass_nonneg _)
  · intro fuel
    calc
      ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots start offset *
              quittingRootCollisionMass (roots (start + offset)) ≤
          ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots start offset *
              (1 - quittingStationaryContinueMass
                (roots (start + offset))) := by
        apply Finset.sum_le_sum
        intro offset _
        apply mul_le_mul_of_nonneg_left _
          (quittingJointSurvivalWeight_nonneg roots start offset)
        exact quittingRootCollisionMass_le_absorptionMass _
      _ = 1 - quittingJointSurvivalWeight roots start fuel :=
        sum_quittingJointSurvivalWeight_mul_one_sub_continueMass
          roots start fuel
      _ ≤ 1 := by
        linarith [quittingJointSurvivalWeight_nonneg roots start fuel]

/-- If every row absorbs with probability at most `rho`, then the total
collision probability is at most the number of player pairs times `rho`
times the total absorption probability. -/
theorem quittingRootSequenceCollisionMass_le
    (roots : ℕ → ι → PMF Bool) (start : ℕ) (rho : ℝ)
    (hcap : ∀ offset,
      quittingRootAbsorptionMass (roots (start + offset)) ≤ rho) :
    quittingRootSequenceCollisionMass roots start ≤
      (Fintype.card ι).choose 2 * rho *
        (1 - quittingJointSurvivalLimit roots start) := by
  have hsummable :=
    summable_quittingJointSurvivalWeight_mul_quittingRootCollisionMass
      roots start
  have hpartial : ∀ fuel,
      (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start offset *
            quittingRootCollisionMass (roots (start + offset))) ≤
        (Fintype.card ι).choose 2 * rho *
          (1 - quittingJointSurvivalWeight roots start fuel) := by
    intro fuel
    calc
      ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots start offset *
              quittingRootCollisionMass (roots (start + offset)) ≤
          ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots start offset *
              ((Fintype.card ι).choose 2 * rho *
                quittingRootAbsorptionMass
                  (roots (start + offset))) := by
        apply Finset.sum_le_sum
        intro offset _
        apply mul_le_mul_of_nonneg_left _
          (quittingJointSurvivalWeight_nonneg roots start offset)
        have hcollision :=
          quittingRootCollisionMass_le_choose_card_mul_absorption_sq
            (roots (start + offset))
        have habsorption :=
          quittingRootAbsorptionMass_nonneg (roots (start + offset))
        have hpairs : 0 ≤ ((Fintype.card ι).choose 2 : ℝ) := by positivity
        calc
          quittingRootCollisionMass (roots (start + offset)) ≤
              (Fintype.card ι).choose 2 *
                quittingRootAbsorptionMass (roots (start + offset)) ^ 2 :=
            hcollision
          _ = ((Fintype.card ι).choose 2 *
                quittingRootAbsorptionMass (roots (start + offset))) *
              quittingRootAbsorptionMass (roots (start + offset)) := by ring
          _ ≤ ((Fintype.card ι).choose 2 * rho) *
              quittingRootAbsorptionMass (roots (start + offset)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hcap offset) hpairs) habsorption
          _ = (Fintype.card ι).choose 2 * rho *
              quittingRootAbsorptionMass (roots (start + offset)) := rfl
      _ = (Fintype.card ι).choose 2 * rho *
          (∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight roots start offset *
              (1 - quittingStationaryContinueMass
                (roots (start + offset)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        rw [quittingRootAbsorptionMass]
        ring
      _ = (Fintype.card ι).choose 2 * rho *
          (1 - quittingJointSurvivalWeight roots start fuel) := by
        rw [sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
  have hleft : Tendsto (fun fuel ↦
      ∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots start offset *
          quittingRootCollisionMass (roots (start + offset))) atTop
      (nhds (quittingRootSequenceCollisionMass roots start)) := by
    unfold quittingRootSequenceCollisionMass
    exact hsummable.hasSum.tendsto_sum_nat
  have hright : Tendsto (fun fuel ↦
      (Fintype.card ι).choose 2 * rho *
        (1 - quittingJointSurvivalWeight roots start fuel)) atTop
      (nhds ((Fintype.card ι).choose 2 * rho *
        (1 - quittingJointSurvivalLimit roots start))) := by
    exact (tendsto_const_nhds.sub
      (tendsto_quittingJointSurvivalLimit roots start)).const_mul _
  exact le_of_tendsto_of_tendsto' hleft hright hpartial

/-- A survival-weighted finite quitting window either has no absorption (and
hence no collision), or its conditional collision mass is at most
`choose (card ι) 2 * rho`.

The weight may be any nonnegative finite-window weight; in applications it
is the live mass before the corresponding row. -/
theorem finiteQuittingRootCollisionConcentration_or_zero
    {κ : Type} [Fintype κ]
    (weight : κ → ℝ) (roots : κ → ι → PMF Bool) (rho : ℝ)
    (hweight : ∀ phase, 0 ≤ weight phase)
    (hcap : ∀ phase, quittingRootAbsorptionMass (roots phase) ≤ rho) :
    ((∑ phase, weight phase * quittingRootAbsorptionMass (roots phase)) = 0 ∧
        (∑ phase, weight phase * quittingRootCollisionMass (roots phase)) = 0) ∨
      (0 < ∑ phase, weight phase * quittingRootAbsorptionMass (roots phase) ∧
        (∑ phase, weight phase * quittingRootCollisionMass (roots phase)) /
            (∑ phase, weight phase * quittingRootAbsorptionMass (roots phase)) ≤
          (Fintype.card ι).choose 2 * rho) := by
  let absorption : κ → ℝ := fun phase =>
    quittingRootAbsorptionMass (roots phase)
  let collision : κ → ℝ := fun phase =>
    quittingRootCollisionMass (roots phase)
  have h := finiteWeightedCollisionConcentration_or_zero (κ := κ)
    weight absorption collision ((Fintype.card ι).choose 2 : ℝ) rho
    hweight
    (fun phase => quittingRootAbsorptionMass_nonneg (roots phase))
    (fun phase => quittingRootCollisionMass_nonneg (roots phase))
    (Nat.cast_nonneg _) hcap
    (fun phase => by
      simpa [absorption, collision] using
        quittingRootCollisionMass_le_choose_card_mul_absorption_sq
          (roots phase))
  exact h

/-- Payoff consequence of finite-window collision concentration.  The full
absorbing contribution is split into singleton contribution `X` and
collision contribution `b`; `S` is singleton mass.  If both reward parts are
bounded by `M` times their corresponding masses, the conditional payoff is
within `2 * M * choose (card ι) 2 * rho` of the normalized singleton
mixture. -/
theorem abs_finiteQuittingRootConditionalPayoff_sub_singletonMixture_le
    {κ : Type} [Fintype κ]
    (weight : κ → ℝ) (roots : κ → ι → PMF Bool) (rho : ℝ)
    {S X b actual mixture M : ℝ}
    (hweight : ∀ phase, 0 ≤ weight phase)
    (hcap : ∀ phase, quittingRootAbsorptionMass (roots phase) ≤ rho)
    (hdecomposition :
      (∑ phase, weight phase * quittingRootAbsorptionMass (roots phase)) =
        S + ∑ phase, weight phase * quittingRootCollisionMass (roots phase))
    (habsorption :
      0 < ∑ phase, weight phase * quittingRootAbsorptionMass (roots phase))
    (hsingleton : 0 < S) (hM : 0 ≤ M)
    (hX : |X| ≤ M * S)
    (hb : |b| ≤ M *
      ∑ phase, weight phase * quittingRootCollisionMass (roots phase))
    (hactual : actual =
      (X + b) /
        ∑ phase, weight phase * quittingRootAbsorptionMass (roots phase))
    (hmixture : mixture = X / S) :
    |actual - mixture| ≤
      2 * M * ((Fintype.card ι).choose 2 * rho) := by
  have hconcentration := finiteQuittingRootCollisionConcentration_or_zero
    weight roots rho hweight hcap
  rcases hconcentration with hzero | hpositive
  · linarith [hzero.1]
  · have happrox := abs_conditionalPayoff_sub_singletonMixture_le
      hdecomposition habsorption hsingleton
      (Finset.sum_nonneg fun phase _ =>
        mul_nonneg (hweight phase)
          (quittingRootCollisionMass_nonneg (roots phase)))
      hM hX hb hactual hmixture
    calc
      |actual - mixture| ≤
          2 * M *
              (∑ phase, weight phase *
                quittingRootCollisionMass (roots phase)) /
            (∑ phase, weight phase *
              quittingRootAbsorptionMass (roots phase)) := happrox
      _ = 2 * M *
          ((∑ phase, weight phase *
              quittingRootCollisionMass (roots phase)) /
            (∑ phase, weight phase *
              quittingRootAbsorptionMass (roots phase))) := by ring
      _ ≤ 2 * M * ((Fintype.card ι).choose 2 * rho) := by
        exact mul_le_mul_of_nonneg_left hpositive.2
          (mul_nonneg (by norm_num) hM)

end GameTheory
