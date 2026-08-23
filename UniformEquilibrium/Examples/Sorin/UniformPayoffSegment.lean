/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.WeightedBlackwellFerguson
import UniformEquilibrium.Examples.Sorin.OccupationStopping

/-!
# The uniform-payoff segment in Sorin's absorbing game

This module constructs the asymmetric Blackwell--Ferguson profiles that
realize the segment

`(a, 2 * (1 - a))`, for `1 / 2 ≤ a ≤ 2 / 3`,

in Sorin's displayed two-player absorbing game.  Player two uses the
stationary column mix with Right probability `a`.  Player one keeps a
centered public account of past live column actions and stops at the
reciprocal quadratic rate matched to that account.

The proof is entirely in finite public-history laws.  Its scalar Bellman and
energy identities are supplied by `MathUE.WeightedBlackwellFerguson`.
-/

noncomputable section

open scoped BigOperators Topology

namespace GameTheory
namespace StochasticGame
namespace SorinAbsorbingGame

open Filter Math.Probability Math.PMFProduct
open MathUE.WeightedBlackwellFerguson

private theorem expect_mono_on_support
    {α : Type} [Finite α] (law : PMF α) (f g : α → ℝ)
    (hfg : ∀ x ∈ law.support, f x ≤ g x) :
    expect law f ≤ expect law g := by
  classical
  let patched : α → ℝ := fun x => if law x = 0 then g x else f x
  calc
    expect law f = expect law patched := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro x hx
      have hx0 : law x ≠ 0 := by
        simpa [PMF.mem_support_iff] using hx
      simp [patched, hx0]
    _ ≤ expect law g := by
      apply expect_mono
      intro x
      by_cases hx : law x = 0
      · simp [patched, hx]
      · simp only [patched, hx, ↓reduceIte]
        exact hfg x (by simpa [PMF.mem_support_iff])

/-- A point on the parameter interval of Sorin's uniform-payoff segment. -/
structure UniformSegmentParameter where
  value : ℝ
  half_le : 1 / 2 ≤ value
  le_two_thirds : value ≤ 2 / 3

namespace UniformSegmentParameter

/-- Probability of `Left` in the prescribed column mix. -/
def leftProbability (parameter : UniformSegmentParameter) : ℝ :=
  1 - parameter.value

/-- Difference between the two row payoffs under the prescribed column mix. -/
def rowSlope (parameter : UniformSegmentParameter) : ℝ :=
  parameter.value - parameter.leftProbability

/-- Difference between player two's two live-action values. -/
def columnSlack (parameter : UniformSegmentParameter) : ℝ :=
  2 * parameter.leftProbability - parameter.value

theorem value_add_leftProbability (parameter : UniformSegmentParameter) :
    parameter.value + parameter.leftProbability = 1 := by
  simp [leftProbability]

theorem mul_value_add_leftProbability (parameter : UniformSegmentParameter)
    (scale : ℝ) :
    scale * parameter.value + scale * parameter.leftProbability = scale := by
  calc
    scale * parameter.value + scale * parameter.leftProbability =
        scale * (parameter.value + parameter.leftProbability) := by ring
    _ = scale := by rw [parameter.value_add_leftProbability]; ring

theorem value_pos (parameter : UniformSegmentParameter) :
    0 < parameter.value := by
  linarith [parameter.half_le]

theorem leftProbability_pos (parameter : UniformSegmentParameter) :
    0 < parameter.leftProbability := by
  unfold leftProbability
  linarith [parameter.le_two_thirds]

theorem leftProbability_le_value (parameter : UniformSegmentParameter) :
    parameter.leftProbability ≤ parameter.value := by
  unfold leftProbability
  linarith [parameter.half_le]

theorem leftProbability_nonneg (parameter : UniformSegmentParameter) :
    0 ≤ parameter.leftProbability :=
  parameter.leftProbability_pos.le

theorem leftProbability_le_one (parameter : UniformSegmentParameter) :
    parameter.leftProbability ≤ 1 := by
  unfold leftProbability
  linarith [parameter.value_pos]

theorem rowSlope_nonneg (parameter : UniformSegmentParameter) :
    0 ≤ parameter.rowSlope := by
  unfold rowSlope
  exact sub_nonneg.mpr parameter.leftProbability_le_value

theorem columnSlack_nonneg (parameter : UniformSegmentParameter) :
    0 ≤ parameter.columnSlack := by
  unfold columnSlack leftProbability
  linarith [parameter.le_two_thirds]

end UniformSegmentParameter

abbrev SegmentParameter := UniformSegmentParameter

/-- The centered column increment: `+a` on Left and `-(1-a)` on Right. -/
def segmentIncrement (parameter : SegmentParameter) (column : Bool) : ℝ :=
  if column then parameter.value else -parameter.leftProbability

theorem segmentIncrement_ge_neg_leftProbability
    (parameter : SegmentParameter) (column : Bool) :
    -parameter.leftProbability ≤ segmentIncrement parameter column := by
  cases column
  · exact le_rfl
  · simp only [segmentIncrement, if_true]
    linarith [parameter.value_pos, parameter.leftProbability_pos]

/-- The accumulated centered column increment on stages that began live. -/
def segmentIncrementSum (parameter : SegmentParameter) {time : ℕ}
    (history : game.Hist time) : ℝ :=
  ∑ stage : Fin time,
    liveIndicator (history.1 stage).1 *
      segmentIncrement parameter ((history.1 stage).2 true)

/-- The raw account before clamping. -/
def segmentRawBalance (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) : ℝ :=
  initial + segmentIncrementSum parameter history

/-- The account denominator, clamped at the negative-step size. -/
def segmentDenom (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) : ℝ :=
  max (segmentRawBalance parameter initial history)
    parameter.leftProbability

theorem leftProbability_le_segmentDenom (parameter : SegmentParameter)
    (initial : ℝ) {time : ℕ} (history : game.Hist time) :
    parameter.leftProbability ≤ segmentDenom parameter initial history :=
  le_max_right _ _

theorem segmentDenom_pos (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) :
    0 < segmentDenom parameter initial history :=
  parameter.leftProbability_pos.trans_le
    (leftProbability_le_segmentDenom parameter initial history)

/-- Player one's stopping probability at a public history. -/
def segmentStopProbability (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) : ℝ :=
  stopProbability parameter.value parameter.leftProbability
    (segmentDenom parameter initial history)

theorem segmentStopProbability_pos (parameter : SegmentParameter)
    (initial : ℝ) {time : ℕ} (history : game.Hist time) :
    0 < segmentStopProbability parameter initial history :=
  stopProbability_pos parameter.leftProbability_le_value
    parameter.leftProbability_pos
    (leftProbability_le_segmentDenom parameter initial history)

theorem segmentStopProbability_nonneg (parameter : SegmentParameter)
    (initial : ℝ) {time : ℕ} (history : game.Hist time) :
    0 ≤ segmentStopProbability parameter initial history :=
  (segmentStopProbability_pos parameter initial history).le

theorem segmentStopProbability_le_one (parameter : SegmentParameter)
    (initial : ℝ) {time : ℕ} (history : game.Hist time) :
    segmentStopProbability parameter initial history ≤ 1 :=
  stopProbability_le_one parameter.leftProbability_le_value
    parameter.leftProbability_pos
    (leftProbability_le_segmentDenom parameter initial history)

theorem segmentStopProbability_eq_one_of_raw_le
    (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time)
    (hraw : segmentRawBalance parameter initial history ≤
      parameter.leftProbability) :
    segmentStopProbability parameter initial history = 1 := by
  rw [segmentStopProbability, segmentDenom, max_eq_right hraw]
  exact stopProbability_at_floor parameter.value_pos.ne'
    parameter.leftProbability_pos.ne'

/-- The history-dependent row strategy. -/
def weightedBlackwellFergusonStrategy (parameter : SegmentParameter)
    (initial : ℝ) : game.BehaviorStrategy false :=
  fun _time history =>
    BigMatch.coinPMF (segmentStopProbability parameter initial history)
      (segmentStopProbability_nonneg parameter initial history)
      (segmentStopProbability_le_one parameter initial history)

/-- Player two's prescribed stationary column coin: Left has probability
`1-a`, hence Right has probability `a`. -/
def segmentColumnCoin (parameter : SegmentParameter) : PMF Bool :=
  BigMatch.coinPMF parameter.leftProbability parameter.leftProbability_nonneg
    parameter.leftProbability_le_one

@[simp] theorem segmentColumnCoin_true_toReal
    (parameter : SegmentParameter) :
    (segmentColumnCoin parameter true).toReal =
      parameter.leftProbability :=
  BigMatch.coinPMF_apply_true_toReal _ _ _

@[simp] theorem segmentColumnCoin_false_toReal
    (parameter : SegmentParameter) :
    (segmentColumnCoin parameter false).toReal = parameter.value := by
  rw [segmentColumnCoin, BigMatch.coinPMF_apply_false_toReal]
  linarith [parameter.value_add_leftProbability]

/-- The prescribed stationary column strategy. -/
def segmentColumnStrategy (parameter : SegmentParameter) :
    game.BehaviorStrategy true :=
  fun _time _history => segmentColumnCoin parameter

/-- The prescribed profile. -/
def segmentProfile (parameter : SegmentParameter) (initial : ℝ) :
    game.BehaviorProfile :=
  fun who time history =>
    if who then segmentColumnStrategy parameter time history
    else weightedBlackwellFergusonStrategy parameter initial time history

/-- Player one's strategy paired with an arbitrary column deviation. -/
def segmentColumnDeviationProfile (parameter : SegmentParameter)
    (initial : ℝ) (deviation : game.BehaviorStrategy true) :
    game.BehaviorProfile :=
  fun who time history =>
    if who then deviation time history
    else weightedBlackwellFergusonStrategy parameter initial time history

/-- An arbitrary row strategy paired with the prescribed column coin. -/
def segmentRowDeviationProfile (parameter : SegmentParameter)
    (deviation : game.BehaviorStrategy false) : game.BehaviorProfile :=
  fun who time history =>
    if who then segmentColumnStrategy parameter time history
    else deviation time history

@[simp] theorem segmentProfile_false (parameter : SegmentParameter)
    (initial : ℝ) :
    segmentProfile parameter initial false =
      weightedBlackwellFergusonStrategy parameter initial := rfl

@[simp] theorem segmentProfile_true (parameter : SegmentParameter)
    (initial : ℝ) :
    segmentProfile parameter initial true = segmentColumnStrategy parameter :=
  rfl

@[simp] theorem segmentColumnDeviationProfile_false
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) :
    segmentColumnDeviationProfile parameter initial deviation false =
      weightedBlackwellFergusonStrategy parameter initial := rfl

@[simp] theorem segmentColumnDeviationProfile_true
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) :
    segmentColumnDeviationProfile parameter initial deviation true = deviation :=
  rfl

theorem stageActionDist_segmentColumnDeviationProfile
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) {time : ℕ}
    (history : game.Hist time) :
    game.stageActionDist
        (segmentColumnDeviationProfile parameter initial deviation) history =
      pmfPi (fun who => if who then deviation time history
        else weightedBlackwellFergusonStrategy parameter initial time history) :=
  rfl

@[simp] theorem segmentIncrementSum_zero (parameter : SegmentParameter)
    (history : game.Hist 0) :
    segmentIncrementSum parameter history = 0 := by
  simp [segmentIncrementSum]

theorem segmentIncrementSum_snoc (parameter : SegmentParameter)
    {time : ℕ} (history : game.Hist time) (action : game.JointAct)
    (next : State) :
    segmentIncrementSum parameter
        ((Fin.snoc history.1 (history.2, action), next) :
          game.Hist (time + 1)) =
      segmentIncrementSum parameter history +
        liveIndicator history.2 * segmentIncrement parameter (action true) := by
  unfold segmentIncrementSum
  rw [Fin.sum_univ_castSucc]
  simp

theorem segmentRawBalance_snoc (parameter : SegmentParameter)
    (initial : ℝ) {time : ℕ} (history : game.Hist time)
    (action : game.JointAct) (next : State) :
    segmentRawBalance parameter initial
        ((Fin.snoc history.1 (history.2, action), next) :
          game.Hist (time + 1)) =
      segmentRawBalance parameter initial history +
        liveIndicator history.2 * segmentIncrement parameter (action true) := by
  rw [segmentRawBalance, segmentIncrementSum_snoc]
  unfold segmentRawBalance
  ring

/-! ## The prescribed column coin and player-one deviation cap -/

/-- Harmonic state value for player one under the prescribed column coin. -/
def segmentPlayerOneValue (parameter : SegmentParameter) : State → ℝ
  | .live => parameter.value
  | .absTL => 0
  | .absTR => 1

/-- Harmonic state value for player two under the prescribed column coin. -/
def segmentPlayerTwoValue (parameter : SegmentParameter) : State → ℝ
  | .live => 2 * parameter.leftProbability
  | .absTL => 2
  | .absTR => 0

theorem expect_next_segmentPlayerOneValue
    (parameter : SegmentParameter) (state : State) (row : PMF Bool) :
    expect (pmfPi (fun who => if who then segmentColumnCoin parameter else row))
        (fun action => expect (game.transition state action)
          (segmentPlayerOneValue parameter)) =
      segmentPlayerOneValue parameter state := by
  rw [BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [expect_eq_sum, Fintype.sum_bool, BigMatch.pmfBool_false_toReal]
  cases state <;>
    simp [BigMatch.expect_coinPMF, segmentColumnCoin, nextState,
      segmentPlayerOneValue]
  linear_combination
    -(row true).toReal * parameter.value_add_leftProbability

theorem expect_next_segmentPlayerTwoValue
    (parameter : SegmentParameter) (state : State) (row : PMF Bool) :
    expect (pmfPi (fun who => if who then segmentColumnCoin parameter else row))
        (fun action => expect (game.transition state action)
          (segmentPlayerTwoValue parameter)) =
      segmentPlayerTwoValue parameter state := by
  rw [BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [expect_eq_sum, Fintype.sum_bool, BigMatch.pmfBool_false_toReal]
  cases state <;>
    simp [BigMatch.expect_coinPMF, segmentColumnCoin, nextState,
      segmentPlayerTwoValue] <;>
    ring

/-- Against the prescribed column coin, every row mix earns at most the
player-one harmonic value in the current stage. -/
theorem expect_stagePayoff_segmentColumnCoin_playerOne_le
    (parameter : SegmentParameter) (state : State) (row : PMF Bool) :
    expect (pmfPi (fun who => if who then segmentColumnCoin parameter else row))
        (fun action => game.stagePayoff state action false) ≤
      segmentPlayerOneValue parameter state := by
  rw [BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [expect_eq_sum, Fintype.sum_bool, BigMatch.pmfBool_false_toReal]
  cases state <;>
    simp [BigMatch.expect_coinPMF, segmentColumnCoin, payoff,
      segmentPlayerOneValue, pair]
  ring_nf
  have hrow1 : (row true).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  have hslope : 0 ≤ parameter.value - parameter.leftProbability :=
    sub_nonneg.mpr parameter.leftProbability_le_value
  have hmul :
      (row true).toReal *
          (parameter.value - parameter.leftProbability) ≤
        parameter.value - parameter.leftProbability := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrow1 hslope
  have hqsum := parameter.mul_value_add_leftProbability (row true).toReal
  calc
    (row true).toReal -
          (row true).toReal * parameter.leftProbability * 2 +
        parameter.leftProbability =
      parameter.leftProbability + (row true).toReal *
        (parameter.value - parameter.leftProbability) := by
          ring_nf at hqsum ⊢
          linarith
    _ ≤ parameter.leftProbability +
        (parameter.value - parameter.leftProbability) :=
      by simpa [add_comm] using
        add_le_add_left hmul parameter.leftProbability
    _ = parameter.value := by ring

theorem stageActionDist_segmentRowDeviationProfile
    (parameter : SegmentParameter) (deviation : game.BehaviorStrategy false)
    {time : ℕ} (history : game.Hist time) :
    game.stageActionDist (segmentRowDeviationProfile parameter deviation) history =
      pmfPi (fun who => if who then segmentColumnCoin parameter
        else deviation time history) :=
  rfl

theorem oneStep_segmentPlayerOneValue
    (parameter : SegmentParameter) (deviation : game.BehaviorStrategy false)
    {time : ℕ} (history : game.Hist time) :
    expect (game.stageActionDist
        (segmentRowDeviationProfile parameter deviation) history)
        (fun action => expect (game.transition history.2 action)
          (segmentPlayerOneValue parameter)) =
      segmentPlayerOneValue parameter history.2 := by
  rw [stageActionDist_segmentRowDeviationProfile]
  exact expect_next_segmentPlayerOneValue parameter history.2
    (deviation time history)

theorem oneStep_segmentPlayerTwoValue
    (parameter : SegmentParameter) (deviation : game.BehaviorStrategy false)
    {time : ℕ} (history : game.Hist time) :
    expect (game.stageActionDist
        (segmentRowDeviationProfile parameter deviation) history)
        (fun action => expect (game.transition history.2 action)
          (segmentPlayerTwoValue parameter)) =
      segmentPlayerTwoValue parameter history.2 := by
  rw [stageActionDist_segmentRowDeviationProfile]
  exact expect_next_segmentPlayerTwoValue parameter history.2
    (deviation time history)

theorem expectedStateValue_segmentPlayerOneValue
    (parameter : SegmentParameter) (deviation : game.BehaviorStrategy false)
    (time : ℕ) :
    game.expectedStateValue (segmentRowDeviationProfile parameter deviation)
        .live time (segmentPlayerOneValue parameter) = parameter.value := by
  induction time with
  | zero => simp [segmentPlayerOneValue]
  | succ time ih =>
      rw [game.expectedStateValue_succ]
      rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
        (fun history _ => oneStep_segmentPlayerOneValue parameter deviation history)]
      exact ih

theorem expectedStateValue_segmentPlayerTwoValue
    (parameter : SegmentParameter) (deviation : game.BehaviorStrategy false)
    (time : ℕ) :
    game.expectedStateValue (segmentRowDeviationProfile parameter deviation)
        .live time (segmentPlayerTwoValue parameter) =
      2 * parameter.leftProbability := by
  induction time with
  | zero => simp [segmentPlayerTwoValue]
  | succ time ih =>
      rw [game.expectedStateValue_succ]
      rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
        (fun history _ => oneStep_segmentPlayerTwoValue parameter deviation history)]
      exact ih

theorem stageEUAt_segmentRowDeviation_playerOne_le
    (parameter : SegmentParameter) (deviation : game.BehaviorStrategy false)
    {time : ℕ} (history : game.Hist time) :
    game.stageEUAt (segmentRowDeviationProfile parameter deviation) history false ≤
      segmentPlayerOneValue parameter history.2 := by
  unfold StochasticGame.stageEUAt
  rw [stageActionDist_segmentRowDeviationProfile]
  exact expect_stagePayoff_segmentColumnCoin_playerOne_le parameter history.2
    (deviation time history)

/-- Every row deviation is capped by `a` at each expected stage. -/
theorem expectedStagePayoff_segmentRowDeviation_playerOne_le
    (parameter : SegmentParameter) (deviation : game.BehaviorStrategy false)
    (time : ℕ) :
    game.expectedStagePayoff
        (segmentRowDeviationProfile parameter deviation) .live time false ≤
      parameter.value := by
  unfold StochasticGame.expectedStagePayoff
  calc
    expect
        (game.histDist (segmentRowDeviationProfile parameter deviation)
          .live time)
        (fun history => game.stageEUAt
          (segmentRowDeviationProfile parameter deviation) history false) ≤
      expect
        (game.histDist (segmentRowDeviationProfile parameter deviation)
          .live time)
        (fun history => segmentPlayerOneValue parameter history.2) := by
          apply expect_mono
          intro history
          exact stageEUAt_segmentRowDeviation_playerOne_le parameter deviation history
    _ = parameter.value :=
      expectedStateValue_segmentPlayerOneValue parameter deviation time

theorem finiteAveragePayoff_segmentRowDeviation_playerOne_le
    (parameter : SegmentParameter) (deviation : game.BehaviorStrategy false)
    {horizon : ℕ} (hhorizon : 0 < horizon) :
    game.finiteAveragePayoff .live horizon
        (segmentRowDeviationProfile parameter deviation) false ≤
      parameter.value := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hsum :
      ∑ time ∈ Finset.range horizon,
          game.expectedStagePayoff
            (segmentRowDeviationProfile parameter deviation) .live time false ≤
        ∑ _time ∈ Finset.range horizon, parameter.value :=
    Finset.sum_le_sum fun time _ =>
      expectedStagePayoff_segmentRowDeviation_playerOne_le parameter deviation time
  have hhorizonReal : (0 : ℝ) < horizon := by exact_mod_cast hhorizon
  calc
    (horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon,
          game.expectedStagePayoff
            (segmentRowDeviationProfile parameter deviation) .live time false ≤
      (horizon : ℝ)⁻¹ *
        ∑ _time ∈ Finset.range horizon, parameter.value :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hhorizonReal.le)
    _ = parameter.value := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

theorem update_segmentProfile_false
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy false) :
    Function.update (segmentProfile parameter initial) false deviation =
      segmentRowDeviationProfile parameter deviation := by
  funext who time history
  cases who <;> simp [segmentProfile, segmentRowDeviationProfile]

/-! ## Exact prescribed stage identities -/

theorem stageEUAt_segmentProfile_playerOne
    (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) :
    game.stageEUAt (segmentProfile parameter initial) history false =
      segmentPlayerOneValue parameter history.2 -
        parameter.rowSlope * liveIndicator history.2 *
          (1 - segmentStopProbability parameter initial history) := by
  unfold StochasticGame.stageEUAt
  change expect
      (pmfPi (fun who => if who then segmentColumnCoin parameter else
        weightedBlackwellFergusonStrategy parameter initial time history))
      (fun action => game.stagePayoff history.2 action false) = _
  rw [BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  unfold weightedBlackwellFergusonStrategy
  rw [BigMatch.expect_coinPMF]
  cases history.2
  · simp [BigMatch.expect_coinPMF, segmentColumnCoin, payoff,
      segmentPlayerOneValue, UniformSegmentParameter.rowSlope, pair]
    have hp := parameter.mul_value_add_leftProbability
      (segmentStopProbability parameter initial history)
    have hb := parameter.mul_value_add_leftProbability
      parameter.leftProbability
    ring_nf at hp hb ⊢
    linarith
  · simp [segmentColumnCoin, payoff,
      segmentPlayerOneValue, UniformSegmentParameter.rowSlope, pair]
  · simp [segmentColumnCoin, payoff,
      segmentPlayerOneValue, UniformSegmentParameter.rowSlope, pair]

theorem stageEUAt_segmentProfile_playerTwo
    (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) :
    game.stageEUAt (segmentProfile parameter initial) history true =
      segmentPlayerTwoValue parameter history.2 -
        parameter.columnSlack * liveIndicator history.2 *
          (1 - segmentStopProbability parameter initial history) := by
  unfold StochasticGame.stageEUAt
  change expect
      (pmfPi (fun who => if who then segmentColumnCoin parameter else
        weightedBlackwellFergusonStrategy parameter initial time history))
      (fun action => game.stagePayoff history.2 action true) = _
  rw [BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  unfold weightedBlackwellFergusonStrategy
  rw [BigMatch.expect_coinPMF]
  cases history.2
  · simp [BigMatch.expect_coinPMF, segmentColumnCoin, payoff,
      segmentPlayerTwoValue, UniformSegmentParameter.columnSlack, pair]
    have hsum := parameter.value_add_leftProbability
    have hp := parameter.mul_value_add_leftProbability
      (segmentStopProbability parameter initial history)
    have ha := parameter.mul_value_add_leftProbability parameter.value
    have hb := parameter.mul_value_add_leftProbability
      parameter.leftProbability
    ring_nf at hsum hp ha hb ⊢
    linarith
  · simp [segmentColumnCoin, payoff,
      segmentPlayerTwoValue, UniformSegmentParameter.columnSlack, pair]
    ring
  · simp [segmentColumnCoin, payoff,
      segmentPlayerTwoValue, UniformSegmentParameter.columnSlack, pair]

theorem expect_next_liveIndicator_segmentProfile
    (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) :
    expect (game.stageActionDist (segmentProfile parameter initial) history)
        (fun action => expect (game.transition history.2 action) liveIndicator) =
      liveIndicator history.2 *
        (1 - segmentStopProbability parameter initial history) := by
  change expect
      (pmfPi (fun who => if who then segmentColumnCoin parameter else
        weightedBlackwellFergusonStrategy parameter initial time history))
      (fun action => expect (game.transition history.2 action) liveIndicator) = _
  rw [BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  unfold weightedBlackwellFergusonStrategy
  rw [BigMatch.expect_coinPMF]
  cases history.2 <;>
    simp [BigMatch.expect_coinPMF, segmentColumnCoin, nextState,
      liveIndicator]

theorem liveProbability_segmentProfile_succ
    (parameter : SegmentParameter) (initial : ℝ) (time : ℕ) :
    liveProbability (segmentProfile parameter initial) (time + 1) =
      expect (game.histDist (segmentProfile parameter initial) .live time)
        (fun history => liveIndicator history.2 *
          (1 - segmentStopProbability parameter initial history)) := by
  rw [liveProbability, game.expectedStateValue_succ]
  exact congrArg
    (expect (game.histDist (segmentProfile parameter initial) .live time))
    (funext fun history =>
      expect_next_liveIndicator_segmentProfile parameter initial history)

theorem expectedStagePayoff_segmentProfile_playerOne
    (parameter : SegmentParameter) (initial : ℝ) (time : ℕ) :
    game.expectedStagePayoff (segmentProfile parameter initial) .live time false =
      parameter.value - parameter.rowSlope *
        liveProbability (segmentProfile parameter initial) (time + 1) := by
  unfold StochasticGame.expectedStagePayoff
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
    (fun history _ => stageEUAt_segmentProfile_playerOne parameter initial history),
    expect_sub]
  have hvalue := expectedStateValue_segmentPlayerOneValue parameter
    (weightedBlackwellFergusonStrategy parameter initial) time
  have hprofile :
      segmentRowDeviationProfile parameter
          (weightedBlackwellFergusonStrategy parameter initial) =
        segmentProfile parameter initial := by
    funext who stage history
    cases who <;> rfl
  rw [hprofile] at hvalue
  unfold StochasticGame.expectedStateValue at hvalue
  have hfactor :
      expect (game.histDist (segmentProfile parameter initial) .live time)
          (fun history => parameter.rowSlope * liveIndicator history.2 *
            (1 - segmentStopProbability parameter initial history)) =
        parameter.rowSlope *
          expect (game.histDist (segmentProfile parameter initial) .live time)
            (fun history => liveIndicator history.2 *
              (1 - segmentStopProbability parameter initial history)) := by
    rw [show
      (fun history : game.Hist time =>
        parameter.rowSlope * liveIndicator history.2 *
          (1 - segmentStopProbability parameter initial history)) =
      (fun history => parameter.rowSlope *
        (liveIndicator history.2 *
          (1 - segmentStopProbability parameter initial history))) by
            funext history
            ring,
      expect_const_mul]
  rw [hfactor, hvalue, ← liveProbability_segmentProfile_succ]

theorem expectedStagePayoff_segmentProfile_playerTwo
    (parameter : SegmentParameter) (initial : ℝ) (time : ℕ) :
    game.expectedStagePayoff (segmentProfile parameter initial) .live time true =
      2 * parameter.leftProbability - parameter.columnSlack *
        liveProbability (segmentProfile parameter initial) (time + 1) := by
  unfold StochasticGame.expectedStagePayoff
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
    (fun history _ => stageEUAt_segmentProfile_playerTwo parameter initial history),
    expect_sub]
  have hvalue := expectedStateValue_segmentPlayerTwoValue parameter
    (weightedBlackwellFergusonStrategy parameter initial) time
  have hprofile :
      segmentRowDeviationProfile parameter
          (weightedBlackwellFergusonStrategy parameter initial) =
        segmentProfile parameter initial := by
    funext who stage history
    cases who <;> rfl
  rw [hprofile] at hvalue
  unfold StochasticGame.expectedStateValue at hvalue
  have hfactor :
      expect (game.histDist (segmentProfile parameter initial) .live time)
          (fun history => parameter.columnSlack * liveIndicator history.2 *
            (1 - segmentStopProbability parameter initial history)) =
        parameter.columnSlack *
          expect (game.histDist (segmentProfile parameter initial) .live time)
            (fun history => liveIndicator history.2 *
              (1 - segmentStopProbability parameter initial history)) := by
    rw [show
      (fun history : game.Hist time =>
        parameter.columnSlack * liveIndicator history.2 *
          (1 - segmentStopProbability parameter initial history)) =
      (fun history => parameter.columnSlack *
        (liveIndicator history.2 *
          (1 - segmentStopProbability parameter initial history))) by
            funext history
            ring,
      expect_const_mul]
  rw [hfactor, hvalue, ← liveProbability_segmentProfile_succ]

/-! ## Reachable account bounds -/

/-- Along a reachable live history, the raw account is strictly positive.
When the clamped denominator reaches its floor, the row player stops surely,
so no live successor remains in support. -/
theorem segmentRawBalance_pos_of_live_of_mem_support
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial)
    (deviation : game.BehaviorStrategy true) :
    ∀ (time : ℕ) (history : game.Hist time),
      history ∈
          (game.histDist
            (segmentColumnDeviationProfile parameter initial deviation)
            .live time).support →
        history.2 = .live →
          0 < segmentRawBalance parameter initial history := by
  intro time
  induction time with
  | zero =>
      intro history _ _
      simp [segmentRawBalance]
      exact parameter.leftProbability_pos.trans_le hinitial
  | succ time ih =>
      intro extended hextended hlive
      rw [game.mem_support_histDist_succ] at hextended
      obtain ⟨history, hhistory, action, haction, next, hnext, rfl⟩ := hextended
      have hnextEq : next = nextState history.2 action := by
        rw [transition_eq, PMF.support_pure, Set.mem_singleton_iff] at hnext
        exact hnext
      have hnextLive : nextState history.2 action = .live := hnextEq ▸ hlive
      have hstate : history.2 = .live := by
        cases h : history.2 <;> simp [h, nextState] at hnextLive ⊢
      have hrow : action false = false := by
        rw [hstate] at hnextLive
        cases h : action false
        · rfl
        · cases hc : action true <;> simp [h, hc, nextState] at hnextLive
      have hrawPos := ih history hhistory hstate
      rw [PMF.mem_support_iff,
        stageActionDist_segmentColumnDeviationProfile] at haction
      rw [pmfPi_apply] at haction
      have hrowMass := Finset.prod_ne_zero_iff.mp haction false
        (Finset.mem_univ false)
      simp only [Bool.false_eq_true, if_false, hrow] at hrowMass
      unfold weightedBlackwellFergusonStrategy at hrowMass
      rw [BigMatch.coinPMF_apply_false] at hrowMass
      have hstopLt :
          segmentStopProbability parameter initial history < 1 := by
        by_contra hnot
        push Not at hnot
        have heq : segmentStopProbability parameter initial history = 1 :=
          le_antisymm
            (segmentStopProbability_le_one parameter initial history) hnot
        rw [heq] at hrowMass
        simp at hrowMass
      have hrawFloor :
          parameter.leftProbability <
            segmentRawBalance parameter initial history := by
        by_contra hnot
        push Not at hnot
        have heq := segmentStopProbability_eq_one_of_raw_le
          parameter initial history hnot
        linarith
      rw [segmentRawBalance_snoc, hstate, liveIndicator_live]
      have hincrement := segmentIncrement_ge_neg_leftProbability
        parameter (action true)
      linarith

/-- The accumulated centered increment is bounded below uniformly over every
reachable history, including histories that have already absorbed. -/
theorem neg_initial_add_leftProbability_le_segmentIncrementSum
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial)
    (deviation : game.BehaviorStrategy true) :
    ∀ (time : ℕ) (history : game.Hist time),
      history ∈
          (game.histDist
            (segmentColumnDeviationProfile parameter initial deviation)
            .live time).support →
        -(initial + parameter.leftProbability) <
          segmentIncrementSum parameter history := by
  intro time
  induction time with
  | zero =>
      intro history _
      simp [segmentIncrementSum]
      have hpositive : 0 < initial + parameter.leftProbability := by
        nlinarith [parameter.leftProbability_pos]
      linarith
  | succ time ih =>
      intro extended hextended
      rw [game.mem_support_histDist_succ] at hextended
      obtain ⟨history, hhistory, action, _haction, next, _hnext, rfl⟩ :=
        hextended
      rw [segmentIncrementSum_snoc]
      by_cases hlive : history.2 = .live
      · rw [hlive, liveIndicator_live, one_mul]
        have hraw := segmentRawBalance_pos_of_live_of_mem_support
          parameter hinitial deviation time history hhistory hlive
        have hincrement := segmentIncrement_ge_neg_leftProbability
          parameter (action true)
        unfold segmentRawBalance at hraw
        linarith
      · have hindicator : liveIndicator history.2 = 0 := by
          cases hstate : history.2 <;> simp_all [liveIndicator]
        rw [hindicator, zero_mul, add_zero]
        exact ih history hhistory

/-! ## Reciprocal potential against arbitrary column deviations -/

/-- History potential used to control player two's unilateral deviations. -/
def segmentRiskPotential (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) : ℝ :=
  match history.2 with
  | .live => potential parameter.value parameter.leftProbability
      (segmentDenom parameter initial history)
  | .absTL => -parameter.value
  | .absTR => parameter.leftProbability

@[simp] theorem segmentRiskPotential_live
    (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} {history : game.Hist time} (hlive : history.2 = .live) :
    segmentRiskPotential parameter initial history =
      potential parameter.value parameter.leftProbability
        (segmentDenom parameter initial history) := by
  simp [segmentRiskPotential, hlive]

@[simp] theorem segmentRiskPotential_absTL
    (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} {history : game.Hist time} (hstate : history.2 = .absTL) :
    segmentRiskPotential parameter initial history = -parameter.value := by
  simp [segmentRiskPotential, hstate]

@[simp] theorem segmentRiskPotential_absTR
    (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} {history : game.Hist time} (hstate : history.2 = .absTR) :
    segmentRiskPotential parameter initial history =
      parameter.leftProbability := by
  simp [segmentRiskPotential, hstate]

theorem potential_at_leftProbability (parameter : SegmentParameter) :
    potential parameter.value parameter.leftProbability
        parameter.leftProbability = -parameter.value := by
  unfold potential
  field_simp [parameter.leftProbability_pos.ne']

/-- For either pure column action, averaging the next risk potential over
player one's stopping coin dominates the current risk potential. -/
theorem segmentRiskPotential_le_expect_row_step
    (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) (column : Bool)
    (hlive : history.2 = .live) :
    segmentRiskPotential parameter initial history ≤
      expect (weightedBlackwellFergusonStrategy parameter initial time history)
        (fun row =>
          let action : game.JointAct := fun who => if who then column else row
          segmentRiskPotential parameter initial
            ((Fin.snoc history.1 (history.2, action),
              nextState history.2 action) : game.Hist (time + 1))) := by
  rw [segmentRiskPotential_live parameter initial hlive]
  unfold weightedBlackwellFergusonStrategy
  rw [BigMatch.expect_coinPMF]
  set raw := segmentRawBalance parameter initial history with hraw
  set b := parameter.leftProbability with hb
  set a := parameter.value with ha
  set D := segmentDenom parameter initial history with hD
  set p := segmentStopProbability parameter initial history with hp
  have hbpos : 0 < b := parameter.leftProbability_pos
  have hapb : a + b = 1 := parameter.value_add_leftProbability
  have hab : b ≤ a := parameter.leftProbability_le_value
  by_cases hfloor : raw ≤ b
  · have hDeq : D = b := by
      rw [hD, segmentDenom, max_eq_right]
      simpa [hraw, hb]
    have hpeq : p = 1 := by
      rw [hp]
      exact segmentStopProbability_eq_one_of_raw_le parameter initial history
        (by simpa [hraw, hb])
    rw [hDeq, potential_at_leftProbability, hpeq]
    cases column
    · simp [hlive, nextState, segmentRiskPotential]
      linarith [parameter.value_pos, parameter.leftProbability_pos]
    · simp [hlive, nextState, segmentRiskPotential]
  · have hrawGt : b < raw := lt_of_not_ge hfloor
    have hDeq : D = raw := by
      rw [hD, segmentDenom, max_eq_left]
      exact hrawGt.le
    have hdenom : segmentDenom parameter initial history = raw :=
      hD.symm.trans hDeq
    have hpEq : p = stopProbability a b raw := by
      rw [hp, segmentStopProbability, hdenom, ← ha, ← hb]
    have hrawPos : 0 < raw := hbpos.trans hrawGt
    have hsecondPos : 0 < raw + (a - b) := by linarith
    cases column
    · have hnextTop :
          nextState history.2 (fun who => if who then false else true) =
            .absTR := by simp [hlive, nextState]
      have hnextBottom :
          nextState history.2 (fun who => if who then false else false) =
            .live := by simp [hlive, nextState]
      dsimp only
      rw [hnextTop, hnextBottom]
      simp only [segmentRiskPotential]
      rw [show
        segmentDenom parameter initial
            ((Fin.snoc history.1
                (history.2, fun who => if who then false else false),
              State.live) : game.Hist (time + 1)) =
          max (raw - b) b by
            rw [segmentDenom, segmentRawBalance_snoc, hlive,
              liveIndicator_live, one_mul]
            simp only [segmentIncrement]
            simp [hraw, hb]
            ring]
      rw [hDeq]
      have hsubPos : 0 < raw - b := sub_pos.mpr hrawGt
      have hidentity := potential_sub_id
        (a := a) (b := b) (D := raw) parameter.value_pos.ne'
        hbpos.ne' hrawPos.ne' hsubPos.ne' hsecondPos.ne'
      by_cases hclamp : b ≤ raw - b
      · rw [max_eq_left hclamp]
        simpa [hpEq, a, ha, b, hb] using hidentity.symm.le
      · rw [max_eq_right (le_of_not_ge hclamp)]
        have hmono :
            potential a b (raw - b) ≤ potential a b b :=
          potential_strictMono_on_pos parameter.value_pos hbpos hsubPos
            (le_of_not_ge hclamp)
        have hpnonneg : 0 ≤ 1 - p := sub_nonneg.mpr
          (by simpa [p, hp] using
            segmentStopProbability_le_one parameter initial history)
        have hweighted := mul_le_mul_of_nonneg_left hmono hpnonneg
        have hfloorPotential : potential a b b = -a := by
          simpa [a, ha, b, hb] using potential_at_leftProbability parameter
        rw [hfloorPotential]
        have hidentity' :
            p * b + (1 - p) * potential a b (raw - b) =
              potential a b raw := by
          simpa [hpEq] using hidentity
        rw [← hb, ← hfloorPotential]
        linarith
    · have hnextTop :
          nextState history.2 (fun who => if who then true else true) =
            .absTL := by simp [hlive, nextState]
      have hnextBottom :
          nextState history.2 (fun who => if who then true else false) =
            .live := by simp [hlive, nextState]
      dsimp only
      rw [hnextTop, hnextBottom]
      simp only [segmentRiskPotential]
      have hrawNext :
          segmentRawBalance parameter initial
              ((Fin.snoc history.1
                  (history.2, fun who => if who then true else false),
                State.live) : game.Hist (time + 1)) = raw + a := by
        rw [segmentRawBalance_snoc, hlive, liveIndicator_live, one_mul]
        simp [segmentIncrement, hraw, ha]
      rw [show
        segmentDenom parameter initial
            ((Fin.snoc history.1
                (history.2, fun who => if who then true else false),
              State.live) : game.Hist (time + 1)) = raw + a by
            rw [segmentDenom, hrawNext]
            rw [max_eq_left]
            linarith]
      rw [hDeq]
      have haddPos : 0 < raw + a := add_pos hrawPos parameter.value_pos
      have hidentity := potential_add_id
        (a := a) (b := b) (D := raw) parameter.value_pos.ne'
        hbpos.ne' hrawPos.ne' haddPos.ne' hsecondPos.ne'
      simpa [hpEq, a, ha, b, hb] using hidentity.symm.le

/-- The expected risk potential is a submartingale against every behavioral
column deviation. -/
theorem segmentRiskPotential_le_expect_step
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) {time : ℕ}
    (history : game.Hist time) :
    segmentRiskPotential parameter initial history ≤
      expect (game.stageActionDist
        (segmentColumnDeviationProfile parameter initial deviation) history)
        (fun action => segmentRiskPotential parameter initial
          ((Fin.snoc history.1 (history.2, action),
            nextState history.2 action) : game.Hist (time + 1))) := by
  cases hstate : history.2 with
  | live =>
      rw [stageActionDist_segmentColumnDeviationProfile,
        BigMatch.expect_pmfPi_bool]
      simp only [Bool.false_eq_true, if_false, if_true]
      have hpoint : ∀ column : Bool,
          segmentRiskPotential parameter initial history ≤
            expect
              (weightedBlackwellFergusonStrategy parameter initial time history)
              (fun row =>
                let action : game.JointAct :=
                  fun who => if who then column else row
                segmentRiskPotential parameter initial
                  ((Fin.snoc history.1 (history.2, action),
                    nextState history.2 action) : game.Hist (time + 1))) :=
        fun column => segmentRiskPotential_le_expect_row_step
          parameter initial history column hstate
      have hpoint' : ∀ column : Bool,
          segmentRiskPotential parameter initial history ≤
            expect
              (weightedBlackwellFergusonStrategy parameter initial time history)
              (fun row =>
                let action : game.JointAct :=
                  fun who => if who then column else row
                segmentRiskPotential parameter initial
                  ((Fin.snoc history.1 (.live, action),
                    nextState .live action) : game.Hist (time + 1))) := by
        intro column
        simpa [hstate] using hpoint column
      have hcomm :
          expect
              (weightedBlackwellFergusonStrategy parameter initial time history)
              (fun row => expect (deviation time history) fun column =>
                segmentRiskPotential parameter initial
                  ((Fin.snoc history.1
                      (.live, fun who => if who then column else row),
                    nextState .live
                      (fun who => if who then column else row)) :
                    game.Hist (time + 1))) =
            expect (deviation time history) (fun column =>
              expect
                (weightedBlackwellFergusonStrategy parameter initial time history)
                (fun row => segmentRiskPotential parameter initial
                  ((Fin.snoc history.1
                      (.live, fun who => if who then column else row),
                    nextState .live
                      (fun who => if who then column else row)) :
                    game.Hist (time + 1)))) := by
        simp only [expect_eq_sum, Fintype.sum_bool]
        ring
      rw [hcomm]
      rw [← expect_const (deviation time history)
        (segmentRiskPotential parameter initial history)]
      exact expect_mono _ _ _ hpoint'
  | absTL =>
      rw [segmentRiskPotential_absTL parameter initial hstate]
      have hconstant : ∀ action,
          segmentRiskPotential parameter initial
            ((Fin.snoc history.1 (.absTL, action),
              nextState .absTL action) : game.Hist (time + 1)) =
            -parameter.value := by
        intro action
        simp [nextState, segmentRiskPotential]
      rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
        (fun action _ => hconstant action), expect_const]
  | absTR =>
      rw [segmentRiskPotential_absTR parameter initial hstate]
      have hconstant : ∀ action,
          segmentRiskPotential parameter initial
            ((Fin.snoc history.1 (.absTR, action),
              nextState .absTR action) : game.Hist (time + 1)) =
            parameter.leftProbability := by
        intro action
        simp [nextState, segmentRiskPotential]
      rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
        (fun action _ => hconstant action), expect_const]

/-- Expected risk potential at one decision epoch. -/
def segmentRiskExpectation (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) : ℝ :=
  expect
    (game.histDist
      (segmentColumnDeviationProfile parameter initial deviation) .live time)
    (segmentRiskPotential parameter initial)

theorem segmentRiskExpectation_le_succ
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) :
    segmentRiskExpectation parameter initial deviation time ≤
      segmentRiskExpectation parameter initial deviation (time + 1) := by
  unfold segmentRiskExpectation
  rw [game.histDist_succ, expect_bind]
  have hcollapse : ∀ history : game.Hist time,
      expect
          ((game.stageActionDist
            (segmentColumnDeviationProfile parameter initial deviation)
            history).bind fun action =>
              (game.transition history.2 action).bind fun next =>
                PMF.pure
                  ((Fin.snoc history.1 (history.2, action), next) :
                    game.Hist (time + 1)))
          (segmentRiskPotential parameter initial) =
        expect
          (game.stageActionDist
            (segmentColumnDeviationProfile parameter initial deviation)
            history)
          (fun action => segmentRiskPotential parameter initial
            ((Fin.snoc history.1 (history.2, action),
              nextState history.2 action) : game.Hist (time + 1))) := by
    intro history
    rw [expect_bind]
    apply congrArg
      (expect (game.stageActionDist
        (segmentColumnDeviationProfile parameter initial deviation) history))
    funext action
    rw [expect_bind, transition_eq, expect_pure, expect_pure]
  simp_rw [hcollapse]
  exact expect_mono _ _ _ fun history =>
    segmentRiskPotential_le_expect_step parameter initial deviation history

theorem segmentRiskExpectation_zero
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial)
    (deviation : game.BehaviorStrategy true) :
    segmentRiskExpectation parameter initial deviation 0 =
      potential parameter.value parameter.leftProbability initial := by
  unfold segmentRiskExpectation
  rw [game.histDist_zero, expect_pure]
  rw [segmentRiskPotential_live parameter initial rfl]
  simp [segmentDenom, segmentRawBalance, segmentIncrementSum,
    max_eq_left hinitial]

theorem segmentRiskExpectation_initial_le
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial)
    (deviation : game.BehaviorStrategy true) (time : ℕ) :
    potential parameter.value parameter.leftProbability initial ≤
      segmentRiskExpectation parameter initial deviation time := by
  rw [← segmentRiskExpectation_zero parameter hinitial deviation]
  exact (monotone_nat_of_le_succ fun stage =>
    segmentRiskExpectation_le_succ parameter initial deviation stage)
      (Nat.zero_le time)

/-! ## Player-two deviation ledger -/

/-- Exact current payoff of player two under an arbitrary column deviation. -/
theorem stageEUAt_segmentColumnDeviation_playerTwo
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) {time : ℕ}
    (history : game.Hist time) :
    game.stageEUAt
        (segmentColumnDeviationProfile parameter initial deviation) history true =
      match history.2 with
      | .live =>
          let p := segmentStopProbability parameter initial history
          let q := (deviation time history true).toReal
          2 * p * q + (1 - p) * (1 - q)
      | .absTL => 2
      | .absTR => 0 := by
  unfold StochasticGame.stageEUAt
  rw [stageActionDist_segmentColumnDeviationProfile,
    BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  unfold weightedBlackwellFergusonStrategy
  rw [BigMatch.expect_coinPMF]
  simp_rw [expect_eq_sum, Fintype.sum_bool,
    BigMatch.pmfBool_false_toReal]
  cases history.2 <;> simp [payoff, pair] <;> ring

/-- Pointwise ledger controlling a column deviation by the reciprocal risk
potential, the centered column increment, and stopping mass. -/
theorem stageEUAt_segmentColumnDeviation_playerTwo_le
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) {time : ℕ}
    (history : game.Hist time) :
    game.stageEUAt
        (segmentColumnDeviationProfile parameter initial deviation) history true ≤
      2 * parameter.leftProbability -
        2 * segmentRiskPotential parameter initial history -
        liveIndicator history.2 *
          ((deviation time history true).toReal -
            parameter.leftProbability) +
        3 * parameter.value * liveIndicator history.2 *
          segmentStopProbability parameter initial history := by
  rw [stageEUAt_segmentColumnDeviation_playerTwo]
  cases hstate : history.2 with
  | live =>
      simp only [liveIndicator_live, one_mul]
      rw [segmentRiskPotential_live parameter initial hstate]
      have hledger := stageReward_le_ledger
        (a := parameter.value) (b := parameter.leftProbability)
        (D := segmentDenom parameter initial history)
        (p := segmentStopProbability parameter initial history)
        (q := (deviation time history true).toReal)
        (μ := (deviation time history true).toReal -
          parameter.leftProbability)
        parameter.value_add_leftProbability rfl
        parameter.columnSlack_nonneg
        (segmentStopProbability_nonneg parameter initial history)
        (segmentStopProbability_le_one parameter initial history)
        (ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _))
        (potential_nonpos parameter.value_pos.le
          parameter.leftProbability_nonneg
          (segmentDenom_pos parameter initial history).le)
      simpa [mul_assoc] using hledger
  | absTL =>
      rw [segmentRiskPotential_absTL parameter initial hstate]
      simp [liveIndicator]
      linarith [parameter.value_add_leftProbability]
  | absTR =>
      rw [segmentRiskPotential_absTR parameter initial hstate]
      simp [liveIndicator]

/-- Expected centered column increment carried by live mass. -/
def segmentLiveMeanExpectation (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) : ℝ :=
  expect
    (game.histDist
      (segmentColumnDeviationProfile parameter initial deviation) .live time)
    (fun history => liveIndicator history.2 *
      ((deviation time history true).toReal - parameter.leftProbability))

/-- Expected stopping mass at one stage. -/
def segmentLiveStopExpectation (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) : ℝ :=
  expect
    (game.histDist
      (segmentColumnDeviationProfile parameter initial deviation) .live time)
    (fun history => liveIndicator history.2 *
      segmentStopProbability parameter initial history)

theorem expectedStagePayoff_segmentColumnDeviation_playerTwo_le
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) :
    game.expectedStagePayoff
        (segmentColumnDeviationProfile parameter initial deviation)
        .live time true ≤
      2 * parameter.leftProbability -
        2 * segmentRiskExpectation parameter initial deviation time -
        segmentLiveMeanExpectation parameter initial deviation time +
        3 * parameter.value *
          segmentLiveStopExpectation parameter initial deviation time := by
  unfold StochasticGame.expectedStagePayoff
  calc
    expect
        (game.histDist
          (segmentColumnDeviationProfile parameter initial deviation)
          .live time)
        (fun history => game.stageEUAt
          (segmentColumnDeviationProfile parameter initial deviation)
          history true) ≤
      expect
        (game.histDist
          (segmentColumnDeviationProfile parameter initial deviation)
          .live time)
        (fun history =>
          2 * parameter.leftProbability -
            2 * segmentRiskPotential parameter initial history -
            liveIndicator history.2 *
              ((deviation time history true).toReal -
                parameter.leftProbability) +
            3 * parameter.value * liveIndicator history.2 *
              segmentStopProbability parameter initial history) := by
                apply expect_mono
                intro history
                exact stageEUAt_segmentColumnDeviation_playerTwo_le
                  parameter initial deviation history
    _ = 2 * parameter.leftProbability -
        2 * segmentRiskExpectation parameter initial deviation time -
        segmentLiveMeanExpectation parameter initial deviation time +
        3 * parameter.value *
          segmentLiveStopExpectation parameter initial deviation time := by
      unfold segmentRiskExpectation segmentLiveMeanExpectation
        segmentLiveStopExpectation
      rw [show
        (fun history =>
          2 * parameter.leftProbability -
            2 * segmentRiskPotential parameter initial history -
            liveIndicator history.2 *
              ((deviation time history true).toReal -
                parameter.leftProbability) +
            3 * parameter.value * liveIndicator history.2 *
              segmentStopProbability parameter initial history) =
        (fun history =>
          2 * parameter.leftProbability -
            2 * segmentRiskPotential parameter initial history -
            liveIndicator history.2 *
              ((deviation time history true).toReal -
                parameter.leftProbability) +
            (3 * parameter.value) *
              (liveIndicator history.2 *
                segmentStopProbability parameter initial history)) by
          funext history
          ring]
      simp_rw [expect_add, expect_sub, expect_const, expect_const_mul]

/-- Marginalizing the joint action over player one's independent stopping
coin recovers the column deviation's expected centered increment. -/
theorem expect_stageAction_segmentIncrement
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) {time : ℕ}
    (history : game.Hist time) :
    expect
        (game.stageActionDist
          (segmentColumnDeviationProfile parameter initial deviation) history)
        (fun action => segmentIncrement parameter (action true)) =
      (deviation time history true).toReal -
        parameter.leftProbability := by
  rw [stageActionDist_segmentColumnDeviationProfile,
    BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true, expect_const]
  rw [expect_eq_sum, Fintype.sum_bool, BigMatch.pmfBool_false_toReal]
  simp [segmentIncrement]
  have hq := parameter.mul_value_add_leftProbability
    (deviation time history true).toReal
  ring_nf at hq ⊢
  linarith

/-- Expected accumulated centered increment. -/
def segmentIncrementExpectation (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) : ℝ :=
  expect
    (game.histDist
      (segmentColumnDeviationProfile parameter initial deviation) .live time)
    (segmentIncrementSum parameter)

theorem segmentIncrementExpectation_succ
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) :
    segmentIncrementExpectation parameter initial deviation (time + 1) =
      segmentIncrementExpectation parameter initial deviation time +
        segmentLiveMeanExpectation parameter initial deviation time := by
  unfold segmentIncrementExpectation segmentLiveMeanExpectation
  rw [game.histDist_succ, expect_bind]
  have hstep : ∀ history : game.Hist time,
      expect
          ((game.stageActionDist
            (segmentColumnDeviationProfile parameter initial deviation)
            history).bind fun action =>
              (game.transition history.2 action).bind fun next =>
                PMF.pure
                  ((Fin.snoc history.1 (history.2, action), next) :
                    game.Hist (time + 1)))
          (segmentIncrementSum parameter) =
        segmentIncrementSum parameter history +
          liveIndicator history.2 *
            ((deviation time history true).toReal -
              parameter.leftProbability) := by
    intro history
    rw [expect_bind]
    have hinner : ∀ action : game.JointAct,
        expect
            ((game.transition history.2 action).bind fun next =>
              PMF.pure
                ((Fin.snoc history.1 (history.2, action), next) :
                  game.Hist (time + 1)))
            (segmentIncrementSum parameter) =
          segmentIncrementSum parameter history +
            liveIndicator history.2 *
              segmentIncrement parameter (action true) := by
      intro action
      rw [expect_bind, transition_eq, expect_pure, expect_pure,
        segmentIncrementSum_snoc]
    simp_rw [hinner]
    rw [expect_add, expect_const, expect_const_mul,
      expect_stageAction_segmentIncrement parameter initial deviation history]
  simp_rw [hstep, expect_add]

theorem segmentIncrementExpectation_eq_sum_liveMean
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) :
    ∀ time : ℕ,
      segmentIncrementExpectation parameter initial deviation time =
        ∑ stage ∈ Finset.range time,
          segmentLiveMeanExpectation parameter initial deviation stage := by
  intro time
  induction time with
  | zero => simp [segmentIncrementExpectation, segmentIncrementSum]
  | succ time ih =>
      rw [segmentIncrementExpectation_succ, ih, Finset.sum_range_succ]

theorem neg_initial_add_leftProbability_le_sum_liveMean
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial)
    (deviation : game.BehaviorStrategy true) (time : ℕ) :
    -(initial + parameter.leftProbability) ≤
      ∑ stage ∈ Finset.range time,
        segmentLiveMeanExpectation parameter initial deviation stage := by
  rw [← segmentIncrementExpectation_eq_sum_liveMean]
  unfold segmentIncrementExpectation
  rw [← expect_const
    (game.histDist
      (segmentColumnDeviationProfile parameter initial deviation) .live time)
    (-(initial + parameter.leftProbability))]
  exact expect_mono_on_support _ _ _ fun history hhistory =>
    (neg_initial_add_leftProbability_le_segmentIncrementSum
      parameter hinitial deviation time history hhistory).le

theorem expect_next_liveIndicator_segmentColumnDeviation
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) {time : ℕ}
    (history : game.Hist time) :
    expect
        (game.stageActionDist
          (segmentColumnDeviationProfile parameter initial deviation) history)
        (fun action => expect (game.transition history.2 action) liveIndicator) =
      liveIndicator history.2 *
        (1 - segmentStopProbability parameter initial history) := by
  rw [stageActionDist_segmentColumnDeviationProfile,
    BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  unfold weightedBlackwellFergusonStrategy
  rw [BigMatch.expect_coinPMF]
  simp_rw [expect_transition]
  cases history.2 <;>
    simp [expect_eq_sum, BigMatch.pmfBool_false_toReal,
      nextState, liveIndicator]

theorem liveProbability_segmentColumnDeviation_succ
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) :
    liveProbability
        (segmentColumnDeviationProfile parameter initial deviation) (time + 1) =
      liveProbability
          (segmentColumnDeviationProfile parameter initial deviation) time -
        segmentLiveStopExpectation parameter initial deviation time := by
  rw [liveProbability, game.expectedStateValue_succ]
  unfold liveProbability StochasticGame.expectedStateValue
    segmentLiveStopExpectation
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
    (fun history _ =>
      expect_next_liveIndicator_segmentColumnDeviation
        parameter initial deviation history)]
  rw [show
      (fun history : game.Hist time => liveIndicator history.2 *
        (1 - segmentStopProbability parameter initial history)) =
      (fun history => liveIndicator history.2 -
        liveIndicator history.2 *
          segmentStopProbability parameter initial history) by
            funext history
            ring,
    expect_sub]

theorem sum_segmentLiveStopExpectation_eq
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) :
    ∑ stage ∈ Finset.range time,
        segmentLiveStopExpectation parameter initial deviation stage =
      1 - liveProbability
        (segmentColumnDeviationProfile parameter initial deviation) time := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [Finset.sum_range_succ, ih,
        liveProbability_segmentColumnDeviation_succ]
      ring

theorem sum_segmentLiveStopExpectation_le_one
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) (time : ℕ) :
    ∑ stage ∈ Finset.range time,
        segmentLiveStopExpectation parameter initial deviation stage ≤ 1 := by
  rw [sum_segmentLiveStopExpectation_eq]
  exact sub_le_self _ (liveProbability_nonneg _ _)

/-- Quantitative finite-horizon cap on every behavioral column deviation. -/
theorem finiteAveragePayoff_segmentColumnDeviation_playerTwo_le
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial)
    (deviation : game.BehaviorStrategy true) {horizon : ℕ}
    (hhorizon : 0 < horizon) :
    game.finiteAveragePayoff .live horizon
        (segmentColumnDeviationProfile parameter initial deviation) true ≤
      2 * parameter.leftProbability +
        2 * parameter.value * parameter.leftProbability / initial +
        (initial + parameter.leftProbability + 3 * parameter.value) /
          horizon := by
  have hinitialPos : 0 < initial :=
    parameter.leftProbability_pos.trans_le hinitial
  have hstage : ∀ stage : ℕ,
      game.expectedStagePayoff
          (segmentColumnDeviationProfile parameter initial deviation)
          .live stage true ≤
        2 * parameter.leftProbability +
          2 * parameter.value * parameter.leftProbability / initial -
          segmentLiveMeanExpectation parameter initial deviation stage +
          3 * parameter.value *
            segmentLiveStopExpectation parameter initial deviation stage := by
    intro stage
    have hrisk := segmentRiskExpectation_initial_le
      parameter hinitial deviation stage
    have hledger := expectedStagePayoff_segmentColumnDeviation_playerTwo_le
      parameter initial deviation stage
    unfold potential at hrisk
    have hscaled := mul_le_mul_of_nonneg_left hrisk (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ ≤ 2 * parameter.leftProbability -
          2 * segmentRiskExpectation parameter initial deviation stage -
          segmentLiveMeanExpectation parameter initial deviation stage +
          3 * parameter.value *
            segmentLiveStopExpectation parameter initial deviation stage :=
        hledger
      _ ≤ _ := by
        ring_nf at hscaled ⊢
        linarith
  have hsum := Finset.sum_le_sum fun stage (_hstage : stage ∈
      Finset.range horizon) => hstage stage
  have hmean := neg_initial_add_leftProbability_le_sum_liveMean
    parameter hinitial deviation horizon
  have hstop := sum_segmentLiveStopExpectation_le_one
    parameter initial deviation horizon
  have hstopWeighted :
      3 * parameter.value *
          (∑ stage ∈ Finset.range horizon,
            segmentLiveStopExpectation parameter initial deviation stage) ≤
        3 * parameter.value := by
    have hcoefficient : (0 : ℝ) ≤ 3 * parameter.value :=
      mul_nonneg (by norm_num) parameter.value_pos.le
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hstop hcoefficient)
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hsumRearranged :
      ∑ stage ∈ Finset.range horizon,
          game.expectedStagePayoff
            (segmentColumnDeviationProfile parameter initial deviation)
            .live stage true ≤
        (horizon : ℝ) *
            (2 * parameter.leftProbability +
              2 * parameter.value * parameter.leftProbability / initial) +
          (initial + parameter.leftProbability) +
          3 * parameter.value := by
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    rw [Finset.mul_sum] at hstopWeighted
    ring_nf at hsum hstopWeighted ⊢
    nlinarith
  have hhorizonReal : (0 : ℝ) < horizon := by exact_mod_cast hhorizon
  calc
    (horizon : ℝ)⁻¹ *
        ∑ stage ∈ Finset.range horizon,
          game.expectedStagePayoff
            (segmentColumnDeviationProfile parameter initial deviation)
            .live stage true ≤
      (horizon : ℝ)⁻¹ *
        ((horizon : ℝ) *
            (2 * parameter.leftProbability +
              2 * parameter.value * parameter.leftProbability / initial) +
          (initial + parameter.leftProbability) +
          3 * parameter.value) :=
      mul_le_mul_of_nonneg_left hsumRearranged
        (inv_nonneg.mpr hhorizonReal.le)
    _ = 2 * parameter.leftProbability +
        2 * parameter.value * parameter.leftProbability / initial +
        (initial + parameter.leftProbability + 3 * parameter.value) /
          horizon := by
      field_simp
      ring

theorem update_segmentProfile_true
    (parameter : SegmentParameter) (initial : ℝ)
    (deviation : game.BehaviorStrategy true) :
    Function.update (segmentProfile parameter initial) true deviation =
      segmentColumnDeviationProfile parameter initial deviation := by
  funext who time history
  cases who <;> simp [segmentProfile, segmentColumnDeviationProfile]

/-! ## Finite-law energy and absorption -/

/-- Live quadratic energy of the raw account. -/
def segmentLiveEnergy (parameter : SegmentParameter) (initial : ℝ)
    {time : ℕ} (history : game.Hist time) : ℝ :=
  liveIndicator history.2 *
    energy parameter.value parameter.leftProbability
      (segmentRawBalance parameter initial history)

/-- Expected live raw-account energy. -/
def segmentLiveEnergyExpectation (parameter : SegmentParameter) (initial : ℝ)
    (time : ℕ) : ℝ :=
  expect (game.histDist (segmentProfile parameter initial) .live time)
    (segmentLiveEnergy parameter initial)

theorem segmentColumnDeviationProfile_columnStrategy
    (parameter : SegmentParameter) (initial : ℝ) :
    segmentColumnDeviationProfile parameter initial
        (segmentColumnStrategy parameter) =
      segmentProfile parameter initial := by
  funext who time history
  cases who <;> rfl

/-- One-step expected live energy does not exceed the current live energy on
every reachable history. -/
theorem expect_next_segmentLiveEnergy_le_of_mem_support
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial)
    {time : ℕ} (history : game.Hist time)
    (hhistory : history ∈
      (game.histDist (segmentProfile parameter initial) .live time).support) :
    expect (game.stageActionDist (segmentProfile parameter initial) history)
        (fun action => segmentLiveEnergy parameter initial
          ((Fin.snoc history.1 (history.2, action),
            nextState history.2 action) : game.Hist (time + 1))) ≤
      segmentLiveEnergy parameter initial history := by
  cases hstate : history.2 with
  | absTL => simp [segmentLiveEnergy, liveIndicator, hstate, nextState]
  | absTR => simp [segmentLiveEnergy, liveIndicator, hstate, nextState]
  | live =>
      have hprofile := segmentColumnDeviationProfile_columnStrategy
        parameter initial
      have hrawPos := segmentRawBalance_pos_of_live_of_mem_support
        parameter hinitial (segmentColumnStrategy parameter) time history
        (by rwa [hprofile]) hstate
      change expect
          (pmfPi (fun who => if who then segmentColumnCoin parameter else
            weightedBlackwellFergusonStrategy parameter initial time history))
          (fun action => segmentLiveEnergy parameter initial
            ((Fin.snoc history.1 (.live, action),
              nextState .live action) : game.Hist (time + 1))) ≤ _
      rw [BigMatch.expect_pmfPi_bool]
      simp only [Bool.false_eq_true, if_false, if_true]
      unfold weightedBlackwellFergusonStrategy
      rw [BigMatch.expect_coinPMF]
      set raw := segmentRawBalance parameter initial history with hraw
      set b := parameter.leftProbability with hb
      set a := parameter.value with ha
      set p := segmentStopProbability parameter initial history with hp
      have hbpos : 0 < b := parameter.leftProbability_pos
      have hab : b ≤ a := parameter.leftProbability_le_value
      have hsum : a + b = 1 := parameter.value_add_leftProbability
      have hcurrent :
          segmentLiveEnergy parameter initial history = energy a b raw := by
        simp [segmentLiveEnergy, hstate, hraw, ha, hb]
      rw [hcurrent]
      have hrawFalse :
          segmentRawBalance parameter initial
              ((Fin.snoc history.1
                  (.live, fun _who => false), .live) : game.Hist (time + 1)) =
            raw - b := by
        rw [show (.live : State) = history.2 from hstate.symm,
          segmentRawBalance_snoc, hstate, liveIndicator_live, one_mul]
        simp [segmentIncrement, hraw, hb]
        ring
      have hrawTrue :
          segmentRawBalance parameter initial
              ((Fin.snoc history.1
                  (.live, fun who => who), .live) : game.Hist (time + 1)) =
            raw + a := by
        rw [show (.live : State) = history.2 from hstate.symm,
          segmentRawBalance_snoc, hstate, liveIndicator_live, one_mul]
        simp [segmentIncrement, hraw, ha]
      have honeSubParameter :
          1 - parameter.leftProbability = parameter.value := by
        linarith [parameter.value_add_leftProbability]
      have hbottom :
          expect (segmentColumnCoin parameter) (fun column =>
            segmentLiveEnergy parameter initial
              ((Fin.snoc history.1
                  (.live, fun who => if who then column else false),
                nextState .live
                  (fun who => if who then column else false)) :
                game.Hist (time + 1))) =
            a * energy a b (raw - b) + b * energy a b (raw + a) := by
        rw [expect_eq_sum, Fintype.sum_bool]
        simp [segmentColumnCoin, segmentLiveEnergy, nextState,
          liveIndicator, hrawFalse, hrawTrue,
          ENNReal.toReal_ofReal parameter.leftProbability_nonneg,
          honeSubParameter,
          ENNReal.toReal_ofReal parameter.value_pos.le,
          ha, hb]
        ring
      have htop :
          expect (segmentColumnCoin parameter) (fun column =>
            segmentLiveEnergy parameter initial
              ((Fin.snoc history.1
                  (.live, fun who => if who then column else true),
                nextState .live
                  (fun who => if who then column else true)) :
                game.Hist (time + 1))) = 0 := by
        rw [expect_eq_sum, Fintype.sum_bool]
        simp [segmentColumnCoin, segmentLiveEnergy, nextState, liveIndicator]
      rw [htop, hbottom]
      rw [energy_expect_step hsum]
      by_cases hfloor : raw ≤ b
      · have hpeq : p = 1 := by
          rw [hp]
          exact segmentStopProbability_eq_one_of_raw_le parameter initial history
            (by simpa [hraw, hb])
        rw [hpeq]
        have henergyNonneg : 0 ≤ energy a b raw := by
          unfold energy
          have hsecond : 0 ≤ raw + (a - b) := by linarith
          positivity
        nlinarith
      · have hrawGe : b ≤ raw := (lt_of_not_ge hfloor).le
        have hpeq : p = stopProbability a b raw := by
          rw [hp, segmentStopProbability, segmentDenom,
            max_eq_left (by simpa [hraw, hb] using hrawGe), ← ha, ← hb]
        rw [hpeq]
        simpa using one_sub_stop_mul_energy_drift_le hab hbpos hrawGe

theorem segmentLiveEnergyExpectation_succ_le
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial) (time : ℕ) :
    segmentLiveEnergyExpectation parameter initial (time + 1) ≤
      segmentLiveEnergyExpectation parameter initial time := by
  unfold segmentLiveEnergyExpectation
  rw [game.histDist_succ, expect_bind]
  have hcollapse : ∀ history : game.Hist time,
      expect
          ((game.stageActionDist (segmentProfile parameter initial) history).bind
            fun action => (game.transition history.2 action).bind fun next =>
              PMF.pure
                ((Fin.snoc history.1 (history.2, action), next) :
                  game.Hist (time + 1)))
          (segmentLiveEnergy parameter initial) =
        expect (game.stageActionDist (segmentProfile parameter initial) history)
          (fun action => segmentLiveEnergy parameter initial
            ((Fin.snoc history.1 (history.2, action),
              nextState history.2 action) : game.Hist (time + 1))) := by
    intro history
    rw [expect_bind]
    apply congrArg (expect
      (game.stageActionDist (segmentProfile parameter initial) history))
    funext action
    rw [expect_bind, transition_eq, expect_pure, expect_pure]
  simp_rw [hcollapse]
  exact expect_mono_on_support _ _ _ fun history hhistory =>
    expect_next_segmentLiveEnergy_le_of_mem_support
      parameter hinitial history hhistory

theorem segmentLiveEnergyExpectation_le_initial
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial) (time : ℕ) :
    segmentLiveEnergyExpectation parameter initial time ≤
      energy parameter.value parameter.leftProbability initial := by
  have hantitone : Antitone (segmentLiveEnergyExpectation parameter initial) :=
    antitone_nat_of_succ_le
      (segmentLiveEnergyExpectation_succ_le parameter hinitial)
  have hzero := hantitone (Nat.zero_le time)
  calc
    segmentLiveEnergyExpectation parameter initial time ≤
        segmentLiveEnergyExpectation parameter initial 0 := hzero
    _ = energy parameter.value parameter.leftProbability initial := by
      unfold segmentLiveEnergyExpectation
      rw [game.histDist_zero, expect_pure]
      have hempty : (game.emptyHist (.live)).2 = .live := rfl
      rw [segmentLiveEnergy, hempty, liveIndicator_live, one_mul]
      simp [segmentRawBalance, segmentIncrementSum]

/-- Cauchy--Schwarz for the live indicator and a positive history weight. -/
theorem sq_expect_liveIndicator_le_mul
    {time : ℕ} (distribution : PMF (game.Hist time))
    (weight : game.Hist time → ℝ) (hweight : ∀ history, 0 < weight history) :
    (expect distribution fun history => liveIndicator history.2) ^ 2 ≤
      (expect distribution fun history =>
        liveIndicator history.2 * weight history) *
      expect distribution (fun history =>
        liveIndicator history.2 / weight history) := by
  rw [expect_eq_sum, expect_eq_sum, expect_eq_sum]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (game.Hist time))
    (r := fun history =>
      (distribution history).toReal * liveIndicator history.2)
    (f := fun history =>
      (distribution history).toReal * liveIndicator history.2 * weight history)
    (g := fun history =>
      (distribution history).toReal * liveIndicator history.2 /
        weight history)
    (fun history _ => mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (liveIndicator_nonneg _))
      (hweight history).le)
    (fun history _ => div_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (liveIndicator_nonneg _))
      (hweight history).le)
    (fun history _ => by
      cases hstate : history.2 with
      | live =>
          simp only [liveIndicator_live, mul_one]
          field_simp [(hweight history).ne']
          exact le_rfl
      | absTL => simp [liveIndicator]
      | absTR => simp [liveIndicator])
  simpa only [div_eq_mul_inv, mul_assoc] using hcs

theorem expected_live_denomEnergy_le
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial) (time : ℕ) :
    expect (game.histDist (segmentProfile parameter initial) .live time)
        (fun history => liveIndicator history.2 *
          energy parameter.value parameter.leftProbability
            (segmentDenom parameter initial history)) ≤
      energy parameter.value parameter.leftProbability initial +
        parameter.value * parameter.leftProbability := by
  calc
    expect (game.histDist (segmentProfile parameter initial) .live time)
        (fun history => liveIndicator history.2 *
          energy parameter.value parameter.leftProbability
            (segmentDenom parameter initial history)) ≤
      expect (game.histDist (segmentProfile parameter initial) .live time)
        (fun history => segmentLiveEnergy parameter initial history +
          parameter.value * parameter.leftProbability) := by
        apply expect_mono_on_support
        intro history hhistory
        cases hstate : history.2 with
        | absTL =>
            simp [segmentLiveEnergy, liveIndicator, hstate,
              mul_nonneg parameter.value_pos.le
                parameter.leftProbability_nonneg]
        | absTR =>
            simp [segmentLiveEnergy, liveIndicator, hstate,
              mul_nonneg parameter.value_pos.le
                parameter.leftProbability_nonneg]
        | live =>
            have hprofile := segmentColumnDeviationProfile_columnStrategy
              parameter initial
            have hrawPos := segmentRawBalance_pos_of_live_of_mem_support
              parameter hinitial (segmentColumnStrategy parameter) time history
              (by rwa [hprofile]) hstate
            simp only [hstate, liveIndicator_live, one_mul, segmentLiveEnergy]
            unfold segmentDenom
            by_cases hfloor : segmentRawBalance parameter initial history ≤
                parameter.leftProbability
            · rw [max_eq_right hfloor]
              have hrawEnergy : 0 ≤
                  energy parameter.value parameter.leftProbability
                    (segmentRawBalance parameter initial history) := by
                unfold energy
                have hsecond : 0 ≤
                    segmentRawBalance parameter initial history +
                      (parameter.value - parameter.leftProbability) := by
                  linarith [parameter.leftProbability_le_value]
                positivity
              have hfloorEnergy :
                  energy parameter.value parameter.leftProbability
                      parameter.leftProbability =
                    parameter.value * parameter.leftProbability := by
                unfold energy
                ring
              rw [hfloorEnergy]
              linarith
            · rw [max_eq_left (le_of_not_ge hfloor)]
              linarith [mul_pos parameter.value_pos
                parameter.leftProbability_pos]
    _ = segmentLiveEnergyExpectation parameter initial time +
        parameter.value * parameter.leftProbability := by
      unfold segmentLiveEnergyExpectation
      rw [expect_add, expect_const]
    _ ≤ energy parameter.value parameter.leftProbability initial +
        parameter.value * parameter.leftProbability := by
      simpa [add_comm] using add_le_add_right
        (segmentLiveEnergyExpectation_le_initial parameter hinitial time)
        (parameter.value * parameter.leftProbability)

theorem denomEnergy_mul_liveStop_ge
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial) (time : ℕ) :
    (energy parameter.value parameter.leftProbability initial +
        parameter.value * parameter.leftProbability) *
        segmentLiveStopExpectation parameter initial
          (segmentColumnStrategy parameter) time ≥
      parameter.value * parameter.leftProbability *
        liveProbability (segmentProfile parameter initial) time ^ 2 := by
  let distribution := game.histDist (segmentProfile parameter initial) .live time
  let weight : game.Hist time → ℝ := fun history =>
    energy parameter.value parameter.leftProbability
      (segmentDenom parameter initial history)
  have hweight : ∀ history, 0 < weight history := fun history =>
    energy_pos parameter.leftProbability_le_value
      parameter.leftProbability_pos
      (leftProbability_le_segmentDenom parameter initial history)
  have hcs := sq_expect_liveIndicator_le_mul distribution weight hweight
  have hstop :
      segmentLiveStopExpectation parameter initial
          (segmentColumnStrategy parameter) time =
        parameter.value * parameter.leftProbability *
          expect distribution (fun history =>
            liveIndicator history.2 / weight history) := by
    unfold segmentLiveStopExpectation segmentStopProbability weight distribution
    rw [segmentColumnDeviationProfile_columnStrategy]
    rw [show
      (fun history : game.Hist time => liveIndicator history.2 *
        stopProbability parameter.value parameter.leftProbability
          (segmentDenom parameter initial history)) =
      (fun history => parameter.value * parameter.leftProbability *
        (liveIndicator history.2 /
          energy parameter.value parameter.leftProbability
            (segmentDenom parameter initial history))) by
              funext history
              unfold stopProbability energy
              field_simp,
      expect_const_mul]
  have henergy := expected_live_denomEnergy_le parameter hinitial time
  unfold distribution weight at hcs hstop
  unfold liveProbability StochasticGame.expectedStateValue
  have hnonneg : 0 ≤ expect
      (game.histDist (segmentProfile parameter initial) .live time)
      (fun history => liveIndicator history.2 /
        energy parameter.value parameter.leftProbability
          (segmentDenom parameter initial history)) :=
    expect_nonneg _ _ fun history => div_nonneg
      (liveIndicator_nonneg _) (hweight history).le
  have hupper := mul_le_mul_of_nonneg_right henergy hnonneg
  have hmain := hcs.trans hupper
  have hab : 0 ≤ parameter.value * parameter.leftProbability :=
    mul_nonneg parameter.value_pos.le parameter.leftProbability_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hmain hab
  rw [hstop]
  nlinarith

/-! ## Almost-sure absorption and prescribed-payoff convergence -/

/-- The reciprocal-energy profile has no positive infinite-survival mass. -/
theorem survivalLimit_segmentProfile_eq_zero
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial) :
    survivalLimit (segmentProfile parameter initial) = 0 := by
  apply le_antisymm _ (survivalLimit_nonneg _)
  by_contra hnot
  have hlimit : 0 < survivalLimit (segmentProfile parameter initial) :=
    lt_of_not_ge hnot
  let coefficient :=
    energy parameter.value parameter.leftProbability initial +
      parameter.value * parameter.leftProbability
  let charge := parameter.value * parameter.leftProbability *
    survivalLimit (segmentProfile parameter initial) ^ 2
  have hab : 0 < parameter.value * parameter.leftProbability :=
    mul_pos parameter.value_pos parameter.leftProbability_pos
  have hcoefficient : 0 < coefficient := by
    dsimp [coefficient]
    have henergy := energy_pos parameter.leftProbability_le_value
      parameter.leftProbability_pos hinitial
    linarith
  have hcharge : 0 < charge := by
    exact mul_pos hab (sq_pos_of_pos hlimit)
  obtain ⟨time, htime⟩ := exists_nat_gt (coefficient / charge)
  have hlarge : coefficient < (time : ℝ) * charge :=
    (div_lt_iff₀ hcharge).mp htime
  have hterm : ∀ stage : ℕ, charge ≤
      coefficient * segmentLiveStopExpectation parameter initial
        (segmentColumnStrategy parameter) stage := by
    intro stage
    have hlower := survivalLimit_le_liveProbability
      (segmentProfile parameter initial) stage
    have hlive := liveProbability_nonneg
      (segmentProfile parameter initial) stage
    have hsquare :
        survivalLimit (segmentProfile parameter initial) ^ 2 ≤
          liveProbability (segmentProfile parameter initial) stage ^ 2 := by
      nlinarith [sq_nonneg
        (liveProbability (segmentProfile parameter initial) stage -
          survivalLimit (segmentProfile parameter initial))]
    have hscaled := mul_le_mul_of_nonneg_left hsquare hab.le
    exact hscaled.trans
      (denomEnergy_mul_liveStop_ge parameter hinitial stage)
  have hlowerSum :
      ∑ stage ∈ Finset.range time, charge ≤
        ∑ stage ∈ Finset.range time,
          coefficient * segmentLiveStopExpectation parameter initial
            (segmentColumnStrategy parameter) stage :=
    Finset.sum_le_sum fun stage _ => hterm stage
  have hstop := sum_segmentLiveStopExpectation_le_one parameter initial
    (segmentColumnStrategy parameter) time
  have hupperSum :
      coefficient *
          (∑ stage ∈ Finset.range time,
            segmentLiveStopExpectation parameter initial
              (segmentColumnStrategy parameter) stage) ≤
        coefficient := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hstop hcoefficient.le
  simp_rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlowerSum
  rw [Finset.mul_sum] at hupperSum
  linarith

theorem tendsto_liveProbability_segmentProfile_zero
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial) :
    Tendsto (liveProbability (segmentProfile parameter initial)) atTop
      (nhds 0) := by
  simpa [survivalLimit_segmentProfile_eq_zero parameter hinitial] using
    tendsto_liveProbability_survivalLimit (segmentProfile parameter initial)

/-- Under the prescribed profile, every finite average converges to the
selected point of the payoff segment. -/
theorem tendsto_finiteAveragePayoff_segmentProfile
    (parameter : SegmentParameter) {initial : ℝ}
    (hinitial : parameter.leftProbability ≤ initial) (who : Player) :
    Tendsto
      (fun horizon => game.finiteAveragePayoff .live horizon
        (segmentProfile parameter initial) who)
      atTop
      (nhds (if who then 2 * parameter.leftProbability else
        parameter.value)) := by
  have hlive : Tendsto
      (fun time => liveProbability (segmentProfile parameter initial) (time + 1))
      atTop (nhds 0) :=
    (tendsto_liveProbability_segmentProfile_zero parameter hinitial).comp
      (tendsto_add_atTop_nat 1)
  have hstage : Tendsto
      (fun time => game.expectedStagePayoff
        (segmentProfile parameter initial) .live time who)
      atTop
      (nhds (if who then 2 * parameter.leftProbability else
        parameter.value)) := by
    cases who with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [show
          (fun time => game.expectedStagePayoff
            (segmentProfile parameter initial) .live time false) =
          (fun time => parameter.value - parameter.rowSlope *
            liveProbability (segmentProfile parameter initial) (time + 1)) by
              funext time
              exact expectedStagePayoff_segmentProfile_playerOne
                parameter initial time]
        convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hlive) using 1
        ring
    | true =>
        simp only [if_true]
        rw [show
          (fun time => game.expectedStagePayoff
            (segmentProfile parameter initial) .live time true) =
          (fun time => 2 * parameter.leftProbability -
            parameter.columnSlack *
              liveProbability (segmentProfile parameter initial) (time + 1)) by
              funext time
              exact expectedStagePayoff_segmentProfile_playerTwo
                parameter initial time]
        convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hlive) using 1
        ring
  simpa only [game.finiteAveragePayoff_eq_sum_expectedStagePayoff] using
    hstage.cesaro

/-! ## Uniform-equilibrium payoff segment -/

/-- Every point `(a, 2(1-a))`, `1/2 ≤ a ≤ 2/3`, is a uniform-equilibrium
payoff of Sorin's absorbing game.  The account size may depend on the target
accuracy, while the payoff target does not. -/
theorem isUniformEquilibriumPayoff_segment
    (parameter : SegmentParameter) :
    game.IsUniformEquilibriumPayoff .live
      (fun who => if who then 2 * parameter.leftProbability else
        parameter.value) := by
  apply game.isUniformEquilibriumPayoff_of_deviation_caps
  intro delta hdelta
  let initial := max parameter.leftProbability
    (4 * parameter.value * parameter.leftProbability / delta)
  have hinitial : parameter.leftProbability ≤ initial := le_max_left _ _
  have hinitialPos : 0 < initial :=
    parameter.leftProbability_pos.trans_le hinitial
  have hrisk :
      2 * parameter.value * parameter.leftProbability / initial ≤
        delta / 2 := by
    rw [div_le_iff₀ hinitialPos]
    have hlarge :
        4 * parameter.value * parameter.leftProbability / delta ≤ initial :=
      le_max_right _ _
    have hdeltaScaled :=
      (div_le_iff₀ hdelta).mp hlarge
    nlinarith
  have hpayoffFalse := Metric.tendsto_atTop.mp
    (tendsto_finiteAveragePayoff_segmentProfile parameter hinitial false)
      delta hdelta
  have hpayoffTrue := Metric.tendsto_atTop.mp
    (tendsto_finiteAveragePayoff_segmentProfile parameter hinitial true)
      delta hdelta
  let remainder :=
    initial + parameter.leftProbability + 3 * parameter.value
  have hremainder : Tendsto (fun horizon : ℕ => remainder / (horizon : ℝ))
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat remainder
  obtain ⟨payoffFalseThreshold, hpayoffFalseThreshold⟩ := hpayoffFalse
  obtain ⟨payoffTrueThreshold, hpayoffTrueThreshold⟩ := hpayoffTrue
  obtain ⟨remainderThreshold, hremainderThreshold⟩ :=
    (Metric.tendsto_atTop.mp hremainder) (delta / 2) (by linarith)
  let threshold := max 1
    (max payoffFalseThreshold (max payoffTrueThreshold remainderThreshold))
  refine ⟨segmentProfile parameter initial, threshold, ?_⟩
  intro horizon hhorizon
  have hhorizonPos : 0 < horizon :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hhorizon)
  have hfalseThreshold : payoffFalseThreshold ≤ horizon :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) hhorizon)
  have htrueThreshold : payoffTrueThreshold ≤ horizon :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hhorizon))
  have hremainderThreshold' : remainderThreshold ≤ horizon :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hhorizon))
  constructor
  · intro who
    cases who with
    | false =>
        simpa only [Bool.false_eq_true, if_false, Real.dist_eq] using
          (hpayoffFalseThreshold horizon hfalseThreshold).le
    | true =>
        simpa only [if_true, Real.dist_eq] using
          (hpayoffTrueThreshold horizon htrueThreshold).le
  · intro who deviation
    cases who with
    | false =>
        rw [update_segmentProfile_false]
        have hcap := finiteAveragePayoff_segmentRowDeviation_playerOne_le
          parameter deviation hhorizonPos
        simp only [Bool.false_eq_true, if_false]
        linarith
    | true =>
        rw [update_segmentProfile_true]
        have hcap := finiteAveragePayoff_segmentColumnDeviation_playerTwo_le
          parameter hinitial deviation hhorizonPos
        have hremainderSmall :=
          (hremainderThreshold horizon hremainderThreshold').le
        rw [Real.dist_eq, sub_zero] at hremainderSmall
        have hremainderUpper : remainder / (horizon : ℝ) ≤ delta / 2 :=
          (le_abs_self _).trans hremainderSmall
        simp only [if_true]
        dsimp [remainder] at hremainderUpper
        exact hcap.trans (by linarith)

/-- Scalar form of the whole segment inclusion. -/
theorem isUniformEquilibriumPayoff_pair_value
    {value : ℝ} (half_le : 1 / 2 ≤ value)
    (le_two_thirds : value ≤ 2 / 3) :
    game.IsUniformEquilibriumPayoff .live
      (pair value (2 * (1 - value))) := by
  let parameter : SegmentParameter :=
    ⟨value, half_le, le_two_thirds⟩
  convert isUniformEquilibriumPayoff_segment parameter using 1
  funext who
  cases who <;>
    simp [parameter, UniformSegmentParameter.leftProbability, pair]

end SorinAbsorbingGame
end StochasticGame
end GameTheory
