import UniformEquilibrium.Certificates.Adaptive.WeightedWelfareBias
import Mathlib.Data.ZMod.Basic

/-!
# Phase-lifted weighted welfare caps

This file formalizes the independent Bellman-calculus component used by
`ideas/CoalitionSplittingGroupActions.md`.

A bounded social bias on the phase-augmented state `ZMod P × State` supplies a
weighted welfare ceiling for every behavior profile.  The endpoint loss is
`2*bound/T`, uniformly in the horizon and in the initial clock phase.
-/

noncomputable section

namespace Research.PhaseLiftedWelfareCap

open scoped BigOperators

open GameTheory
open Math.Probability

namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

/-- Universal Bellman upper certificate on the phase-augmented state. -/
def HasPhaseWeightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {P : ℕ} [NeZero P]
    (weight : ι → ℝ) (target : Payoff ι) : Prop :=
  ∃ (bias : ZMod P → G.State → ℝ) (bound : ℝ),
    0 ≤ bound ∧
    (∀ phase state, |bias phase state| ≤ bound) ∧
    ∀ (phase : ZMod P) (state : G.State) (action : G.JointAct),
      (∑ i, weight i * G.stagePayoff state action i) +
          expect (G.transition state action) (bias (phase + 1)) ≤
        (∑ i, weight i * target i) + bias phase state

/-- Expected phase-dependent state bias at time `t`. -/
def expectedPhaseBias
    (G : StochasticGame ι) [Fintype ι]
    {P : ℕ} [NeZero P]
    (profile : G.BehaviorProfile) (s₀ : G.State)
    (bias : ZMod P → G.State → ℝ) (time : ℕ) : ℝ :=
  G.expectedStateValue profile s₀ time (bias (time : ZMod P))

/-- Exact quantitative consequence of a phase-lifted social bias. -/
theorem weightedFiniteAverage_le_target_add_boundary_of_phaseBias
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {P : ℕ} [NeZero P]
    (s₀ : G.State) (weight : ι → ℝ) (targetPayoff : Payoff ι)
    (bias : ZMod P → G.State → ℝ) (bound : ℝ)
    (bias_bound : ∀ phase state, |bias phase state| ≤ bound)
    (bellman :
      ∀ (phase : ZMod P) (state : G.State) (action : G.JointAct),
        (∑ i, weight i * G.stagePayoff state action i) +
            expect (G.transition state action) (bias (phase + 1)) ≤
          (∑ i, weight i * targetPayoff i) + bias phase state)
    (profile : G.BehaviorProfile) (T : ℕ) (T_pos : 0 < T) :
    (∑ i, weight i * G.finiteAveragePayoff s₀ T profile i) ≤
      (∑ i, weight i * targetPayoff i) +
        2 * bound / (T : ℝ) := by
  classical
  let target : ℝ := ∑ i, weight i * targetPayoff i
  have phaseSucc (time : ℕ) :
      ((time + 1 : ℕ) : ZMod P) = (time : ZMod P) + 1 := by
    push_cast
    ring
  have expectedStep (time : ℕ) :
      (∑ i, weight i * G.expectedStagePayoff profile s₀ time i) +
          expectedPhaseBias G profile s₀ bias (time + 1) ≤
        target + expectedPhaseBias G profile s₀ bias time := by
    unfold expectedPhaseBias
    rw [GameTheory.StochasticGame.weightedExpectedStagePayoff_eq_expect]
    rw [G.expectedStateValue_succ]
    rw [phaseSucc]
    rw [← expect_add]
    calc
      expect (G.histDist profile s₀ time)
          (fun history =>
            (∑ i, weight i * G.stageEUAt profile history i) +
              expect (G.stageActionDist profile history)
                (fun action =>
                  expect (G.transition history.2 action)
                    (bias ((time : ZMod P) + 1)))) ≤
          expect (G.histDist profile s₀ time)
            (fun history => target + bias (time : ZMod P) history.2) := by
        apply expect_mono
        intro history
        rw [GameTheory.StochasticGame.weightedStageEU_eq_expect, ← expect_add]
        calc
          expect (G.stageActionDist profile history)
              (fun action =>
                (∑ i, weight i * G.stagePayoff history.2 action i) +
                  expect (G.transition history.2 action)
                    (bias ((time : ZMod P) + 1))) ≤
              expect (G.stageActionDist profile history)
                (fun _ => target + bias (time : ZMod P) history.2) := by
            apply expect_mono
            intro action
            simpa only [target] using
              bellman (time : ZMod P) history.2 action
          _ = target + bias (time : ZMod P) history.2 := expect_const _ _
      _ = target +
          G.expectedStateValue profile s₀ time
            (bias (time : ZMod P)) := by
        rw [expect_add, expect_const]
        rfl
  have telescope : ∀ horizon : ℕ,
      (∑ time ∈ Finset.range horizon,
          ∑ i, weight i * G.expectedStagePayoff profile s₀ time i) +
          expectedPhaseBias G profile s₀ bias horizon ≤
        (horizon : ℝ) * target + bias 0 s₀ := by
    intro horizon
    induction horizon with
    | zero => simp [expectedPhaseBias,
        GameTheory.StochasticGame.expectedStateValue_zero]
    | succ horizon inductionHypothesis =>
      rw [Finset.sum_range_succ]
      push_cast
      linarith [expectedStep horizon]
  have expectedBias_abs :
      |expectedPhaseBias G profile s₀ bias T| ≤ bound := by
    unfold expectedPhaseBias GameTheory.StochasticGame.expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun history => bias_bound _ history.2
  have totalStageCap :
      (∑ time ∈ Finset.range T,
          ∑ i, weight i * G.expectedStagePayoff profile s₀ time i) ≤
        (T : ℝ) * target + 2 * bound := by
    have initialBiasUpper := (abs_le.mp (bias_bound 0 s₀)).2
    have terminalBiasLower := (abs_le.mp expectedBias_abs).1
    linarith [telescope T]
  have weightedAverage_eq :
      (∑ i, weight i * G.finiteAveragePayoff s₀ T profile i) =
        (T : ℝ)⁻¹ *
          ∑ time ∈ Finset.range T,
            ∑ i, weight i * G.expectedStagePayoff profile s₀ time i := by
    simp_rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    calc
      (∑ i, weight i *
          ((T : ℝ)⁻¹ *
            ∑ time ∈ Finset.range T,
              G.expectedStagePayoff profile s₀ time i)) =
          (T : ℝ)⁻¹ *
            ∑ i, weight i *
              ∑ time ∈ Finset.range T,
                G.expectedStagePayoff profile s₀ time i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i i_mem
        ring
      _ = (T : ℝ)⁻¹ *
          ∑ i, ∑ time ∈ Finset.range T,
            weight i * G.expectedStagePayoff profile s₀ time i := by
        congr 1
        apply Finset.sum_congr rfl
        intro i i_mem
        rw [Finset.mul_sum]
      _ = (T : ℝ)⁻¹ *
          ∑ time ∈ Finset.range T,
            ∑ i, weight i * G.expectedStagePayoff profile s₀ time i := by
        congr 1
        rw [Finset.sum_comm]
  have T_real_pos : (0 : ℝ) < T := by exact_mod_cast T_pos
  rw [weightedAverage_eq]
  have scaledCap := mul_le_mul_of_nonneg_left totalStageCap
    (inv_nonneg.mpr T_real_pos.le)
  have inverse_mul_T : (T : ℝ)⁻¹ * T = 1 :=
    inv_mul_cancel₀ T_real_pos.ne'
  rw [mul_add, ← mul_assoc, inverse_mul_T, one_mul] at scaledCap
  rw [show (T : ℝ)⁻¹ * (2 * bound) = 2 * bound / T by
    rw [div_eq_mul_inv]
    ring] at scaledCap
  exact scaledCap

/-- A phase-lifted Bellman certificate supplies the semantic uniform welfare
cap required by weighted security--welfare assembly. -/
theorem hasUniformWeightedWelfareCap_of_hasPhaseWeightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    {P : ℕ} [NeZero P]
    (s₀ : G.State) (weight : ι → ℝ) (target : Payoff ι)
    (certificate : HasPhaseWeightedWelfareBias (P := P) G weight target) :
    GameTheory.StochasticGame.HasUniformWeightedWelfareCap
      G s₀ weight target := by
  obtain ⟨bias, bound, _bound_nonneg, bias_bound, bellman⟩ := certificate
  intro error error_pos
  obtain ⟨cutoff, cutoff_gt⟩ := exists_nat_gt (2 * bound / error)
  refine ⟨max 1 (cutoff + 1), fun profile T T_ge => ?_⟩
  have T_pos : 0 < T := by
    have : 1 ≤ T := (Nat.le_max_left 1 (cutoff + 1)).trans T_ge
    omega
  have cutoff_lt_T : cutoff < T := by
    have : cutoff + 1 ≤ T :=
      (Nat.le_max_right 1 (cutoff + 1)).trans T_ge
    omega
  have quantitative :=
    weightedFiniteAverage_le_target_add_boundary_of_phaseBias
      (P := P) G s₀ weight target bias bound bias_bound bellman
        profile T T_pos
  have T_real_pos : (0 : ℝ) < T := by exact_mod_cast T_pos
  have cutoff_real_lt : (cutoff : ℝ) < T := by exact_mod_cast cutoff_lt_T
  have boundary_lt : 2 * bound / (T : ℝ) < error := by
    have positiveProduct : (cutoff : ℝ) * error < (T : ℝ) * error :=
      mul_lt_mul_of_pos_right cutoff_real_lt error_pos
    rw [div_lt_iff₀ error_pos] at cutoff_gt
    apply (div_lt_iff₀ T_real_pos).2
    linarith
  simpa using quantitative.trans (by linarith)

end StochasticGame

end Research.PhaseLiftedWelfareCap
