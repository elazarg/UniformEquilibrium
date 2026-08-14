import UniformEquilibrium.Certificates.Adaptive.Certificate

/-!
# Weighted security--welfare assembly

This experiment proves the main assembly proposal from
`ideas/CoalitionSecurityWelfareAssembly.md`.

Separate one-sided uniform security strategies are compatible whenever one
positive weighted welfare ceiling is saturated by their target values.  The
proof combines the security strategies coordinatewise; the welfare ceiling
then supplies both the missing on-path upper bounds and every unilateral
deviation cap.
-/

noncomputable section

namespace Experiments.WeightedSecurityWelfareAssembly

open scoped BigOperators

open GameTheory
open Math.Probability

namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

/-- A uniform upper bound on positive weighted total payoff, valid for every
behavior profile.  The target level is the weighted sum of `v`. -/
def HasUniformWeightedWelfareCap
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (weight : ι → ℝ) (v : Payoff ι) : Prop :=
  ∀ error : ℝ, 0 < error → ∃ horizon : ℕ,
    ∀ (profile : G.BehaviorProfile) (T : ℕ), horizon ≤ T →
      (∑ i, weight i * G.finiteAveragePayoff s₀ T profile i) ≤
        (∑ i, weight i * v i) + error

/-- **Weighted security--welfare assembly.**

Each player separately secures its coordinate of `v` against every opponent
completion.  If every weight is at least one and no profile can asymptotically
exceed the weighted target welfare, the product of the securing strategies is
a uniform equilibrium profile.  Requiring weights at least one loses no
generality at the semantic level: a finite positive family can be rescaled by
its positive minimum. -/
theorem isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_weightedWelfareCap
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (weight : ι → ℝ) (v : Payoff ι)
    (weight_ge_one : ∀ i, 1 ≤ weight i)
    (security : ∀ i, G.IsOneSidedGuaranteeCertificate s₀ i (v i))
    (welfareCap : HasUniformWeightedWelfareCap G s₀ weight v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  classical
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ v
  intro error error_pos
  let totalWeight : ℝ := ∑ i, weight i
  have totalWeight_nonneg : 0 ≤ totalWeight := by
    exact Finset.sum_nonneg fun i _ => (zero_le_one.trans (weight_ge_one i))
  let securityError : ℝ := error / (4 * (totalWeight + 1))
  let capError : ℝ := error / 4
  have denominator_pos : 0 < 4 * (totalWeight + 1) := by
    positivity
  have securityError_pos : 0 < securityError := by
    exact div_pos error_pos denominator_pos
  have capError_pos : 0 < capError := by
    dsimp only [capError]
    positivity
  have securityError_le_error : securityError ≤ error := by
    apply (div_le_iff₀ denominator_pos).2
    have denominator_ge_one : 1 ≤ 4 * (totalWeight + 1) := by
      nlinarith
    nlinarith
  have scaledSecurityError_le :
      securityError * totalWeight ≤ error / 4 := by
    have ratio_le_one : totalWeight / (totalWeight + 1) ≤ 1 := by
      apply (div_le_one (by linarith)).2
      linarith
    calc
      securityError * totalWeight =
          (error / 4) * (totalWeight / (totalWeight + 1)) := by
        dsimp only [securityError]
        field_simp
      _ ≤ (error / 4) * 1 := by
        exact mul_le_mul_of_nonneg_left ratio_le_one (by positivity)
      _ = error / 4 := by ring
  have combinedError_le :
      capError + securityError * totalWeight ≤ error := by
    dsimp only [capError]
    nlinarith
  have securityAt : ∀ i, ∃ (strategy : G.BehaviorStrategy i) (horizon : ℕ),
      2 ≤ horizon ∧ ∀ (opp : G.BehaviorProfile) (T : ℕ), horizon ≤ T →
        v i - securityError ≤
          G.finiteAveragePayoff s₀ T
            (Function.update opp i strategy) i := by
    intro i
    exact security i securityError securityError_pos
  choose secureStrategy secureHorizon secureHorizon_ge_two secure using securityAt
  obtain ⟨capHorizon, cap⟩ := welfareCap capError capError_pos
  let profile : G.BehaviorProfile := fun i => secureStrategy i
  let securityHorizon : ℕ := Finset.univ.sup secureHorizon
  let commonHorizon : ℕ := max capHorizon securityHorizon
  have secureHorizon_le (i : ι) : secureHorizon i ≤ commonHorizon := by
    exact
      (Finset.le_sup (s := Finset.univ) (f := secureHorizon)
        (Finset.mem_univ i)).trans (Nat.le_max_right _ _)
  have capHorizon_le : capHorizon ≤ commonHorizon := Nat.le_max_left _ _
  refine ⟨profile, commonHorizon, fun T T_ge => ?_⟩
  have T_ge_cap : capHorizon ≤ T := capHorizon_le.trans T_ge
  have T_ge_secure (i : ι) : secureHorizon i ≤ T :=
    (secureHorizon_le i).trans T_ge
  have onPathLower (i : ι) :
      v i - securityError ≤ G.finiteAveragePayoff s₀ T profile i := by
    have fixed : Function.update profile i (secureStrategy i) = profile := by
      change Function.update profile i (profile i) = profile
      exact Function.update_eq_self i profile
    simpa only [fixed] using secure i profile T (T_ge_secure i)
  have onPathCap := cap profile T T_ge_cap
  have onPathUpper (i : ι) :
      G.finiteAveragePayoff s₀ T profile i ≤ v i + error := by
    let others : Finset ι := Finset.univ.erase i
    have othersTarget_le :
        (∑ j ∈ others, weight j * v j) ≤
          (∑ j ∈ others,
            weight j * G.finiteAveragePayoff s₀ T profile j) +
              securityError * ∑ j ∈ others, weight j := by
      calc
        (∑ j ∈ others, weight j * v j) ≤
            ∑ j ∈ others,
              (weight j * G.finiteAveragePayoff s₀ T profile j +
                weight j * securityError) := by
          apply Finset.sum_le_sum
          intro j j_mem
          have weighted := mul_le_mul_of_nonneg_left (onPathLower j)
            (zero_le_one.trans (weight_ge_one j))
          nlinarith
        _ = (∑ j ∈ others,
              weight j * G.finiteAveragePayoff s₀ T profile j) +
              securityError * ∑ j ∈ others, weight j := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          ring
    have othersWeight_le : (∑ j ∈ others, weight j) ≤ totalWeight := by
      have split := Finset.sum_erase_add
        (s := (Finset.univ : Finset ι)) (f := fun j => weight j)
        (a := i) (Finset.mem_univ i)
      change (∑ j ∈ Finset.univ.erase i, weight j) ≤ totalWeight
      dsimp only [totalWeight]
      nlinarith [zero_le_one.trans (weight_ge_one i)]
    have scaledOthersWeight_le :
        securityError * ∑ j ∈ others, weight j ≤
          securityError * totalWeight :=
      mul_le_mul_of_nonneg_left othersWeight_le securityError_pos.le
    have capSplit := onPathCap
    rw [← Finset.sum_erase_add
          (s := (Finset.univ : Finset ι))
          (f := fun j =>
            weight j * G.finiteAveragePayoff s₀ T profile j)
          (a := i) (Finset.mem_univ i),
        ← Finset.sum_erase_add
          (s := (Finset.univ : Finset ι))
          (f := fun j => weight j * v j)
          (a := i) (Finset.mem_univ i)] at capSplit
    have weightedExcess :
        weight i *
            (G.finiteAveragePayoff s₀ T profile i - v i) ≤
          capError + securityError * totalWeight := by
      dsimp only [others] at othersTarget_le
      linarith
    by_contra not_upper
    have strictUpper : v i + error <
        G.finiteAveragePayoff s₀ T profile i := lt_of_not_ge not_upper
    have weight_pos : 0 < weight i := zero_lt_one.trans_le (weight_ge_one i)
    have weightedStrict := mul_lt_mul_of_pos_left strictUpper weight_pos
    have error_le_weightedError : error ≤ weight i * error := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (weight_ge_one i)) error_pos.le]
    nlinarith
  constructor
  · intro i
    apply abs_le.mpr
    constructor
    · linarith [onPathLower i, securityError_le_error]
    · linarith [onPathUpper i]
  · intro i dev
    let deviatingProfile : G.BehaviorProfile := Function.update profile i dev
    have deviatingOthersLower (j : ι) (j_ne_i : j ≠ i) :
        v j - securityError ≤
          G.finiteAveragePayoff s₀ T deviatingProfile j := by
      have coordinate : deviatingProfile j = secureStrategy j := by
        simp only [deviatingProfile, Function.update_of_ne j_ne_i, profile]
      have fixed :
          Function.update deviatingProfile j (secureStrategy j) =
            deviatingProfile := by
        rw [← coordinate]
        exact Function.update_eq_self j deviatingProfile
      simpa only [fixed] using
        secure j deviatingProfile T (T_ge_secure j)
    have deviatingCap := cap deviatingProfile T T_ge_cap
    let others : Finset ι := Finset.univ.erase i
    have othersTarget_le :
        (∑ j ∈ others, weight j * v j) ≤
          (∑ j ∈ others,
            weight j * G.finiteAveragePayoff s₀ T deviatingProfile j) +
              securityError * ∑ j ∈ others, weight j := by
      calc
        (∑ j ∈ others, weight j * v j) ≤
            ∑ j ∈ others,
              (weight j *
                  G.finiteAveragePayoff s₀ T deviatingProfile j +
                weight j * securityError) := by
          apply Finset.sum_le_sum
          intro j j_mem
          have j_ne_i : j ≠ i := by
            exact Finset.ne_of_mem_erase j_mem
          have weighted :=
            mul_le_mul_of_nonneg_left (deviatingOthersLower j j_ne_i)
              (zero_le_one.trans (weight_ge_one j))
          nlinarith
        _ = (∑ j ∈ others,
              weight j *
                G.finiteAveragePayoff s₀ T deviatingProfile j) +
              securityError * ∑ j ∈ others, weight j := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          ring
    have othersWeight_le : (∑ j ∈ others, weight j) ≤ totalWeight := by
      have split := Finset.sum_erase_add
        (s := (Finset.univ : Finset ι)) (f := fun j => weight j)
        (a := i) (Finset.mem_univ i)
      change (∑ j ∈ Finset.univ.erase i, weight j) ≤ totalWeight
      dsimp only [totalWeight]
      nlinarith [zero_le_one.trans (weight_ge_one i)]
    have scaledOthersWeight_le :
        securityError * ∑ j ∈ others, weight j ≤
          securityError * totalWeight :=
      mul_le_mul_of_nonneg_left othersWeight_le securityError_pos.le
    rw [← Finset.sum_erase_add
          (s := (Finset.univ : Finset ι))
          (f := fun j =>
            weight j *
              G.finiteAveragePayoff s₀ T deviatingProfile j)
          (a := i) (Finset.mem_univ i),
        ← Finset.sum_erase_add
          (s := (Finset.univ : Finset ι))
          (f := fun j => weight j * v j)
          (a := i) (Finset.mem_univ i)] at deviatingCap
    have weightedExcess :
        weight i *
            (G.finiteAveragePayoff s₀ T deviatingProfile i - v i) ≤
          capError + securityError * totalWeight := by
      dsimp only [others] at othersTarget_le
      linarith
    have upper :
        G.finiteAveragePayoff s₀ T deviatingProfile i ≤ v i + error := by
      by_contra not_upper
      have strictUpper : v i + error <
          G.finiteAveragePayoff s₀ T deviatingProfile i :=
        lt_of_not_ge not_upper
      have weight_pos : 0 < weight i := zero_lt_one.trans_le (weight_ge_one i)
      have weightedStrict := mul_lt_mul_of_pos_left strictUpper weight_pos
      have error_le_weightedError : error ≤ weight i * error := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (weight_ge_one i)) error_pos.le]
      nlinarith
    simpa only [deviatingProfile] using upper

/-- Positive weights can be normalized to the `weight >= 1` form used by the
quantitative proof above.  Thus the semantic assembly theorem holds for every
strictly positive finite weight family. -/
theorem isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_positiveWeightedWelfareCap
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (weight : ι → ℝ) (v : Payoff ι)
    (weight_pos : ∀ i, 0 < weight i)
    (security : ∀ i, G.IsOneSidedGuaranteeCertificate s₀ i (v i))
    (welfareCap : HasUniformWeightedWelfareCap G s₀ weight v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  classical
  let scale : ℝ := ∑ i, (weight i)⁻¹
  have scale_pos : 0 < scale := by
    apply Finset.sum_pos'
    · intro i i_mem
      exact inv_nonneg.mpr (weight_pos i).le
    · let i : ι := Classical.arbitrary ι
      exact ⟨i, Finset.mem_univ i, inv_pos.mpr (weight_pos i)⟩
  let normalizedWeight : ι → ℝ := fun i => scale * weight i
  have normalizedWeight_ge_one (i : ι) : 1 ≤ normalizedWeight i := by
    have inverse_le_scale : (weight i)⁻¹ ≤ scale := by
      exact Finset.single_le_sum
        (fun j _ => inv_nonneg.mpr (weight_pos j).le)
        (Finset.mem_univ i)
    have scaled :=
      mul_le_mul_of_nonneg_right inverse_le_scale (weight_pos i).le
    dsimp only [normalizedWeight]
    rw [inv_mul_cancel₀ (weight_pos i).ne'] at scaled
    simpa [mul_comm] using scaled
  have normalizedCap :
      HasUniformWeightedWelfareCap G s₀ normalizedWeight v := by
    intro error error_pos
    have scaledError_pos : 0 < error / scale := div_pos error_pos scale_pos
    obtain ⟨horizon, cap⟩ := welfareCap (error / scale) scaledError_pos
    refine ⟨horizon, fun profile T T_ge => ?_⟩
    have originalCap := cap profile T T_ge
    have multiplied :=
      mul_le_mul_of_nonneg_left originalCap scale_pos.le
    calc
      (∑ i, normalizedWeight i *
          G.finiteAveragePayoff s₀ T profile i) =
          scale *
            ∑ i, weight i * G.finiteAveragePayoff s₀ T profile i := by
        dsimp only [normalizedWeight]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i i_mem
        ring
      _ ≤ scale * ((∑ i, weight i * v i) + error / scale) :=
        multiplied
      _ = (∑ i, normalizedWeight i * v i) + error := by
        dsimp only [normalizedWeight]
        rw [show (∑ i, scale * weight i * v i) =
            scale * ∑ i, weight i * v i by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i i_mem
          ring]
        field_simp
  exact
    isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_weightedWelfareCap
      G s₀ normalizedWeight v normalizedWeight_ge_one security normalizedCap

/-! ## A bounded Bellman bias supplies the welfare cap -/

/-- A scalar social bias whose one-step drift universally caps weighted stage
welfare.  This is an average-reward upper Bellman certificate for the
grand-coalition planner problem. -/
def HasWeightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (weight : ι → ℝ) (v : Payoff ι) : Prop :=
  ∃ (bias : G.State → ℝ) (bound : ℝ),
    0 ≤ bound ∧
    (∀ state, |bias state| ≤ bound) ∧
    ∀ (state : G.State) (action : G.JointAct),
      (∑ i, weight i * G.stagePayoff state action i) +
          expect (G.transition state action) bias ≤
        (∑ i, weight i * v i) + bias state

private theorem weightedStageEU_eq_expect
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (weight : ι → ℝ) (profile : G.BehaviorProfile)
    {time : ℕ} (history : G.Hist time) :
    (∑ i, weight i * G.stageEUAt profile history i) =
      expect (G.stageActionDist profile history)
        (fun action => ∑ i, weight i * G.stagePayoff history.2 action i) := by
  rw [← expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i i_mem
  unfold GameTheory.StochasticGame.stageEUAt
  rw [expect_const_mul]

private theorem weightedExpectedStagePayoff_eq_expect
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (weight : ι → ℝ) (profile : G.BehaviorProfile)
    (s₀ : G.State) (time : ℕ) :
    (∑ i, weight i * G.expectedStagePayoff profile s₀ time i) =
      expect (G.histDist profile s₀ time)
        (fun history => ∑ i, weight i * G.stageEUAt profile history i) := by
  rw [← expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i i_mem
  unfold GameTheory.StochasticGame.expectedStagePayoff
  rw [expect_const_mul]

/-- A bounded universal weighted-welfare Bellman bias gives the semantic
uniform welfare cap, with the usual `2 * bound / T` endpoint loss. -/
theorem hasUniformWeightedWelfareCap_of_hasWeightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (weight : ι → ℝ) (v : Payoff ι)
    (certificate : HasWeightedWelfareBias G weight v) :
    HasUniformWeightedWelfareCap G s₀ weight v := by
  classical
  obtain ⟨bias, bound, bound_nonneg, bias_bound, bellman⟩ := certificate
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
  let target : ℝ := ∑ i, weight i * v i
  have expectedStep (time : ℕ) :
      (∑ i, weight i * G.expectedStagePayoff profile s₀ time i) +
          G.expectedStateValue profile s₀ (time + 1) bias ≤
        target + G.expectedStateValue profile s₀ time bias := by
    rw [weightedExpectedStagePayoff_eq_expect]
    rw [G.expectedStateValue_succ]
    rw [← expect_add]
    calc
      expect (G.histDist profile s₀ time)
          (fun history =>
            (∑ i, weight i * G.stageEUAt profile history i) +
              expect (G.stageActionDist profile history)
                (fun action => expect (G.transition history.2 action) bias)) ≤
          expect (G.histDist profile s₀ time)
            (fun history => target + bias history.2) := by
        apply expect_mono
        intro history
        rw [weightedStageEU_eq_expect, ← expect_add]
        calc
          expect (G.stageActionDist profile history)
              (fun action =>
                (∑ i, weight i * G.stagePayoff history.2 action i) +
                  expect (G.transition history.2 action) bias) ≤
              expect (G.stageActionDist profile history)
                (fun _ => target + bias history.2) := by
            apply expect_mono
            intro action
            simpa only [target] using bellman history.2 action
          _ = target + bias history.2 := expect_const _ _
      _ = target + G.expectedStateValue profile s₀ time bias := by
        rw [expect_add, expect_const]
        rfl
  have telescope : ∀ horizon : ℕ,
      (∑ time ∈ Finset.range horizon,
          ∑ i, weight i * G.expectedStagePayoff profile s₀ time i) +
          G.expectedStateValue profile s₀ horizon bias ≤
        (horizon : ℝ) * target + bias s₀ := by
    intro horizon
    induction horizon with
    | zero => simp [GameTheory.StochasticGame.expectedStateValue_zero]
    | succ horizon inductionHypothesis =>
      rw [Finset.sum_range_succ]
      push_cast
      linarith [expectedStep horizon]
  have expectedBias_abs :
      |G.expectedStateValue profile s₀ T bias| ≤ bound := by
    unfold GameTheory.StochasticGame.expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun history => bias_bound history.2
  have totalStageCap :
      (∑ time ∈ Finset.range T,
          ∑ i, weight i * G.expectedStagePayoff profile s₀ time i) ≤
        (T : ℝ) * target + 2 * bound := by
    have initialBiasUpper := (abs_le.mp (bias_bound s₀)).2
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
  have cutoff_real_lt : (cutoff : ℝ) < T := by exact_mod_cast cutoff_lt_T
  have boundary_lt : 2 * bound / (T : ℝ) < error := by
    have positiveProduct : (cutoff : ℝ) * error < (T : ℝ) * error :=
      mul_lt_mul_of_pos_right cutoff_real_lt error_pos
    rw [div_lt_iff₀ error_pos] at cutoff_gt
    apply (div_lt_iff₀ T_real_pos).2
    linarith
  rw [weightedAverage_eq]
  have scaledCap := mul_le_mul_of_nonneg_left totalStageCap
    (inv_nonneg.mpr T_real_pos.le)
  have inverse_mul_T : (T : ℝ)⁻¹ * T = 1 := inv_mul_cancel₀ T_real_pos.ne'
  rw [mul_add, ← mul_assoc, inverse_mul_T, one_mul] at scaledCap
  rw [show (T : ℝ)⁻¹ * (2 * bound) = 2 * bound / T by
    rw [div_eq_mul_inv]
    ring] at scaledCap
  dsimp only [target] at scaledCap ⊢
  linarith

/-- Concrete composition: one-sided security guarantees together with a
bounded universal social Bellman bias imply a uniform equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_weightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (weight : ι → ℝ) (v : Payoff ι)
    (weight_ge_one : ∀ i, 1 ≤ weight i)
    (security : ∀ i, G.IsOneSidedGuaranteeCertificate s₀ i (v i))
    (bias : HasWeightedWelfareBias G weight v) :
    G.IsUniformEquilibriumPayoff s₀ v :=
  isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_weightedWelfareCap
    G s₀ weight v weight_ge_one security
      (hasUniformWeightedWelfareCap_of_hasWeightedWelfareBias
        G s₀ weight v bias)

end StochasticGame

end Experiments.WeightedSecurityWelfareAssembly
