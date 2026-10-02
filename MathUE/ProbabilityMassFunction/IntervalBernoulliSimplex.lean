import MathUE.ProbabilityMassFunction.Simplex

/-! # Continuous clipped Bernoulli simplex coordinates -/

noncomputable section

namespace Math.ProbabilityMassFunction

/-- Scalar clipping to the closed unit interval. -/
def unitIntervalClip (value : ℝ) : ℝ := min 1 (max 0 value)

theorem unitIntervalClip_nonneg (value : ℝ) : 0 ≤ unitIntervalClip value :=
  le_min zero_le_one (le_max_left _ _)

theorem unitIntervalClip_le_one (value : ℝ) : unitIntervalClip value ≤ 1 :=
  min_le_left _ _

theorem unitIntervalClip_eq_self {value : ℝ} (hzero : 0 ≤ value) (hone : value ≤ 1) :
    unitIntervalClip value = value := by
  simp [unitIntervalClip, max_eq_right hzero, min_eq_right hone]

theorem continuous_unitIntervalClip : Continuous unitIntervalClip :=
  continuous_const.min (continuous_const.max continuous_id)

/-- A globally continuous simplex-valued Bernoulli map, exact on the unit interval. -/
def intervalBernoulliSimplex (value : ℝ) : Convexity.StdSimplex ℝ Bool :=
  stdSimplexEquiv (bernoulliBool (unitIntervalClip value)
    (unitIntervalClip_nonneg value) (unitIntervalClip_le_one value))

@[simp] theorem intervalBernoulliSimplex_weights_true (value : ℝ) :
    (intervalBernoulliSimplex value).weights true = unitIntervalClip value := by
  simp [intervalBernoulliSimplex, simplexEquiv_apply_weights, toVector]

@[simp] theorem intervalBernoulliSimplex_weights_false (value : ℝ) :
    (intervalBernoulliSimplex value).weights false = 1 - unitIntervalClip value := by
  simp [intervalBernoulliSimplex, simplexEquiv_apply_weights, toVector]

theorem continuous_intervalBernoulliSimplex : Continuous intervalBernoulliSimplex := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Bool).continuous_iff.mpr
  apply continuous_pi
  intro action
  cases action
  · simpa [Function.comp_def] using! continuous_const.sub continuous_unitIntervalClip
  · simpa [Function.comp_def] using continuous_unitIntervalClip

end Math.ProbabilityMassFunction
