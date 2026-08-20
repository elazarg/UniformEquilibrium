import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted

/-!
# Dynamic common interest modulo a coboundary

This experiment formalizes the algebraic core of the dynamic-potential idea in
`ideas/CoalitionSecurityWelfareAssembly.md`.

Suppose player `i`'s stage payoff is an affine transform of one common reward,
up to a state-potential coboundary

`u_i(s,a) = c_i r(s,a) + d_i + h_i(s) - E[h_i(s') | s,a]`.

For every behavior profile—not only Markov or equilibrium profiles—the
coboundary telescopes in expectation.  Thus the finite average payoff differs
from the corresponding affine common-objective average only by the two endpoint
potentials divided by the horizon.  A bounded potential gives an explicit
`2 C / T` error.
-/

noncomputable section

namespace Research.DynamicPotentialCoboundary

open scoped BigOperators

open GameTheory
open Math.Probability

namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

/-- Expected value of a common stage reward at epoch `t`. -/
def expectedCommonStageReward
    (G : StochasticGame ι) [Fintype ι]
    (reward : G.State → G.JointAct → ℝ)
    (profile : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) : ℝ :=
  expect (G.histDist profile s₀ t) fun history =>
    expect (G.stageActionDist profile history) fun action =>
      reward history.2 action

/-- The finite Cesàro average of a common stage reward. -/
def finiteAverageCommonReward
    (G : StochasticGame ι) [Fintype ι]
    (reward : G.State → G.JointAct → ℝ)
    (profile : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T,
      expectedCommonStageReward G reward profile s₀ t

/-- Player `who` is an affine copy of `reward`, modulo a one-step expected
state-potential coboundary. -/
def IsAffineCoboundaryDecomposition
    (G : StochasticGame ι) [Fintype ι]
    (who : ι) (coefficient offset : ℝ)
    (reward : G.State → G.JointAct → ℝ)
    (bias : G.State → ℝ) : Prop :=
  ∀ state action,
    G.stagePayoff state action who =
      coefficient * reward state action + offset + bias state -
        expect (G.transition state action) bias

/-- The local decomposition survives averaging over the current mixed action. -/
theorem stageEUAt_eq_affineCommonReward_add_coboundary
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : ι} {coefficient offset : ℝ}
    {reward : G.State → G.JointAct → ℝ} {bias : G.State → ℝ}
    (decomposition :
      IsAffineCoboundaryDecomposition G who coefficient offset reward bias)
    (profile : G.BehaviorProfile) {t : ℕ} (history : G.Hist t) :
    G.stageEUAt profile history who =
      coefficient *
          expect (G.stageActionDist profile history)
            (fun action => reward history.2 action) +
        offset + bias history.2 -
          expect (G.stageActionDist profile history) (fun action =>
            expect (G.transition history.2 action) bias) := by
  unfold GameTheory.StochasticGame.stageEUAt
  rw [show (fun action => G.stagePayoff history.2 action who) =
      (fun action =>
        coefficient * reward history.2 action + offset + bias history.2 -
          expect (G.transition history.2 action) bias) by
    funext action
    exact decomposition history.2 action]
  rw [expect_sub, expect_add, expect_add, expect_const_mul,
    expect_const, expect_const]

/-- The expected payoff identity at epoch `t`; the next-potential term is
exactly the expected state value at epoch `t+1`. -/
theorem expectedStagePayoff_eq_affineCommonReward_add_coboundary
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : ι} {coefficient offset : ℝ}
    {reward : G.State → G.JointAct → ℝ} {bias : G.State → ℝ}
    (decomposition :
      IsAffineCoboundaryDecomposition G who coefficient offset reward bias)
    (profile : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    G.expectedStagePayoff profile s₀ t who =
      coefficient * expectedCommonStageReward G reward profile s₀ t + offset +
        G.expectedStateValue profile s₀ t bias -
          G.expectedStateValue profile s₀ (t + 1) bias := by
  unfold GameTheory.StochasticGame.expectedStagePayoff expectedCommonStageReward
  rw [show (fun history => G.stageEUAt profile history who) =
      (fun history =>
        coefficient *
            expect (G.stageActionDist profile history)
              (fun action => reward history.2 action) +
          offset + bias history.2 -
            expect (G.stageActionDist profile history) (fun action =>
              expect (G.transition history.2 action) bias)) by
    funext history
    exact stageEUAt_eq_affineCommonReward_add_coboundary
      decomposition profile history]
  rw [expect_sub, expect_add, expect_add, expect_const_mul, expect_const]
  change
    coefficient *
          expect (G.histDist profile s₀ t) (fun history =>
            expect (G.stageActionDist profile history) (fun action =>
              reward history.2 action)) +
        offset + G.expectedStateValue profile s₀ t bias -
      expect (G.histDist profile s₀ t) (fun history =>
        expect (G.stageActionDist profile history) (fun action =>
          expect (G.transition history.2 action) bias)) = _
  rw [← G.expectedStateValue_succ]

/-- Pure algebraic telescope for affine coboundary sequences. -/
theorem sum_range_affine_coboundary
    (payoff objective potential : ℕ → ℝ) (coefficient offset : ℝ)
    (stage : ∀ t,
      payoff t = coefficient * objective t + offset + potential t - potential (t + 1))
    (T : ℕ) :
    (∑ t ∈ Finset.range T, payoff t) =
      coefficient * (∑ t ∈ Finset.range T, objective t) +
        (T : ℝ) * offset + potential 0 - potential T := by
  induction T with
  | zero => simp
  | succ T inductionHypothesis =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        inductionHypothesis, stage]
      push_cast
      ring

/-- Exact finite-horizon payoff sum: all intermediate potentials cancel. -/
theorem sum_expectedStagePayoff_eq_affineCommonReward_add_endpoints
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : ι} {coefficient offset : ℝ}
    {reward : G.State → G.JointAct → ℝ} {bias : G.State → ℝ}
    (decomposition :
      IsAffineCoboundaryDecomposition G who coefficient offset reward bias)
    (profile : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) :
    (∑ t ∈ Finset.range T, G.expectedStagePayoff profile s₀ t who) =
      coefficient *
          (∑ t ∈ Finset.range T,
            expectedCommonStageReward G reward profile s₀ t) +
        (T : ℝ) * offset + bias s₀ -
          G.expectedStateValue profile s₀ T bias := by
  have telescope := sum_range_affine_coboundary
    (fun t => G.expectedStagePayoff profile s₀ t who)
    (fun t => expectedCommonStageReward G reward profile s₀ t)
    (fun t => G.expectedStateValue profile s₀ t bias)
    coefficient offset
    (fun t => expectedStagePayoff_eq_affineCommonReward_add_coboundary
      decomposition profile s₀ t)
    T
  simpa using telescope

/-- Exact Cesàro identity.  No equilibrium or Markov assumption on `profile`
is used. -/
theorem finiteAveragePayoff_eq_affineCommonReward_add_boundary
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : ι} {coefficient offset : ℝ}
    {reward : G.State → G.JointAct → ℝ} {bias : G.State → ℝ}
    (decomposition :
      IsAffineCoboundaryDecomposition G who coefficient offset reward bias)
    (profile : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T profile who =
      coefficient * finiteAverageCommonReward G reward profile s₀ T + offset +
        (bias s₀ - G.expectedStateValue profile s₀ T bias) / (T : ℝ) := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    sum_expectedStagePayoff_eq_affineCommonReward_add_endpoints
      decomposition]
  unfold finiteAverageCommonReward
  have hTreal : (T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hT)
  field_simp [hTreal]
  ring

/-- A uniformly `C`-bounded bias costs at most `2 C / T`. -/
theorem abs_finiteAveragePayoff_sub_affineCommonReward_le
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : ι} {coefficient offset C : ℝ}
    {reward : G.State → G.JointAct → ℝ} {bias : G.State → ℝ}
    (decomposition :
      IsAffineCoboundaryDecomposition G who coefficient offset reward bias)
    (biasBound : ∀ state, |bias state| ≤ C)
    (profile : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) (hT : 0 < T) :
    |G.finiteAveragePayoff s₀ T profile who -
        (coefficient * finiteAverageCommonReward G reward profile s₀ T + offset)| ≤
      2 * C / (T : ℝ) := by
  have exactIdentity :=
    finiteAveragePayoff_eq_affineCommonReward_add_boundary
      decomposition profile s₀ T hT
  have endpointBound :
      |G.expectedStateValue profile s₀ T bias| ≤ C := by
    unfold GameTheory.StochasticGame.expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun history => biasBound history.2
  have numeratorBound :
      |bias s₀ - G.expectedStateValue profile s₀ T bias| ≤ 2 * C := by
    calc
      |bias s₀ - G.expectedStateValue profile s₀ T bias| ≤
          |bias s₀| + |G.expectedStateValue profile s₀ T bias| := abs_sub _ _
      _ ≤ C + C := add_le_add (biasBound s₀) endpointBound
      _ = 2 * C := by ring
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  rw [exactIdentity]
  have differenceIdentity :
      coefficient * finiteAverageCommonReward G reward profile s₀ T + offset +
            (bias s₀ - G.expectedStateValue profile s₀ T bias) / (T : ℝ) -
          (coefficient * finiteAverageCommonReward G reward profile s₀ T + offset) =
        (bias s₀ - G.expectedStateValue profile s₀ T bias) / (T : ℝ) := by
    ring
  rw [differenceIdentity, abs_div, abs_of_pos hTreal]
  exact div_le_div_of_nonneg_right numeratorBound hTreal.le

end StochasticGame

end Research.DynamicPotentialCoboundary
