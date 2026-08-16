import UniformEquilibrium.Certificates.Adaptive.WeightedSecurityWelfareAssembly
import Mathlib

/-!
# Finite-group invariant welfare weights

This independent experiment checks the Reynolds-sum algebra from
`ideas/FiniteGroupInvariantWeights.md`.

Orbit-summing a player weight makes it invariant.  Strict positivity is
preserved, and a family of inequalities for all translated weights sums to
the corresponding inequality for the invariant orbit weight.
-/

noncomputable section

namespace Research.FiniteGroupInvariantWeights

open scoped BigOperators

variable {Gamma Player : Type}
  [Group Gamma] [Fintype Gamma] [MulAction Gamma Player]

/-- Unnormalized Reynolds sum of a player weight. -/
def orbitWeight (weight : Player → ℝ) (player : Player) : ℝ :=
  ∑ g : Gamma, weight (g • player)

/-- Right translation permutes the finite group, so the orbit weight is
invariant under the player action. -/
theorem orbitWeight_smul (weight : Player → ℝ)
    (h : Gamma) (player : Player) :
    orbitWeight (Gamma := Gamma) weight (h • player) =
      orbitWeight (Gamma := Gamma) weight player := by
  simpa [orbitWeight, mul_smul] using
    Fintype.sum_bijective (fun g : Gamma => g * h)
      (Group.mulRight_bijective h)
      (fun g => weight (g • (h • player)))
      (fun g => weight (g • player)) (by simp [mul_smul])

/-- A finite orbit sum of a strictly positive weight is strictly positive. -/
theorem orbitWeight_pos (weight : Player → ℝ)
    (weight_pos : ∀ player, 0 < weight player) (player : Player) :
    0 < orbitWeight (Gamma := Gamma) weight player := by
  unfold orbitWeight
  apply Finset.sum_pos'
  · intro g g_mem
    exact (weight_pos (g • player)).le
  · exact ⟨1, Finset.mem_univ 1, weight_pos (1 • player)⟩

variable [Fintype Player]

/-- Weighted evaluation of a player-indexed vector. -/
def weightedValue (weight value : Player → ℝ) : ℝ :=
  ∑ player, weight player * value player

/-- Evaluation at the Reynolds-summed weight is the sum of evaluations at
all translated weights. -/
theorem weightedValue_orbitWeight (weight value : Player → ℝ) :
    weightedValue (orbitWeight (Gamma := Gamma) weight) value =
      ∑ g : Gamma,
        weightedValue (fun player => weight (g • player)) value := by
  simp only [weightedValue, orbitWeight, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Summing one cap for each translated weight gives the cap for the
invariant orbit weight. -/
theorem weightedValue_orbitWeight_le
    (weight value target : Player → ℝ) (error : ℝ)
    (translatedCaps : ∀ g : Gamma,
      weightedValue (fun player => weight (g • player)) value ≤
        weightedValue (fun player => weight (g • player)) target + error) :
    weightedValue (orbitWeight (Gamma := Gamma) weight) value ≤
      weightedValue (orbitWeight (Gamma := Gamma) weight) target +
        Fintype.card Gamma * error := by
  rw [weightedValue_orbitWeight, weightedValue_orbitWeight]
  calc
    (∑ g : Gamma,
        weightedValue (fun player => weight (g • player)) value) ≤
        ∑ g : Gamma,
          (weightedValue (fun player => weight (g • player)) target +
            error) :=
      Finset.sum_le_sum fun g _ => translatedCaps g
    _ = (∑ g : Gamma,
          weightedValue (fun player => weight (g • player)) target) +
        Fintype.card Gamma * error := by
      rw [Finset.sum_add_distrib]
      simp

/-! ## Semantic uniform-cap assembly -/

open GameTheory

variable {G : StochasticGame Player}
  [Finite G.State] [∀ player, Finite (G.Act player)]

/-- A uniform welfare cap for every translated weight combines into a cap for
the positive invariant orbit weight.  The missing game-facing input is the
transport theorem that produces `translatedCaps` from one cap. -/
theorem hasUniformWeightedWelfareCap_orbitWeight
    (s₀ : G.State) (weight : Player → ℝ) (target : Payoff Player)
    (translatedCaps : ∀ g : Gamma,
      GameTheory.StochasticGame.HasUniformWeightedWelfareCap
        G s₀ (fun player => weight (g • player)) target) :
    GameTheory.StochasticGame.HasUniformWeightedWelfareCap
      G s₀ (orbitWeight (Gamma := Gamma) weight) target := by
  classical
  intro error error_pos
  have card_pos_nat : 0 < Fintype.card Gamma := Fintype.card_pos
  have card_pos_real : (0 : ℝ) < Fintype.card Gamma := by
    exact_mod_cast card_pos_nat
  let translatedError : ℝ := error / Fintype.card Gamma
  have translatedError_pos : 0 < translatedError :=
    div_pos error_pos card_pos_real
  have capAt : ∀ g : Gamma, ∃ horizon : ℕ,
      ∀ (profile : G.BehaviorProfile) (T : ℕ), horizon ≤ T →
        weightedValue (fun player => weight (g • player))
            (fun player => G.finiteAveragePayoff s₀ T profile player) ≤
          weightedValue (fun player => weight (g • player)) target +
            translatedError := by
    intro g
    simpa only [weightedValue] using
      translatedCaps g translatedError translatedError_pos
  choose horizon cap using capAt
  let commonHorizon : ℕ := Finset.univ.sup horizon
  refine ⟨commonHorizon, fun profile T T_ge => ?_⟩
  have eachCap : ∀ g : Gamma,
      weightedValue (fun player => weight (g • player))
          (fun player => G.finiteAveragePayoff s₀ T profile player) ≤
        weightedValue (fun player => weight (g • player)) target +
          translatedError := by
    intro g
    apply cap g profile T
    exact (Finset.le_sup (s := Finset.univ) (f := horizon)
      (Finset.mem_univ g)).trans T_ge
  have summed := weightedValue_orbitWeight_le
    (Gamma := Gamma) weight
    (fun player => G.finiteAveragePayoff s₀ T profile player)
    target translatedError eachCap
  have error_eq : (Fintype.card Gamma : ℝ) * translatedError = error := by
    dsimp only [translatedError]
    exact mul_div_cancel₀ error card_pos_real.ne'
  simpa only [weightedValue, error_eq] using summed

end Research.FiniteGroupInvariantWeights
