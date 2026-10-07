import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.Game
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Asymptotic.LiminfAverageBridge
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Expected pathwise limiting payoff of a recursive absorption game

The payoff is the expectation of the pathwise liminf of stage averages under
the actual infinite-play measure. Every behavioral profile, including every
unilateral deviation, produces paths which stay forever at the live zero-payoff
state or eventually stay at one absorbing payoff state. Hence the pathwise
averages converge almost surely, and dominated convergence identifies their
expected limit with the limit of finite-average payoffs.

This is a specialization to the canonical recursive absorption model, not an
unconditional interchange of expectation and liminf for arbitrary games.
Absorption probabilities may be zero, and the initial state is arbitrary.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

namespace GameTheory.RecursiveAbsorption

variable {I J : Type} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
/-- A supported one-stage extension cannot leave an absorbing payoff state. -/
private theorem supported_history_succ_absorber (D : Data I J)
    (σ : (game D).BehaviorProfile) (initial : (game D).State) (n : ℕ)
    (history : (game D).Hist (n + 1))
    (hsupport : history ∈ ((game D).histDist σ initial (n + 1)).support)
    (pair : I × J) (habsorbed : (history.1 (Fin.last n)).1 = some pair) :
    history.2 = some pair := by
  obtain ⟨previous, -, action, -, next, hnext, rfl⟩ :=
    ((game D).mem_support_histDist_succ σ initial n history).mp hsupport
  simp only [Fin.snoc_last] at habsorbed
  rw [habsorbed, transition_some] at hnext
  change next ∈ (PMF.pure (some pair) : PMF (Option (I × J))).support at hnext
  exact (PMF.mem_support_pure_iff _ _).mp hnext

/-- Almost every actual play remains in a payoff state once it has reached that state. -/
theorem ae_absorber_persists (D : Data I J) (σ : (game D).BehaviorProfile)
    (initial : (game D).State) :
    ∀ᵐ play ∂(game D).infinitePlayMeasure σ initial,
      ∀ n (pair : I × J), (play n).1 = some pair → (play (n + 1)).1 = some pair := by
  classical
  have hsupport : ∀ n, ∀ᵐ history ∂((game D).histDist σ initial n).toMeasure,
      history ∈ ((game D).histDist σ initial n).support := by
    intro n
    rw [ae_iff]
    apply (PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete).2
    exact Set.disjoint_left.mpr fun _ hmem hnot => hnot hmem
  have hplay : ∀ n, ∀ᵐ play ∂(game D).infinitePlayMeasure σ initial,
      (game D).histOfPlay n play ∈ ((game D).histDist σ initial n).support := by
    intro n
    apply ae_of_ae_map ((game D).measurable_histOfPlay n).aemeasurable
    rw [(game D).map_histOfPlay_infinitePlayMeasure]
    exact hsupport n
  filter_upwards [ae_all_iff.mpr hplay] with play hplay
  intro n pair habsorbed
  exact supported_history_succ_absorber D σ initial n
    ((game D).histOfPlay (n + 1) play) (hplay (n + 1)) pair
    (by
      change (play n).1 = some pair
      exact habsorbed)

omit [Fintype I] [Fintype J] in
/-- Absorber persistence alone makes the realized recursive payoff averages converge. -/
private theorem exists_pathwiseAveragePayoff_limit (D : Data I J)
    (play : (game D).Play)
    (hpersist : ∀ n (pair : I × J),
      (play n).1 = some pair → (play (n + 1)).1 = some pair) (who : Bool) :
    ∃ value : ℝ, Tendsto (fun n => (game D).pathwiseAveragePayoff who n play)
      atTop (𝓝 value) := by
  classical
  let stage : ℕ → ℝ := fun n => (game D).stagePayoff (play n).1 (play n).2 who
  have haverage : ∀ n, (game D).pathwiseAveragePayoff who n play =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, stage k := by
    intro n
    change (n : ℝ)⁻¹ * (∑ k : Fin n, stage k.1) = _
    exact congrArg (fun value : ℝ => (n : ℝ)⁻¹ * value)
      (Fin.sum_univ_eq_sum_range stage n)
  by_cases hlive : ∀ n, (play n).1 = none
  · have hstage : stage = fun _ => 0 := by
      funext n
      simp [stage, hlive n]
    refine ⟨0, ?_⟩
    simp only [haverage, hstage, Finset.sum_const_zero, mul_zero]
    exact tendsto_const_nhds
  · obtain ⟨time, htime⟩ := not_forall.mp hlive
    cases hstate : (play time).1 with
    | none => exact (htime hstate).elim
    | some pair =>
      have htail : ∀ offset, (play (time + offset)).1 = some pair := by
        intro offset
        induction offset with
        | zero => simpa using hstate
        | succ offset ih =>
          simpa only [Nat.add_succ] using hpersist (time + offset) pair ih
      have hevent : stage =ᶠ[atTop] fun _ => D.reward pair.1 pair.2 who := by
        filter_upwards [eventually_ge_atTop time] with n hn
        obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hn
        simp [stage, htail offset]
      have hstage : Tendsto stage atTop (𝓝 (D.reward pair.1 pair.2 who)) :=
        tendsto_const_nhds.congr' hevent.symm
      refine ⟨D.reward pair.1 pair.2 who, ?_⟩
      simpa only [haverage] using hstage.cesaro

/-- Every actual behavioral profile has almost-sure convergence of its pathwise averages. -/
theorem ae_tendsto_pathwiseAveragePayoff_liminf (D : Data I J)
    (σ : (game D).BehaviorProfile) (initial : (game D).State) (who : Bool) :
    ∀ᵐ play ∂(game D).infinitePlayMeasure σ initial,
      Tendsto (fun n => (game D).pathwiseAveragePayoff who n play) atTop
        (𝓝 (liminf (fun n => (game D).pathwiseAveragePayoff who n play) atTop)) := by
  filter_upwards [ae_absorber_persists D σ initial] with play hpersist
  obtain ⟨value, hvalue⟩ := exists_pathwiseAveragePayoff_limit D play hpersist who
  simpa only [hvalue.liminf_eq] using hvalue

/-- Literal expected pathwise liminf payoff under the actual infinite-play law. -/
def liminfPayoff (D : Data I J) (initial : (game D).State)
    (σ : (game D).BehaviorProfile) (who : Bool) : ℝ :=
  ∫ play, liminf (fun n => (game D).pathwiseAveragePayoff who n play) atTop
    ∂(game D).infinitePlayMeasure σ initial

/-- Finite-average payoffs converge to expected pathwise liminf for every actual profile. -/
theorem tendsto_finiteAveragePayoff_liminfPayoff (D : Data I J)
    (σ : (game D).BehaviorProfile) (initial : (game D).State) (who : Bool) :
    Tendsto (fun n => (game D).finiteAveragePayoff initial n σ who) atTop
      (𝓝 (liminfPayoff D initial σ who)) := by
  classical
  obtain ⟨C, hC⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun pair : I × J => D.reward pair.1 pair.2 who)
  have hstage : ∀ state action, |(game D).stagePayoff state action who| ≤ max C 0 := by
    intro state action
    cases state with
    | none => simp
    | some pair => exact (hC pair).trans (le_max_left C 0)
  have hbounded := (game D).abs_pathwiseAveragePayoff_le who (le_max_right C 0) hstage
  have hlimit := tendsto_integral_of_dominated_convergence
    (μ := (game D).infinitePlayMeasure σ initial) (fun _ => max C 0)
    (fun n => ((game D).measurable_pathwiseAveragePayoff who n).aestronglyMeasurable)
    (integrable_const (max C 0))
    (fun n => ae_of_all _ fun play => by simpa using hbounded n play)
    (ae_tendsto_pathwiseAveragePayoff_liminf D σ initial who)
  simpa only [StochasticGame.integral_pathwiseAveragePayoff, liminfPayoff] using hlimit

end GameTheory.RecursiveAbsorption
