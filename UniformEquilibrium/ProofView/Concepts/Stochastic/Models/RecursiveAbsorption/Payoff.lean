import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.Game
import UniformEquilibrium.ProofView.Concepts.Stochastic.Classes.ActionIndependentAbsorptionPayoff

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

/-- Almost every actual play remains in a payoff state once it has reached that state. -/
theorem ae_absorber_persists (D : Data I J) (σ : (game D).BehaviorProfile)
    (initial : (game D).State) :
    ∀ᵐ play ∂(game D).infinitePlayMeasure σ initial,
      ∀ n (pair : I × J), (play n).1 = some pair → (play (n + 1)).1 = some pair := by
  filter_upwards [(game D).ae_isAbsorbingState_persists σ initial] with play hpersist
  intro n pair habsorbed
  have hAbs : (game D).IsAbsorbingState (play n).1 := by
    rw [habsorbed]
    exact isAbsorbingState_some D pair
  exact (hpersist n hAbs).trans habsorbed

/-- Every actual behavioral profile has almost-sure convergence of its pathwise averages. -/
theorem ae_tendsto_pathwiseAveragePayoff_liminf (D : Data I J)
    (σ : (game D).BehaviorProfile) (initial : (game D).State) (who : Bool) :
    ∀ᵐ play ∂(game D).infinitePlayMeasure σ initial,
      Tendsto (fun n => (game D).pathwiseAveragePayoff who n play) atTop
        (𝓝 (liminf (fun n => (game D).pathwiseAveragePayoff who n play) atTop)) := by
  apply (game D).ae_tendsto_pathwiseAveragePayoff_liminf_of_actionIndependent_singleLive
    none ?_ who ?_ σ initial
  · intro state hstate
    cases state with
    | none => exact (hstate rfl).elim
    | some pair => exact isAbsorbingState_some D pair
  · intro state first second
    rfl

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
  simpa only [liminfPayoff] using
    (game D).tendsto_finiteAveragePayoff_integral_liminf_of_ae_tendsto σ initial who
      (ae_tendsto_pathwiseAveragePayoff_liminf D σ initial who)

end GameTheory.RecursiveAbsorption
