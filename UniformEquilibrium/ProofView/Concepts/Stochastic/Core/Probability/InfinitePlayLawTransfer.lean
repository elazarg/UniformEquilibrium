import Mathlib.Probability.Process.FiniteDimensionalLaws
import MathUE.ProbabilityMassFunction
import UniformEquilibrium.ProofView.Concepts.Stochastic.Core.Probability.InfinitePlayMeasure

/-!
# Supported-action-law transfer

Two behavioral profiles need only choose the same joint-action law at histories
supported by the first profile. This one-sided agreement identifies their
finite history laws and, when agreement holds at every time, their actual
infinite-play measures. No reward, equilibrium, or Markov assumption is used.
-/

noncomputable section

namespace GameTheory.StochasticGame

open MeasureTheory

variable {ι : Type} (G : StochasticGame ι) [Fintype ι]

/-- Supported joint-action-law agreement before a horizon identifies all history laws through it. -/
theorem histDist_eq_of_stageActionDist_eq_on_support
    {left right : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
    (hagree : ∀ time (history : G.Hist time), time < fuel →
      history ∈ (G.histDist left initial time).support →
        G.stageActionDist left history = G.stageActionDist right history) :
    ∀ time, time ≤ fuel → G.histDist left initial time = G.histDist right initial time := by
  intro time htime
  induction time with
  | zero => rfl
  | succ time ih =>
      have hbefore : time < fuel := by omega
      rw [G.histDist_succ, G.histDist_succ, ← ih (Nat.le_of_lt hbefore)]
      apply Math.ProbabilityMassFunction.bind_congr_on_support
      intro history hhistory
      rw [hagree time history hbefore hhistory]

/-- Agreement on supported joint-action laws at every time identifies every history law. -/
theorem histDist_eq_of_stageActionDist_eq_on_support_allTime
    {left right : G.BehaviorProfile} {initial : G.State}
    (hagree : ∀ time (history : G.Hist time),
      history ∈ (G.histDist left initial time).support →
        G.stageActionDist left history = G.stageActionDist right history) (time : ℕ) :
    G.histDist left initial time = G.histDist right initial time :=
  G.histDist_eq_of_stageActionDist_eq_on_support
    (fun time history _ hhistory => hagree time history hhistory) time le_rfl

private theorem coordsDist_eq_of_stageActionDist_eq_on_support
    {left right : G.BehaviorProfile} {initial : G.State}
    (hagree : ∀ time (history : G.Hist time),
      history ∈ (G.histDist left initial time).support →
        G.stageActionDist left history = G.stageActionDist right history) (time : ℕ) :
    G.coordsDist left initial time = G.coordsDist right initial time := by
  rw [G.coordsDist_eq_histDist_bind, G.coordsDist_eq_histDist_bind,
    ← G.histDist_eq_of_stageActionDist_eq_on_support_allTime hagree time]
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro history hhistory
  rw [hagree time history hhistory]

/-- All-time supported joint-action-law agreement identifies the actual infinite-play measures. -/
theorem infinitePlayMeasure_eq_of_stageActionDist_eq_on_support
    [Countable G.State] [∀ who, Countable (G.Act who)]
    {left right : G.BehaviorProfile} {initial : G.State}
    (hagree : ∀ time (history : G.Hist time),
      history ∈ (G.histDist left initial time).support →
        G.stageActionDist left history = G.stageActionDist right history) :
    G.infinitePlayMeasure left initial = G.infinitePlayMeasure right initial := by
  let μ := G.infinitePlayMeasure left initial
  let family (indices : Finset ℕ) : Measure ((index : indices) → G.StageOutcome) :=
    μ.map indices.restrict
  have hfamily : IsProjectiveMeasureFamily (α := fun _ : ℕ => G.StageOutcome) family :=
    ProbabilityTheory.isProjectiveMeasureFamily_map_restrict
      (P := μ) (X := fun time (play : G.Play) => play time)
      (fun time => (measurable_pi_apply time).aemeasurable)
  let (indices : Finset ℕ) : IsFiniteMeasure (family indices) := by
    dsimp [family, μ]
    infer_instance
  have hleft : IsProjectiveLimit μ family := fun _ => rfl
  have hright : IsProjectiveLimit (G.infinitePlayMeasure right initial) family := by
    apply (isProjectiveLimit_nat_iff hfamily _).mpr
    intro time
    change (G.infinitePlayMeasure right initial).map
        (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) time) =
      (G.infinitePlayMeasure left initial).map
        (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) time)
    rw [G.map_frestrictLe_infinitePlayMeasure, G.map_frestrictLe_infinitePlayMeasure,
      G.coordsDist_eq_of_stageActionDist_eq_on_support hagree time]
  exact hleft.unique hright

end GameTheory.StochasticGame
