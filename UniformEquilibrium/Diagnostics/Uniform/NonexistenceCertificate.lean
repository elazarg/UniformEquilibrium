/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Uniform

/-!
# Late-horizon certificates for failure of uniform-equilibrium existence

The direct certificate asks for one positive exploitability gap at arbitrarily
late horizons, uniformly over the proposed behavior profile.  The player and
the unilateral deviation may depend on both the profile and the horizon.  This
is enough because a uniform approximate equilibrium must control every
deviation at every horizon beyond one common threshold.
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every behavior profile is exploitable by at least `gap` at arbitrarily
late finite horizons.  The witness player and deviation may depend on the
horizon. -/
def HasArbitrarilyLateExploitabilityGap
    (G : StochasticGame ι) (s₀ : G.State) (gap : ℝ) : Prop :=
  ∀ σ : G.BehaviorProfile, ∀ threshold : ℕ,
    ∃ (horizon : ℕ) (who : ι) (dev : G.BehaviorStrategy who),
      threshold ≤ horizon ∧
        G.finiteAveragePayoff s₀ horizon σ who + gap ≤
          G.finiteAveragePayoff s₀ horizon
            (Function.update σ who dev) who

/-- A uniform positive late-horizon exploitability gap rules out every
uniform-equilibrium payoff.  Applying the purported uniform payoff at
accuracy `gap / 2` makes the weak gain bound strictly incompatible with its
Nash inequality. -/
theorem not_exists_uniformEquilibriumPayoff_of_arbitrarilyLateExploitabilityGap
    (G : StochasticGame ι) (s₀ : G.State) {gap : ℝ}
    (hgap : 0 < gap)
    (hexploit : G.HasArbitrarilyLateExploitabilityGap s₀ gap) :
    ¬ ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  rintro ⟨v, hv⟩
  have hhalf : 0 < gap / 2 := by linarith
  obtain ⟨σ, threshold, huniform⟩ := hv (gap / 2) hhalf
  obtain ⟨horizon, who, dev, hhorizon, hexploit'⟩ :=
    hexploit σ threshold
  have hnash := (huniform horizon hhorizon).1 who dev
  linarith

end StochasticGame

end GameTheory
