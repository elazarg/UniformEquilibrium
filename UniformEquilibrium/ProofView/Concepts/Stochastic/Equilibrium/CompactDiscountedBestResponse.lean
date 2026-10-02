import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.Compact
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted

/-!
# Compact-to-behavioral discounted best-response attainment

An exact compact unilateral presentation supplies an actual behavioral
best response. Both transfers keep the actual opponents fixed and cover
every full behavioral deviation. The maximizer is selected internally by
the standard extreme-value theorem, not supplied as a premise.
-/

namespace GameTheory.StochasticGame

/-- Transfer an internally selected compact payoff maximizer to an actual
full behavioral best response against fixed behavioral opponents. -/
theorem exists_discountedBestResponse_of_compact_transfer
    {ι : Type} {X : Type*} (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (β : ℝ) (initial : G.State) (profile : G.BehaviorProfile) (who : ι)
    (value : C(X, ℝ)) (encode : G.BehaviorStrategy who → X)
    (decode : X → G.BehaviorStrategy who)
    (hencode : ∀ deviation, value (encode deviation) =
      G.discountedPayoff β (Function.update profile who deviation) initial who)
    (hdecode : ∀ candidate,
      G.discountedPayoff β (Function.update profile who (decode candidate)) initial who =
        value candidate) :
    ∃ deviation : G.BehaviorStrategy who, ∀ alternative : G.BehaviorStrategy who,
      G.discountedPayoff β (Function.update profile who alternative) initial who ≤
        G.discountedPayoff β (Function.update profile who deviation) initial who := by
  obtain ⟨candidate, _, hmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty value.continuous.continuousOn
  refine ⟨decode candidate, ?_⟩
  intro alternative
  rw [hdecode, ← hencode]
  exact hmax (Set.mem_univ (encode alternative))

end GameTheory.StochasticGame
