import UniformEquilibrium.Certificates.Adaptive.WeightedSecurityWelfareAssembly
import Mathlib.Algebra.Group.Action.Pretransitive

/-!
# Equivariant coalition-split assembly

This is the coalition-specific composition experiment promised by
`ideas/CoalitionSplittingGroupActions.md`.

For a transitive player action, one singleton-split security certificate and
an explicit transport law supply security for every player.  Given the
production welfare-cap predicate, the landed positive weighted
security--welfare theorem then assembles a uniform-equilibrium payoff.  The
independent `PhaseLiftedWelfareCap.lean` experiment proves that a periodic
social bias supplies exactly this predicate.

The transport law is deliberately an assumption: this experiment does not
pretend that an abstract action on players is already an automorphism of the
game's states, dependent actions, transition kernel, and payoffs.
-/

noncomputable section

namespace Experiments.CoalitionEquivariantAssembly

open GameTheory

variable {Player Gamma : Type}
  [Fintype Player] [DecidableEq Player] [Nonempty Player]
  [Group Gamma] [MulAction Gamma Player]
  [MulAction.IsPretransitive Gamma Player]

variable {G : StochasticGame Player}
  [Finite G.State] [∀ player, Finite (G.Act player)]

/-- **Transitive equivariant coalition-split assembly.**

The representative certificate is the usable output of one
singleton-versus-complement split.  `transportSecurity` is the exact missing
game-automorphism adapter.  The supplied policy-universal welfare ceiling and
transported security certificates are precisely the hypotheses of the
production assembly theorem. -/
theorem isUniformEquilibriumPayoff_of_transitive_splitSecurity_of_welfareCap
    (s₀ : G.State) (weight : Player → ℝ) (target : Payoff Player)
    (weight_pos : ∀ player, 0 < weight player)
    (representative : Player)
    (representativeSecurity :
      G.IsOneSidedGuaranteeCertificate s₀ representative
        (target representative))
    (transportSecurity : ∀ (g : Gamma) (player : Player),
      G.IsOneSidedGuaranteeCertificate s₀ player (target player) →
      G.IsOneSidedGuaranteeCertificate s₀ (g • player)
        (target (g • player)))
    (welfareCap :
      GameTheory.StochasticGame.HasUniformWeightedWelfareCap
        G s₀ weight target) :
    G.IsUniformEquilibriumPayoff s₀ target := by
  have security : ∀ player,
      G.IsOneSidedGuaranteeCertificate s₀ player (target player) :=
    fun player => by
      obtain ⟨g, moved⟩ :=
        MulAction.IsPretransitive.exists_smul_eq (M := Gamma)
          representative player
      rw [← moved]
      exact transportSecurity g representative representativeSecurity
  exact GameTheory.StochasticGame.isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_positiveWeightedWelfareCap
    G s₀ weight target weight_pos security welfareCap

end Experiments.CoalitionEquivariantAssembly
