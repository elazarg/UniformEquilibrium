import UniformEquilibrium.Certificates.Adaptive.WeightedSecurityWelfareAssembly
import UniformEquilibrium.Certificates.Adaptive.PhaseLiftedWelfareCap
import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality

/-!
# Equivariant security--welfare assembly for quitting games

A transitive group of player relabelings transports one one-sided security
certificate to every player when it preserves the terminal reward table and
target payoff.  A positive weighted welfare cap then assembles a
uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {Player Gamma : Type}
  [Fintype Player] [DecidableEq Player]
  [Group Gamma] [MulAction Gamma Player]
  [MulAction.IsPretransitive Gamma Player]

/-- One representative security certificate suffices for a transitive
quitting-table symmetry.  The hypotheses explicitly require invariance of the
reward table and target; an abstract player action alone is not enough. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_transitive_rewardSymmetry
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (weight : Player → ℝ) (target : Payoff Player)
    (weight_pos : ∀ player, 0 < weight player)
    (reward_invariant : ∀ g : Gamma,
      quittingRewardReindex (MulAction.toPerm g) reward = reward)
    (target_invariant : ∀ (g : Gamma) (player : Player),
      target (g • player) = target player)
    (representative : Player)
    (representativeSecurity :
      (quittingGame reward).IsOneSidedGuaranteeCertificate none representative
        (target representative))
    (welfareCap : HasUniformWeightedWelfareCap
      (quittingGame reward) none weight target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply isUniformEquilibriumPayoff_of_transitiveSecurity_of_welfareCap
    (G := quittingGame reward) (Gamma := Gamma) (s₀ := none)
    (weight := weight) (v := target) weight_pos representative
  · intro g
    have htransport := isOneSidedGuaranteeCertificate_reindex
      (MulAction.toPerm g) reward representative (target representative)
        representativeSecurity
    rw [reward_invariant g] at htransport
    rw [target_invariant g representative]
    exact htransport
  · exact welfareCap

/-- A phase-dependent Bellman welfare bias supplies the welfare-cap input of
the equivariant quitting-game assembly theorem. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_transitive_rewardSymmetry_of_phaseBias
    {P : ℕ} [NeZero P]
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (weight : Player → ℝ) (target : Payoff Player)
    (weight_pos : ∀ player, 0 < weight player)
    (reward_invariant : ∀ g : Gamma,
      quittingRewardReindex (MulAction.toPerm g) reward = reward)
    (target_invariant : ∀ (g : Gamma) (player : Player),
      target (g • player) = target player)
    (representative : Player)
    (representativeSecurity :
      (quittingGame reward).IsOneSidedGuaranteeCertificate none representative
        (target representative))
    (phaseBias : HasPhaseWeightedWelfareBias (P := P)
      (quittingGame reward) weight target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_transitive_rewardSymmetry
    weight target weight_pos reward_invariant target_invariant representative
      representativeSecurity
  exact hasUniformWeightedWelfareCap_of_hasPhaseWeightedWelfareBias
    (P := P) (quittingGame reward) none weight target phaseBias

end GameTheory
