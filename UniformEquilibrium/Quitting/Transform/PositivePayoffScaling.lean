import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.Game
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.Payoff.AffinePayoff

/-! # Literal positive scaling of quitting games

The identity uses zero shift at every state, including the live state. Uniform
equilibrium transport is delegated to the canonical stochastic-game affine API.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- Common scaling of the literal terminal table is zero-shift scaling of
the entire stochastic game: state, action, transition, and discount data agree. -/
theorem quittingGame_scale_eq_affinePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (scale : ℝ) :
    quittingGame (fun terminal who => scale * reward terminal who) =
      (quittingGame reward).affinePayoff scale 0 := by
  unfold quittingGame StochasticGame.affinePayoff
  congr 1
  funext state action who
  cases state <;> simp

/-- Positive scaling preserves the existence of a uniform-equilibrium payoff
from the live state. Both directions use the canonical behavioral semantics. -/
theorem quittingGame_exists_uniformPayoff_scale_iff
    [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale : ℝ) (hscale : 0 < scale) :
    (∃ payoff : Payoff ι,
      (quittingGame (fun terminal who => scale * reward terminal who)).IsUniformEquilibriumPayoff
        none payoff) ↔
      ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  have : ∀ who : ι, Finite ((quittingGame reward).Act who) :=
    fun _ => inferInstanceAs (Finite Bool)
  have hstage :
      (fun (state : Option {S : Finset ι // S.Nonempty}) (_ : ι → Bool) (who : ι) =>
        match state with
        | none => 0
        | some terminal => scale * reward terminal who) =
      (fun state action who => scale * (quittingGame reward).stagePayoff state action who +
        (0 : Payoff ι) who) := by
    funext state action who
    cases state <;> simp [quittingGame]
  have hbridge (target : Payoff ι) := congrArg
    (fun stage => ((quittingGame reward).withStagePayoff stage).IsUniformEquilibriumPayoff
      none target) hstage
  constructor
  · rintro ⟨payoff, hpayoff⟩
    have hscaled : ((quittingGame reward).affinePayoff scale 0).IsUniformEquilibriumPayoff
        none payoff := by
      exact Eq.mp (hbridge payoff) hpayoff
    exact ⟨_, (quittingGame reward).isUniformEquilibriumPayoff_of_affinePayoff
      scale hscale 0 none payoff hscaled⟩
  · rintro ⟨payoff, hpayoff⟩
    refine ⟨fun who => scale * payoff who, ?_⟩
    have hscaled : ((quittingGame reward).affinePayoff scale 0).IsUniformEquilibriumPayoff
        none (fun who => scale * payoff who) := by
      simpa only [Pi.zero_apply, add_zero] using
        ((quittingGame reward).isUniformEquilibriumPayoff_affinePayoff_iff
          scale hscale 0 none payoff).mpr hpayoff
    exact Eq.mpr (hbridge (fun who => scale * payoff who)) hscaled

end GameTheory
