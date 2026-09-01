/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.ExceptionalOwnerPrefixConcentration
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedPriorityRegimes

/-!
# Final source boundary of the corrected stationarily generated branch

After fixed horizons and vanishing live mass are routed to S.2, the remaining
positive-live family has divergent horizons.  The existing deleted-clock
split then yields S.1, S.3, a positive-reach endpoint, or one exceptional
owner.  Consuming the sure-exit and nonnegative-solo cases leaves exactly two
literal residuals: a no-sure-exit punishment endpoint, or a divergent
exceptional owner with negative singleton self-payoff.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- The exact exceptional-owner residual after horizon divergence and the
nonnegative singleton stationary repair have both been consumed. -/
structure QuittingDivergentNegativeExceptionalOwnerResidual
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota) where
  source : QuittingUniqueExceptionalOwnerSource reward
  horizon_tendsto : Tendsto
    (fun n ↦ source.family.horizon (source.selected n)) atTop atTop
  solo_self_neg :
    quittingSoloReward reward source.owner source.owner < 0

/-- **Corrected-Simon source capstone.**  A diffuse stationarily generated
family yields one of the three AKRS branches, the finite-dimensional
positive-reach no-sure-exit residual, or a divergent exceptional owner whose
singleton self-payoff is strictly negative. -/
theorem stationary_or_instant_or_wellSupported_or_noSureExit_or_negativeOwner
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria
      reward) :
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward ∨
          Nonempty
              (QuittingPositiveJointPrefixReachNoSureExitResidual reward) ∨
            Nonempty
              (QuittingDivergentNegativeExceptionalOwnerResidual reward) := by
  rcases
      instant_or_positiveJointNoSureExitResidual_or_positiveLive_divergentHorizon
        hgenerated with hinstant | hnoSureExit | hdivergent
  · exact Or.inr (Or.inl hinstant)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hnoSureExit)))
  · obtain ⟨family, subsequence, punished, liveLimit, hsubsequence,
        hpunished, hlivePositive, hlive, hhorizon⟩ := hdivergent
    rcases
        stationary_or_wellSupported_or_divergentPositiveJoint_or_divergentExceptional
          family subsequence punished liveLimit hsubsequence hpunished
            hlivePositive hlive hhorizon with
      hstationary | hwellSupported | hpositive | hexceptional
    · exact Or.inl hstationary
    · exact Or.inr (Or.inr (Or.inl hwellSupported))
    · obtain ⟨source, _hsourceHorizon⟩ := hpositive
      rcases source.instantPunishment_or_noSureExitResidual with
        hinstant | hnoSureExit
      · exact Or.inr (Or.inl hinstant)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hnoSureExit)))
    · obtain ⟨source, hsourceHorizon⟩ := hexceptional
      rcases source.stationary_or_negativeSolo hsourceHorizon with
        hstationary | hnegative
      · exact Or.inl hstationary
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨source,
          hsourceHorizon, hnegative⟩⟩)))

end GameTheory
