/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.PositiveRhoLandingCompactLimit
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Terminal consumer for positive-rho source limits

A positive-rho compact limit retains more than local Nash--Bellman data.  Its
literal source profiles can be restarted at the crossing row with one common
positive reach floor.  The restarted global Nash errors therefore vanish,
while their actual terminal payoff vectors converge to the compact limit's
`actualTail`.  Terminal target selection makes that specified limit a uniform
equilibrium payoff.

This uses the original source root sequences and all behavioral deviations.
It does not identify consecutive limiting values, assert recurrence, or turn
the projective exact spine into an executable chronology.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual tail selected by a positive-rho compact limit is a uniform
equilibrium payoff.  The profiles are literal source suffixes, not profiles
reconstructed from the limiting Nash--Bellman rows. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.isUniformEquilibriumPayoff_actualTail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing) :
    (quittingGame reward).IsUniformEquilibriumPayoff none limit.actualTail := by
  let sourceAt := fun n ↦ landing.family.source (limit.index n)
  let profiles : ℕ → (quittingGame reward).BehaviorProfile := fun n ↦
    quittingRootSequenceProfile reward (sourceAt n).roots
      (sourceAt n).crossingStage
  have hreach : ∀ n, 0 < quittingJointSurvivalWeight
      (sourceAt n).roots 0 (sourceAt n).crossingStage := by
    intro n
    have hlower : 0 < u * landing.rho / 2 :=
      div_pos (mul_pos landing.family.u_pos landing.rho_pos) (by norm_num)
    exact hlower.trans (limit.landingAt n).2.2.1
  have hnash : ∀ n,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (limit.crossingError n)
          (profiles n) := by
    intro n
    have hshift := isεQuittingRootSequenceNash_shift_of_survival_ge
      reward (sourceAt n).roots
        (landing.family.accuracy_pos (limit.index n)).le (hreach n)
        (sourceAt n).sourceNash (sourceAt n).crossingStage le_rfl
    have hbehavior :=
      (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
        (landing.family.accuracy (limit.index n) /
          quittingJointSurvivalWeight (sourceAt n).roots 0
            (sourceAt n).crossingStage)
        (fun offset ↦ (sourceAt n).roots
          ((sourceAt n).crossingStage + offset))).mp hshift
    rw [← quittingRootSequenceProfile_eq_shift reward (sourceAt n).roots
      (sourceAt n).crossingStage] at hbehavior
    simpa [profiles, sourceAt,
      QuittingLowSurvivalPositiveRhoCompactLimit.crossingError,
      QuittingLowSurvivalPositiveRhoLandingFamily.crossingSurvival] using
        hbehavior
  have htarget : Tendsto
      (fun n ↦ quittingTerminalPayoff reward (profiles n)) atTop
        (nhds limit.actualTail) := by
    change Tendsto
      (fun n ↦ quittingRootSequenceTailVector reward
        (sourceAt n).roots (sourceAt n).crossingStage) atTop
          (nhds limit.actualTail)
    simpa [sourceAt,
      QuittingLowSurvivalPositiveRhoLandingFamily.actualTail] using
        limit.actualTail_tendsto
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    (filter := atTop) reward limit.actualTail limit.crossingError profiles
      limit.crossingError_tendsto_zero
      (Filter.Frequently.of_forall hnash) htarget

/-- Every literal positive-rho landing family selects a uniform payoff after
compactifying its actual source tails. -/
theorem
    QuittingLowSurvivalPositiveRhoLandingFamily.exists_uniformEquilibriumPayoff
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨limit⟩ :=
    exists_quittingLowSurvivalPositiveRhoCompactLimit landing
  exact ⟨limit.actualTail, limit.isUniformEquilibriumPayoff_actualTail⟩

/-- The former positive-absorption attachment residual retains the compact
source datum that already selects its actual-tail uniform payoff. -/
theorem
    QuittingLowSurvivalPositiveAbsorptionAttachmentResidual.isUniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (residual :
      QuittingLowSurvivalPositiveAbsorptionAttachmentResidual reward u) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      residual.base.actualTail :=
  residual.base.isUniformEquilibriumPayoff_actualTail

/-- At actual source scope, the low-survival compact-scale arm has only the
checked instant-punishment producer or a uniform-payoff output. -/
theorem instantPunishment_or_uniformPayoff_of_lowSurvivalPrefixes
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {u : ℝ} (hu : 0 < u) (huOne : u < 1)
    (hlow : HasLowSurvivalPrefixesAtCompactScales reward u) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases
      instantPunishmentExistence_or_positiveRhoLandingFamily_of_lowSurvivalPrefixes
        reward hu huOne hlow with hinstant | hlanding
  · exact Or.inl hinstant
  · obtain ⟨landing⟩ := hlanding
    exact Or.inr landing.exists_uniformEquilibriumPayoff

end GameTheory
