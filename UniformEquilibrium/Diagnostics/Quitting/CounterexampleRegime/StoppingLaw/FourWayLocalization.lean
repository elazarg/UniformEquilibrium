/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ObserverAbsent.ForcedOwnerDispatch
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ReachedRowDebtLocalization

/-!
# Four-way localization of a quitting counterexample

A rectangle terminal that contains its observer enters one of two signed
actual-row branches. A negative observer reward gives the source-row atomic
dispatch. A positive observer reward gives the target-row reached-debt
localization. The rectangle atom rules out zero reward, and neither route
requires a lower bound on the terminal cardinality.

Consequently, one counterexample regime and one of its stopping-law frontiers
admit four exhaustive branches: prescribed comparison, observer absence,
negative observer-containing target, or positive observer-containing target.
The branch data is a consequence of nonexistence; no converse is asserted.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The four provenance-preserving outputs of stopping-law localization:
prescribed comparison, observer absence, a negative observer-containing row,
or a positive observer-containing row. -/
def HasQuittingStoppingLawFourWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) : Prop :=
  Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
    (∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
      packet.observer ∉ packet.terminal.val ∧
        HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch packet
          (quittingStoppingLawObserverAbsentMassLower packet)) ∨
    (∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
      packet.observer ∈ packet.terminal.val ∧
        reward packet.terminal packet.observer < 0 ∧
        HasQuittingStoppingLawNegativeTargetAtomicDispatch packet
          (quittingStoppingLawNegativeTargetMassLower packet)) ∨
    ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
      packet.observer ∈ packet.terminal.val ∧
        0 < reward packet.terminal packet.observer ∧
        HasQuittingStoppingLawPositiveTargetReachedRowLocalization packet
          ((packet.charge / 4) /
            ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
              quittingRewardBound reward))

/-- An observer-containing rectangle packet enters its negative source-row
dispatch or its positive target-row localization. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerContaining_signedRowElimination
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hobserver : packet.observer ∈ packet.terminal.val) :
    (reward packet.terminal packet.observer < 0 ∧
        HasQuittingStoppingLawNegativeTargetAtomicDispatch packet
          (quittingStoppingLawNegativeTargetMassLower packet)) ∨
      (0 < reward packet.terminal packet.observer ∧
        HasQuittingStoppingLawPositiveTargetReachedRowLocalization packet
          ((packet.charge / 4) /
            ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
              quittingRewardBound reward))) := by
  classical
  by_cases hpositive : 0 < reward packet.terminal packet.observer
  · exact Or.inr ⟨hpositive,
      packet.positiveTarget_reachedRowLocalization hobserver hpositive⟩
  · have hnegative : reward packet.terminal packet.observer < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpositive) packet.reward_ne_zero
    exact Or.inl ⟨hnegative,
      packet.negativeTarget_atomicDispatch hobserver hnegative⟩

namespace QuittingCounterexampleStoppingLawFrontier

/-- Every stopping-law frontier has the cardinality-free four-way
localization. -/
theorem fourWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    HasQuittingStoppingLawFourWayLocalization frontier := by
  classical
  rcases frontier.exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence
      with hprescribed | hrectangle
  · exact Or.inl hprescribed
  · obtain ⟨packet⟩ := hrectangle
    by_cases hobserver : packet.observer ∈ packet.terminal.val
    · rcases packet.observerContaining_signedRowElimination hobserver with
        hnegative | hpositive
      · exact Or.inr (Or.inr (Or.inl ⟨packet, hobserver, hnegative⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨packet, hobserver, hpositive⟩))
    · exact Or.inr (Or.inl
        ⟨packet, hobserver,
          packet.observerAbsent_forcedOwnerDispatch hobserver⟩)

end QuittingCounterexampleStoppingLawFrontier

/-- A counterexample regime supplies a four-way localization on one of its
stopping-law frontiers. -/
theorem QuittingCounterexampleRegime.exists_stoppingLaw_fourWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
      HasQuittingStoppingLawFourWayLocalization frontier := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
  exact ⟨frontier, frontier.fourWayLocalization⟩

/-- Failure of ordinary uniform-equilibrium payoff existence produces one
counterexample regime, one frontier, and the four-way localization on that
frontier. -/
theorem exists_stoppingLaw_fourWayLocalization_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ regime : QuittingCounterexampleRegime reward,
      ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
        HasQuittingStoppingLawFourWayLocalization frontier := by
  let regime := quittingCounterexampleRegimeOfNoUniformPayoff reward hno
  obtain ⟨frontier, hlocalization⟩ :=
    regime.exists_stoppingLaw_fourWayLocalization
  exact ⟨regime, frontier, hlocalization⟩

end GameTheory
