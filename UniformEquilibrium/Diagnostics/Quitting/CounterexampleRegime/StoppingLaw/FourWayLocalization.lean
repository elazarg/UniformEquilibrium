/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ObserverAbsent.ForcedOwnerDispatch
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ReachedRowDebtLocalization

/-!
# Four-way localization of a quitting counterexample

This module eliminates the former observer-singleton branch.  Once the fixed
rectangle terminal contains the observer, the positive atom makes the
observer's reward nonzero.  A negative reward enters the existing actual
source-row atomic dispatch, while a positive reward enters the cardinality-free
actual target-row localization.  Neither route uses the terminal cardinality.

The conjecture-facing theorem therefore preserves one counterexample regime
and one frontier across four branches: prescribed comparison, observer absence,
negative observer-containing target, or positive observer-containing target.
It proves only the localization consequence of nonexistence.  No converse is
asserted from the branch data.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The four provenance-preserving outputs of the stopping-law localization:
prescribed comparison, observer absence, a negative observer-containing row,
or a positive observer-containing row.  Singleton terminals belong to one of
the last two branches according to the sign of their observer reward. -/
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
        HasQuittingStoppingLawNegativeCollisionAtomicDispatch packet
          (quittingStoppingLawNegativeCollisionMassLower packet)) ∨
    ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
      packet.observer ∈ packet.terminal.val ∧
        0 < reward packet.terminal packet.observer ∧
        HasQuittingStoppingLawPositiveCollisionReachedRowLocalization packet
          ((packet.charge / 4) /
            ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
              quittingRewardBound reward))

/-- **Direct elimination of the former singleton leaf.**  Its packet-specific
information is only that the observer belongs to the terminal.  The packet's
positive atom makes the observer reward nonzero, so its sign routes the same
literal packet to the negative source-row dispatch or the positive target-row
localization.  The singleton cardinality and ambient static dispatch are not
used. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.singleton_signedRowElimination
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (orientation : HasQuittingStoppingLawSingletonStrategicOrientation packet) :
    (reward packet.terminal packet.observer < 0 ∧
        HasQuittingStoppingLawNegativeCollisionAtomicDispatch packet
          (quittingStoppingLawNegativeCollisionMassLower packet)) ∨
      (0 < reward packet.terminal packet.observer ∧
        HasQuittingStoppingLawPositiveCollisionReachedRowLocalization packet
          ((packet.charge / 4) /
            ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
              quittingRewardBound reward))) := by
  classical
  rcases orientation with ⟨hobserver, _hcard, _hstatic⟩
  by_cases hpositive : 0 < reward packet.terminal packet.observer
  · exact Or.inr ⟨hpositive,
      packet.positiveTarget_reachedRowLocalization hobserver hpositive⟩
  · have hnegative : reward packet.terminal packet.observer < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpositive) packet.reward_ne_zero
    exact Or.inl ⟨hnegative,
      packet.negativeCollision_atomicDispatch hobserver hnegative⟩

namespace QuittingCounterexampleStoppingLawFrontier

/-- **Cardinality-free exhaustive stopping-law capstone.**  The former
singleton branch is absorbed by the two signed observer-containing branches.
The negative route uses the literal source row and the positive route uses the
literal target row; both are valid for every nonempty terminal cardinality. -/
theorem fourWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    HasQuittingStoppingLawFourWayLocalization frontier := by
  classical
  rcases frontier.exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence
      with hprescribed | ⟨packet⟩
  · exact Or.inl hprescribed
  · by_cases hobserver : packet.observer ∈ packet.terminal.val
    · by_cases hpositive : 0 < reward packet.terminal packet.observer
      · exact Or.inr (Or.inr (Or.inr
          ⟨packet, hobserver, hpositive,
            packet.positiveTarget_reachedRowLocalization hobserver
              hpositive⟩))
      · have hnegative : reward packet.terminal packet.observer < 0 :=
          lt_of_le_of_ne (le_of_not_gt hpositive) packet.reward_ne_zero
        exact Or.inr (Or.inr (Or.inl
          ⟨packet, hobserver, hnegative,
            packet.negativeCollision_atomicDispatch hobserver hnegative⟩))
    · exact Or.inr (Or.inl
        ⟨packet, hobserver,
          packet.observerAbsent_forcedOwnerDispatch hobserver⟩)

end QuittingCounterexampleStoppingLawFrontier

/-- A fixed counterexample regime supplies the four-way localization on one
of its exhaustive stopping-law frontiers. -/
theorem QuittingCounterexampleRegime.exists_stoppingLaw_fourWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
      HasQuittingStoppingLawFourWayLocalization frontier := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
  exact ⟨frontier, frontier.fourWayLocalization⟩

/-- **Conjecture-facing four-way localization.** Failure of ordinary
uniform-equilibrium payoff existence produces a counterexample regime, one
frontier for that regime, and the four-branch localization on the same
frontier.  No converse is asserted from the branch data. -/
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
