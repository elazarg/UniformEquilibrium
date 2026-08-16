/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ObserverAbsent.ForcedOwnerDispatch
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.StaticStrategicOrientation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonStrategicCompression

/-!
# Five-way localization of a quitting counterexample

This module packages the orientation-preserving stopping-law capstone in the
five branches used by the readable guide. The singleton branch is compressed
to the static atomic-toggle handoff or exact player deletion, so positive
punishment is not retained as a spurious sixth branch.

The conjecture-facing theorem preserves one counterexample regime and one
frontier across all five branches.  It proves only the localization consequence
of nonexistence.  None of the branch data is asserted to imply nonexistence in
the reverse direction.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The five provenance-preserving outputs of the stopping-law localization:
prescribed comparison, observer absence, observer singleton, negative
observer-containing collision, or positive observer-containing collision. -/
def HasQuittingStoppingLawFiveWayLocalization
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
        packet.terminal.val.card = 1 ∧
        (HasQuittingStaticAtomicToggleHandoff reward ∨
          HasQuittingExactPlayerDeletionAtGap reward packet.observer
            regime.terminalGap)) ∨
    (∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
      packet.observer ∈ packet.terminal.val ∧
        1 < packet.terminal.val.card ∧
        reward packet.terminal packet.observer < 0 ∧
        HasQuittingStoppingLawNegativeCollisionAtomicDispatch packet
          (quittingStoppingLawNegativeCollisionMassLower packet)) ∨
    ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
      packet.observer ∈ packet.terminal.val ∧
        1 < packet.terminal.val.card ∧
        0 < reward packet.terminal packet.observer ∧
        HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch packet
          ((packet.charge / 4) /
            ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
              quittingRewardBound reward))

namespace QuittingCounterexampleStoppingLawFrontier

/-- The orientation-preserving strategic capstone, with its singleton branch
compressed, yields the five-way localization used in the guide. -/
theorem fiveWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    HasQuittingStoppingLawFiveWayLocalization frontier := by
  classical
  rcases frontier.exists_prescribed_or_orientationPreservingStrategicDispatch
      with hprescribed | ⟨packet, hdispatch⟩
  · exact Or.inl hprescribed
  · rcases hdispatch with habsent | hsingleton | hnegative | hpositive
    · exact Or.inr (Or.inl ⟨packet, habsent⟩)
    · have hcompressed :=
        regime.stoppingLawSingletonStrategicOrientation_compress packet hsingleton
      exact Or.inr (Or.inr (Or.inl
        ⟨packet, hsingleton.1, hsingleton.2.1, hcompressed⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨packet, hnegative⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨packet, hpositive⟩)))

end QuittingCounterexampleStoppingLawFrontier

/-- A fixed counterexample regime supplies the five-way localization on one
of its exhaustive stopping-law frontiers. -/
theorem QuittingCounterexampleRegime.exists_stoppingLaw_fiveWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
      HasQuittingStoppingLawFiveWayLocalization frontier := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
  exact ⟨frontier, frontier.fiveWayLocalization⟩

/-- **Conjecture-facing five-way localization.** Failure of ordinary
uniform-equilibrium payoff existence produces a counterexample regime, one
frontier for that regime, and the five-branch localization on the same
frontier.  No converse is asserted from the branch data. -/
theorem exists_stoppingLaw_fiveWayLocalization_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ regime : QuittingCounterexampleRegime reward,
      ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
        HasQuittingStoppingLawFiveWayLocalization frontier := by
  let regime := quittingCounterexampleRegimeOfNoUniformPayoff reward hno
  obtain ⟨frontier, hlocalization⟩ :=
    regime.exists_stoppingLaw_fiveWayLocalization
  exact ⟨regime, frontier, hlocalization⟩

end GameTheory
