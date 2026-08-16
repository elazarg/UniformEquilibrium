/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeObserverAbsentForcedOwnerDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonStrategicCompression

/-!
# Five-way localization of a quitting counterexample

This module packages the orientation-preserving stopping-law capstone in the
five branches used by the readable guide. The singleton branch is compressed
to the static atomic-toggle handoff or exact player deletion, so positive
punishment is not retained as a spurious sixth branch.

The conjecture-facing predicate includes the counterexample regime and its
frontier, rather than only the five branch conclusions. Consequently it is
equivalent to nonexistence of a uniform-equilibrium payoff. The reverse
implication uses the packaged regime; it does not say that an unbundled static
branch certificate is independently sufficient for nonexistence.
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

/-- A counterexample regime, its common stopping-law frontier, and the five-way
localization on that same frontier. -/
def HasQuittingCounterexampleFiveWayLocalization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ regime : QuittingCounterexampleRegime reward,
    ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
      HasQuittingStoppingLawFiveWayLocalization frontier

/-- **Exact conjecture-facing five-way localization.** Failure of ordinary
uniform-equilibrium payoff existence is equivalent to a counterexample regime
carrying its exhaustive frontier and the five-branch localization. -/
theorem
    not_exists_uniformEquilibriumPayoff_iff_hasQuittingCounterexampleFiveWayLocalization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      HasQuittingCounterexampleFiveWayLocalization reward := by
  constructor
  · intro hno
    letI : Nonempty ι := by
      obtain ⟨_gap, _hgap, hexploit⟩ :=
        (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
          reward).mp hno
      obtain ⟨who, _deviation, _hgain⟩ :=
        hexploit (quittingAlwaysContinueProfile reward)
      exact ⟨who⟩
    let regime := quittingCounterexampleRegimeOfNoUniformPayoff reward hno
    obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
    exact ⟨regime, frontier, frontier.fiveWayLocalization⟩
  · rintro ⟨regime, _frontier, _localization⟩
    exact regime.not_exists_uniformEquilibriumPayoff

end GameTheory
