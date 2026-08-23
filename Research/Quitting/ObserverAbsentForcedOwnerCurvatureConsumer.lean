/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ObserverAbsent.ForcedOwnerDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerWallRectangleCurvature

/-!
# Consuming the observer-absent forced-owner wall

The landed observer-absent dispatch leaves a counterfactual forced-Quit row:
either an outsider has a large coordinate defect there, or the owner has a
large refusal gap.  The first branch is not an independent obstruction.

At every row, its mass-weighted forced outsider defect is converted into
either ordinary Nash-defect occupation on the actual row or a positive
owner-action / outsider-deviation rectangle carried by the same terminal
cylinder.  The same pure outsider endpoint is used on both owner faces.

Thus the observer-absent branch has only two genuine currencies left:
owner refusal, or an actual two-coordinate square.  This file does not yet
sum or integrate the square into a state-matched reset chronology.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Pointwise consumer for one row of an observer-absent forced-owner wall. -/
def HasObserverAbsentForcedOwnerCurvatureRow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ) : Prop :=
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let root := quittingProfileLiveRoot reward profile time
  let forcedRoot := Function.update root owner (PMF.pure true)
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let mass := quittingStageCoalitionMass reward profile time packet.terminal
  ((∃ who action,
      who ≠ owner ∧
      let quitGain := quittingRootDeviationGain reward tail.1 forcedRoot who
        (PMF.pure action)
      let continueGain := quittingRootDeviationGain reward tail.1
        (Function.update root owner (PMF.pure false)) who (PMF.pure action)
      quitGain = quittingRootCoordinateNashDefect reward tail.1
          forcedRoot who ∧
        witness.terminalGap ≤
          quittingRootCoordinateNashDefect reward tail.1 forcedRoot who ∧
        (mass * witness.terminalGap / 2 ≤
            quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward tail.1 root who ∨
          mass * witness.terminalGap / 2 ≤
            mass * (root owner false).toReal *
              (quitGain - continueGain))) ∨
    (witness.terminalGap ≤
        max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) ∧
      mass * witness.terminalGap ≤
        mass * max 0
          (-quittingAtomicBlockerBalance reward forcedRoot owner)))

/-- **Observer-absent wall consumption.**  Every literal row in the
preemption clock is already an owner-refusal row, an actual Nash-defect row,
or a positive same-witness rectangle row. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_forcedOwnerCurvatureRows
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val) :
    ∀ n time,
      (match packet.quitTime n with
        | some stop => time < stop
        | none => True) →
      HasObserverAbsentForcedOwnerCurvatureRow (witness := witness) packet n time := by
  have hdispatch := packet.observerAbsent_forcedOwnerDispatch
    (witness := witness) habsent
  unfold HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch at hdispatch
  rcases hdispatch with
    ⟨howner, _hownerObserver, _hlower, _hside, _hmassLower,
      _hweightedLower, _hmassAccount, hrows⟩
  intro n time htime
  have hrow := hrows n time htime
  dsimp only at hrow
  rcases hrow with
    ⟨_hobserverContinue, _hforcedRoot, _hmassLe, _hbarrier,
      _hweightedBarrier, hcases⟩
  unfold HasObserverAbsentForcedOwnerCurvatureRow
  dsimp only
  rcases hcases with hdefect | hrefusal
  · rcases hdefect with ⟨who, hwho, hgap, hweightedGap⟩
    left
    obtain ⟨action, hrealize, halt⟩ :=
      stageCoalitionMass_gap_actualDefect_or_rectangle reward
        (quittingStoppingLawObserverAbsentCarrierProfile packet n)
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (quittingStoppingLawObserverAbsentCarrierProfile packet n)
            (time + 1))).1
        time (quittingStoppingLawObserverAbsentOwner packet) who hwho.symm
        packet.terminal howner witness.terminalGap hweightedGap
    exact ⟨who, action, hwho, hrealize, hgap, halt⟩
  · exact Or.inr hrefusal

end GameTheory
