/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.ActiveTransferCycle
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.PositiveTotalSlopeAtomAccess

/-!
# Binary dynamic stopping-law localization

The positive-total-slope alternative is genuine quantitative information and
is not contradictory.  It is nevertheless unnecessary as a separate label in
the existential dynamic localization: independently of the sign of the total
slope, every frontier either has a zero-debt support entry or its active
positive-transfer relation is serial and closes into a finite cycle.

This is a theorem-level rerouting, not a consumption of either remaining
branch.  When positive total slope is present, the endpoint/atom passport in
`PositiveTotalSlopeAtomAccess` remains available in parallel with the binary
entry-or-cycle localization.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Collision and preemption data together with the genuinely binary
stopping-law localization. -/
structure QuittingCounterexampleReducedDynamicLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) where
  collision : QuittingImmediateSingletonCollision reward regime.terminalGap
  preemptionCycle : QuittingSoloPreemptionCycle reward regime.terminalGap
  frontier : QuittingCounterexampleStoppingLawFrontier regime
  branch :
    HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent ∨
      Nonempty (QuittingStoppingLawActiveTransferCycle frontier)

/-- Every stopping-law frontier admits the binary support-entry/active-cycle
alternative.  Positive total slope is not used in this proof. -/
theorem QuittingCounterexampleStoppingLawFrontier.entry_or_activeTransferCycle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent ∨
      Nonempty (QuittingStoppingLawActiveTransferCycle frontier) := by
  by_cases hentry : HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.active frontier.tangent
  · exact Or.inl hentry
  · exact Or.inr (frontier.nonempty_activeTransferCycle_of_noEntry hentry)

/-- Forget the redundant branch label in an existing dynamic localization,
without changing its collision, preemption cycle, or stopping-law frontier. -/
def QuittingCounterexampleDynamicLocalization.toReduced
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (localization : QuittingCounterexampleDynamicLocalization regime) :
    QuittingCounterexampleReducedDynamicLocalization regime where
  collision := localization.collision
  preemptionCycle := localization.preemptionCycle
  frontier := localization.frontier
  branch := localization.frontier.entry_or_activeTransferCycle

/-- Every counterexample regime has the binary dynamic localization. -/
theorem QuittingCounterexampleRegime.nonempty_reducedDynamicLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    Nonempty (QuittingCounterexampleReducedDynamicLocalization regime) := by
  obtain ⟨localization⟩ := regime.nonempty_dynamicLocalization
  exact ⟨localization.toReduced⟩

end GameTheory
