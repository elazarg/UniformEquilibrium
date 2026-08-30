/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceA4
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionChronologicalA3

/-!
# Singleton derivatives of chronological absorbing-completion limits

The chronological limit of an absorbing-completion diagonal satisfies
absorption-path axiom A4.  Together with the existing A1--A3 results, this
gives the literal `IsAbsorptionPath` conjunction.  No sequential perfection
is asserted.
-/

noncomputable section

namespace GameTheory

open Filter Finset MeasureTheory Set StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

namespace ChronologicalLimit

omit [Nonempty ι] in
/-- The decoded chronological absorbing-completion limit satisfies the
literal absorption-path A4 quantifiers. -/
theorem absorptionPathA4
    (limit : diagonal.ChronologicalLimit) :
    ∀ time ∈ QuittingAbsorptionPath.pathTimes limit.path, time ≠ 1 →
      ∀ coalition,
        QuittingAbsorptionPath.pathRightDerivative
            limit.path time coalition ≠ 0 →
          coalition.1.card = 1 := by
  let certificates := fun rank ↦
    (diagonal.completion (limit.subsequence rank))
      |>.finiteAbsorptionCertificate
  simpa only [path] using
    QuittingAbsorptionPath.absorptionPathA4_chronologicalCadlagPath_of_tendsto
      certificates limit.law limit.law_tendsto
      limit.le_pathTotal limit.hasClockGap_chronologicalClockCDF

omit [Nonempty ι] in
/-- The shared chronological limit path satisfies all four absorption-path
axioms.  This theorem adds no sequential-perfection assertion. -/
theorem isAbsorptionPath
    (limit : diagonal.ChronologicalLimit) :
    QuittingAbsorptionPath.IsAbsorptionPath limit.path := by
  exact ⟨limit.le_pathTotal, limit.absorptionPathA2,
    limit.absorptionPathA3, limit.absorptionPathA4⟩

end ChronologicalLimit

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory
