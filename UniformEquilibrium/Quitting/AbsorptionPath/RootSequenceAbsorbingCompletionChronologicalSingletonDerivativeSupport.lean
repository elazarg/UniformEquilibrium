/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceSingletonDerivativeSupport
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionChronologicalJumpRootRealization

/-!
# Singleton derivative support for chronological absorbing-completion limits

The chronological limit of an absorbing-completion diagonal has
singleton-supported nonzero right derivatives.  Together with clock
domination, constant totals on gap components, and product-root jump
realization, this gives the literal `IsAbsorptionPath` conjunction.  No
sequential perfection is asserted.
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
/-- Every nonzero right derivative of the chronological
absorbing-completion limit is supported on a singleton coalition. -/
theorem rightDerivative_supports_singletons
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
    QuittingAbsorptionPath.chronologicalCadlagPath_rightDerivative_supports_singletons_of_tendsto
      certificates limit.law limit.law_tendsto
      limit.le_pathTotal limit.hasClockGap_chronologicalClockCDF

omit [Nonempty ι] in
/-- The shared chronological limit path satisfies the complete absorption
path definition.  This theorem adds no sequential-perfection assertion. -/
theorem isAbsorptionPath
    (limit : diagonal.ChronologicalLimit) :
    QuittingAbsorptionPath.IsAbsorptionPath limit.path := by
  exact ⟨limit.le_pathTotal, limit.hasConstantTotalOnGapComponents,
    limit.everyPathJump_hasProductRoot,
    limit.rightDerivative_supports_singletons⟩

end ChronologicalLimit

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory
