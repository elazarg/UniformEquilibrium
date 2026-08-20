/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import GameTheory.Math.Probability.Measure

/-!
# Integrating finite-support laws

This file connects GameTheory's executable finite-support expectation to the
ordinary Bochner integral of its associated measure.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

open MeasureTheory

/-- Integrating a uniformly bounded real observable against the ordinary
measure of a finite law gives its executable finite expectation. -/
theorem integral_toMeasure_eq_expect_of_bound
    {X : Type*} [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSingletonClass X] (law : FinDist X) (f : X → ℝ)
    {bound : ℝ} (hbound : ∀ x, ‖f x‖ ≤ bound) :
    (∫ x, f x ∂law.toMeasure) = law.expect f := by
  unfold FinDist.toMeasure
  rw [PMF.integral_eq_tsum law.toPMF f]
  · rfl
  · apply Integrable.of_bound
      Measurable.of_discrete.aestronglyMeasurable bound
    exact Filter.Eventually.of_forall hbound

end GameTheory.Math.Probability.FinDist
