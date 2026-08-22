/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable selection from set-valued maps

This file starts the project-owned measurable-selection layer with the
countable-dense approximation underlying the Kuratowski--Ryll-Nardzewski
construction.  It is game-independent and therefore belongs in `MathUE`.
-/

noncomputable section

open Set TopologicalSpace

namespace Math

variable {X Y : Type*} [MeasurableSpace X]

/-- A set-valued map is weakly measurable when the set of points where its
value meets any open set is measurable. -/
def WeaklyMeasurableCorrespondence
    [TopologicalSpace Y] (F : X → Set Y) : Prop :=
  ∀ U : Set Y, IsOpen U → MeasurableSet {x | (F x ∩ U).Nonempty}

/-- A nonempty weakly measurable correspondence into a separable metric
space admits a measurable selector lying within any prescribed positive
distance of its value.

This is the countable-dense approximation step in measurable-selection
proofs.  Closedness and completeness are not needed until one passes from
these approximate selectors to an exact selector. -/
theorem exists_measurable_nearSelector
    [PseudoMetricSpace Y] [SeparableSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (F : X → Set Y) (hnonempty : ∀ x, (F x).Nonempty)
    (hmeasurable : WeaklyMeasurableCorrespondence F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : X → Y, Measurable f ∧
      ∀ x, ∃ y ∈ F x, dist (f x) y < ε := by
  classical
  let dense : ℕ → Y := denseSeq Y
  let candidate : X → ℕ → Prop := fun x n ↦
    (F x ∩ Metric.ball (dense n) ε).Nonempty
  have hexists : ∀ x, ∃ n, candidate x n := by
    intro x
    obtain ⟨y, hy⟩ := hnonempty x
    obtain ⟨n, hn⟩ := (denseRange_denseSeq Y).exists_dist_lt y hε
    refine ⟨n, y, hy, ?_⟩
    simpa only [Metric.mem_ball, dist_comm] using hn
  have hcandidate : ∀ n, MeasurableSet {x | candidate x n} := by
    intro n
    exact hmeasurable (Metric.ball (dense n) ε) Metric.isOpen_ball
  let index : X → ℕ := fun x ↦ Nat.find (hexists x)
  let f : X → Y := fun x ↦ dense (index x)
  refine ⟨f, ?_, ?_⟩
  · exact measurable_from_nat.comp (measurable_find hexists hcandidate)
  · intro x
    obtain ⟨y, hyF, hyball⟩ := Nat.find_spec (hexists x)
    refine ⟨y, hyF, ?_⟩
    simpa only [f, index, Metric.mem_ball, dist_comm] using hyball

end Math
