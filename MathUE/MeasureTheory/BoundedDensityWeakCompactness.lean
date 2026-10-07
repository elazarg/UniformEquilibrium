import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-! # Weak limits of dominated probability measures

Portmanteau on open sets and outer regularity preserve domination by a fixed
measure. Compactness of probability measures on a compact metrizable space
therefore produces an actual dominated probability limit along a subsequence.

This is the measure-valued compactness foundation for bounded likelihoods on a
compact interval. It does not assert convergence of discontinuous moving tests,
marked calendars, ties, or stopping-game response caps.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace MeasureTheory.ProbabilityMeasure

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- Domination passes to a weak probability limit. Neither compactness nor an
already supplied density for the limit is needed. -/
theorem le_of_tendsto_of_le_measure
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {J : Type*} {filter : Filter J} [filter.NeBot]
    {laws : J → ProbabilityMeasure X} {limit : ProbabilityMeasure X}
    (bound : Measure X) [bound.OuterRegular]
    (hlimit : Tendsto laws filter (𝓝 limit))
    (hbound : ∀ᶠ j in filter, (laws j : Measure X) ≤ bound) :
    (limit : Measure X) ≤ bound := by
  apply Measure.le_iff'.mpr
  intro s
  rw [s.measure_eq_iInf_isOpen bound]
  refine le_iInf fun U => le_iInf fun hsU => le_iInf fun hU => ?_
  apply (measure_mono hsU).trans
  apply (le_liminf_measure_open_of_tendsto hlimit hU).trans
  apply (Filter.liminf_le_limsup).trans
  exact Filter.limsup_le_of_le (by isBoundedDefault)
    (hbound.mono fun j hj => Measure.le_iff'.mp hj U)

/-- Every sequence of probabilities uniformly dominated by a finite multiple
of a fixed base probability on a compact metrizable Borel space has a dominated
probability subsequential limit. The constant need not be positive as a premise;
inconsistent bounds simply admit no such sequence. -/
theorem exists_dominated_subsequence
    [TopologicalSpace.MetrizableSpace X] [CompactSpace X] [BorelSpace X]
    (base : ProbabilityMeasure X) (constant : NNReal)
    (laws : ℕ → ProbabilityMeasure X)
    (hbound : ∀ j, (laws j : Measure X) ≤ constant • (base : Measure X)) :
    ∃ (limit : ProbabilityMeasure X) (subsequence : ℕ → ℕ),
      StrictMono subsequence ∧
      Tendsto (laws ∘ subsequence) atTop (𝓝 limit) ∧
      (limit : Measure X) ≤ constant • (base : Measure X) := by
  obtain ⟨limit, subsequence, hmono, hlimit⟩ := CompactSpace.tendsto_subseq laws
  refine ⟨limit, subsequence, hmono, hlimit, ?_⟩
  exact le_of_tendsto_of_le_measure _ hlimit
    (Eventually.of_forall fun j => hbound (subsequence j))

end MeasureTheory.ProbabilityMeasure
