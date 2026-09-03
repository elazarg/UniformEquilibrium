/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.WeakPathConvergence

/-!
# Moving evaluations of monotone paths under weak convergence

Coordinatewise weak convergence at fixed continuity times also controls a
source evaluation time that approaches such a time from the right.  The proof
uses monotonicity for the lower bound and a decreasing sequence of nearby
continuity times for the upper bound.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A moving source-time evaluation converges at a continuity time of the
limit when the source times approach that time from the right. -/
theorem WeaklyConvergesAbsorptionPaths.value_tendsto_of_tendsto_fromAbove
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)}
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    {times : ℕ → ℝ} {time : ℝ}
    (htime : time ∈ Icc (0 : ℝ) 1)
    (htimeOne : time ≠ 1)
    (hnotJump : time ∉ pathJumps limit.1)
    (htimes : ∀ index, times index ∈ Icc (0 : ℝ) 1)
    (hfromAbove : ∀ index, time ≤ times index)
    (htimesTendsto : Tendsto times atTop (nhds time))
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun index ↦ (paths index).1.value (times index) coalition)
      atTop (nhds (limit.1.value time coalition)) := by
  apply tendsto_order.2
  constructor
  · intro lower hlower
    have hfixed := tendsto_pi_nhds.mp (hweak time htime hnotJump) coalition
    filter_upwards [hfixed.eventually (Ioi_mem_nhds hlower)] with index hindex
    exact hindex.trans_le <|
      (paths index).1.monotone coalition htime (htimes index)
        (hfromAbove index)
  · intro upper hupper
    have htimeLtOne : time < 1 :=
      lt_of_le_of_ne htime.2 htimeOne
    have hdense : Dense ((pathJumps limit.1)ᶜ) :=
      (countable_pathJumps limit.1).dense_compl ℝ
    obtain ⟨probe, _hprobeStrictAnti, hprobeMem, hprobeTendsto⟩ :=
      hdense.exists_seq_strictAnti_tendsto_of_lt htimeLtOne
    have hprobeWithin : Tendsto probe atTop
        (nhdsWithin time (Icc time 1)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hprobeTendsto,
        Filter.Eventually.of_forall fun rank ↦
          ⟨(hprobeMem rank).1.1.le, (hprobeMem rank).1.2.le⟩⟩
    have hlimitProbe : Tendsto
        (fun rank ↦ limit.1.value (probe rank) coalition) atTop
        (nhds (limit.1.value time coalition)) :=
      (limit.1.right_continuous coalition time htime).comp hprobeWithin
    obtain ⟨rank, hrankUpper⟩ :=
      (hlimitProbe.eventually (Iio_mem_nhds hupper)).exists
    have htimesBefore : ∀ᶠ index in atTop, times index < probe rank :=
      htimesTendsto.eventually_lt_const (hprobeMem rank).1.1
    have hsourceProbe := tendsto_pi_nhds.mp
      (hweak (probe rank)
        ⟨htime.1.trans (hprobeMem rank).1.1.le,
          (hprobeMem rank).1.2.le⟩
        (hprobeMem rank).2) coalition
    have hsourceUpper : ∀ᶠ index in atTop,
        (paths index).1.value (probe rank) coalition < upper :=
      hsourceProbe.eventually_lt_const hrankUpper
    filter_upwards [htimesBefore, hsourceUpper] with index hbefore hsource
    exact ((paths index).1.monotone coalition (htimes index)
      ⟨htime.1.trans (hprobeMem rank).1.1.le,
        (hprobeMem rank).1.2.le⟩ hbefore.le).trans_lt hsource

end GameTheory.QuittingAbsorptionPath
