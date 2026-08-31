/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences

/-!
# One-sided affine limits

An affine inequality valid strictly to the right of a point remains valid at
the point.  This is game-independent real analysis.
-/

namespace Math.Topology

open Filter
open scoped Topology

/-- An affine inequality holding at every point immediately to the right of
`base` also holds at `base`.  The explicit sequence keeps the theorem free of
one-sided-neighborhood bookkeeping. -/
theorem affine_le_of_forall_right
    (base leftConstant leftSlope rightSource rightTarget : ℝ)
    (hbase : base < 1)
    (hineq : ∀ theta, base < theta → theta < 1 →
      leftConstant + (1 - theta) * leftSlope ≤
        (1 - theta) * rightSource + theta * rightTarget) :
    leftConstant + (1 - base) * leftSlope ≤
      (1 - base) * rightSource + base * rightTarget := by
  let theta : ℕ → ℝ := fun n =>
    base + (1 - base) * (1 / ((n : ℝ) + 1)) / 2
  have hreciprocal : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htheta : Tendsto theta atTop (nhds base) := by
    have hscaled : Tendsto
        (fun n : ℕ => (1 - base) * (1 / ((n : ℝ) + 1)) / 2)
        atTop (nhds 0) := by
      simpa using
        ((tendsto_const_nhds.mul hreciprocal).div_const (2 : ℝ))
    simpa only [theta, add_zero] using tendsto_const_nhds.add hscaled
  have hthetaLower : ∀ n, base < theta n := by
    intro n
    have hgap : 0 < 1 - base := sub_pos.mpr hbase
    have hreciprocalPos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    dsimp only [theta]
    nlinarith [mul_pos hgap hreciprocalPos]
  have hthetaUpper : ∀ n, theta n < 1 := by
    intro n
    have hgap : 0 < 1 - base := sub_pos.mpr hbase
    have hreciprocalPos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hreciprocalLe : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    dsimp only [theta]
    nlinarith [mul_pos hgap hreciprocalPos]
  have hleft : Tendsto
      (fun n => leftConstant + (1 - theta n) * leftSlope)
      atTop (nhds (leftConstant + (1 - base) * leftSlope)) := by
    exact tendsto_const_nhds.add
      ((tendsto_const_nhds.sub htheta).mul tendsto_const_nhds)
  have hright : Tendsto
      (fun n => (1 - theta n) * rightSource + theta n * rightTarget)
      atTop (nhds ((1 - base) * rightSource + base * rightTarget)) := by
    exact ((tendsto_const_nhds.sub htheta).mul tendsto_const_nhds).add
      (htheta.mul tendsto_const_nhds)
  exact le_of_tendsto_of_tendsto hleft hright <|
    Eventually.of_forall fun n => hineq (theta n) (hthetaLower n) (hthetaUpper n)

end Math.Topology
