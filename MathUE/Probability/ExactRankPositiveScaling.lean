/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic.FieldSimp
import MathUE.CurveSelection.PositiveRoot

/-!
# Exact-rank positive scaling

A positive target can be represented exactly as a positive base times a
positive common factor raised to any prescribed positive rank. Along a target
tending to zero, the common factor tends to zero while the equality is
preserved at every index. When the target does not exceed the base, the factor
lies in `(0, 1]` and can therefore serve as a probability.
-/

noncomputable section

namespace Math.Probability.ExactRankPositiveScaling

/-- At any prescribed positive rank, a canonical positive factor realizes
`scale` exactly after multiplication by `base`. -/
theorem exactRankPositiveFactor
    (rank : ℕ) (hrank : 0 < rank)
    (base scale : ℝ) (hbase : 0 < base) (hscale : 0 < scale) :
    let factor :=
      Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot rank
        (scale / base)
    0 < factor ∧ base * factor ^ rank = scale := by
  dsimp only
  have hquot : 0 < scale / base := div_pos hscale hbase
  refine ⟨Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot_pos hquot, ?_⟩
  rw [Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot_pow hrank hquot.le]
  field_simp

/-- If `scale ≤ base`, the canonical exact-rank factor lies in `(0, 1]`. -/
theorem exactRankUnitFactor
    (rank : ℕ) (hrank : 0 < rank)
    (base scale : ℝ) (hbase : 0 < base) (hscale : 0 < scale)
    (hscaleBase : scale ≤ base) :
    let factor :=
      Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot rank
        (scale / base)
    factor ∈ Set.Ioc (0 : ℝ) 1 ∧ base * factor ^ rank = scale := by
  let factor :=
    Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot rank
      (scale / base)
  have hfactor := exactRankPositiveFactor rank hrank base scale hbase hscale
  have hpow : factor ^ rank = scale / base := by
    dsimp [factor]
    exact Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot_pow
      hrank (div_nonneg hscale.le hbase.le)
  have hfactorOne : factor ≤ 1 := by
    by_contra hnot
    have hone : 1 < factor := lt_of_not_ge hnot
    have honePow : 1 < factor ^ rank := one_lt_pow₀ hone hrank.ne'
    have hquotOne : scale / base ≤ 1 := (div_le_one hbase).2 hscaleBase
    linarith
  exact ⟨⟨hfactor.1, hfactorOne⟩, hfactor.2⟩

/-- Sequential form: the common positive factor tends to zero while the exact
rank-scaled value remains equal to the chosen target. -/
theorem exactRankPositiveFactorSequence
    (rank : ℕ) (hrank : 0 < rank) (base : ℝ) (hbase : 0 < base)
    (scale : ℕ → ℝ) (hscalePos : ∀ index, 0 < scale index)
    (hscale : Filter.Tendsto scale Filter.atTop (nhds 0)) :
    let factor : ℕ → ℝ := fun index ↦
      Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot rank
        (scale index / base)
    Filter.Tendsto factor Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) ∧
      ∀ index, base * factor index ^ rank = scale index := by
  dsimp only
  have hquotPos : ∀ index, 0 < scale index / base := fun index ↦
    div_pos (hscalePos index) hbase
  have hquot : Filter.Tendsto (fun index ↦ scale index / base)
      Filter.atTop (nhds 0) := by
    simpa only [zero_div] using hscale.div_const base
  refine ⟨Math.CurveSelection.Internal.PositiveRoot.tendsto_positiveNatRoot
      hrank hquotPos hquot, ?_⟩
  intro index
  rw [Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot_pow
    hrank (hquotPos index).le]
  field_simp

end Math.Probability.ExactRankPositiveScaling
