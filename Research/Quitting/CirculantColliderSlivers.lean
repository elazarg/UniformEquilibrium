/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CirculantColliderCompletion

/-!
# The two vanishing-margin faces of the collider-completion pocket

The pocket of `Research/Quitting/CirculantColliderCompletion.lean` is cut out
by `m 1 < 0`, `m 4 < 0`, `0 ≤ m 2`, `0 ≤ m 3` and a positive margin sum.  Its
two faces `m 2 = 0` and `m 3 = 0` are handled here, by constant-step cycles of
step two and step three respectively rather than of step four.

On the face `m 2 = 0` the step-two anchor cubic factors as
`q * (m 4 + m 1 q + m 3 q²)`, so its nonzero roots are the roots of a
quadratic; that quadratic has a root in `(0, 1)` exactly when the margin sum is
positive, and at such a root all four floors of the step-two profile hold.  The
face `m 3 = 0` is the mirror statement with the quadratic
`m 1 + m 4 q + m 2 q²` and step three.

Both faces need `low ≤ s`: the join margin of the collider completion is
`low - s` at every distance except four, and the phase-one floor of a step
other than four is exactly that margin being nonpositive.

## Main results

* `exists_sliverTwoRoot`, `exists_sliverThreeRoot` — the quadratic roots
* `pos_sum_of_sliverTwoRoot`, `pos_sum_of_sliverThreeRoot` — the converse
  direction: a root in `(0, 1)` forces a positive margin sum
* `isEmpty_counterexampleRegime_colliderSliverTwo`,
  `isEmpty_counterexampleRegime_colliderSliverThree` — the two faces carry no
  counterexample regime
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderCompletion

open CirculantConstantStepCycle

variable {s low : ℝ} {m : ZMod 5 → ℝ}

/-! ## The face `m 2 = 0` -/

/-- **The step-two quadratic root.**  On the face `m 2 = 0` a negative `m 4`
and a positive margin sum place a root of `m 4 + m 1 q + m 3 q²` strictly
inside the unit interval. -/
theorem exists_sliverTwoRoot (hm4 : m 4 < 0) (hsum : 0 < m 1 + m 3 + m 4) :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, m 4 + m 1 * q + m 3 * q ^ 2 = 0 := by
  obtain ⟨q, hq, hroot⟩ :=
    Math.exists_cubicAnchor_root_mem_Ioo (a := m 4) (b := m 1) (c := m 3) (d := 0)
      hm4 (by linarith)
  refine ⟨q, hq, ?_⟩
  rw [Math.cubicAnchor] at hroot
  linarith

/-- **The converse on the face `m 2 = 0`.**  A root of the step-two quadratic
strictly inside the unit interval forces a positive margin sum. -/
theorem pos_sum_of_sliverTwoRoot {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hm3 : 0 ≤ m 3) (hm4 : m 4 < 0) (hroot : m 4 + m 1 * q + m 3 * q ^ 2 = 0) :
    0 < m 1 + m 3 + m 4 := by
  have hkey : q * (m 1 + m 3 + m 4) = (1 - q) * (m 3 * q - m 4) := by
    linear_combination hroot
  have hpos : 0 < (1 - q) * (m 3 * q - m 4) := by
    refine mul_pos (by linarith [hq.2]) ?_
    nlinarith [hq.1]
  nlinarith [hq.1]

/-- **The face `m 2 = 0` carries no counterexample regime.**  The step-two
constant-step cyclic profile is an exact equilibrium at the root of the
step-two quadratic. -/
theorem isEmpty_counterexampleRegime_colliderSliverTwo
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ s)
    (hm2 : m 2 = 0) (hm3 : 0 ≤ m 3) (hm4 : m 4 < 0)
    (hsum : 0 < m 1 + m 3 + m 4) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) := by
  obtain ⟨q, hq, hroot⟩ := exists_sliverTwoRoot hm4 hsum
  have hq0 : 0 < q := hq.1
  have hq1 : q < 1 := hq.2
  have h24 : (2 : ZMod 5) * 2 = 4 := by decide
  have h32 : (3 : ZMod 5) * 2 = 1 := by decide
  have h42 : (4 : ZMod 5) * 2 = 3 := by decide
  have hanchor : stepAnchor m 2 q = 0 := by
    rw [stepAnchor_eq, h24, h32, h42, hm2]
    linear_combination q * hroot
  -- the anchor equation funds the deepest partial sum
  have htail : 0 < m 1 + q * m 3 := by
    nlinarith [hq0]
  refine isEmpty_counterexampleRegime_constantStep (c' := 2)
    (isCirculantPairTable_colliderReward s low m hm0) (by decide) hs hq0 hq1
    hanchor ?_ ?_ ?_ ?_
  · rw [colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h24, h32, h42, colliderJoin_four]
    linarith
  · rw [h32, h42, colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h42, colliderJoin_of_ne s low (by decide)]
    linarith

/-! ## The face `m 3 = 0` -/

/-- **The step-three quadratic root.**  On the face `m 3 = 0` a negative `m 1`
and a positive margin sum place a root of `m 1 + m 4 q + m 2 q²` strictly
inside the unit interval. -/
theorem exists_sliverThreeRoot (hm1 : m 1 < 0) (hsum : 0 < m 1 + m 2 + m 4) :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, m 1 + m 4 * q + m 2 * q ^ 2 = 0 := by
  obtain ⟨q, hq, hroot⟩ :=
    Math.exists_cubicAnchor_root_mem_Ioo (a := m 1) (b := m 4) (c := m 2) (d := 0)
      hm1 (by linarith)
  refine ⟨q, hq, ?_⟩
  rw [Math.cubicAnchor] at hroot
  linarith

/-- **The converse on the face `m 3 = 0`.**  A root of the step-three quadratic
strictly inside the unit interval forces a positive margin sum. -/
theorem pos_sum_of_sliverThreeRoot {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hm2 : 0 ≤ m 2) (hm1 : m 1 < 0) (hroot : m 1 + m 4 * q + m 2 * q ^ 2 = 0) :
    0 < m 1 + m 2 + m 4 := by
  have hkey : q * (m 1 + m 2 + m 4) = (1 - q) * (m 2 * q - m 1) := by
    linear_combination hroot
  have hpos : 0 < (1 - q) * (m 2 * q - m 1) := by
    refine mul_pos (by linarith [hq.2]) ?_
    nlinarith [hq.1]
  nlinarith [hq.1]

/-- **The face `m 3 = 0` carries no counterexample regime.**  The step-three
constant-step cyclic profile is an exact equilibrium at the root of the
step-three quadratic. -/
theorem isEmpty_counterexampleRegime_colliderSliverThree
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ s)
    (hm3 : m 3 = 0) (hm2 : 0 ≤ m 2) (hm1 : m 1 < 0)
    (hsum : 0 < m 1 + m 2 + m 4) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) := by
  obtain ⟨q, hq, hroot⟩ := exists_sliverThreeRoot hm1 hsum
  have hq0 : 0 < q := hq.1
  have hq1 : q < 1 := hq.2
  have h23 : (2 : ZMod 5) * 3 = 1 := by decide
  have h33 : (3 : ZMod 5) * 3 = 4 := by decide
  have h43 : (4 : ZMod 5) * 3 = 2 := by decide
  have hanchor : stepAnchor m 3 q = 0 := by
    rw [stepAnchor_eq, h23, h33, h43, hm3]
    linear_combination q * hroot
  have htail : 0 < m 4 + q * m 2 := by
    nlinarith [hq0]
  refine isEmpty_counterexampleRegime_constantStep (c' := 3)
    (isCirculantPairTable_colliderReward s low m hm0) (by decide) hs hq0 hq1
    hanchor ?_ ?_ ?_ ?_
  · rw [colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h23, h33, h43, colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h33, h43, colliderJoin_four]
    linarith
  · rw [h43, colliderJoin_of_ne s low (by decide)]
    linarith

end CirculantColliderCompletion
end GameTheory
