/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Circulant.ColliderCompletion
import UniformEquilibrium.Quitting.Classification.Circulant.ColliderCompletion

/-!
# The two vanishing-margin slabs of the collider completion

The pocket of `Research/Quitting/CirculantColliderCompletion.lean` is cut out
by `m 1 ≤ 0`, `m 4 < 0`, `0 ≤ m 2`, `0 ≤ m 3` and a positive margin sum, and is
closed there by a constant-step cycle of step four.  The two hyperplanes
`m 2 = 0` and `m 3 = 0` are closed here instead, by constant-step cycles of
step two and step three.

On `m 2 = 0` the step-two anchor cubic factors as `q * (m 4 + m 1 q + m 3 q²)`,
so its nonzero roots are the roots of a quadratic; a negative `m 4` and a
positive `m 1 + m 3 + m 4` place such a root in `(0, 1)`, and at it all four
floors of the step-two profile hold.  The hyperplane `m 3 = 0` is the mirror
statement with the quadratic `m 1 + m 4 q + m 2 q²` and step three.

Neither statement constrains the sign of the margin opposite the step: on
`m 2 = 0` the neighbour margin `m 1` is free and only `m 4` must be negative,
and on `m 3 = 0` the roles are exchanged.  Each therefore covers a slab
strictly larger than the corresponding face of the pocket.

Both slabs need `low ≤ s`: the join margin of the collider completion is
`low - s` at every distance except four, and the phase-one floor of a step
other than four is exactly that margin being nonpositive.  The remaining
margin-side hypothesis is one more floor of the same shape — `low - s ≤ m 3`
on `m 2 = 0` and `low - s ≤ m 2` on `m 3 = 0` — which nonnegativity of that
margin implies but does not exhaust.

The roots come from `MathUE/CubicAnchorRoot.lean`, where
`Math.quadratic_total_pos_iff_exists_root_mem_Ioo` also records that at a
nonnegative leading square coefficient the positive total and the interior root
are the same condition.

## Main results

* `isEmpty_terminalExploitabilityWitness_colliderSliverTwo`,
  `isEmpty_terminalExploitabilityWitness_colliderSliverThree` — the two slabs carry no
  terminal exploitability witness
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderCompletion

open CirculantConstantStepCycle

variable {s low : ℝ} {m : ZMod 5 → ℝ}

/-! ## The hyperplane `m 2 = 0` -/

/-- **The slab `m 2 = 0` carries no terminal exploitability witness.**  The step-two
constant-step cyclic profile is an exact equilibrium at the root in `(0, 1)` of
`m 4 + m 1 q + m 3 q²`.  The neighbour margin `m 1` is unconstrained. -/
theorem isEmpty_terminalExploitabilityWitness_colliderSliverTwo
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ s)
    (hm2 : m 2 = 0) (hm4 : m 4 < 0) (hsum : 0 < m 1 + m 3 + m 4)
    (hfloor : low - s ≤ m 3) :
    IsEmpty (QuittingTerminalExploitabilityWitness (colliderReward s low m)) := by
  obtain ⟨q, hq, hroot⟩ :=
    Math.exists_quadratic_root_mem_Ioo (a := m 4) (b := m 1) (c := m 3) hm4
      (by linarith)
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
  refine isEmpty_terminalExploitabilityWitness_constantStep (c' := 2)
    (isCirculantPairTable_colliderReward s low m hm0) (by decide) hs hq0.le hq1
    hanchor ?_ ?_ ?_ ?_
  · rw [colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h24, h32, h42, colliderJoin_four]
    linarith
  · rw [h32, h42, colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h42, colliderJoin_of_ne s low (by decide)]
    exact hfloor

/-! ## The hyperplane `m 3 = 0` -/

/-- **The slab `m 3 = 0` carries no terminal exploitability witness.**  The step-three
constant-step cyclic profile is an exact equilibrium at the root in `(0, 1)` of
`m 1 + m 4 q + m 2 q²`.  The distance-four margin `m 4` is unconstrained. -/
theorem isEmpty_terminalExploitabilityWitness_colliderSliverThree
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ s)
    (hm3 : m 3 = 0) (hm1 : m 1 < 0) (hsum : 0 < m 1 + m 2 + m 4)
    (hfloor : low - s ≤ m 2) :
    IsEmpty (QuittingTerminalExploitabilityWitness (colliderReward s low m)) := by
  obtain ⟨q, hq, hroot⟩ :=
    Math.exists_quadratic_root_mem_Ioo (a := m 1) (b := m 4) (c := m 2) hm1
      (by linarith)
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
  refine isEmpty_terminalExploitabilityWitness_constantStep (c' := 3)
    (isCirculantPairTable_colliderReward s low m hm0) (by decide) hs hq0.le hq1
    hanchor ?_ ?_ ?_ ?_
  · rw [colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h23, h33, h43, colliderJoin_of_ne s low (by decide)]
    linarith
  · rw [h33, h43, colliderJoin_four]
    linarith
  · rw [h43, colliderJoin_of_ne s low (by decide)]
    exact hfloor

end CirculantColliderCompletion
end GameTheory
