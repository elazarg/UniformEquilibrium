/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Extended orbits of a correspondence

An extended orbit is a sequence of finite or infinite orbit segments. A finite
segment is joined to the next one at its last point; an infinite segment is
joined by convergence. This is the source-neutral orbit grammar used in
Simon's topological formulation of quitting games.

The variation functional is parameterized by an edge cost. This matters when
the ambient topology is the finite-product topology but the source measures
variation with a separately specified Euclidean norm.
-/

noncomputable section

namespace Math
namespace Topology

open Filter Set
open scoped BigOperators Topology

/-- A correspondence is represented by its set-valued fibers. -/
abbrev Correspondence (X Y : Type*) := X → Set Y

/-- Restrict a correspondence to a subset of its domain. -/
def Correspondence.restrict {X Y : Type*} (relation : Correspondence X Y)
    (domain : Set X) : Correspondence X Y := by
  classical
  exact fun point ↦ if point ∈ domain then relation point else ∅

/-- Points at which a correspondence has a nonempty fiber. -/
def Correspondence.domain {X Y : Type*} (relation : Correspondence X Y) : Set X :=
  {point | (relation point).Nonempty}

/-- The union of all fibers of a correspondence. -/
def Correspondence.image {X Y : Type*} (relation : Correspondence X Y) : Set Y :=
  ⋃ point, relation point

/-- An infinite orbit follows the correspondence at every adjacent pair. -/
def IsInfiniteOrbit {X : Type*} (relation : Correspondence X X)
    (point : ℕ → X) : Prop :=
  ∀ index, point (index + 1) ∈ relation (point index)

/-- A finite orbit of `length` edges follows the correspondence at each edge. -/
def IsFiniteOrbit {X : Type*} (relation : Correspondence X X) {length : ℕ}
    (point : Fin (length + 1) → X) : Prop :=
  ∀ index : Fin length, point index.succ ∈ relation (point index.castSucc)

/-- Accumulated cost along the edges of a finite orbit candidate. -/
def finiteOrbitVariationWith {X : Type*} {length : ℕ}
    (cost : X → X → ℝ) (point : Fin (length + 1) → X) : ℝ :=
  ∑ index : Fin length, cost (point index.castSucc) (point index.succ)

/-- A correspondence has finite orbits with arbitrarily large accumulated
cost. The orbit length and points may depend on the requested bound. -/
def HasArbitrarilyLargeFiniteOrbitVariationWith {X : Type*}
    (relation : Correspondence X X) (cost : X → X → ℝ) : Prop :=
  ∀ bound : ℝ, ∃ length : ℕ, ∃ point : Fin (length + 1) → X,
    IsFiniteOrbit relation point ∧ bound ≤ finiteOrbitVariationWith cost point

/-- Successive potential drops along a finite orbit candidate telescope to
the difference between its endpoints. -/
theorem finiteOrbitPotentialDrop_sum {X : Type*} (potential : X → ℝ) :
    ∀ {length : ℕ} (point : Fin (length + 1) → X),
      (∑ index : Fin length,
        (potential (point index.castSucc) - potential (point index.succ))) =
      potential (point 0) - potential (point (Fin.last length)) := by
  intro length
  induction length with
  | zero => simp
  | succ length ih =>
      intro point
      have ih' := ih (fun index ↦ point index.succ)
      rw [Fin.sum_univ_succ]
      rw [show (∑ index : Fin length,
          (potential (point index.succ.castSucc) -
            potential (point index.succ.succ))) =
          potential (point (Fin.succ 0)) -
            potential (point (Fin.last length).succ) by
        simpa only [Fin.succ_castSucc] using ih']
      simpa only [Fin.castSucc_zero, Fin.succ_last] using
        sub_add_sub_cancel
          (potential (point 0))
          (potential (point (Fin.succ 0)))
          (potential (point (Fin.last (length + 1))))

/-- A potential whose edge decrease dominates `constant` times a supplied
cost pays that scaled cost along every finite orbit. No sign assumption on
the cost or on `constant` is needed for this endpoint inequality. -/
theorem IsFiniteOrbit.constant_mul_finiteOrbitVariationWith_le_potentialDrop
    {X : Type*} {relation : Correspondence X X} {length : ℕ}
    {point : Fin (length + 1) → X} {cost : X → X → ℝ}
    {potential : X → ℝ} {constant : ℝ}
    (horbit : IsFiniteOrbit relation point)
    (hdecrease : ∀ first next, next ∈ relation first →
      potential next ≤ potential first - constant * cost first next) :
    constant * finiteOrbitVariationWith cost point ≤
      potential (point 0) - potential (point (Fin.last length)) := by
  rw [finiteOrbitVariationWith, Finset.mul_sum]
  calc
    ∑ index : Fin length,
          constant * cost (point index.castSucc) (point index.succ) ≤
        ∑ index : Fin length,
          (potential (point index.castSucc) - potential (point index.succ)) := by
      apply Finset.sum_le_sum
      intro index _
      exact (le_sub_iff_add_le).2 (by
        simpa only [add_comm] using
          (le_sub_iff_add_le.1
            (hdecrease _ _ (horbit index))))
    _ = potential (point 0) - potential (point (Fin.last length)) :=
      finiteOrbitPotentialDrop_sum potential point

/-- Explicit lower and upper bounds on a strict Lyapunov potential give one
horizon-independent bound on the accumulated cost of every finite orbit. -/
theorem IsFiniteOrbit.finiteOrbitVariationWith_le_of_potential_bounds
    {X : Type*} {relation : Correspondence X X} {length : ℕ}
    {point : Fin (length + 1) → X} {cost : X → X → ℝ}
    {potential : X → ℝ} {constant lower upper : ℝ}
    (horbit : IsFiniteOrbit relation point) (hconstant : 0 < constant)
    (hlower : ∀ state, lower ≤ potential state)
    (hupper : ∀ state, potential state ≤ upper)
    (hdecrease : ∀ first next, next ∈ relation first →
      potential next ≤ potential first - constant * cost first next) :
    finiteOrbitVariationWith cost point ≤ (upper - lower) / constant := by
  apply (le_div_iff₀ hconstant).2
  have hdrop :=
    horbit.constant_mul_finiteOrbitVariationWith_le_potentialDrop hdecrease
  have hendpoint :
      potential (point 0) - potential (point (Fin.last length)) ≤
        upper - lower :=
    sub_le_sub (hupper _) (hlower _)
  simpa only [mul_comm] using hdrop.trans hendpoint

/-- A bounded strict Lyapunov potential rules out finite orbits with
arbitrarily large accumulated cost. This is only an orbit obstruction; it
does not assert that such a potential exists or connect the obstruction to
any game-semantic equilibrium claim. -/
theorem not_hasArbitrarilyLargeFiniteOrbitVariationWith_of_potential_bounds
    {X : Type*} {relation : Correspondence X X} {cost : X → X → ℝ}
    {potential : X → ℝ} {constant lower upper : ℝ}
    (hconstant : 0 < constant)
    (hlower : ∀ state, lower ≤ potential state)
    (hupper : ∀ state, potential state ≤ upper)
    (hdecrease : ∀ first next, next ∈ relation first →
      potential next ≤ potential first - constant * cost first next) :
    ¬HasArbitrarilyLargeFiniteOrbitVariationWith relation cost := by
  intro hunbounded
  let bound := (upper - lower) / constant
  obtain ⟨length, point, horbit, hbound⟩ := hunbounded (bound + 1)
  have hvariation : finiteOrbitVariationWith cost point ≤ bound :=
    horbit.finiteOrbitVariationWith_le_of_potential_bounds
      hconstant hlower hupper hdecrease
  exact (not_le_of_gt (lt_add_one bound)) (hbound.trans hvariation)

/-- `none` means an infinite segment; `some k` means exactly `k` points. -/
def SegmentIndex (length : Option ℕ) (index : ℕ) : Prop :=
  ∀ k, length = some k → index < k

/-- `none` means infinitely many segments; `some k` means exactly `k` segments. -/
def ActiveSegment (count : Option ℕ) (segment : ℕ) : Prop :=
  ∀ k, count = some k → segment < k

/-- Every predecessor of an active segment is active. -/
theorem ActiveSegment.pred {count : Option ℕ} {segment : ℕ}
    (hactive : ActiveSegment count (segment + 1)) :
    ActiveSegment count segment := by
  intro total htotal
  exact (Nat.lt_succ_self segment).trans (hactive total htotal)

/-- Validity of a segment index is inherited by smaller indices. -/
theorem SegmentIndex.mono {length : Option ℕ} {first second : ℕ}
    (hle : first ≤ second) (hsecond : SegmentIndex length second) :
    SegmentIndex length first := by
  intro total htotal
  exact lt_of_le_of_lt hle (hsecond total htotal)

/--
An extended orbit consists of finite or infinite orbit segments. Finite
segments share their last point with the next segment, while infinite
segments converge to the first point of the next segment.
-/
structure ExtendedOrbitData {X : Type*} [TopologicalSpace X]
    (relation : Correspondence X X) where
  segmentCount : Option ℕ
  segmentCountPositive : ∀ count, segmentCount = some count → 0 < count
  segmentLength : ℕ → Option ℕ
  segmentLengthPositive : ∀ segment, ActiveSegment segmentCount segment →
    ∀ length, segmentLength segment = some length → 0 < length
  point : ℕ → ℕ → X
  step : ∀ segment, ActiveSegment segmentCount segment → ∀ index,
    SegmentIndex (segmentLength segment) (index + 1) →
      point segment (index + 1) ∈ relation (point segment index)
  finiteStitch : ∀ segment, ActiveSegment segmentCount (segment + 1) →
    ∀ length, segmentLength segment = some length →
      point segment (length - 1) = point (segment + 1) 0
  infiniteStitch : ∀ segment, ActiveSegment segmentCount (segment + 1) →
    segmentLength segment = none →
      Tendsto (point segment) atTop (nhds (point (segment + 1) 0))

/-- An ordinary infinite orbit is an extended orbit with one infinite segment. -/
def ExtendedOrbitData.ofInfiniteOrbit {X : Type*} [TopologicalSpace X]
    {relation : Correspondence X X} (point : ℕ → X)
    (hstep : IsInfiniteOrbit relation point) : ExtendedOrbitData relation where
  segmentCount := some 1
  segmentCountPositive := by
    intro count hcount
    cases hcount
    exact Nat.zero_lt_succ 0
  segmentLength := fun _ ↦ none
  segmentLengthPositive := by simp
  point := fun _ ↦ point
  step := by
    intro segment hsegment index _
    have hzero : segment = 0 := by
      have := hsegment 1 rfl
      omega
    subst segment
    exact hstep index
  finiteStitch := by
    intro segment hsegment
    have := hsegment 1 rfl
    omega
  infiniteStitch := by
    intro segment hsegment
    have := hsegment 1 rfl
    omega

@[simp] theorem ExtendedOrbitData.ofInfiniteOrbit_point
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (point : ℕ → X) (hstep : IsInfiniteOrbit relation point)
    (segment index : ℕ) :
    (ExtendedOrbitData.ofInfiniteOrbit point hstep).point segment index = point index :=
  rfl

/-- Rectangular-prefix variation of an extended orbit for a supplied edge cost. -/
def ExtendedOrbitData.prefixVariationWith {X : Type*} [TopologicalSpace X]
    {relation : Correspondence X X} (orbit : ExtendedOrbitData relation)
    (cost : X → X → ℝ) (segments points : ℕ) : ℝ := by
  classical
  exact ∑ segment ∈ Finset.range segments, ∑ index ∈ Finset.range points,
    if ActiveSegment orbit.segmentCount segment ∧
        SegmentIndex (orbit.segmentLength segment) (index + 1)
    then cost (orbit.point segment index) (orbit.point segment (index + 1))
    else 0

/-- Prefix variation of an ordinary infinite orbit, viewed as one extended segment. -/
theorem ExtendedOrbitData.prefixVariationWith_ofInfiniteOrbit
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (point : ℕ → X) (hstep : IsInfiniteOrbit relation point)
    (cost : X → X → ℝ) (points : ℕ) :
    (ExtendedOrbitData.ofInfiniteOrbit point hstep).prefixVariationWith
        cost 1 points =
      ∑ index ∈ Finset.range points, cost (point index) (point (index + 1)) := by
  classical
  simp [ExtendedOrbitData.prefixVariationWith, ExtendedOrbitData.ofInfiniteOrbit,
    ActiveSegment, SegmentIndex]

/-- Finite rectangular prefixes have unbounded variation for a supplied edge cost. -/
def HasUnboundedExtendedVariationWith {X : Type*} [TopologicalSpace X]
    {relation : Correspondence X X} (cost : X → X → ℝ)
    (orbit : ExtendedOrbitData relation) : Prop :=
  ∀ bound : ℝ, ∃ segments points : ℕ,
    bound ≤ orbit.prefixVariationWith cost segments points

/-- Metric total variation of an extended orbit is unbounded. -/
def HasUnboundedExtendedVariation {X : Type*} [PseudoMetricSpace X]
    {relation : Correspondence X X} (orbit : ExtendedOrbitData relation) : Prop :=
  HasUnboundedExtendedVariationWith dist orbit

end Topology
end Math
