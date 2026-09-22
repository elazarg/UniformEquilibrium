/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Instances.Real.Lemmas

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

open scoped BigOperators Topology

namespace Math
namespace Topology

open Filter Set

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

/-- A positive potential drop along a sequence gives a uniform bound on every
finite prefix of its accumulated cost. -/
theorem sum_range_cost_le_of_potential_bounds
    {X : Type*} {point : ℕ → X}
    {cost : X → X → ℝ} {potential : X → ℝ}
    {constant lower upper : ℝ}
    (hconstant : 0 < constant)
    (hlower : ∀ index, lower ≤ potential (point index))
    (hupper : potential (point 0) ≤ upper)
    (hdecrease : ∀ index,
      potential (point (index + 1)) ≤
        potential (point index) - constant * cost (point index) (point (index + 1)))
    (horizon : ℕ) :
    ∑ index ∈ Finset.range horizon,
        cost (point index) (point (index + 1)) ≤
      (upper - lower) / constant := by
  apply (le_div_iff₀ hconstant).2
  rw [Finset.sum_mul]
  calc
    ∑ index ∈ Finset.range horizon,
          cost (point index) (point (index + 1)) * constant ≤
        ∑ index ∈ Finset.range horizon,
          (potential (point index) - potential (point (index + 1))) := by
      apply Finset.sum_le_sum
      intro index _
      simpa only [mul_comm] using
        (le_sub_iff_add_le.2 (by
          simpa only [add_comm] using
            (le_sub_iff_add_le.1 (hdecrease index))))
    _ = potential (point 0) - potential (point horizon) := by
      rw [Finset.sum_range_sub']
    _ ≤ upper - lower := sub_le_sub hupper (hlower horizon)

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

/-- A continuous scalar potential that decreases along every valid edge is
no larger at the next segment start than at any point of the current segment.
The finite and infinite stitch clauses are used separately. -/
theorem ExtendedOrbitData.potential_nextStart_le_point
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation)
    (potential : X → ℝ) (hcontinuous : Continuous potential)
    (hstep : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      potential (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index))
    (segment : ℕ)
    (hnextActive : ActiveSegment orbit.segmentCount (segment + 1))
    (index : ℕ)
    (hindex : SegmentIndex (orbit.segmentLength segment) index) :
    potential (orbit.point (segment + 1) 0) ≤
      potential (orbit.point segment index) := by
  have hactive : ActiveSegment orbit.segmentCount segment := hnextActive.pred
  cases hlength : orbit.segmentLength segment with
  | some length =>
      have hlengthPositive : 0 < length :=
        orbit.segmentLengthPositive segment hactive length hlength
      have hindexLt : index < length := hindex length hlength
      have hindexEnd : index ≤ length - 1 := by omega
      have hreach : ∀ endpoint, index ≤ endpoint → endpoint < length →
          potential (orbit.point segment endpoint) ≤
            potential (orbit.point segment index) := by
        intro endpoint hindexEndpoint
        induction endpoint, hindexEndpoint using Nat.le_induction with
        | base =>
            intro _
            exact le_rfl
        | succ later hindexLater ih =>
            intro hlaterSucc
            have hlaterIndex :
                SegmentIndex (orbit.segmentLength segment) (later + 1) := by
              intro total htotal
              have htotalLength : total = length :=
                Option.some.inj (htotal.symm.trans hlength)
              subst total
              omega
            exact (hstep segment later hactive hlaterIndex).trans
              (ih (by omega))
      have hendLe : potential (orbit.point segment (length - 1)) ≤
          potential (orbit.point segment index) :=
        hreach (length - 1) hindexEnd (by omega)
      rw [← orbit.finiteStitch segment hnextActive length hlength]
      exact hendLe
  | none =>
      have hanti : Antitone (fun i => potential (orbit.point segment i)) := by
        apply antitone_nat_of_succ_le
        intro i
        apply hstep segment i hactive
        simp [SegmentIndex, hlength]
      have htendsto : Tendsto (fun i => potential (orbit.point segment i))
          atTop (nhds (potential (orbit.point (segment + 1) 0))) :=
        hcontinuous.continuousAt.tendsto.comp
          (orbit.infiniteStitch segment hnextActive hlength)
      apply le_of_tendsto htendsto
      filter_upwards [eventually_ge_atTop index] with later hlater
      exact hanti hlater

/-- A progressive cluster point of an extended orbit is approached either
along segment indices tending to infinity, or along point indices tending to
infinity in the final segment. This excludes arbitrary repeated selections
that do not move forward through the extended orbit. -/
def ExtendedOrbitData.IsProgressiveClusterPoint
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation) (limit : X) : Prop :=
  ∃ segment index : ℕ → ℕ,
    (∀ rank, ActiveSegment orbit.segmentCount (segment rank)) ∧
    (∀ rank, SegmentIndex (orbit.segmentLength (segment rank)) (index rank)) ∧
    Tendsto (fun rank ↦ orbit.point (segment rank) (index rank))
      atTop (nhds limit) ∧
    ((orbit.segmentCount = none ∧ Tendsto segment atTop atTop) ∨
      ∃ count, orbit.segmentCount = some count ∧ 0 < count ∧
        (∀ᶠ rank in atTop, segment rank = count - 1) ∧
        Tendsto index atTop atTop)

/-- A scalar potential decreasing on valid edges decreases between any two
valid points of the same segment that occur in order. -/
theorem ExtendedOrbitData.potential_point_le_point_of_le
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation)
    (potential : X → ℝ)
    (hstep : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      potential (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index))
    (segment first later : ℕ)
    (hactive : ActiveSegment orbit.segmentCount segment)
    (hlater : SegmentIndex (orbit.segmentLength segment) later)
    (hfirstLater : first ≤ later) :
    potential (orbit.point segment later) ≤
      potential (orbit.point segment first) := by
  induction later, hfirstLater using Nat.le_induction with
  | base => exact le_rfl
  | succ later hfirstLater ih =>
      exact (hstep segment later hactive hlater).trans
        (ih (hlater.mono (Nat.le_succ later)))

/-- A continuous scalar potential decreasing on valid edges is no larger at
a point of a later active segment than at any valid point of an earlier one.
Finite and infinite stitches are both handled by
`potential_nextStart_le_point`. -/
theorem ExtendedOrbitData.potential_point_le_point_of_segment_lt
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation)
    (potential : X → ℝ) (hcontinuous : Continuous potential)
    (hstep : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      potential (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index))
    (firstSegment laterSegment firstIndex laterIndex : ℕ)
    (hlaterActive : ActiveSegment orbit.segmentCount laterSegment)
    (hfirstIndex : SegmentIndex
      (orbit.segmentLength firstSegment) firstIndex)
    (hlaterIndex : SegmentIndex
      (orbit.segmentLength laterSegment) laterIndex)
    (hsegment : firstSegment < laterSegment) :
    potential (orbit.point laterSegment laterIndex) ≤
      potential (orbit.point firstSegment firstIndex) := by
  have hfirstNextActive : ActiveSegment orbit.segmentCount (firstSegment + 1) := by
    intro total htotal
    exact (Nat.succ_le_of_lt hsegment).trans_lt (hlaterActive total htotal)
  have hfirstNext : potential (orbit.point (firstSegment + 1) 0) ≤
      potential (orbit.point firstSegment firstIndex) := by
    apply orbit.potential_nextStart_le_point potential hcontinuous hstep
      firstSegment hfirstNextActive firstIndex hfirstIndex
  have hstarts : ∀ segment, firstSegment + 1 ≤ segment →
      ActiveSegment orbit.segmentCount segment →
      potential (orbit.point segment 0) ≤
        potential (orbit.point firstSegment firstIndex) := by
    intro segment hfirstSegment
    induction segment, hfirstSegment using Nat.le_induction with
    | base =>
        intro _
        exact hfirstNext
    | succ segment hfirstSegment ih =>
        intro hactive
        have hzero : SegmentIndex (orbit.segmentLength segment) 0 := by
          intro length hlength
          exact orbit.segmentLengthPositive segment hactive.pred length hlength
        exact (orbit.potential_nextStart_le_point potential hcontinuous hstep
          segment hactive 0 hzero).trans (ih hactive.pred)
  exact (orbit.potential_point_le_point_of_le potential hstep laterSegment
    0 laterIndex hlaterActive hlaterIndex (Nat.zero_le _)).trans
      (hstarts laterSegment (Nat.succ_le_of_lt hsegment) hlaterActive)

/-- The value at a progressive cluster point of a continuous scalar potential
decreasing on valid edges is no larger than at any valid orbit point. -/
theorem ExtendedOrbitData.IsProgressiveClusterPoint.potential_le_point
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    {orbit : ExtendedOrbitData relation} {limit : X}
    (hcluster : orbit.IsProgressiveClusterPoint limit)
    (potential : X → ℝ) (hcontinuous : Continuous potential)
    (hstep : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      potential (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index))
    (segment index : ℕ)
    (hactive : ActiveSegment orbit.segmentCount segment)
    (hindex : SegmentIndex (orbit.segmentLength segment) index) :
    potential limit ≤ potential (orbit.point segment index) := by
  rcases hcluster with
    ⟨selectedSegment, selectedIndex, hselectedActive, hselectedIndex,
      htendsto, hprogress⟩
  have hpotentialTendsto : Tendsto
      (fun rank ↦ potential
        (orbit.point (selectedSegment rank) (selectedIndex rank)))
      atTop (nhds (potential limit)) :=
    hcontinuous.continuousAt.tendsto.comp htendsto
  apply le_of_tendsto hpotentialTendsto
  rcases hprogress with hsegments | hlast
  · filter_upwards
      [hsegments.2.eventually (eventually_ge_atTop (segment + 1))]
      with rank hrank
    exact orbit.potential_point_le_point_of_segment_lt potential hcontinuous
      hstep segment (selectedSegment rank) index (selectedIndex rank)
        (hselectedActive rank) hindex (hselectedIndex rank) (by omega)
  · obtain ⟨count, hcount, hcountPositive, hsegmentEventually,
        hindexTendsto⟩ := hlast
    have hsegmentLt : segment < count := hactive count hcount
    by_cases hbeforeLast : segment < count - 1
    · filter_upwards [hsegmentEventually] with rank hrank
      have hrankActive : ActiveSegment orbit.segmentCount (count - 1) := by
        simpa only [hrank] using hselectedActive rank
      have hrankIndex : SegmentIndex (orbit.segmentLength (count - 1))
          (selectedIndex rank) := by
        simpa only [hrank] using hselectedIndex rank
      simpa only [hrank] using
        (orbit.potential_point_le_point_of_segment_lt potential hcontinuous
          hstep segment (count - 1) index (selectedIndex rank)
            hrankActive hindex hrankIndex hbeforeLast)
    · have hsegmentLast : segment = count - 1 := by omega
      filter_upwards
        [hsegmentEventually,
          hindexTendsto.eventually (eventually_ge_atTop index)]
        with rank hrankSegment hrankIndex
      have hrankActive : ActiveSegment orbit.segmentCount segment := by
        simpa only [hrankSegment, hsegmentLast] using hselectedActive rank
      have hrankValid : SegmentIndex (orbit.segmentLength segment)
          (selectedIndex rank) := by
        simpa only [hrankSegment, hsegmentLast] using hselectedIndex rank
      simpa only [hrankSegment, hsegmentLast] using
        (orbit.potential_point_le_point_of_le potential hstep segment
          index (selectedIndex rank) hrankActive hrankValid hrankIndex)

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

/-- The last point reached by a rectangular prefix inside one segment. -/
def segmentPrefixEndpoint (length : Option ℕ) (points : ℕ) : ℕ :=
  match length with
  | none => points
  | some total => min points (total - 1)

/-- Accumulated cost in one rectangular-prefix row of an extended orbit. -/
def ExtendedOrbitData.segmentPrefixVariationWith
    {X : Type*} [TopologicalSpace X]
    {relation : Correspondence X X} (orbit : ExtendedOrbitData relation)
    (cost : X → X → ℝ) (segment points : ℕ) : ℝ := by
  classical
  exact ∑ index ∈ Finset.range points,
    if SegmentIndex (orbit.segmentLength segment) (index + 1)
    then cost (orbit.point segment index) (orbit.point segment (index + 1))
    else 0

/-- The endpoint of a segment prefix is a valid point whenever the segment is
active. Positivity of finite segment lengths handles the zero endpoint. -/
theorem ExtendedOrbitData.segmentPrefixEndpoint_index
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation) (segment points : ℕ)
    (hactive : ActiveSegment orbit.segmentCount segment) :
    SegmentIndex (orbit.segmentLength segment)
      (segmentPrefixEndpoint (orbit.segmentLength segment) points) := by
  cases hlength : orbit.segmentLength segment with
  | none => simp [SegmentIndex, segmentPrefixEndpoint]
  | some length =>
      have hpositive :=
        orbit.segmentLengthPositive segment hactive length hlength
      intro total htotal
      have htotalLength : total = length := Option.some.inj htotal.symm
      subst total
      simp only [segmentPrefixEndpoint]
      omega

/-- If a potential pays a fixed multiple of every valid edge cost, then it
pays every finite prefix of one segment out of the potential drop to the
prefix endpoint. -/
theorem ExtendedOrbitData.constant_mul_segmentPrefixVariationWith_le
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation)
    (cost : X → X → ℝ) (potential : X → ℝ) (constant : ℝ)
    (hscaled : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      constant * cost (orbit.point segment index)
          (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index) -
          potential (orbit.point segment (index + 1)))
    (segment points : ℕ)
    (hactive : ActiveSegment orbit.segmentCount segment) :
    constant * orbit.segmentPrefixVariationWith cost segment points ≤
      potential (orbit.point segment 0) -
        potential (orbit.point segment
          (segmentPrefixEndpoint (orbit.segmentLength segment) points)) := by
  classical
  have htelescope : ∀ horizon,
      (∑ index ∈ Finset.range horizon,
        if SegmentIndex (orbit.segmentLength segment) (index + 1)
        then potential (orbit.point segment index) -
          potential (orbit.point segment (index + 1))
        else 0) =
      potential (orbit.point segment 0) -
        potential (orbit.point segment
          (segmentPrefixEndpoint (orbit.segmentLength segment) horizon)) := by
    intro horizon
    cases hlength : orbit.segmentLength segment with
    | none =>
        simp only [SegmentIndex, reduceCtorEq, false_implies,
          forall_const, ite_true, segmentPrefixEndpoint]
        exact Finset.sum_range_sub' (fun index ↦
          potential (orbit.point segment index)) horizon
    | some length =>
        induction horizon with
        | zero => simp [segmentPrefixEndpoint]
        | succ horizon ih =>
            rw [Finset.sum_range_succ, ih]
            by_cases hvalid : horizon + 1 < length
            · have hmin : min horizon (length - 1) = horizon := by omega
              have hminSucc : min (horizon + 1) (length - 1) =
                  horizon + 1 := by omega
              rw [ite_eq_left]
              · simp only [segmentPrefixEndpoint, hmin, hminSucc]
                ring
              · intro total htotal
                have htotalLength : total = length := Option.some.inj htotal.symm
                subst total
                exact hvalid
            · have hmin : min horizon (length - 1) = length - 1 := by omega
              have hminSucc : min (horizon + 1) (length - 1) =
                  length - 1 := by omega
              rw [ite_eq_right]
              · simp only [segmentPrefixEndpoint, hmin, hminSucc,
                  add_zero]
              · intro hindex
                exact hvalid (hindex length rfl)
  rw [ExtendedOrbitData.segmentPrefixVariationWith, Finset.mul_sum]
  calc
    ∑ index ∈ Finset.range points,
          constant *
            (if SegmentIndex (orbit.segmentLength segment) (index + 1)
            then cost (orbit.point segment index)
              (orbit.point segment (index + 1))
            else 0) ≤
        ∑ index ∈ Finset.range points,
          if SegmentIndex (orbit.segmentLength segment) (index + 1)
          then potential (orbit.point segment index) -
            potential (orbit.point segment (index + 1))
          else 0 := by
      apply Finset.sum_le_sum
      intro index _
      by_cases hindex :
          SegmentIndex (orbit.segmentLength segment) (index + 1)
      · simpa only [hindex, ite_true] using hscaled segment index hactive hindex
      · simp only [hindex, ite_false, mul_zero]
        exact le_rfl
    _ = potential (orbit.point segment 0) -
        potential (orbit.point segment
          (segmentPrefixEndpoint (orbit.segmentLength segment) points)) :=
      htelescope points

/-- The scaled cost of a segment prefix is paid by the potential drop to the
next segment start. This is the common finite/infinite stitch interface. -/
theorem ExtendedOrbitData.constant_mul_segmentPrefixVariationWith_le_nextStart
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation)
    (cost : X → X → ℝ) (potential : X → ℝ)
    (hcontinuous : Continuous potential) (constant : ℝ)
    (hstep : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      potential (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index))
    (hscaled : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      constant * cost (orbit.point segment index)
          (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index) -
          potential (orbit.point segment (index + 1)))
    (segment points : ℕ)
    (hnextActive : ActiveSegment orbit.segmentCount (segment + 1)) :
    constant * orbit.segmentPrefixVariationWith cost segment points ≤
      potential (orbit.point segment 0) -
        potential (orbit.point (segment + 1) 0) := by
  have hactive := hnextActive.pred
  have hendpoint := orbit.segmentPrefixEndpoint_index segment points hactive
  exact (orbit.constant_mul_segmentPrefixVariationWith_le cost potential constant
    hscaled segment points hactive).trans
      (sub_le_sub_left
        (orbit.potential_nextStart_le_point potential hcontinuous hstep segment
          hnextActive _ hendpoint) _)

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

/-- A continuous lower-bounded Lyapunov potential paying a positive multiple
of every valid edge cost rules out unbounded rectangular-prefix variation of
an extended orbit. Infinite segment counts telescope through the stitches;
for a finite segment count, the final segment is charged to its own valid
prefix endpoint. -/
theorem ExtendedOrbitData.not_hasUnboundedExtendedVariationWith_of_potential
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation)
    (cost : X → X → ℝ) (potential : X → ℝ)
    (hcontinuous : Continuous potential) (constant lower : ℝ)
    (hconstant : 0 < constant)
    (hlower : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) index →
      lower ≤ potential (orbit.point segment index))
    (hstep : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      potential (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index))
    (hscaled : ∀ segment index,
      ActiveSegment orbit.segmentCount segment →
      SegmentIndex (orbit.segmentLength segment) (index + 1) →
      constant * cost (orbit.point segment index)
          (orbit.point segment (index + 1)) ≤
        potential (orbit.point segment index) -
          potential (orbit.point segment (index + 1))) :
    ¬HasUnboundedExtendedVariationWith cost orbit := by
  classical
  intro hunbounded
  have hzeroActive : ActiveSegment orbit.segmentCount 0 := by
    intro count hcount
    exact orbit.segmentCountPositive count hcount
  have hzeroIndex : SegmentIndex (orbit.segmentLength 0) 0 := by
    intro length hlength
    exact orbit.segmentLengthPositive 0 hzeroActive length hlength
  have hbudgetNonneg : 0 ≤ potential (orbit.point 0 0) - lower :=
    sub_nonneg.mpr (hlower 0 0 hzeroActive hzeroIndex)
  cases hcount : orbit.segmentCount with
  | none =>
      let bound := (potential (orbit.point 0 0) - lower) / constant
      obtain ⟨segments, points, hlarge⟩ := hunbounded (bound + 1)
      have hactive : ∀ segment,
          ActiveSegment orbit.segmentCount segment := by
        intro segment
        simp [ActiveSegment, hcount]
      have hprefix : orbit.prefixVariationWith cost segments points =
          ∑ segment ∈ Finset.range segments,
            orbit.segmentPrefixVariationWith cost segment points := by
        simp [ExtendedOrbitData.prefixVariationWith,
          ExtendedOrbitData.segmentPrefixVariationWith, ActiveSegment, hcount]
      have hscaledPrefix : constant * orbit.prefixVariationWith
          cost segments points ≤ potential (orbit.point 0 0) - lower := by
        rw [hprefix, Finset.mul_sum]
        calc
          ∑ segment ∈ Finset.range segments,
                constant * orbit.segmentPrefixVariationWith
                  cost segment points ≤
              ∑ segment ∈ Finset.range segments,
                (potential (orbit.point segment 0) -
                  potential (orbit.point (segment + 1) 0)) := by
            apply Finset.sum_le_sum
            intro segment _
            exact orbit.constant_mul_segmentPrefixVariationWith_le_nextStart
              cost potential hcontinuous constant hstep hscaled segment points
                (hactive (segment + 1))
          _ = potential (orbit.point 0 0) -
              potential (orbit.point segments 0) := by
            rw [Finset.sum_range_sub']
          _ ≤ potential (orbit.point 0 0) - lower :=
            sub_le_sub_left
              (hlower segments 0 (hactive segments) (by
                intro length hlength
                exact orbit.segmentLengthPositive segments (hactive segments)
                  length hlength)) _
      have hprefixBound : orbit.prefixVariationWith cost segments points ≤
          bound := by
        apply (le_div_iff₀ hconstant).2
        simpa only [mul_comm] using hscaledPrefix
      exact (not_le_of_gt (lt_add_one bound)) (hlarge.trans hprefixBound)
  | some count =>
      let budget := potential (orbit.point 0 0) - lower
      let bound := (count : ℝ) * budget / constant
      obtain ⟨segments, points, hlarge⟩ := hunbounded (bound + 1)
      let activeSegments :=
        (Finset.range segments).filter (fun segment ↦ segment < count)
      have hactiveSegmentsCard : activeSegments.card ≤ count := by
        have hsubset : activeSegments ⊆ Finset.range count := by
          intro segment hsegment
          simp only [activeSegments, Finset.mem_filter,
            Finset.mem_range] at hsegment
          exact Finset.mem_range.mpr hsegment.2
        simpa only [Finset.card_range] using Finset.card_le_card hsubset
      have hprefix : orbit.prefixVariationWith cost segments points =
          ∑ segment ∈ activeSegments,
            orbit.segmentPrefixVariationWith cost segment points := by
        simp only [ExtendedOrbitData.prefixVariationWith,
          ExtendedOrbitData.segmentPrefixVariationWith, activeSegments,
          Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro segment hsegment
        have hactiveIff :
            ActiveSegment orbit.segmentCount segment ↔ segment < count := by
          constructor
          · intro hactive
            exact hactive count hcount
          · intro hsegmentCount total htotal
            have htotalCount : total = count :=
              Option.some.inj (htotal.symm.trans hcount)
            subst total
            exact hsegmentCount
        by_cases hsegmentCount : segment < count
        · have hactive := hactiveIff.mpr hsegmentCount
          simp only [hsegmentCount, hactive, true_and, ite_true]
        · have hnotActive : ¬ActiveSegment orbit.segmentCount segment :=
            fun hactive => hsegmentCount (hactiveIff.mp hactive)
          simp only [hsegmentCount, hnotActive, false_and, ite_false]
          exact Finset.sum_const_zero
      have hsegmentBound : ∀ segment, segment ∈ activeSegments →
          constant * orbit.segmentPrefixVariationWith cost segment points ≤
            budget := by
        intro segment hsegment
        have hsegmentCount : segment < count := by
          have hsegment' := hsegment
          simp only [activeSegments, Finset.mem_filter,
            Finset.mem_range] at hsegment'
          exact hsegment'.2
        have hactive : ActiveSegment orbit.segmentCount segment := by
          intro total htotal
          have htotalCount : total = count :=
            Option.some.inj (htotal.symm.trans hcount)
          subst total
          exact hsegmentCount
        have hendpoint := orbit.segmentPrefixEndpoint_index segment points hactive
        have hdrop := orbit.constant_mul_segmentPrefixVariationWith_le
          cost potential constant hscaled segment points hactive
        have hlowerEndpoint := hlower segment _ hactive hendpoint
        have hstart : potential (orbit.point segment 0) ≤
            potential (orbit.point 0 0) := by
          by_cases hsegmentZero : segment = 0
          · subst segment
            exact le_rfl
          · have hzeroIndexSegment : SegmentIndex
                (orbit.segmentLength segment) 0 := by
              intro length hlength
              exact orbit.segmentLengthPositive segment hactive length hlength
            exact orbit.potential_point_le_point_of_segment_lt
              potential hcontinuous hstep 0 segment 0 0 hactive hzeroIndex
                hzeroIndexSegment (Nat.pos_of_ne_zero hsegmentZero)
        dsimp only [budget]
        exact hdrop.trans <| (sub_le_sub_left hlowerEndpoint _).trans
          (sub_le_sub_right hstart lower)
      have hscaledPrefix : constant * orbit.prefixVariationWith
          cost segments points ≤ (count : ℝ) * budget := by
        rw [hprefix, Finset.mul_sum]
        calc
          ∑ segment ∈ activeSegments,
                constant * orbit.segmentPrefixVariationWith
                  cost segment points ≤
              ∑ _segment ∈ activeSegments, budget := by
            apply Finset.sum_le_sum
            intro segment hsegment
            exact hsegmentBound segment hsegment
          _ = (activeSegments.card : ℝ) * budget := by simp
          _ ≤ (count : ℝ) * budget := by
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast hactiveSegmentsCard) (by
                dsimp only [budget]
                exact hbudgetNonneg)
      have hprefixBound : orbit.prefixVariationWith cost segments points ≤
          bound := by
        apply (le_div_iff₀ hconstant).2
        simpa only [bound, mul_comm] using hscaledPrefix
      exact (not_le_of_gt (lt_add_one bound)) (hlarge.trans hprefixBound)

end Topology
end Math
