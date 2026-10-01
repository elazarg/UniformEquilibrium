import MathUE.Topology.ExtendedOrbit
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Actual finite or convergent-infinite segment followed by a finite word

These constructors only change the indexing grammar, not the original words.
Finite lengths count points. The finite word is extended constantly after its
last point, where the extended-orbit grammar no longer queries its edges.
-/

noncomputable section

open scoped BigOperators Topology Classical

namespace Math.Topology

open Filter Set

/-- Enlarge only the edge relation, retaining all original points, lengths
and finite or convergence stitches. -/
def ExtendedOrbitData.mapRelation {X : Type*} [TopologicalSpace X]
    {first second : Correspondence X X} (orbit : ExtendedOrbitData first)
    (hsubset : ∀ point, first point ⊆ second point) : ExtendedOrbitData second where
  segmentCount := orbit.segmentCount
  segmentCountPositive := orbit.segmentCountPositive
  segmentLength := orbit.segmentLength
  segmentLengthPositive := orbit.segmentLengthPositive
  point := orbit.point
  step := fun segment hsegment index hindex =>
    hsubset _ (orbit.step segment hsegment index hindex)
  finiteStitch := orbit.finiteStitch
  infiniteStitch := orbit.infiniteStitch

/-- The original finite word, constant after its last point. -/
def finiteOrbitNatWord {X : Type*} {length : ℕ} (word : Fin (length + 1) → X)
    (index : ℕ) : X := word ⟨min index length, by omega⟩

theorem finiteOrbitNatWord_fin {X : Type*} {length : ℕ}
    (word : Fin (length + 1) → X) (index : Fin (length + 1)) :
    finiteOrbitNatWord word index = word index := by
  apply congrArg word
  apply Fin.ext
  exact min_eq_left (by omega)

@[simp] theorem finiteOrbitNatWord_zero {X : Type*} {length : ℕ}
    (word : Fin (length + 1) → X) : finiteOrbitNatWord word 0 = word 0 :=
  finiteOrbitNatWord_fin word 0

@[simp] theorem finiteOrbitNatWord_last {X : Type*} {length : ℕ}
    (word : Fin (length + 1) → X) :
    finiteOrbitNatWord word length = word (Fin.last length) :=
  finiteOrbitNatWord_fin word (Fin.last length)

theorem finiteOrbitNatWord_step {X : Type*} {relation : Correspondence X X}
    {length : ℕ} (word : Fin (length + 1) → X) (horbit : IsFiniteOrbit relation word)
    (index : ℕ) (hindex : index + 1 < length + 1) :
    finiteOrbitNatWord word (index + 1) ∈ relation (finiteOrbitNatWord word index) := by
  let edge : Fin length := ⟨index, by omega⟩
  have hfirst : finiteOrbitNatWord word index = word edge.castSucc :=
    finiteOrbitNatWord_fin word edge.castSucc
  have hnext : finiteOrbitNatWord word (index + 1) = word edge.succ :=
    finiteOrbitNatWord_fin word edge.succ
  rw [hfirst, hnext]
  exact horbit edge

theorem finiteOrbitNatWord_segmentStep {X : Type*} {relation : Correspondence X X}
    {length : ℕ} (word : Fin (length + 1) → X) (horbit : IsFiniteOrbit relation word)
    (index : ℕ) (hindex : SegmentIndex (some (length + 1)) (index + 1)) :
    finiteOrbitNatWord word (index + 1) ∈ relation (finiteOrbitNatWord word index) :=
  finiteOrbitNatWord_step word horbit index (hindex (length + 1) rfl)

theorem finiteOrbitNatWord_stays {X : Type*} {length : ℕ}
    (word : Fin (length + 1) → X) (carrier : Set X) (hword : ∀ index, word index ∈ carrier)
    (index : ℕ) : finiteOrbitNatWord word index ∈ carrier :=
  hword ⟨min index length, by omega⟩

/-- The finite prefix pays exactly the original finite-word edge cost. -/
theorem finiteOrbitNatWord_variation {X : Type*} {length : ℕ}
    (word : Fin (length + 1) → X) (cost : X → X → ℝ) :
    (∑ index ∈ Finset.range length,
      cost (finiteOrbitNatWord word index) (finiteOrbitNatWord word (index + 1))) =
      finiteOrbitVariationWith cost word := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro index _
  have hfirst : finiteOrbitNatWord word index = word index.castSucc :=
    finiteOrbitNatWord_fin word index.castSucc
  have hnext : finiteOrbitNatWord word (index + 1) = word index.succ :=
    finiteOrbitNatWord_fin word index.succ
  rw [hfirst, hnext]

theorem finiteOrbitNatWord_segmentPrefix_variation {X : Type*} {length : ℕ}
    (word : Fin (length + 1) → X) (cost : X → X → ℝ) :
    (∑ index ∈ Finset.range length, if SegmentIndex (some (length + 1)) (index + 1)
      then cost (finiteOrbitNatWord word index) (finiteOrbitNatWord word (index + 1))
      else 0) = finiteOrbitVariationWith cost word := by
  calc
    _ = ∑ index ∈ Finset.range length,
        cost (finiteOrbitNatWord word index) (finiteOrbitNatWord word (index + 1)) := by
      apply Finset.sum_congr rfl
      intro index hindex
      have hvalid : SegmentIndex (some (length + 1)) (index + 1) := by
        intro total htotal
        have hequal : length + 1 = total := Option.some.inj htotal
        have hlt := Finset.mem_range.mp hindex
        omega
      rw [ite_eq_left hvalid]
    _ = finiteOrbitVariationWith cost word := finiteOrbitNatWord_variation word cost

/-- Form the actual pair: a finite or convergent-infinite first segment and
the unchanged finite return word. The source supplies actual edges and seam. -/
def ExtendedOrbitData.ofSegmentThenFinite
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (firstLength : Option ℕ) (first : ℕ → X)
    (hpositive : ∀ length, firstLength = some length → 0 < length)
    (hfirst : ∀ index, SegmentIndex firstLength (index + 1) →
      first (index + 1) ∈ relation (first index))
    {length : ℕ} (word : Fin (length + 1) → X) (hword : IsFiniteOrbit relation word)
    (hfinite : ∀ total, firstLength = some total → first (total - 1) = word 0)
    (hinfinite : firstLength = none → Tendsto first atTop (𝓝 (word 0))) :
    ExtendedOrbitData relation where
  segmentCount := some 2
  segmentCountPositive := by intro count hcount; cases hcount; decide
  segmentLength := fun segment => if segment = 0 then firstLength else some (length + 1)
  segmentLengthPositive := by
    intro segment _ total htotal
    by_cases hzero : segment = 0
    · subst segment
      exact hpositive total htotal
    · have hequal : length + 1 = total := by
        exact Option.some.inj (by simpa only [ite_eq_right hzero] using htotal)
      omega
  point := fun segment index =>
    if segment = 0 then first index else finiteOrbitNatWord word index
  step := by
    intro segment hactive index hindex
    have hlt : segment < 2 := hactive 2 rfl
    rcases (show segment = 0 ∨ segment = 1 by omega) with rfl | rfl
    · exact hfirst index hindex
    · have hindex' : index + 1 < length + 1 := by
        apply hindex (length + 1)
        rfl
      exact finiteOrbitNatWord_step word hword index hindex'
  finiteStitch := by
    intro segment hactive total htotal
    have hzero : segment = 0 := by have := hactive 2 rfl; omega
    subst segment
    change first (total - 1) = finiteOrbitNatWord word 0
    rw [finiteOrbitNatWord_zero]
    exact hfinite total htotal
  infiniteStitch := by
    intro segment hactive hnone
    have hzero : segment = 0 := by have := hactive 2 rfl; omega
    subst segment
    change Tendsto first atTop (𝓝 (finiteOrbitNatWord word 0))
    rw [finiteOrbitNatWord_zero]
    exact hinfinite hnone

/-- The source carrier is preserved at every valid point of both original
segments, including the finite word's endpoint and an infinite first segment. -/
theorem ExtendedOrbitData.ofSegmentThenFinite_stays
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (firstLength : Option ℕ) (first : ℕ → X)
    (hpositive : ∀ length, firstLength = some length → 0 < length)
    (hfirst : ∀ index, SegmentIndex firstLength (index + 1) →
      first (index + 1) ∈ relation (first index))
    {length : ℕ} (word : Fin (length + 1) → X) (hword : IsFiniteOrbit relation word)
    (hfinite : ∀ total, firstLength = some total → first (total - 1) = word 0)
    (hinfinite : firstLength = none → Tendsto first atTop (𝓝 (word 0)))
    (carrier : Set X) (hfirstCarrier : ∀ index,
      SegmentIndex firstLength index → first index ∈ carrier)
    (hwordCarrier : ∀ index, word index ∈ carrier) :
    let block := ExtendedOrbitData.ofSegmentThenFinite
      firstLength first hpositive hfirst word hword hfinite hinfinite
    ∀ segment, ActiveSegment block.segmentCount segment → ∀ index,
      SegmentIndex (block.segmentLength segment) index → block.point segment index ∈ carrier := by
  dsimp only
  intro segment hactive index hindex
  have hlt : segment < 2 := hactive 2 rfl
  rcases (show segment = 0 ∨ segment = 1 by omega) with rfl | rfl
  · exact hfirstCarrier index hindex
  · have hindex' : index < length + 1 := hindex (length + 1) rfl
    change finiteOrbitNatWord word index ∈ carrier
    rw [show finiteOrbitNatWord word index = word ⟨index, hindex'⟩ from
      finiteOrbitNatWord_fin word ⟨index, hindex'⟩]
    exact hwordCarrier ⟨index, hindex'⟩

/-- A pair pays at least the first segment's actual prefix cost. The added
finite return contributes a nonnegative cost, rather than a supplied charge. -/
theorem ExtendedOrbitData.prefixVariationWith_ofSegmentThenFinite_ge_first
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (firstLength : Option ℕ) (first : ℕ → X)
    (hpositive : ∀ length, firstLength = some length → 0 < length)
    (hfirst : ∀ index, SegmentIndex firstLength (index + 1) →
      first (index + 1) ∈ relation (first index))
    {length : ℕ} (word : Fin (length + 1) → X) (hword : IsFiniteOrbit relation word)
    (hfinite : ∀ total, firstLength = some total → first (total - 1) = word 0)
    (hinfinite : firstLength = none → Tendsto first atTop (𝓝 (word 0)))
    (cost : X → X → ℝ) (hcost : ∀ previous next, 0 ≤ cost previous next) (points : ℕ) :
    (∑ index ∈ Finset.range points, if SegmentIndex firstLength (index + 1)
      then cost (first index) (first (index + 1)) else 0) ≤
      ExtendedOrbitData.prefixVariationWith (ExtendedOrbitData.ofSegmentThenFinite
        firstLength first hpositive hfirst word hword hfinite hinfinite) cost 2 points := by
  classical
  have hreturn : 0 ≤ ∑ index ∈ Finset.range points,
      if SegmentIndex (some (length + 1)) (index + 1)
      then cost (finiteOrbitNatWord word index) (finiteOrbitNatWord word (index + 1))
      else 0 := by
    apply Finset.sum_nonneg
    intro index _
    split_ifs
    · exact hcost _ _
    · exact le_rfl
  have hbound :
      (∑ index ∈ Finset.range points, if SegmentIndex firstLength (index + 1)
        then cost (first index) (first (index + 1)) else 0) ≤
      (∑ index ∈ Finset.range points, if SegmentIndex firstLength (index + 1)
        then cost (first index) (first (index + 1)) else 0) +
      ∑ index ∈ Finset.range points, if SegmentIndex (some (length + 1)) (index + 1)
        then cost (finiteOrbitNatWord word index) (finiteOrbitNatWord word (index + 1))
        else 0 := le_add_of_nonneg_right hreturn
  simpa [ExtendedOrbitData.prefixVariationWith, ExtendedOrbitData.ofSegmentThenFinite,
    ActiveSegment, Finset.sum_range_succ] using hbound

end Math.Topology
