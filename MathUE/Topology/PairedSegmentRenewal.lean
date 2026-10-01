import MathUE.Topology.ExtendedOrbit
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases

/-!
# Renewal by actual pairs of finite or convergent-infinite orbit segments

Local returns are selected recursively from existence at every restart point.
The construction preserves every selected segment literally. A fixed positive
charge in a finite rectangular prefix of each pair forces unbounded variation
of the same renewed extended orbit. No compactness or game hypothesis occurs.
-/

noncomputable section

open scoped BigOperators Topology

namespace Math.Topology

open Filter Set

/-- Increasing the point width cannot decrease rectangular variation when
the edge cost is nonnegative. This uses the existing variation functional. -/
theorem ExtendedOrbitData.prefixVariationWith_mono_points
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (orbit : ExtendedOrbitData relation) (cost : X → X → ℝ)
    (hcost : ∀ first next, 0 ≤ cost first next) (segments : ℕ)
    {first later : ℕ} (hle : first ≤ later) :
    orbit.prefixVariationWith cost segments first ≤
      orbit.prefixVariationWith cost segments later := by
  classical
  simp only [ExtendedOrbitData.prefixVariationWith]
  apply Finset.sum_le_sum
  intro segment _
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle)
  intro index _ _
  split_ifs
  · exact hcost _ _
  · exact le_rfl

private theorem sum_range_double (value : ℕ → ℝ) (count : ℕ) :
    (∑ segment ∈ Finset.range (2 * count), value segment) =
      ∑ rank ∈ Finset.range count, (value (2 * rank) + value (2 * rank + 1)) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show 2 * (count + 1) = 2 * count + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      exact add_assoc _ _ _

/-- Concatenate an actual sequence of two-segment blocks. The second segment
of each block is finite and ends at the first point of the next block. -/
def ExtendedOrbitData.ofPairwiseBlocks
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (block : ℕ → ExtendedOrbitData relation) (lastLength : ℕ → ℕ)
    (hcount : ∀ rank, (block rank).segmentCount = some 2)
    (hlength : ∀ rank, (block rank).segmentLength 1 = some (lastLength rank))
    (hstitch : ∀ rank, (block rank).point 1 (lastLength rank - 1) =
      (block (rank + 1)).point 0 0) : ExtendedOrbitData relation where
  segmentCount := none
  segmentCountPositive := by simp
  segmentLength := fun segment =>
    if segment % 2 = 0 then (block (segment / 2)).segmentLength 0
    else (block (segment / 2)).segmentLength 1
  segmentLengthPositive := by
    intro segment _ length hfinite
    by_cases heven : segment % 2 = 0
    · apply (block (segment / 2)).segmentLengthPositive 0
        (by simp [ActiveSegment, hcount]) length
      simpa only [heven, ite_true] using hfinite
    · apply (block (segment / 2)).segmentLengthPositive 1
        (by simp [ActiveSegment, hcount]) length
      simpa only [heven, ite_false] using hfinite
  point := fun segment index =>
    if segment % 2 = 0 then (block (segment / 2)).point 0 index
    else (block (segment / 2)).point 1 index
  step := by
    intro segment _ index hindex
    by_cases heven : segment % 2 = 0
    · have hindex' : SegmentIndex ((block (segment / 2)).segmentLength 0)
          (index + 1) := by simpa only [heven, ite_true] using hindex
      simpa only [heven, ite_true] using
        (block (segment / 2)).step 0 (by simp [ActiveSegment, hcount]) index hindex'
    · have hindex' : SegmentIndex ((block (segment / 2)).segmentLength 1)
          (index + 1) := by simpa only [heven, ite_false] using hindex
      simpa only [heven, ite_false] using
        (block (segment / 2)).step 1 (by simp [ActiveSegment, hcount]) index hindex'
  finiteStitch := by
    intro segment _ length hfinite
    by_cases heven : segment % 2 = 0
    · have hnextOdd : (segment + 1) % 2 ≠ 0 := by omega
      have hnextDiv : (segment + 1) / 2 = segment / 2 := by omega
      have hfinite' : (block (segment / 2)).segmentLength 0 = some length := by
        simpa only [heven, ite_true] using hfinite
      simpa only [heven, ite_true, hnextOdd, ite_false, hnextDiv] using
        (block (segment / 2)).finiteStitch 0
          (by simp [ActiveSegment, hcount]) length hfinite'
    · have hnextEven : (segment + 1) % 2 = 0 := by omega
      have hnextDiv : (segment + 1) / 2 = segment / 2 + 1 := by omega
      have hfinite' : some (lastLength (segment / 2)) = some length := by
        simpa only [heven, ite_false, hlength] using hfinite
      have hequal : lastLength (segment / 2) = length := Option.some.inj hfinite'
      simpa only [heven, ite_false, hnextEven, ite_true, hnextDiv, hequal] using
        hstitch (segment / 2)
  infiniteStitch := by
    intro segment _ hinfinite
    by_cases heven : segment % 2 = 0
    · have hnextOdd : (segment + 1) % 2 ≠ 0 := by omega
      have hnextDiv : (segment + 1) / 2 = segment / 2 := by omega
      have hinfinite' : (block (segment / 2)).segmentLength 0 = none := by
        simpa only [heven, ite_true] using hinfinite
      simpa only [heven, ite_true, hnextOdd, ite_false, hnextDiv] using
        (block (segment / 2)).infiniteStitch 0
          (by simp [ActiveSegment, hcount]) hinfinite'
    · have hfalse : some (lastLength (segment / 2)) = none := by
        simpa only [heven, ite_false, hlength] using hinfinite
      cases hfalse

@[simp] theorem ExtendedOrbitData.ofPairwiseBlocks_count
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (block : ℕ → ExtendedOrbitData relation) (lastLength : ℕ → ℕ)
    (hcount : ∀ rank, (block rank).segmentCount = some 2)
    (hlength : ∀ rank, (block rank).segmentLength 1 = some (lastLength rank))
    (hstitch : ∀ rank, (block rank).point 1 (lastLength rank - 1) =
      (block (rank + 1)).point 0 0) :
    (ExtendedOrbitData.ofPairwiseBlocks block lastLength hcount hlength hstitch).segmentCount =
      none := rfl

@[simp] theorem ExtendedOrbitData.ofPairwiseBlocks_point
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (block : ℕ → ExtendedOrbitData relation) (lastLength : ℕ → ℕ)
    (hcount : ∀ rank, (block rank).segmentCount = some 2)
    (hlength : ∀ rank, (block rank).segmentLength 1 = some (lastLength rank))
    (hstitch : ∀ rank, (block rank).point 1 (lastLength rank - 1) =
      (block (rank + 1)).point 0 0) (rank : ℕ) (segment : Fin 2) (index : ℕ) :
    (ExtendedOrbitData.ofPairwiseBlocks block lastLength hcount hlength hstitch).point
        (2 * rank + segment) index = (block rank).point segment index := by
  have hdiv : (2 * rank + (segment : ℕ)) / 2 = rank := by omega
  have hmod : (2 * rank + (segment : ℕ)) % 2 = segment := by omega
  change (if (2 * rank + (segment : ℕ)) % 2 = 0
    then (block ((2 * rank + segment) / 2)).point 0 index
    else (block ((2 * rank + segment) / 2)).point 1 index) = _
  rw [hdiv, hmod]
  fin_cases segment
  · rfl
  · rfl

@[simp] theorem ExtendedOrbitData.ofPairwiseBlocks_length
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (block : ℕ → ExtendedOrbitData relation) (lastLength : ℕ → ℕ)
    (hcount : ∀ rank, (block rank).segmentCount = some 2)
    (hlength : ∀ rank, (block rank).segmentLength 1 = some (lastLength rank))
    (hstitch : ∀ rank, (block rank).point 1 (lastLength rank - 1) =
      (block (rank + 1)).point 0 0) (rank : ℕ) (segment : Fin 2) :
    (ExtendedOrbitData.ofPairwiseBlocks block lastLength hcount hlength hstitch).segmentLength
        (2 * rank + segment) = (block rank).segmentLength segment := by
  have hdiv : (2 * rank + (segment : ℕ)) / 2 = rank := by omega
  have hmod : (2 * rank + (segment : ℕ)) % 2 = segment := by omega
  change (if (2 * rank + (segment : ℕ)) % 2 = 0
    then (block ((2 * rank + segment) / 2)).segmentLength 0
    else (block ((2 * rank + segment) / 2)).segmentLength 1) = _
  rw [hdiv, hmod]
  fin_cases segment
  · rfl
  · rfl

/-- The SAME renewed orbit's rectangular prefix is exactly the sum of its
selected blocks' prefixes at the SAME point width. -/
theorem ExtendedOrbitData.prefixVariationWith_ofPairwiseBlocks
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (block : ℕ → ExtendedOrbitData relation) (lastLength : ℕ → ℕ)
    (hcount : ∀ rank, (block rank).segmentCount = some 2)
    (hlength : ∀ rank, (block rank).segmentLength 1 = some (lastLength rank))
    (hstitch : ∀ rank, (block rank).point 1 (lastLength rank - 1) =
      (block (rank + 1)).point 0 0) (cost : X → X → ℝ) (count points : ℕ) :
    ExtendedOrbitData.prefixVariationWith
        (ExtendedOrbitData.ofPairwiseBlocks block lastLength hcount hlength hstitch)
        cost (2 * count) points =
      ∑ rank ∈ Finset.range count, (block rank).prefixVariationWith cost 2 points := by
  classical
  rw [ExtendedOrbitData.prefixVariationWith, sum_range_double]
  apply Finset.sum_congr rfl
  intro rank _
  have hpointZero := ExtendedOrbitData.ofPairwiseBlocks_point
    block lastLength hcount hlength hstitch rank 0
  have hpointOne := ExtendedOrbitData.ofPairwiseBlocks_point
    block lastLength hcount hlength hstitch rank 1
  have hlengthZero := ExtendedOrbitData.ofPairwiseBlocks_length
    block lastLength hcount hlength hstitch rank 0
  have hlengthOne := ExtendedOrbitData.ofPairwiseBlocks_length
    block lastLength hcount hlength hstitch rank 1
  simp only [Fin.val_zero, Nat.add_zero] at hpointZero hlengthZero
  simp only [Fin.val_one] at hpointOne hlengthOne
  simp [ExtendedOrbitData.prefixVariationWith, ActiveSegment, hcount rank,
    hpointZero, hpointOne, hlengthZero, hlengthOne, Finset.sum_range_succ]

/-- Actual local two-segment returns at every restart point produce one
renewed extended orbit. Its second segment is finite; its first can be finite
or convergent-infinite. A positive uniform local charge implies unbounded
rectangular variation, without supplying the renewed orbit or its variation. -/
theorem exists_renewedExtendedOrbit_of_charged_twoSegment_returns
    {X : Type*} [TopologicalSpace X] {relation : Correspondence X X}
    (carrier restart : Set X) (cost : X → X → ℝ)
    (hcost : ∀ first next, 0 ≤ cost first next) (charge : ℝ) (hcharge : 0 < charge)
    (hreturns : ∀ start ∈ restart,
      ∃ (block : ExtendedOrbitData relation) (length : ℕ),
        block.segmentCount = some 2 ∧ block.segmentLength 1 = some length ∧
        block.point 0 0 = start ∧
        (∀ segment, ActiveSegment block.segmentCount segment → ∀ index,
          SegmentIndex (block.segmentLength segment) index → block.point segment index ∈ carrier) ∧
        block.point 1 (length - 1) ∈ restart ∧
        ∃ points, charge ≤ block.prefixVariationWith cost 2 points)
    (start : X) (hstart : start ∈ restart) :
    ∃ orbit : ExtendedOrbitData relation,
      orbit.segmentCount = none ∧ orbit.point 0 0 = start ∧
      (∀ segment, ActiveSegment orbit.segmentCount segment → ∀ index,
        SegmentIndex (orbit.segmentLength segment) index → orbit.point segment index ∈ carrier) ∧
      HasUnboundedExtendedVariationWith cost orbit := by
  classical
  have hlocal : ∀ point : restart,
      ∃ (block : ExtendedOrbitData relation) (length : ℕ),
        block.segmentCount = some 2 ∧ block.segmentLength 1 = some length ∧
        block.point 0 0 = point.val ∧
        (∀ segment, ActiveSegment block.segmentCount segment → ∀ index,
          SegmentIndex (block.segmentLength segment) index → block.point segment index ∈ carrier) ∧
        block.point 1 (length - 1) ∈ restart ∧
        ∃ points, charge ≤ block.prefixVariationWith cost 2 points :=
    fun point => hreturns point.val point.property
  choose selected selectedLength hcount hlength hzero hstay hrestart hpaid using hlocal
  let next : restart → restart := fun point =>
    ⟨(selected point).point 1 (selectedLength point - 1), hrestart point⟩
  let state : ℕ → restart := Nat.rec ⟨start, hstart⟩ (fun _ point => next point)
  let block : ℕ → ExtendedOrbitData relation := fun rank => selected (state rank)
  let lastLength : ℕ → ℕ := fun rank => selectedLength (state rank)
  have hblockCount : ∀ rank, (block rank).segmentCount = some 2 :=
    fun rank => hcount (state rank)
  have hblockLength : ∀ rank, (block rank).segmentLength 1 = some (lastLength rank) :=
    fun rank => hlength (state rank)
  have hstitch : ∀ rank, (block rank).point 1 (lastLength rank - 1) =
      (block (rank + 1)).point 0 0 := by
    intro rank
    calc
      (block rank).point 1 (lastLength rank - 1) = (state (rank + 1)).val := rfl
      _ = (block (rank + 1)).point 0 0 := (hzero (state (rank + 1))).symm
  let orbit := ExtendedOrbitData.ofPairwiseBlocks
    block lastLength hblockCount hblockLength hstitch
  have horbitCount : orbit.segmentCount = none := rfl
  have horbitPoint : ∀ rank (segment : Fin 2) index,
      orbit.point (2 * rank + segment) index = (block rank).point segment index :=
    ExtendedOrbitData.ofPairwiseBlocks_point
      block lastLength hblockCount hblockLength hstitch
  have horbitLength : ∀ rank (segment : Fin 2),
      orbit.segmentLength (2 * rank + segment) = (block rank).segmentLength segment :=
    ExtendedOrbitData.ofPairwiseBlocks_length
      block lastLength hblockCount hblockLength hstitch
  refine ⟨orbit, horbitCount, ?_, ?_, ?_⟩
  · have hequal := horbitPoint 0 0 0
    exact hequal.trans (hzero (state 0))
  · intro segment _ index hindex
    let localSegment : Fin 2 := ⟨segment % 2, Nat.mod_lt segment (by decide)⟩
    have hsegment : 2 * (segment / 2) + (localSegment : ℕ) = segment := by
      dsimp only [localSegment]
      omega
    have hlength' : orbit.segmentLength segment =
        (block (segment / 2)).segmentLength localSegment := by
      exact (congrArg orbit.segmentLength hsegment).symm.trans
        (horbitLength (segment / 2) localSegment)
    have hindex' : SegmentIndex ((block (segment / 2)).segmentLength localSegment) index := by
      rwa [hlength'] at hindex
    have hpoint' : orbit.point segment index =
        (block (segment / 2)).point localSegment index := by
      exact (congrArg (fun value => orbit.point value index) hsegment).symm.trans
        (horbitPoint (segment / 2) localSegment index)
    rw [hpoint']
    have hactive' : ActiveSegment ((block (segment / 2)).segmentCount) localSegment := by
      simpa [ActiveSegment, hblockCount] using localSegment.isLt
    exact hstay (state (segment / 2)) localSegment
      hactive' index hindex'
  · choose width hwidth using (fun rank => hpaid (state rank))
    intro bound
    obtain ⟨count, hcountLarge⟩ := exists_nat_gt (bound / charge)
    let points := (Finset.range count).sup width
    have hbound : bound ≤ (count : ℝ) * charge :=
      ((div_lt_iff₀ hcharge).mp hcountLarge).le
    refine ⟨2 * count, points, hbound.trans ?_⟩
    change (count : ℝ) * charge ≤ ExtendedOrbitData.prefixVariationWith
      (ExtendedOrbitData.ofPairwiseBlocks block lastLength hblockCount hblockLength hstitch)
      cost (2 * count) points
    rw [ExtendedOrbitData.prefixVariationWith_ofPairwiseBlocks]
    calc
      (count : ℝ) * charge = ∑ rank ∈ Finset.range count, charge := by simp
      _ ≤ ∑ rank ∈ Finset.range count, (block rank).prefixVariationWith cost 2 points := by
        apply Finset.sum_le_sum
        intro rank hrank
        exact (hwidth rank).trans
          ((block rank).prefixVariationWith_mono_points cost hcost 2
            (Finset.le_sup (f := width) hrank))

end Math.Topology
