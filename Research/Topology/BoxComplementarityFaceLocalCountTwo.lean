/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Topology.BoxComplementarityFaceLocalCountZero

/-!
# The local count of a sharp binding-pair face is two

On a region of the four-dimensional unit cube with negative leading gain,
suppose both trailing coordinates have exact affine face gains with strictly
positive own defect and strictly positive cross term.  Each trailing gain then
changes sign at one interior Quit probability, and at a grid resolution fine
enough to separate that probability from zero the reduced label of a face grid
vertex is a fixed arithmetic function of the two trailing grid coordinates and
the two sign-change grid counts.

Combined with the forced chain position, the three labels at least two are the
labels of the first three chain vertices, so a complete grid simplex is
determined by its base trailing coordinates and by which trailing coordinate
its first step raises.  Exactly two positions carry three distinct labels: the
origin corner and the corner just below both sign changes, both raising the
second trailing coordinate first.  The local complete-simplex count is
therefore two, and its residue modulo two is zero.
-/

noncomputable section

namespace Math

open Classical Set

/-! ## The sign change of an exact affine face gain -/

/-- The Quit probability at which an exact affine face gain with own defect
`defect` and cross term `cross` changes sign. -/
def boxComplementarityFaceThreshold (defect cross : ℝ) : ℝ :=
  defect / (defect + cross)

theorem boxComplementarityFaceThreshold_pos {defect cross : ℝ}
    (hdefect : 0 < defect) (hcross : 0 < cross) :
    0 < boxComplementarityFaceThreshold defect cross :=
  div_pos hdefect (by linarith)

theorem boxComplementarityFaceThreshold_lt_one {defect cross : ℝ}
    (hdefect : 0 < defect) (hcross : 0 < cross) :
    boxComplementarityFaceThreshold defect cross < 1 := by
  rw [boxComplementarityFaceThreshold, div_lt_one (by linarith)]
  linarith

/-- An exact affine face gain is negative exactly below its sign change. -/
theorem affineFaceGain_neg_iff {defect cross value : ℝ}
    (hdefect : 0 < defect) (hcross : 0 < cross) :
    -(1 - value) * defect + value * cross < 0 ↔
      value < boxComplementarityFaceThreshold defect cross := by
  rw [boxComplementarityFaceThreshold, lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

/-! ## The sign-change grid count -/

/-- The number of grid steps strictly below the sign change of an exact
affine face gain. -/
def boxComplementarityFaceGridBound (p : ℕ) (defect cross : ℝ) : ℕ :=
  ⌈(p : ℝ) * boxComplementarityFaceThreshold defect cross⌉₊

/-- A grid coordinate lies below the sign change exactly when its index is
below the sign-change grid count. -/
theorem lt_boxComplementarityFaceGridBound_iff (p : ℕ) (hp : 0 < p)
    (defect cross : ℝ) (value : ℕ) :
    value < boxComplementarityFaceGridBound p defect cross ↔
      (value : ℝ) / p < boxComplementarityFaceThreshold defect cross := by
  have hpositive : (0 : ℝ) < p := by exact_mod_cast hp
  rw [boxComplementarityFaceGridBound, Nat.lt_ceil, div_lt_iff₀ hpositive,
    mul_comm]

/-- The sign-change grid count never exceeds the resolution. -/
theorem boxComplementarityFaceGridBound_le (p : ℕ) {defect cross : ℝ}
    (hdefect : 0 < defect) (hcross : 0 < cross) :
    boxComplementarityFaceGridBound p defect cross ≤ p := by
  rw [boxComplementarityFaceGridBound, Nat.ceil_le]
  have hthreshold :=
    (boxComplementarityFaceThreshold_lt_one hdefect hcross).le
  have hpositive : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith

/-! ## Sharp binding-pair face data -/

/-- Exact affine face gains for both trailing coordinates, each with strictly
positive own defect and strictly positive cross term. -/
structure BoxComplementarityProblem.IsSharpBindingPairFace
    (problem : BoxComplementarityProblem (Fin 4))
    (region : Set (UnitCube (Fin 4)))
    (defectTwo crossTwo defectThree crossThree : ℝ) : Prop where
  /-- The own defect of the first trailing coordinate is positive. -/
  defectTwo_pos : 0 < defectTwo
  /-- The cross term of the first trailing coordinate is positive. -/
  crossTwo_pos : 0 < crossTwo
  /-- The own defect of the second trailing coordinate is positive. -/
  defectThree_pos : 0 < defectThree
  /-- The cross term of the second trailing coordinate is positive. -/
  crossThree_pos : 0 < crossThree
  /-- The two exact affine face formulas hold on the region. -/
  affine : problem.HasAffineFaceGain region defectTwo crossTwo defectThree
    crossThree

/-! ## The face label -/

/-- The reduced label of a face grid vertex, as an arithmetic function of the
two trailing grid coordinates and the two sign-change grid counts. -/
def boxComplementarityFaceLabel
    (boundTwo boundThree first second : ℕ) : ℕ :=
  if 1 ≤ first ∧ second < boundTwo then 2
  else if 1 ≤ second ∧ first < boundThree then 3
  else 4

/-- A chain step raising the first trailing coordinate before the second one
always repeats a face label. -/
theorem boxComplementarityFaceLabel_leading_step_not_distinct
    (boundTwo boundThree first second : ℕ)
    (hTwo : 2 ≤ boundTwo) (hThree : 2 ≤ boundThree) :
    boxComplementarityFaceLabel boundTwo boundThree first second =
        boxComplementarityFaceLabel boundTwo boundThree (first + 1) second ∨
      boxComplementarityFaceLabel boundTwo boundThree first second =
        boxComplementarityFaceLabel boundTwo boundThree (first + 1)
          (second + 1) ∨
      boxComplementarityFaceLabel boundTwo boundThree (first + 1) second =
        boxComplementarityFaceLabel boundTwo boundThree (first + 1)
          (second + 1) := by
  unfold boxComplementarityFaceLabel
  split_ifs <;> omega

/-- A chain step raising the second trailing coordinate first has three
distinct face labels exactly at the origin corner and at the corner just
below both sign changes. -/
theorem boxComplementarityFaceLabel_trailing_step_distinct_iff
    (boundTwo boundThree first second : ℕ)
    (hTwo : 2 ≤ boundTwo) (hThree : 2 ≤ boundThree) :
    (boxComplementarityFaceLabel boundTwo boundThree first second ≠
          boxComplementarityFaceLabel boundTwo boundThree first (second + 1) ∧
        boxComplementarityFaceLabel boundTwo boundThree first second ≠
          boxComplementarityFaceLabel boundTwo boundThree (first + 1)
            (second + 1) ∧
        boxComplementarityFaceLabel boundTwo boundThree first (second + 1) ≠
          boxComplementarityFaceLabel boundTwo boundThree (first + 1)
            (second + 1)) ↔
      ((first = 0 ∧ second = 0) ∨
        (first = boundThree - 1 ∧ second = boundTwo - 1)) := by
  unfold boxComplementarityFaceLabel
  split_ifs <;> omega

/-! ## The reduced label on the face -/

variable {problem : BoxComplementarityProblem (Fin 4)} {p : ℕ}
variable {region : Set (UnitCube (Fin 4))}
variable {defectTwo crossTwo defectThree crossThree : ℝ}

/-- On the face, the trailing gains take their exact affine values. -/
theorem boxComplementarityFaceGain_eq (p : ℕ)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (vertex : Fin 4 → Fin (p + 1))
    (hmem : boxComplementarityGridPoint p vertex ∈ region)
    (hzero : (vertex 0).1 = 0) (hone : (vertex 1).1 = 0) :
    problem.gain (boxComplementarityGridPoint p vertex) 2 =
        -(1 - ((vertex 3).1 : ℝ) / p) * defectTwo +
          ((vertex 3).1 : ℝ) / p * crossTwo ∧
      problem.gain (boxComplementarityGridPoint p vertex) 3 =
        -(1 - ((vertex 2).1 : ℝ) / p) * defectThree +
          ((vertex 2).1 : ℝ) / p * crossThree := by
  have hzeroReal : ((boxComplementarityGridPoint p vertex (0 : Fin 4) :
      Set.Icc (0 : ℝ) 1) : ℝ) = 0 :=
    boxComplementarityGridPoint_eq_zero (n := 4) p vertex 0
      (Fin.val_injective hzero)
  have honeReal : ((boxComplementarityGridPoint p vertex (1 : Fin 4) :
      Set.Icc (0 : ℝ) 1) : ℝ) = 0 :=
    boxComplementarityGridPoint_eq_zero (n := 4) p vertex 1
      (Fin.val_injective hone)
  have hvalues := hsharp.affine _ hmem hzeroReal honeReal
  rw [boxComplementarityGridPoint_val, boxComplementarityGridPoint_val]
    at hvalues
  exact hvalues

/-- On the face, the first trailing gain is negative exactly when the second
trailing grid coordinate lies below its sign-change count. -/
theorem boxComplementarityFaceGain_two_neg_iff (p : ℕ) (hp : 0 < p)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (vertex : Fin 4 → Fin (p + 1))
    (hmem : boxComplementarityGridPoint p vertex ∈ region)
    (hzero : (vertex 0).1 = 0) (hone : (vertex 1).1 = 0) :
    problem.gain (boxComplementarityGridPoint p vertex) 2 < 0 ↔
      (vertex 3).1 < boxComplementarityFaceGridBound p defectTwo crossTwo := by
  rw [(boxComplementarityFaceGain_eq p hsharp vertex hmem hzero hone).1,
    affineFaceGain_neg_iff hsharp.defectTwo_pos hsharp.crossTwo_pos,
    lt_boxComplementarityFaceGridBound_iff p hp]

/-- On the face, the second trailing gain is negative exactly when the first
trailing grid coordinate lies below its sign-change count. -/
theorem boxComplementarityFaceGain_three_neg_iff (p : ℕ) (hp : 0 < p)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (vertex : Fin 4 → Fin (p + 1))
    (hmem : boxComplementarityGridPoint p vertex ∈ region)
    (hzero : (vertex 0).1 = 0) (hone : (vertex 1).1 = 0) :
    problem.gain (boxComplementarityGridPoint p vertex) 3 < 0 ↔
      (vertex 2).1 <
        boxComplementarityFaceGridBound p defectThree crossThree := by
  rw [(boxComplementarityFaceGain_eq p hsharp vertex hmem hzero hone).2,
    affineFaceGain_neg_iff hsharp.defectThree_pos hsharp.crossThree_pos,
    lt_boxComplementarityFaceGridBound_iff p hp]

/-- On the face, a trailing coordinate is a grid violation exactly when it is
positive and its gain is negative. -/
theorem boxComplementarityFaceViolation_two_iff (p : ℕ) (hp : 0 < p)
    (hregion : problem.IsLeadingNegativeRegion region)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (vertex : Fin 4 → Fin (p + 1))
    (hmem : boxComplementarityGridPoint p vertex ∈ region)
    (hzero : (vertex 0).1 = 0) (hone : (vertex 1).1 = 0) :
    problem.IsGridViolation p vertex (2 : Fin 4) ↔
      (1 ≤ (vertex 2).1 ∧
        (vertex 3).1 < boxComplementarityFaceGridBound p defectTwo crossTwo) := by
  rw [BoxComplementarityProblem.IsGridViolation]
  constructor
  · rintro (⟨hpositive, hnegative⟩ | htop)
    · refine ⟨?_, (boxComplementarityFaceGain_two_neg_iff p hp hsharp vertex
        hmem hzero hone).1 hnegative⟩
      have := (boxComplementarityGridPoint_pos_iff p hp vertex (2 : Fin 4)).1
        hpositive
      omega
    · exact absurd htop (ne_of_lt (hregion.lt_one _ hmem (2 : Fin 4)))
  · rintro ⟨hcoordinate, hbound⟩
    refine Or.inl ⟨(boxComplementarityGridPoint_pos_iff p hp vertex
      (2 : Fin 4)).2 (by omega), ?_⟩
    exact (boxComplementarityFaceGain_two_neg_iff p hp hsharp vertex hmem
      hzero hone).2 hbound

/-- The same for the second trailing coordinate. -/
theorem boxComplementarityFaceViolation_three_iff (p : ℕ) (hp : 0 < p)
    (hregion : problem.IsLeadingNegativeRegion region)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (vertex : Fin 4 → Fin (p + 1))
    (hmem : boxComplementarityGridPoint p vertex ∈ region)
    (hzero : (vertex 0).1 = 0) (hone : (vertex 1).1 = 0) :
    problem.IsGridViolation p vertex (3 : Fin 4) ↔
      (1 ≤ (vertex 3).1 ∧
        (vertex 2).1 <
          boxComplementarityFaceGridBound p defectThree crossThree) := by
  rw [BoxComplementarityProblem.IsGridViolation]
  constructor
  · rintro (⟨hpositive, hnegative⟩ | htop)
    · refine ⟨?_, (boxComplementarityFaceGain_three_neg_iff p hp hsharp vertex
        hmem hzero hone).1 hnegative⟩
      have := (boxComplementarityGridPoint_pos_iff p hp vertex (3 : Fin 4)).1
        hpositive
      omega
    · exact absurd htop (ne_of_lt (hregion.lt_one _ hmem (3 : Fin 4)))
  · rintro ⟨hcoordinate, hbound⟩
    refine Or.inl ⟨(boxComplementarityGridPoint_pos_iff p hp vertex
      (3 : Fin 4)).2 (by omega), ?_⟩
    exact (boxComplementarityFaceGain_three_neg_iff p hp hsharp vertex hmem
      hzero hone).2 hbound

/-- **The face label formula.**  A face grid vertex of the region carries the
arithmetic face label of its two trailing grid coordinates. -/
theorem boxComplementarityReducedLabel_face_eq (p : ℕ) (hp : 0 < p)
    (hregion : problem.IsLeadingNegativeRegion region)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (vertex : Fin 4 → Fin (p + 1))
    (hmem : boxComplementarityGridPoint p vertex ∈ region)
    (hzero : (vertex 0).1 = 0) (hone : (vertex 1).1 = 0) :
    boxComplementarityReducedLabel problem p vertex =
      boxComplementarityFaceLabel
        (boxComplementarityFaceGridBound p defectTwo crossTwo)
        (boxComplementarityFaceGridBound p defectThree crossThree)
        (vertex 2).1 (vertex 3).1 := by
  have hval2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have hval3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  have hprops := boxComplementarityReducedLabel_properties problem p vertex
  have hneZero : boxComplementarityReducedLabel problem p vertex ≠ 0 :=
    boxComplementarityReducedLabel_ne_of_val_eq_zero problem p vertex
      (0 : Fin 4) hzero
  have hneOne : boxComplementarityReducedLabel problem p vertex ≠ 1 :=
    boxComplementarityReducedLabel_ne_of_val_eq_zero problem p vertex
      (1 : Fin 4) hone
  have htwo := boxComplementarityFaceViolation_two_iff p hp hregion hsharp
    vertex hmem hzero hone
  have hthree := boxComplementarityFaceViolation_three_iff p hp hregion hsharp
    vertex hmem hzero hone
  rw [boxComplementarityFaceLabel]
  by_cases hviolationTwo : 1 ≤ (vertex 2).1 ∧
      (vertex 3).1 < boxComplementarityFaceGridBound p defectTwo crossTwo
  · rw [if_pos hviolationTwo]
    have hle := (hprops.2 (2 : Fin 4)).2 (htwo.2 hviolationTwo)
    omega
  · rw [if_neg hviolationTwo]
    have hneTwo : boxComplementarityReducedLabel problem p vertex ≠ 2 := by
      intro heq
      exact hviolationTwo (htwo.1 ((hprops.2 (2 : Fin 4)).1 (by omega)))
    by_cases hviolationThree : 1 ≤ (vertex 3).1 ∧
        (vertex 2).1 <
          boxComplementarityFaceGridBound p defectThree crossThree
    · rw [if_pos hviolationThree]
      have hle := (hprops.2 (3 : Fin 4)).2 (hthree.2 hviolationThree)
      omega
    · rw [if_neg hviolationThree]
      have hneThree : boxComplementarityReducedLabel problem p vertex ≠ 3 := by
        intro heq
        exact hviolationThree (hthree.1 ((hprops.2 (3 : Fin 4)).1 (by omega)))
      have hle := hprops.1
      omega

/-! ## The two candidate chains -/

private theorem fin_four_eq_cases :
    ∀ who : Fin 4, who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by decide

private theorem fin_five_eq_cases :
    ∀ index : Fin (4 + 1),
      index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by decide

private theorem fin_numeral_vals :
    ((0 : Fin 4) : ℕ) = 0 ∧ ((1 : Fin 4) : ℕ) = 1 ∧ ((2 : Fin 4) : ℕ) = 2 ∧
      ((3 : Fin 4) : ℕ) = 3 ∧ ((0 : Fin (4 + 1)) : ℕ) = 0 ∧
      ((1 : Fin (4 + 1)) : ℕ) = 1 ∧ ((2 : Fin (4 + 1)) : ℕ) = 2 ∧
      ((3 : Fin (4 + 1)) : ℕ) = 3 ∧ ((4 : Fin (4 + 1)) : ℕ) = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Grid coordinates of the origin-corner chain, in which coordinate `who` is
raised at step `3 - who`. -/
def boxComplementarityOriginChainValue (index : Fin (4 + 1)) (who : Fin 4) : ℕ :=
  if 3 - (who : ℕ) < (index : ℕ) then 1 else 0

/-- Grid coordinates of the chain based at the corner just below both sign
changes. -/
def boxComplementarityCornerChainValue (boundTwo boundThree : ℕ)
    (index : Fin (4 + 1)) (who : Fin 4) : ℕ :=
  if (who : ℕ) = 0 then (if 3 < (index : ℕ) then 1 else 0)
  else if (who : ℕ) = 1 then (if 2 < (index : ℕ) then 1 else 0)
  else if (who : ℕ) = 2 then
    (if 1 < (index : ℕ) then boundThree else boundThree - 1)
  else (if 0 < (index : ℕ) then boundTwo else boundTwo - 1)

/-! ## Only the two candidate chains are complete -/

/-- **The uniqueness direction.**  A complete grid simplex all of whose
vertices lie in a sharp binding-pair face region has the grid coordinates of
one of the two candidate chains. -/
theorem boxComplementarityCompleteSimplex_value_eq (p : ℕ) (hp : 0 < p)
    (hregion : problem.IsLeadingNegativeRegion region)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (hboundTwo : 2 ≤ boxComplementarityFaceGridBound p defectTwo crossTwo)
    (hboundThree : 2 ≤ boxComplementarityFaceGridBound p defectThree crossThree)
    (vertices : Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) 4 vertices)
    (hin : ∀ index, boxComplementarityGridPoint p (vertices index) ∈ region) :
    (∀ index who, (vertices index who).1 =
        boxComplementarityOriginChainValue index who) ∨
      (∀ index who, (vertices index who).1 =
        boxComplementarityCornerChainValue
          (boxComplementarityFaceGridBound p defectTwo crossTwo)
          (boxComplementarityFaceGridBound p defectThree crossThree)
          index who) := by
  obtain ⟨hleadZero, hleadOne⟩ := boxComplementarityFaceChain_leading_eq
    problem p hp region hregion vertices hcomplete hin
  have hposition := boxComplementarityFaceChainPosition_of_mem
    problem p hp region hregion vertices hcomplete hin
  have hlabel : ∀ index : Fin (4 + 1), (index : ℕ) ≤ 2 →
      boxComplementarityReducedLabel problem p (vertices index) =
        boxComplementarityFaceLabel
          (boxComplementarityFaceGridBound p defectTwo crossTwo)
          (boxComplementarityFaceGridBound p defectThree crossThree)
          (vertices index (2 : Fin 4)).1 (vertices index (3 : Fin 4)).1 := by
    intro index hle
    exact boxComplementarityReducedLabel_face_eq p hp hregion hsharp
      (vertices index) (hin index) (hposition.leading_eq_zero index hle).1
      (hposition.leading_eq_zero index hle).2
  have hinjective := rl_inj_of_complete 4 vertices hcomplete
  have hdistinct : ∀ first second : Fin (4 + 1), first ≠ second →
      boxComplementarityReducedLabel problem p (vertices first) ≠
        boxComplementarityReducedLabel problem p (vertices second) :=
    fun first second hne heq ↦ hne (hinjective first second heq)
  have htrail : ∀ index : Fin (4 + 1), 2 ≤ (index : ℕ) →
      ∀ who : Fin 4, 2 ≤ (who : ℕ) →
        (vertices index who).1 = (vertices 0 who).1 + 1 :=
    fun index hindex who hwho ↦
      hposition.trailing_raised who hwho index hindex
  have hzero := hlabel 0 (by decide)
  have hone := hlabel 1 (by decide)
  have htwo := hlabel 2 (by decide)
  rw [htrail 2 (by decide) (2 : Fin 4) (by decide),
    htrail 2 (by decide) (3 : Fin 4) (by decide)] at htwo
  rcases hposition.trailing_middle with ⟨hmiddleTwo, hmiddleThree⟩ |
    ⟨hmiddleTwo, hmiddleThree⟩
  · -- the first step raises the first trailing coordinate: labels repeat
    exfalso
    rw [hmiddleTwo, hmiddleThree] at hone
    rcases boxComplementarityFaceLabel_leading_step_not_distinct
      (boxComplementarityFaceGridBound p defectTwo crossTwo)
      (boxComplementarityFaceGridBound p defectThree crossThree)
      (vertices 0 (2 : Fin 4)).1 (vertices 0 (3 : Fin 4)).1
      hboundTwo hboundThree with hcase | hcase | hcase
    · exact hdistinct 0 1 (by decide) (by rw [hzero, hone, hcase])
    · exact hdistinct 0 2 (by decide) (by rw [hzero, htwo, hcase])
    · exact hdistinct 1 2 (by decide) (by rw [hone, htwo, hcase])
  · -- the first step raises the second trailing coordinate
    rw [hmiddleTwo, hmiddleThree] at hone
    have hcorner := (boxComplementarityFaceLabel_trailing_step_distinct_iff
      (boxComplementarityFaceGridBound p defectTwo crossTwo)
      (boxComplementarityFaceGridBound p defectThree crossThree)
      (vertices 0 (2 : Fin 4)).1 (vertices 0 (3 : Fin 4)).1
      hboundTwo hboundThree).1
        ⟨by rw [← hzero, ← hone]; exact hdistinct 0 1 (by decide),
          by rw [← hzero, ← htwo]; exact hdistinct 0 2 (by decide),
          by rw [← hone, ← htwo]; exact hdistinct 1 2 (by decide)⟩
    -- the four coordinate profiles of the chain
    have hcoordinateTwo : ∀ index : Fin (4 + 1),
        (vertices index (2 : Fin 4)).1 =
          if (index : ℕ) ≤ 1 then (vertices 0 (2 : Fin 4)).1
          else (vertices 0 (2 : Fin 4)).1 + 1 := by
      intro index
      by_cases hle : (index : ℕ) ≤ 1
      · rw [if_pos hle]
        rcases fin_five_eq_cases index with rfl | rfl | rfl | rfl | rfl
        · rfl
        · exact hmiddleTwo
        all_goals exact absurd hle (by decide)
      · rw [if_neg hle]
        exact htrail index (by omega) (2 : Fin 4) (by decide)
    have hcoordinateThree : ∀ index : Fin (4 + 1),
        (vertices index (3 : Fin 4)).1 =
          if (index : ℕ) ≤ 0 then (vertices 0 (3 : Fin 4)).1
          else (vertices 0 (3 : Fin 4)).1 + 1 := by
      intro index
      by_cases hle : (index : ℕ) ≤ 0
      · rw [if_pos hle]
        rcases fin_five_eq_cases index with rfl | rfl | rfl | rfl | rfl
        · rfl
        all_goals exact absurd hle (by decide)
      · rw [if_neg hle]
        rcases fin_five_eq_cases index with rfl | rfl | rfl | rfl | rfl
        · exact absurd (by decide : ((0 : Fin (4 + 1)) : ℕ) ≤ 0) hle
        · exact hmiddleThree
        · exact htrail 2 (by decide) (3 : Fin 4) (by decide)
        · exact htrail 3 (by decide) (3 : Fin 4) (by decide)
        · exact htrail 4 (by decide) (3 : Fin 4) (by decide)
    rcases hcorner with ⟨hbase2, hbase3⟩ | ⟨hbase2, hbase3⟩
    · left
      intro index who
      rcases fin_four_eq_cases who with rfl | rfl | rfl | rfl
      · rw [hleadZero index, boxComplementarityOriginChainValue]
        split_ifs <;> omega
      · rw [hleadOne index, boxComplementarityOriginChainValue]
        split_ifs <;> omega
      · rw [hcoordinateTwo index, hbase2, boxComplementarityOriginChainValue]
        split_ifs <;> omega
      · rw [hcoordinateThree index, hbase3, boxComplementarityOriginChainValue]
        split_ifs <;> omega
    · right
      intro index who
      rcases fin_four_eq_cases who with rfl | rfl | rfl | rfl
      · rw [hleadZero index, boxComplementarityCornerChainValue]
        split_ifs <;> omega
      · rw [hleadOne index, boxComplementarityCornerChainValue]
        split_ifs <;> omega
      · rw [hcoordinateTwo index, hbase2, boxComplementarityCornerChainValue]
        split_ifs <;> omega
      · rw [hcoordinateThree index, hbase3, boxComplementarityCornerChainValue]
        split_ifs <;> omega

/-! ## The candidate chains are grid simplices -/

theorem boxComplementarityOriginChainValue_injective :
    ∀ first second : Fin (4 + 1),
      (∀ who, boxComplementarityOriginChainValue first who =
        boxComplementarityOriginChainValue second who) → first = second := by
  decide

theorem boxComplementarityCornerChainValue_leading (boundTwo boundThree : ℕ)
    (index : Fin (4 + 1)) :
    boxComplementarityCornerChainValue boundTwo boundThree index 0 =
      if 3 < (index : ℕ) then 1 else 0 := rfl

theorem boxComplementarityCornerChainValue_second (boundTwo boundThree : ℕ)
    (index : Fin (4 + 1)) :
    boxComplementarityCornerChainValue boundTwo boundThree index 1 =
      if 2 < (index : ℕ) then 1 else 0 := rfl

theorem boxComplementarityCornerChainValue_third (boundTwo boundThree : ℕ)
    (index : Fin (4 + 1)) :
    boxComplementarityCornerChainValue boundTwo boundThree index 2 =
      if 1 < (index : ℕ) then boundThree else boundThree - 1 := rfl

theorem boxComplementarityCornerChainValue_fourth (boundTwo boundThree : ℕ)
    (index : Fin (4 + 1)) :
    boxComplementarityCornerChainValue boundTwo boundThree index 3 =
      if 0 < (index : ℕ) then boundTwo else boundTwo - 1 := rfl

theorem boxComplementarityCornerChainValue_injective (boundTwo boundThree : ℕ)
    (hTwo : 2 ≤ boundTwo) (hThree : 2 ≤ boundThree) :
    ∀ first second : Fin (4 + 1),
      (∀ who, boxComplementarityCornerChainValue boundTwo boundThree first who =
        boxComplementarityCornerChainValue boundTwo boundThree second who) →
      first = second := by
  intro first second hvalues
  have hzero := hvalues 0
  have hone := hvalues 1
  have htwo := hvalues 2
  have hthree := hvalues 3
  rw [boxComplementarityCornerChainValue_leading,
    boxComplementarityCornerChainValue_leading] at hzero
  rw [boxComplementarityCornerChainValue_second,
    boxComplementarityCornerChainValue_second] at hone
  rw [boxComplementarityCornerChainValue_third,
    boxComplementarityCornerChainValue_third] at htwo
  rw [boxComplementarityCornerChainValue_fourth,
    boxComplementarityCornerChainValue_fourth] at hthree
  apply Fin.val_injective
  have hfirst := first.isLt
  have hsecond := second.isLt
  split_ifs at hzero hone htwo hthree <;> omega

/-- The origin-corner chain at one resolution. -/
def boxComplementarityOriginChain (p : ℕ) (hp : 0 < p) :
    Fin (4 + 1) → Fin 4 → Fin (p + 1) :=
  fun index who ↦ ⟨boxComplementarityOriginChainValue index who, by
    rw [boxComplementarityOriginChainValue]
    split_ifs <;> omega⟩

@[simp] theorem boxComplementarityOriginChain_val (p : ℕ) (hp : 0 < p)
    (index : Fin (4 + 1)) (who : Fin 4) :
    (boxComplementarityOriginChain p hp index who).1 =
      boxComplementarityOriginChainValue index who := rfl

/-- The chain based at the corner just below both sign changes, clamped to the
resolution so that it is total. -/
def boxComplementarityCornerChain (p : ℕ)
    (boundTwo boundThree : ℕ) : Fin (4 + 1) → Fin 4 → Fin (p + 1) :=
  fun index who ↦
    ⟨min (boxComplementarityCornerChainValue boundTwo boundThree index who) p,
      by omega⟩

theorem boxComplementarityCornerChain_val (p : ℕ) (hp : 0 < p)
    {boundTwo boundThree : ℕ} (hTwo : boundTwo ≤ p) (hThree : boundThree ≤ p)
    (index : Fin (4 + 1)) (who : Fin 4) :
    (boxComplementarityCornerChain p boundTwo boundThree index who).1 =
      boxComplementarityCornerChainValue boundTwo boundThree index who := by
  show min (boxComplementarityCornerChainValue boundTwo boundThree index who) p
    = _
  apply min_eq_left
  rw [boxComplementarityCornerChainValue]
  split_ifs <;> omega

theorem simplex_boxComplementarityOriginChain
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p) :
    simplex (boxComplementaritySpernerCube problem p hp) 4
      (boxComplementarityOriginChain p hp) := by
  apply simplex_of_step_le
  · intro first second heq
    refine boxComplementarityOriginChainValue_injective first second fun who ↦ ?_
    exact congrArg Fin.val (congrFun heq who)
  · intro i who
    show boxComplementarityOriginChainValue i.castSucc who ≤
      boxComplementarityOriginChainValue i.succ who
    have hcast : (i.castSucc : ℕ) = (i : ℕ) := rfl
    have hsucc : (i.succ : ℕ) = (i : ℕ) + 1 := rfl
    rw [boxComplementarityOriginChainValue, boxComplementarityOriginChainValue]
    split_ifs <;> omega
  · intro who
    show boxComplementarityOriginChainValue (Fin.last 4) who ≤
      boxComplementarityOriginChainValue 0 who + 1
    have hlast : ((Fin.last 4 : Fin (4 + 1)) : ℕ) = 4 := rfl
    have hzero : ((0 : Fin (4 + 1)) : ℕ) = 0 := rfl
    rw [boxComplementarityOriginChainValue, boxComplementarityOriginChainValue]
    split_ifs <;> omega

theorem simplex_boxComplementarityCornerChain
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    {boundTwo boundThree : ℕ} (hTwoLe : boundTwo ≤ p) (hThreeLe : boundThree ≤ p)
    (hTwo : 2 ≤ boundTwo) (hThree : 2 ≤ boundThree) :
    simplex (boxComplementaritySpernerCube problem p hp) 4
      (boxComplementarityCornerChain p boundTwo boundThree) := by
  apply simplex_of_step_le
  · intro first second heq
    refine boxComplementarityCornerChainValue_injective boundTwo boundThree
      hTwo hThree first second fun who ↦ ?_
    rw [← boxComplementarityCornerChain_val p hp hTwoLe hThreeLe,
      ← boxComplementarityCornerChain_val p hp hTwoLe hThreeLe]
    exact congrArg Fin.val (congrFun heq who)
  · intro i who
    rw [boxComplementarityCornerChain_val p hp hTwoLe hThreeLe,
      boxComplementarityCornerChain_val p hp hTwoLe hThreeLe,
      boxComplementarityCornerChainValue, boxComplementarityCornerChainValue]
    have hcast : (i.castSucc : ℕ) = (i : ℕ) := rfl
    have hsucc : (i.succ : ℕ) = (i : ℕ) + 1 := rfl
    split_ifs <;> omega
  · intro who
    rw [boxComplementarityCornerChain_val p hp hTwoLe hThreeLe,
      boxComplementarityCornerChain_val p hp hTwoLe hThreeLe,
      boxComplementarityCornerChainValue, boxComplementarityCornerChainValue]
    have hlast : ((Fin.last 4 : Fin (4 + 1)) : ℕ) = 4 := rfl
    have hzero : ((0 : Fin (4 + 1)) : ℕ) = 0 := rfl
    split_ifs <;> omega

/-! ## Labels of the candidate chains -/

/-- The origin-corner chain carries the reduced labels `4, 3, 2, 1, 0`. -/
theorem boxComplementarityOriginChain_label (p : ℕ) (hp : 0 < p)
    (hregion : problem.IsLeadingNegativeRegion region)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (hboundTwo : 2 ≤ boxComplementarityFaceGridBound p defectTwo crossTwo)
    (hboundThree : 2 ≤ boxComplementarityFaceGridBound p defectThree crossThree)
    (hin : ∀ index, boxComplementarityGridPoint p
      (boxComplementarityOriginChain p hp index) ∈ region)
    (index : Fin (4 + 1)) :
    boxComplementarityReducedLabel problem p
        (boxComplementarityOriginChain p hp index) = 4 - (index : ℕ) := by
  obtain ⟨hv0, hv1, hv2, hv3, hi0, hi1, hi2, hi3, hi4⟩ := fin_numeral_vals
  have hface : ∀ index : Fin (4 + 1), (index : ℕ) ≤ 2 →
      boxComplementarityReducedLabel problem p
          (boxComplementarityOriginChain p hp index) =
        boxComplementarityFaceLabel
          (boxComplementarityFaceGridBound p defectTwo crossTwo)
          (boxComplementarityFaceGridBound p defectThree crossThree)
          (boxComplementarityOriginChainValue index 2)
          (boxComplementarityOriginChainValue index 3) := by
    intro index hle
    refine boxComplementarityReducedLabel_face_eq p hp hregion hsharp _
      (hin index) ?_ ?_
    · show boxComplementarityOriginChainValue index 0 = 0
      rw [boxComplementarityOriginChainValue]
      have hwho : ((0 : Fin 4) : ℕ) = 0 := rfl
      split_ifs <;> omega
    · show boxComplementarityOriginChainValue index 1 = 0
      rw [boxComplementarityOriginChainValue]
      have hwho : ((1 : Fin 4) : ℕ) = 1 := rfl
      split_ifs <;> omega
  have hleadingZero : ∀ index : Fin (4 + 1),
      (boxComplementarityOriginChain p hp index 0).1 =
        if 3 < (index : ℕ) then 1 else 0 := fun _ ↦ rfl
  have hleadingOne : ∀ index : Fin (4 + 1),
      (boxComplementarityOriginChain p hp index 1).1 =
        if 2 < (index : ℕ) then 1 else 0 := fun _ ↦ rfl
  rcases fin_five_eq_cases index with rfl | rfl | rfl | rfl | rfl
  · rw [hface 0 (by decide)]
    simp only [boxComplementarityOriginChainValue,
      boxComplementarityFaceLabel]
    split_ifs <;> omega
  · rw [hface 1 (by decide)]
    simp only [boxComplementarityOriginChainValue,
      boxComplementarityFaceLabel]
    split_ifs <;> omega
  · rw [hface 2 (by decide)]
    simp only [boxComplementarityOriginChainValue,
      boxComplementarityFaceLabel]
    split_ifs <;> omega
  · have hneZero := boxComplementarityReducedLabel_ne_of_val_eq_zero problem p
      (boxComplementarityOriginChain p hp 3) (0 : Fin 4) (by
        rw [hleadingZero 3]
        decide)
    have hle := boxComplementarityReducedLabel_le_of_leading_ne_zero problem p
      hp region hregion (boxComplementarityOriginChain p hp 3) (hin 3)
      (1 : Fin 4) (by decide) (by rw [hleadingOne 3]; decide)
    have hval : ((1 : Fin 4) : ℕ) = 1 := rfl
    have hindex : ((3 : Fin (4 + 1)) : ℕ) = 3 := rfl
    omega
  · have hle := boxComplementarityReducedLabel_le_of_leading_ne_zero problem p
      hp region hregion (boxComplementarityOriginChain p hp 4) (hin 4)
      (0 : Fin 4) (by decide) (by rw [hleadingZero 4]; decide)
    have hval : ((0 : Fin 4) : ℕ) = 0 := rfl
    have hindex : ((4 : Fin (4 + 1)) : ℕ) = 4 := rfl
    omega

/-- The corner chain carries the reduced labels `2, 3, 4, 1, 0`. -/
theorem boxComplementarityCornerChain_label (p : ℕ) (hp : 0 < p)
    (hregion : problem.IsLeadingNegativeRegion region)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (hboundTwo : 2 ≤ boxComplementarityFaceGridBound p defectTwo crossTwo)
    (hboundThree : 2 ≤ boxComplementarityFaceGridBound p defectThree crossThree)
    (hin : ∀ index, boxComplementarityGridPoint p
      (boxComplementarityCornerChain p
        (boxComplementarityFaceGridBound p defectTwo crossTwo)
        (boxComplementarityFaceGridBound p defectThree crossThree) index) ∈
      region)
    (index : Fin (4 + 1)) :
    boxComplementarityReducedLabel problem p
        (boxComplementarityCornerChain p
          (boxComplementarityFaceGridBound p defectTwo crossTwo)
          (boxComplementarityFaceGridBound p defectThree crossThree) index) =
      if (index : ℕ) ≤ 2 then (index : ℕ) + 2 else 4 - (index : ℕ) := by
  obtain ⟨hv0, hv1, hv2, hv3, hi0, hi1, hi2, hi3, hi4⟩ := fin_numeral_vals
  have hTwoLe := boxComplementarityFaceGridBound_le p hsharp.defectTwo_pos
    hsharp.crossTwo_pos
  have hThreeLe := boxComplementarityFaceGridBound_le p hsharp.defectThree_pos
    hsharp.crossThree_pos
  have hvalue := boxComplementarityCornerChain_val p hp hTwoLe hThreeLe
  have hface : ∀ index : Fin (4 + 1), (index : ℕ) ≤ 2 →
      boxComplementarityReducedLabel problem p
          (boxComplementarityCornerChain p
            (boxComplementarityFaceGridBound p defectTwo crossTwo)
            (boxComplementarityFaceGridBound p defectThree crossThree) index) =
        boxComplementarityFaceLabel
          (boxComplementarityFaceGridBound p defectTwo crossTwo)
          (boxComplementarityFaceGridBound p defectThree crossThree)
          (boxComplementarityCornerChainValue
            (boxComplementarityFaceGridBound p defectTwo crossTwo)
            (boxComplementarityFaceGridBound p defectThree crossThree) index 2)
          (boxComplementarityCornerChainValue
            (boxComplementarityFaceGridBound p defectTwo crossTwo)
            (boxComplementarityFaceGridBound p defectThree crossThree)
            index 3) := by
    intro index hle
    rw [← hvalue index 2, ← hvalue index 3]
    refine boxComplementarityReducedLabel_face_eq p hp hregion hsharp _
      (hin index) ?_ ?_
    · rw [hvalue index 0, boxComplementarityCornerChainValue_leading]
      split_ifs <;> omega
    · rw [hvalue index 1, boxComplementarityCornerChainValue_second]
      split_ifs <;> omega
  rcases fin_five_eq_cases index with rfl | rfl | rfl | rfl | rfl
  · rw [hface 0 (by decide), boxComplementarityCornerChainValue_third,
      boxComplementarityCornerChainValue_fourth, boxComplementarityFaceLabel]
    split_ifs <;> omega
  · rw [hface 1 (by decide), boxComplementarityCornerChainValue_third,
      boxComplementarityCornerChainValue_fourth, boxComplementarityFaceLabel]
    split_ifs <;> omega
  · rw [hface 2 (by decide), boxComplementarityCornerChainValue_third,
      boxComplementarityCornerChainValue_fourth, boxComplementarityFaceLabel]
    split_ifs <;> omega
  · have hneZero := boxComplementarityReducedLabel_ne_of_val_eq_zero problem p _
      (0 : Fin 4) (by
        rw [hvalue 3 0, boxComplementarityCornerChainValue_leading]
        decide)
    have hle := boxComplementarityReducedLabel_le_of_leading_ne_zero problem p
      hp region hregion _ (hin 3) (1 : Fin 4) (by decide) (by
        rw [hvalue 3 1, boxComplementarityCornerChainValue_second]
        decide)
    have hval : ((1 : Fin 4) : ℕ) = 1 := rfl
    have hindex : ((3 : Fin (4 + 1)) : ℕ) = 3 := rfl
    rw [if_neg (by omega)]
    omega
  · have hle := boxComplementarityReducedLabel_le_of_leading_ne_zero problem p
      hp region hregion _ (hin 4) (0 : Fin 4) (by decide) (by
        rw [hvalue 4 0, boxComplementarityCornerChainValue_leading]
        decide)
    have hval : ((0 : Fin 4) : ℕ) = 0 := rfl
    have hindex : ((4 : Fin (4 + 1)) : ℕ) = 4 := rfl
    rw [if_neg (by omega)]
    omega

/-! ## Completeness of the candidate chains -/

/-- A grid simplex whose reduced labels realize every value at most four is a
complete grid simplex. -/
theorem completeSimplex_of_label
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (chain : Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hsimplex : simplex (boxComplementaritySpernerCube problem p hp) 4 chain)
    (label : Fin (4 + 1) → ℕ)
    (hlabel : ∀ index,
      boxComplementarityReducedLabel problem p (chain index) = label index)
    (hbounded : ∀ index, label index ≤ 4)
    (hsurjective : ∀ value : ℕ, value ≤ 4 → ∃ index, label index = value) :
    complete_simplex (boxComplementaritySpernerCube problem p hp) 4 chain := by
  refine ⟨hsimplex, ?_⟩
  ext value
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨index, hindex⟩
    rw [← hindex]
    show boxComplementarityReducedLabel problem p (chain index) ≤ 4
    rw [hlabel index]
    exact hbounded index
  · intro hvalue
    obtain ⟨index, hindex⟩ := hsurjective value hvalue
    refine ⟨index, ?_⟩
    show boxComplementarityReducedLabel problem p (chain index) = value
    rw [hlabel index, hindex]

/-- The selected anchor is the unique chain position carrying label four. -/
theorem anchorIndex_eq_of_label
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (chain : Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) 4 chain)
    (label : Fin (4 + 1) → ℕ)
    (hlabel : ∀ index,
      boxComplementarityReducedLabel problem p (chain index) = label index)
    (position : Fin (4 + 1))
    (hunique : ∀ index, label index = 4 → index = position) :
    boxComplementarityCompleteSimplexAnchorIndex problem p hp chain hcomplete =
      position := by
  have hanchor := boxComplementarityCompleteSimplexAnchorIndex_label
    problem p hp chain hcomplete
  rw [hlabel _] at hanchor
  exact hunique _ hanchor

/-! ## The local count -/

/-- **The sharp binding-pair face carries exactly two complete simplices**:
the one based at the origin corner and the one based at the corner just below
both sign changes. -/
theorem boxComplementarityLocalCompleteSimplices_card_eq_two_of_sharpFace
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (defectTwo crossTwo defectThree crossThree : ℝ)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (hboundTwo : 2 ≤ boxComplementarityFaceGridBound p defectTwo crossTwo)
    (hboundThree : 2 ≤ boxComplementarityFaceGridBound p defectThree crossThree)
    (target : Set (UnitCube (Fin 4)))
    (hthicken : ∀ chain :
        Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G,
      simplex (boxComplementaritySpernerCube problem p hp) 4 chain →
      (∃ index, boxComplementarityGridPoint p (chain index) ∈ target) →
      ∀ index, boxComplementarityGridPoint p (chain index) ∈ region)
    (hanchorOrigin : boxComplementarityGridPoint p
      (boxComplementarityOriginChain p hp 0) ∈ target)
    (hanchorCorner : boxComplementarityGridPoint p
      (boxComplementarityCornerChain p
        (boxComplementarityFaceGridBound p defectTwo crossTwo)
        (boxComplementarityFaceGridBound p defectThree crossThree) 2) ∈
      target) :
    (boxComplementarityLocalCompleteSimplices problem p hp target).card = 2 := by
  obtain ⟨hv0, hv1, hv2, hv3, hi0, hi1, hi2, hi3, hi4⟩ := fin_numeral_vals
  have hTwoLe := boxComplementarityFaceGridBound_le p hsharp.defectTwo_pos
    hsharp.crossTwo_pos
  have hThreeLe := boxComplementarityFaceGridBound_le p hsharp.defectThree_pos
    hsharp.crossThree_pos
  have hsimplexOrigin := simplex_boxComplementarityOriginChain problem p hp
  have hsimplexCorner := simplex_boxComplementarityCornerChain problem p hp
    hTwoLe hThreeLe hboundTwo hboundThree
  have hinOrigin := hthicken _ hsimplexOrigin ⟨0, hanchorOrigin⟩
  have hinCorner := hthicken _ hsimplexCorner ⟨2, hanchorCorner⟩
  have hlabelOrigin := boxComplementarityOriginChain_label p hp hregion hsharp
    hboundTwo hboundThree hinOrigin
  have hlabelCorner := boxComplementarityCornerChain_label p hp hregion hsharp
    hboundTwo hboundThree hinCorner
  have hcompleteOrigin := completeSimplex_of_label problem p hp _
    hsimplexOrigin (fun index ↦ 4 - (index : ℕ)) hlabelOrigin
    (fun index ↦ by omega)
    (fun value hvalue ↦ ⟨⟨4 - value, by omega⟩, by
      show 4 - (4 - value) = value
      omega⟩)
  have hcompleteCorner := completeSimplex_of_label problem p hp _
    hsimplexCorner
    (fun index ↦ if (index : ℕ) ≤ 2 then (index : ℕ) + 2 else 4 - (index : ℕ))
    hlabelCorner
    (fun index ↦ by have := index.isLt; split_ifs <;> omega)
    (fun value hvalue ↦ by
      rcases Nat.lt_or_ge value 2 with hlt | hge
      · exact ⟨⟨4 - value, by omega⟩, by
          show (if 4 - value ≤ 2 then 4 - value + 2 else 4 - (4 - value)) = value
          rw [if_neg (by omega)]
          omega⟩
      · exact ⟨⟨value - 2, by omega⟩, by
          show (if value - 2 ≤ 2 then value - 2 + 2 else 4 - (value - 2)) = value
          rw [if_pos (by omega)]
          omega⟩)
  have hanchorIndexOrigin := anchorIndex_eq_of_label problem p hp _
    hcompleteOrigin (fun index ↦ 4 - (index : ℕ)) hlabelOrigin 0
    (fun index hindex ↦ Fin.val_injective (by
      have := index.isLt
      omega))
  have hanchorIndexCorner := anchorIndex_eq_of_label problem p hp _
    hcompleteCorner
    (fun index ↦ if (index : ℕ) ≤ 2 then (index : ℕ) + 2 else 4 - (index : ℕ))
    hlabelCorner 2
    (fun index hindex ↦ Fin.val_injective (by
      have hbound := index.isLt
      split_ifs at hindex <;> omega))
  have hdistinct : (boxComplementarityOriginChain p hp :
        Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G) ≠
      boxComplementarityCornerChain p
        (boxComplementarityFaceGridBound p defectTwo crossTwo)
        (boxComplementarityFaceGridBound p defectThree crossThree) := by
    intro heq
    have hcoordinate := congrArg Fin.val (congrFun (congrFun heq 0) 3)
    rw [boxComplementarityCornerChain_val p hp hTwoLe hThreeLe,
      boxComplementarityCornerChainValue_fourth] at hcoordinate
    have hleft : (boxComplementarityOriginChain p hp 0 3).1 = 0 := rfl
    rw [hleft] at hcoordinate
    rw [if_neg (by omega)] at hcoordinate
    omega
  refine Finset.card_eq_two.2 ⟨boxComplementarityOriginChain p hp,
    boxComplementarityCornerChain p
      (boxComplementarityFaceGridBound p defectTwo crossTwo)
      (boxComplementarityFaceGridBound p defectThree crossThree),
    hdistinct, ?_⟩
  ext chain
  rw [mem_boxComplementarityLocalCompleteSimplices_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hcomplete, hanchor⟩
    have hin := hthicken chain hcomplete.1
      ⟨boxComplementarityCompleteSimplexAnchorIndex problem p hp chain
        hcomplete, hanchor⟩
    rcases boxComplementarityCompleteSimplex_value_eq p hp hregion hsharp
      hboundTwo hboundThree chain hcomplete hin with hvalues | hvalues
    · left
      funext index who
      exact Fin.val_injective (hvalues index who)
    · right
      funext index who
      refine Fin.val_injective ?_
      rw [hvalues index who,
        boxComplementarityCornerChain_val p hp hTwoLe hThreeLe]
  · rintro (rfl | rfl)
    · refine ⟨hcompleteOrigin, ?_⟩
      show boxComplementarityGridPoint p
        (boxComplementarityOriginChain p hp
          (boxComplementarityCompleteSimplexAnchorIndex problem p hp _
            hcompleteOrigin)) ∈ target
      rw [hanchorIndexOrigin]
      exact hanchorOrigin
    · refine ⟨hcompleteCorner, ?_⟩
      show boxComplementarityGridPoint p
        (boxComplementarityCornerChain p _ _
          (boxComplementarityCompleteSimplexAnchorIndex problem p hp _
            hcompleteCorner)) ∈ target
      rw [hanchorIndexCorner]
      exact hanchorCorner

/-- Consequently the sharp binding-pair face has local complete-simplex count
zero modulo two. -/
theorem boxComplementarityLocalCompleteSimplexParity_eq_zero_of_sharpFace
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (defectTwo crossTwo defectThree crossThree : ℝ)
    (hsharp : problem.IsSharpBindingPairFace region defectTwo crossTwo
      defectThree crossThree)
    (hboundTwo : 2 ≤ boxComplementarityFaceGridBound p defectTwo crossTwo)
    (hboundThree : 2 ≤ boxComplementarityFaceGridBound p defectThree crossThree)
    (target : Set (UnitCube (Fin 4)))
    (hthicken : ∀ chain :
        Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G,
      simplex (boxComplementaritySpernerCube problem p hp) 4 chain →
      (∃ index, boxComplementarityGridPoint p (chain index) ∈ target) →
      ∀ index, boxComplementarityGridPoint p (chain index) ∈ region)
    (hanchorOrigin : boxComplementarityGridPoint p
      (boxComplementarityOriginChain p hp 0) ∈ target)
    (hanchorCorner : boxComplementarityGridPoint p
      (boxComplementarityCornerChain p
        (boxComplementarityFaceGridBound p defectTwo crossTwo)
        (boxComplementarityFaceGridBound p defectThree crossThree) 2) ∈
      target) :
    boxComplementarityLocalCompleteSimplexParity problem p hp target = 0 := by
  rw [boxComplementarityLocalCompleteSimplexParity,
    boxComplementarityLocalCompleteSimplices_card_eq_two_of_sharpFace problem p
      hp region hregion defectTwo crossTwo defectThree crossThree hsharp
      hboundTwo hboundThree target hthicken hanchorOrigin hanchorCorner]
  decide

end Math
