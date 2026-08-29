/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Topology.BoxComplementaritySpernerApproximation
import Research.Topology.CubicalSpernerKuhnChain

/-!
# Face position of complete grid simplices with negative leading gain

On a region of the four-dimensional unit cube where the two leading
coordinates have strictly negative gain and no coordinate reaches the upper
face, a coordinate is a grid violation exactly when it is positive.  Hence
every grid vertex whose reduced label is at least two has both leading grid
coordinates equal to zero.

A complete grid simplex all of whose vertices lie in such a region therefore
carries its three labels at least two on three chain vertices of the face
where the leading coordinates vanish.  Combined with the unit-step structure
of a top-dimensional chain, this pins the chain down completely: the first
three vertices lie on that face, the fourth raises the second coordinate and
carries label one, the fifth raises the first coordinate and carries label
zero, and both trailing coordinates are raised within the first two steps.

Consequently the gain of a trailing coordinate is only ever read on the face
where the leading coordinates vanish.
-/

noncomputable section

namespace Math

open Classical Set

/-! ## Regions with negative leading gain -/

/-- A region of the four-dimensional unit cube on which no coordinate reaches
the upper face and the two leading coordinates have strictly negative gain. -/
structure BoxComplementarityProblem.IsLeadingNegativeRegion
    (problem : BoxComplementarityProblem (Fin 4))
    (region : Set (UnitCube (Fin 4))) : Prop where
  /-- No coordinate reaches the upper face of the cube. -/
  lt_one : ∀ point ∈ region, ∀ who : Fin 4, (point who : ℝ) < 1
  /-- The two leading coordinates strictly prefer the lower action. -/
  gain_neg : ∀ point ∈ region, ∀ who : Fin 4, (who : ℕ) < 2 →
    problem.gain point who < 0

/-! ## Grid points and positivity -/

variable {n : ℕ}

/-- The real coordinate of a grid point is the grid value over the
resolution. -/
theorem boxComplementarityGridPoint_val (p : ℕ) (vertex : Fin n → Fin (p + 1))
    (who : Fin n) :
    ((boxComplementarityGridPoint p vertex who : Set.Icc (0 : ℝ) 1) : ℝ) =
      ((vertex who).1 : ℝ) / p := rfl

/-- A grid coordinate is positive exactly when its grid value is nonzero. -/
theorem boxComplementarityGridPoint_pos_iff (p : ℕ) (hp : 0 < p)
    (vertex : Fin n → Fin (p + 1)) (who : Fin n) :
    0 < ((boxComplementarityGridPoint p vertex who : Set.Icc (0 : ℝ) 1) : ℝ) ↔
      (vertex who).1 ≠ 0 := by
  have hcast : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · intro hpositive hzero
    rw [boxComplementarityGridPoint_val, hzero] at hpositive
    norm_num at hpositive
  · intro hne
    rw [boxComplementarityGridPoint_val]
    have hnumerator : (0 : ℝ) < ((vertex who).1 : ℝ) := by
      have hpos : 0 < (vertex who).1 := Nat.pos_of_ne_zero hne
      exact_mod_cast hpos
    exact div_pos hnumerator hcast

/-! ## Labels and the leading face -/

/-- On a region with negative leading gain, a positive leading grid coordinate
bounds the reduced label. -/
theorem boxComplementarityReducedLabel_le_of_leading_ne_zero
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (vertex : Fin 4 → Fin (p + 1))
    (hmem : boxComplementarityGridPoint p vertex ∈ region)
    (who : Fin 4) (hwho : (who : ℕ) < 2) (hne : (vertex who).1 ≠ 0) :
    boxComplementarityReducedLabel problem p vertex ≤ (who : ℕ) := by
  refine ((boxComplementarityReducedLabel_properties problem p vertex).2 who).2 ?_
  exact Or.inl ⟨(boxComplementarityGridPoint_pos_iff p hp vertex who).2 hne,
    hregion.gain_neg _ hmem who hwho⟩

/-- A grid vertex of such a region whose reduced label is at least two lies on
the face where both leading grid coordinates vanish. -/
theorem boxComplementarityLeading_eq_zero_of_two_le_label
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (vertex : Fin 4 → Fin (p + 1))
    (hmem : boxComplementarityGridPoint p vertex ∈ region)
    (hlabel : 2 ≤ boxComplementarityReducedLabel problem p vertex)
    (who : Fin 4) (hwho : (who : ℕ) < 2) :
    (vertex who).1 = 0 := by
  by_contra hne
  have hle := boxComplementarityReducedLabel_le_of_leading_ne_zero
    problem p hp region hregion vertex hmem who hwho hne
  omega

/-- A vanishing grid coordinate cannot carry its own reduced label. -/
theorem boxComplementarityReducedLabel_ne_of_val_eq_zero
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ)
    (vertex : Fin n → Fin (p + 1)) (who : Fin n)
    (hzero : (vertex who).1 = 0) :
    boxComplementarityReducedLabel problem p vertex ≠ (who : ℕ) :=
  boxComplementarityReducedLabel_ne_of_eq_zero problem p vertex who
    (Fin.val_injective hzero)

/-! ## The leading coordinate profile of a complete chain -/

/-- Numeric values of the four coordinate names. -/
private theorem fin_four_vals :
    ((0 : Fin 4) : ℕ) = 0 ∧ ((1 : Fin 4) : ℕ) = 1 ∧ ((2 : Fin 4) : ℕ) = 2 ∧
      ((3 : Fin 4) : ℕ) = 3 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Numeric values of the five chain positions. -/
private theorem fin_five_vals :
    ((0 : Fin (4 + 1)) : ℕ) = 0 ∧ ((1 : Fin (4 + 1)) : ℕ) = 1 ∧
      ((2 : Fin (4 + 1)) : ℕ) = 2 ∧ ((3 : Fin (4 + 1)) : ℕ) = 3 ∧
      ((4 : Fin (4 + 1)) : ℕ) = 4 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- In a complete grid simplex all of whose vertices lie in a region with
negative leading gain, the first leading coordinate is raised at the last step
and the second leading coordinate at the second-to-last step. -/
theorem boxComplementarityFaceChain_leading_eq
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (vertices : Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) 4 vertices)
    (hin : ∀ index, boxComplementarityGridPoint p (vertices index) ∈ region) :
    (∀ index : Fin (4 + 1),
        (vertices index (0 : Fin 4)).1 = if (index : ℕ) ≤ 3 then 0 else 1) ∧
      ∀ index : Fin (4 + 1),
        (vertices index (1 : Fin 4)).1 = if (index : ℕ) ≤ 2 then 0 else 1 := by
  obtain ⟨hval0, hval1, hval2, hval3⟩ := fin_four_vals
  obtain ⟨hidx0, hidx1, hidx2, hidx3, hidx4⟩ := fin_five_vals
  have hs : simplex (boxComplementaritySpernerCube problem p hp) 4 vertices :=
    hcomplete.1
  have hm : (4 : ℕ) = (boxComplementaritySpernerCube problem p hp).n := rfl
  have hinj : ∀ first second : Fin (4 + 1),
      boxComplementarityReducedLabel problem p (vertices first) =
        boxComplementarityReducedLabel problem p (vertices second) →
      first = second :=
    rl_inj_of_complete 4 vertices hcomplete
  -- the three vertices carrying labels at least two lie on the leading face
  have hface : ∀ index : Fin (4 + 1),
      2 ≤ boxComplementarityReducedLabel problem p (vertices index) →
      ∀ who : Fin 4, (who : ℕ) < 2 → (vertices index who).1 = 0 :=
    fun index hlabel who hwho ↦ boxComplementarityLeading_eq_zero_of_two_le_label
      problem p hp region hregion (vertices index) (hin index) hlabel who hwho
  have hlabelAnchor := boxComplementarityCompleteSimplexAnchorIndex_label
    problem p hp vertices hcomplete
  have hlabelTwo := boxComplementarityCompleteSimplexCoordinateIndex_label
    problem p hp vertices hcomplete (2 : Fin 4)
  have hlabelThree := boxComplementarityCompleteSimplexCoordinateIndex_label
    problem p hp vertices hcomplete (3 : Fin 4)
  rw [hval2] at hlabelTwo
  rw [hval3] at hlabelThree
  -- the initial vertex already lies on the leading face
  have hbase : ∀ who : Fin 4, (who : ℕ) < 2 → (vertices 0 who).1 = 0 := by
    intro who hwho
    have hanchor := hface (boxComplementarityCompleteSimplexAnchorIndex
      problem p hp vertices hcomplete) (by omega) who hwho
    have hmono := spernerSimplex_val_le_of_le hs
      (Fin.zero_le (boxComplementarityCompleteSimplexAnchorIndex
        problem p hp vertices hcomplete)) who
    omega
  -- the raising steps of the leading coordinates
  have hraise : ∀ who : Fin 4, ∀ index : Fin (4 + 1),
      ((vertices index who).1 = (vertices 0 who).1 ↔
        (index : ℕ) ≤ (spernerChainRaiseIndex hs hm who : ℕ)) :=
    fun who index ↦ spernerChain_val_eq_base_iff hs hm who index
  have hraiseLt : ∀ who : Fin 4, ∀ index : Fin (4 + 1),
      (spernerChainRaiseIndex hs hm who : ℕ) < (index : ℕ) →
        (vertices index who).1 = (vertices 0 who).1 + 1 :=
    fun who index hlt ↦ spernerChain_val_eq_of_raiseIndex_lt hs hm who hlt
  have hleadingLe : ∀ index : Fin (4 + 1),
      2 ≤ boxComplementarityReducedLabel problem p (vertices index) →
      (index : ℕ) ≤ (spernerChainRaiseIndex hs hm (0 : Fin 4) : ℕ) ∧
        (index : ℕ) ≤ (spernerChainRaiseIndex hs hm (1 : Fin 4) : ℕ) := by
    intro index hlabel
    constructor
    · exact (hraise (0 : Fin 4) index).1 (by
        rw [hface index hlabel (0 : Fin 4) (by omega),
          hbase (0 : Fin 4) (by omega)])
    · exact (hraise (1 : Fin 4) index).1 (by
        rw [hface index hlabel (1 : Fin 4) (by omega),
          hbase (1 : Fin 4) (by omega)])
  have hanchorLe := hleadingLe _ (by omega : 2 ≤
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexAnchorIndex problem p hp vertices
        hcomplete)))
  have htwoLe := hleadingLe _ (by omega : 2 ≤
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexCoordinateIndex problem p hp vertices
        hcomplete (2 : Fin 4))))
  have hthreeLe := hleadingLe _ (by omega : 2 ≤
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexCoordinateIndex problem p hp vertices
        hcomplete (3 : Fin 4))))
  -- the three carriers are distinct chain positions
  have hdistinct : ∀ first second : Fin (4 + 1),
      boxComplementarityReducedLabel problem p (vertices first) ≠
        boxComplementarityReducedLabel problem p (vertices second) →
      (first : ℕ) ≠ (second : ℕ) := by
    intro first second hne heq
    exact hne (by rw [Fin.val_injective heq])
  have hne23 := hdistinct _ _ (by omega :
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexCoordinateIndex problem p hp vertices
        hcomplete (2 : Fin 4))) ≠
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexCoordinateIndex problem p hp vertices
        hcomplete (3 : Fin 4))))
  have hne24 := hdistinct _ _ (by omega :
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexCoordinateIndex problem p hp vertices
        hcomplete (2 : Fin 4))) ≠
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexAnchorIndex problem p hp vertices
        hcomplete)))
  have hne34 := hdistinct _ _ (by omega :
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexCoordinateIndex problem p hp vertices
        hcomplete (3 : Fin 4))) ≠
    boxComplementarityReducedLabel problem p (vertices
      (boxComplementarityCompleteSimplexAnchorIndex problem p hp vertices
        hcomplete)))
  -- the two raising steps are distinct and at least two
  have hraiseNe : (spernerChainRaiseIndex hs hm (0 : Fin 4) : ℕ) ≠
      (spernerChainRaiseIndex hs hm (1 : Fin 4) : ℕ) := by
    intro heq
    have hstep : spernerChainRaiseIndex hs hm (0 : Fin 4) =
        spernerChainRaiseIndex hs hm (1 : Fin 4) := Fin.val_injective heq
    have hcoordinate : (0 : Fin 4) = (1 : Fin 4) :=
      spernerChainRaiseIndex_injective hs hm hstep
    exact absurd hcoordinate (by decide)
  have hbound0 : (spernerChainRaiseIndex hs hm (0 : Fin 4) : ℕ) < 4 :=
    (spernerChainRaiseIndex hs hm (0 : Fin 4)).isLt
  have hbound1 : (spernerChainRaiseIndex hs hm (1 : Fin 4) : ℕ) < 4 :=
    (spernerChainRaiseIndex hs hm (1 : Fin 4)).isLt
  -- the first leading coordinate is raised last
  have hzeroLast : (spernerChainRaiseIndex hs hm (0 : Fin 4) : ℕ) = 3 := by
    by_contra hne
    have hlt3 : (spernerChainRaiseIndex hs hm (0 : Fin 4) : ℕ) < 3 := by omega
    have hthreeVal : (vertices 3 (0 : Fin 4)).1 =
        (vertices 0 (0 : Fin 4)).1 + 1 := hraiseLt (0 : Fin 4) 3 (by omega)
    have hfourVal : (vertices 4 (0 : Fin 4)).1 =
        (vertices 0 (0 : Fin 4)).1 + 1 := hraiseLt (0 : Fin 4) 4 (by omega)
    have hzero := hbase (0 : Fin 4) (by omega)
    have hthreeLabel := boxComplementarityReducedLabel_le_of_leading_ne_zero
      problem p hp region hregion (vertices 3) (hin 3) (0 : Fin 4) (by omega)
      (by omega)
    have hfourLabel := boxComplementarityReducedLabel_le_of_leading_ne_zero
      problem p hp region hregion (vertices 4) (hin 4) (0 : Fin 4) (by omega)
      (by omega)
    have hsame : (3 : Fin (4 + 1)) = (4 : Fin (4 + 1)) :=
      hinj 3 4 (by omega)
    have := congrArg Fin.val hsame
    omega
  have honeLast : (spernerChainRaiseIndex hs hm (1 : Fin 4) : ℕ) = 2 := by
    omega
  constructor
  · intro index
    by_cases hle : (index : ℕ) ≤ 3
    · rw [if_pos hle]
      rw [(hraise (0 : Fin 4) index).2 (by omega)]
      exact hbase (0 : Fin 4) (by omega)
    · rw [if_neg hle]
      rw [hraiseLt (0 : Fin 4) index (by omega), hbase (0 : Fin 4) (by omega)]
  · intro index
    by_cases hle : (index : ℕ) ≤ 2
    · rw [if_pos hle]
      rw [(hraise (1 : Fin 4) index).2 (by omega)]
      exact hbase (1 : Fin 4) (by omega)
    · rw [if_neg hle]
      rw [hraiseLt (1 : Fin 4) index (by omega), hbase (1 : Fin 4) (by omega)]

/-! ## The forced chain position -/

/-- Positions and labels forced on a complete grid simplex all of whose
vertices lie in a region with negative leading gain. -/
structure BoxComplementarityFaceChainPosition
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (vertices : Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G) :
    Prop where
  /-- The first three chain vertices lie on the face where both leading
  coordinates vanish. -/
  leading_eq_zero : ∀ index : Fin (4 + 1), (index : ℕ) ≤ 2 →
    (vertices index (0 : Fin 4)).1 = 0 ∧ (vertices index (1 : Fin 4)).1 = 0
  /-- Those three vertices carry the three reduced labels at least two. -/
  two_le_label : ∀ index : Fin (4 + 1), (index : ℕ) ≤ 2 →
    2 ≤ boxComplementarityReducedLabel problem p (vertices index)
  /-- The fourth vertex raises the second leading coordinate only. -/
  leading_three :
    (vertices 3 (0 : Fin 4)).1 = 0 ∧ (vertices 3 (1 : Fin 4)).1 = 1
  /-- The last vertex raises the first leading coordinate as well. -/
  leading_four :
    (vertices 4 (0 : Fin 4)).1 = 1 ∧ (vertices 4 (1 : Fin 4)).1 = 1
  /-- The fourth vertex carries reduced label one. -/
  label_three : boxComplementarityReducedLabel problem p (vertices 3) = 1
  /-- The last vertex carries reduced label zero. -/
  label_four : boxComplementarityReducedLabel problem p (vertices 4) = 0
  /-- Both trailing coordinates are raised within the first two steps. -/
  trailing_raised : ∀ who : Fin 4, 2 ≤ (who : ℕ) → ∀ index : Fin (4 + 1),
    2 ≤ (index : ℕ) → (vertices index who).1 = (vertices 0 who).1 + 1
  /-- Exactly one trailing coordinate is raised at the first step. -/
  trailing_middle :
    ((vertices 1 (2 : Fin 4)).1 = (vertices 0 (2 : Fin 4)).1 + 1 ∧
        (vertices 1 (3 : Fin 4)).1 = (vertices 0 (3 : Fin 4)).1) ∨
      ((vertices 1 (2 : Fin 4)).1 = (vertices 0 (2 : Fin 4)).1 ∧
        (vertices 1 (3 : Fin 4)).1 = (vertices 0 (3 : Fin 4)).1 + 1)

/-- Only the first three chain positions carry a reduced label of at least
two. -/
theorem BoxComplementarityFaceChainPosition.index_le_two_of_two_le_label
    {problem : BoxComplementarityProblem (Fin 4)} {p : ℕ} {hp : 0 < p}
    {vertices : Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G}
    (hposition : BoxComplementarityFaceChainPosition problem p hp vertices)
    (index : Fin (4 + 1))
    (hlabel : 2 ≤ boxComplementarityReducedLabel problem p (vertices index)) :
    (index : ℕ) ≤ 2 := by
  obtain ⟨-, -, -, hidx3, hidx4⟩ := fin_five_vals
  by_contra hgt
  have hbound : (index : ℕ) < 4 + 1 := index.isLt
  have hcases : index = 3 ∨ index = 4 := by
    rcases Nat.lt_or_ge (index : ℕ) 4 with hlt | hge
    · exact Or.inl (Fin.val_injective (by omega))
    · exact Or.inr (Fin.val_injective (by omega))
  rcases hcases with hcase | hcase <;> rw [hcase] at hlabel
  · have := hposition.label_three
    omega
  · have := hposition.label_four
    omega

/-- Every complete grid simplex all of whose vertices lie in a region with
negative leading gain has the forced chain position. -/
theorem boxComplementarityFaceChainPosition_of_mem
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (vertices : Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) 4 vertices)
    (hin : ∀ index, boxComplementarityGridPoint p (vertices index) ∈ region) :
    BoxComplementarityFaceChainPosition problem p hp vertices := by
  obtain ⟨hval0, hval1, hval2, hval3⟩ := fin_four_vals
  obtain ⟨hidx0, hidx1, hidx2, hidx3, hidx4⟩ := fin_five_vals
  have hs : simplex (boxComplementaritySpernerCube problem p hp) 4 vertices :=
    hcomplete.1
  have hm : (4 : ℕ) = (boxComplementaritySpernerCube problem p hp).n := rfl
  obtain ⟨hcoordZero, hcoordOne⟩ := boxComplementarityFaceChain_leading_eq
    problem p hp region hregion vertices hcomplete hin
  -- values of the leading coordinates at the five chain positions
  have hzeroFace : ∀ index : Fin (4 + 1), (index : ℕ) ≤ 2 →
      (vertices index (0 : Fin 4)).1 = 0 ∧ (vertices index (1 : Fin 4)).1 = 0 := by
    intro index hle
    refine ⟨?_, ?_⟩
    · rw [hcoordZero index, if_pos (by omega)]
    · rw [hcoordOne index, if_pos (by omega)]
  have hthreeZero : (vertices 3 (0 : Fin 4)).1 = 0 := by
    rw [hcoordZero 3, if_pos (by omega)]
  have hthreeOne : (vertices 3 (1 : Fin 4)).1 = 1 := by
    rw [hcoordOne 3, if_neg (by omega)]
  have hfourZero : (vertices 4 (0 : Fin 4)).1 = 1 := by
    rw [hcoordZero 4, if_neg (by omega)]
  have hfourOne : (vertices 4 (1 : Fin 4)).1 = 1 := by
    rw [hcoordOne 4, if_neg (by omega)]
  -- labels of the last two chain positions
  have hlabelFour : boxComplementarityReducedLabel problem p (vertices 4) = 0 := by
    have hle := boxComplementarityReducedLabel_le_of_leading_ne_zero
      problem p hp region hregion (vertices 4) (hin 4) (0 : Fin 4) (by omega)
      (by omega)
    omega
  have hlabelThree : boxComplementarityReducedLabel problem p (vertices 3) = 1 := by
    have hne := boxComplementarityReducedLabel_ne_of_val_eq_zero
      problem p (vertices 3) (0 : Fin 4) hthreeZero
    have hle := boxComplementarityReducedLabel_le_of_leading_ne_zero
      problem p hp region hregion (vertices 3) (hin 3) (1 : Fin 4) (by omega)
      (by omega)
    omega
  -- the raising steps of the two leading coordinates
  have hraise : ∀ who : Fin 4, ∀ index : Fin (4 + 1),
      ((vertices index who).1 = (vertices 0 who).1 ↔
        (index : ℕ) ≤ (spernerChainRaiseIndex hs hm who : ℕ)) :=
    fun who index ↦ spernerChain_val_eq_base_iff hs hm who index
  have hraiseLt : ∀ who : Fin 4, ∀ index : Fin (4 + 1),
      (spernerChainRaiseIndex hs hm who : ℕ) < (index : ℕ) →
        (vertices index who).1 = (vertices 0 who).1 + 1 :=
    fun who index hlt ↦ spernerChain_val_eq_of_raiseIndex_lt hs hm who hlt
  have hbaseZero : (vertices 0 (0 : Fin 4)).1 = 0 := (hzeroFace 0 (by omega)).1
  have hbaseOne : (vertices 0 (1 : Fin 4)).1 = 0 := (hzeroFace 0 (by omega)).2
  have hraiseZero : (spernerChainRaiseIndex hs hm (0 : Fin 4) : ℕ) = 3 := by
    have hupper : ¬((4 : ℕ) ≤ (spernerChainRaiseIndex hs hm (0 : Fin 4) : ℕ)) := by
      intro hge
      have := (hraise (0 : Fin 4) 4).2 (by omega)
      omega
    have hlower : (3 : ℕ) ≤ (spernerChainRaiseIndex hs hm (0 : Fin 4) : ℕ) := by
      have := (hraise (0 : Fin 4) 3).1 (by omega)
      omega
    omega
  have hraiseOne : (spernerChainRaiseIndex hs hm (1 : Fin 4) : ℕ) = 2 := by
    have hupper : ¬((3 : ℕ) ≤ (spernerChainRaiseIndex hs hm (1 : Fin 4) : ℕ)) := by
      intro hge
      have := (hraise (1 : Fin 4) 3).2 (by omega)
      omega
    have hlower : (2 : ℕ) ≤ (spernerChainRaiseIndex hs hm (1 : Fin 4) : ℕ) := by
      have := (hraise (1 : Fin 4) 2).1 (by
        rw [(hzeroFace 2 (by omega)).2, hbaseOne])
      omega
    omega
  -- the trailing coordinates are raised at the first two steps
  have hraiseNe : ∀ first second : Fin 4, first ≠ second →
      (spernerChainRaiseIndex hs hm first : ℕ) ≠
        (spernerChainRaiseIndex hs hm second : ℕ) := by
    intro first second hne heq
    exact hne (spernerChainRaiseIndex_injective hs hm (Fin.val_injective heq))
  have hraiseTwoBound : (spernerChainRaiseIndex hs hm (2 : Fin 4) : ℕ) < 4 :=
    (spernerChainRaiseIndex hs hm (2 : Fin 4)).isLt
  have hraiseThreeBound : (spernerChainRaiseIndex hs hm (3 : Fin 4) : ℕ) < 4 :=
    (spernerChainRaiseIndex hs hm (3 : Fin 4)).isLt
  have hne20 := hraiseNe (2 : Fin 4) (0 : Fin 4) (by decide)
  have hne21 := hraiseNe (2 : Fin 4) (1 : Fin 4) (by decide)
  have hne30 := hraiseNe (3 : Fin 4) (0 : Fin 4) (by decide)
  have hne31 := hraiseNe (3 : Fin 4) (1 : Fin 4) (by decide)
  have hne23 := hraiseNe (2 : Fin 4) (3 : Fin 4) (by decide)
  refine ⟨hzeroFace, ?_, ⟨hthreeZero, hthreeOne⟩, ⟨hfourZero, hfourOne⟩,
    hlabelThree, hlabelFour, ?_, ?_⟩
  · intro index hle
    have hne0 := boxComplementarityReducedLabel_ne_of_val_eq_zero
      problem p (vertices index) (0 : Fin 4) (hzeroFace index hle).1
    have hne1 := boxComplementarityReducedLabel_ne_of_val_eq_zero
      problem p (vertices index) (1 : Fin 4) (hzeroFace index hle).2
    omega
  · intro who hwho index hindex
    have hcases : who = (2 : Fin 4) ∨ who = (3 : Fin 4) := by
      have hbound : (who : ℕ) < 4 := who.isLt
      rcases Nat.lt_or_ge (who : ℕ) 3 with hlt | hge
      · exact Or.inl (Fin.val_injective (by omega))
      · exact Or.inr (Fin.val_injective (by omega))
    rcases hcases with hcase | hcase <;> subst hcase <;>
      exact hraiseLt _ index (by omega)
  · rcases Nat.lt_or_ge (spernerChainRaiseIndex hs hm (2 : Fin 4) : ℕ) 1 with
      hlt | hge
    · refine Or.inl ⟨hraiseLt (2 : Fin 4) 1 (by omega), ?_⟩
      exact (hraise (3 : Fin 4) 1).2 (by omega)
    · refine Or.inr ⟨(hraise (2 : Fin 4) 1).2 (by omega), ?_⟩
      exact hraiseLt (3 : Fin 4) 1 (by omega)

end Math
