/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Topology.BoxComplementarityFaceSimplexPosition
import Research.Topology.BoxComplementaritySpernerLocalCount

/-!
# Vanishing local counts from a nonnegative trailing face gain

On a region of the four-dimensional unit cube where the two leading
coordinates have strictly negative gain and no coordinate reaches the upper
face, every complete grid simplex reads the gain of a trailing coordinate only
on the face where the leading coordinates vanish.  If that gain is nonnegative
there, the trailing label cannot be carried at all, so no complete grid
simplex has all its vertices in the region and the local complete-simplex
count of any region whose anchors thicken into it is zero.

The affine specialization is the degenerate binding face: when the own defect
of a trailing coordinate vanishes and its cross term is nonnegative, its exact
affine face gain is the product of the other trailing coordinate with that
cross term, hence nonnegative.  Both trailing coordinates are treated, so
either degenerate binding support gives a zero local count.
-/

noncomputable section

namespace Math

open Classical Set

/-! ## A nonnegative trailing face gain excludes complete simplices -/

/-- If a trailing coordinate has nonnegative gain on the face of a region with
negative leading gain, no complete grid simplex has all of its vertices in
that region. -/
theorem not_completeSimplex_of_face_gain_nonneg
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (who : Fin 4) (hwho : 2 ≤ (who : ℕ))
    (hface : ∀ point ∈ region,
      ((point 0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 →
      ((point 1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 → 0 ≤ problem.gain point who)
    (vertices : Fin (4 + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) 4 vertices)
    (hin : ∀ index, boxComplementarityGridPoint p (vertices index) ∈ region) :
    False := by
  have hposition := boxComplementarityFaceChainPosition_of_mem
    problem p hp region hregion vertices hcomplete hin
  obtain ⟨carrier, hcarrierLabel, hcarrierViolation⟩ :
      ∃ carrier : Fin (4 + 1),
        boxComplementarityReducedLabel problem p (vertices carrier) = (who : ℕ) ∧
          problem.IsGridViolation p (vertices carrier) who :=
    ⟨boxComplementarityCompleteSimplexCoordinateIndex problem p hp vertices
        hcomplete who,
      boxComplementarityCompleteSimplexCoordinateIndex_label problem p hp
        vertices hcomplete who,
      isGridViolation_completeSimplexCoordinate problem p hp vertices hcomplete
        who⟩
  have hindex := hposition.index_le_two_of_two_le_label carrier (by omega)
  obtain ⟨hleadingZero, hleadingOne⟩ := hposition.leading_eq_zero carrier hindex
  have hmem := hin carrier
  have hzeroReal : ((boxComplementarityGridPoint p (vertices carrier)
      (0 : Fin 4) : Set.Icc (0 : ℝ) 1) : ℝ) = 0 :=
    boxComplementarityGridPoint_eq_zero (n := 4) p (vertices carrier) 0
      (Fin.val_injective hleadingZero)
  have honeReal : ((boxComplementarityGridPoint p (vertices carrier)
      (1 : Fin 4) : Set.Icc (0 : ℝ) 1) : ℝ) = 0 :=
    boxComplementarityGridPoint_eq_zero (n := 4) p (vertices carrier) 1
      (Fin.val_injective hleadingOne)
  rw [BoxComplementarityProblem.IsGridViolation] at hcarrierViolation
  rcases hcarrierViolation with ⟨-, hnegative⟩ | htop
  · exact absurd (hface _ hmem hzeroReal honeReal) (not_le.2 hnegative)
  · exact absurd htop (ne_of_lt (hregion.lt_one _ hmem who))

/-- Under the same hypotheses the local complete-simplex count of any region
whose anchors thicken into the displayed one is zero. -/
theorem boxComplementarityLocalCompleteSimplexParity_eq_zero_of_face_gain_nonneg
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (who : Fin 4) (hwho : 2 ≤ (who : ℕ))
    (hface : ∀ point ∈ region,
      ((point 0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 →
      ((point 1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 → 0 ≤ problem.gain point who)
    (target : Set (UnitCube (Fin 4)))
    (hthicken : ∀ vertices (hcomplete : complete_simplex
        (boxComplementaritySpernerCube problem p hp) 4 vertices),
      boxComplementarityCompleteSimplexAnchorPoint problem p hp vertices
          hcomplete ∈ target →
        ∀ index, boxComplementarityGridPoint p (vertices index) ∈ region) :
    boxComplementarityLocalCompleteSimplexParity problem p hp target = 0 := by
  have hempty :
      boxComplementarityLocalCompleteSimplices problem p hp target = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨vertices, hvertices⟩
    obtain ⟨hcomplete, hanchor⟩ :=
      (mem_boxComplementarityLocalCompleteSimplices_iff problem p hp target
        vertices).1 hvertices
    exact not_completeSimplex_of_face_gain_nonneg problem p hp region hregion
      who hwho hface vertices hcomplete (hthicken vertices hcomplete hanchor)
  rw [boxComplementarityLocalCompleteSimplexParity, hempty]
  norm_num

/-! ## The exact affine face gains -/

/-- Exact affine gains of the two trailing coordinates on the face where both
leading coordinates vanish, with own defects `deltaTwo`, `deltaThree` and
cross terms `jTwoThree`, `jThreeTwo`. -/
def BoxComplementarityProblem.HasAffineFaceGain
    (problem : BoxComplementarityProblem (Fin 4))
    (region : Set (UnitCube (Fin 4)))
    (deltaTwo jTwoThree deltaThree jThreeTwo : ℝ) : Prop :=
  ∀ point ∈ region,
    ((point 0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 →
    ((point 1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 →
      problem.gain point 2 =
          -(1 - ((point 3 : Set.Icc (0 : ℝ) 1) : ℝ)) * deltaTwo +
            ((point 3 : Set.Icc (0 : ℝ) 1) : ℝ) * jTwoThree ∧
        problem.gain point 3 =
          -(1 - ((point 2 : Set.Icc (0 : ℝ) 1) : ℝ)) * deltaThree +
            ((point 2 : Set.Icc (0 : ℝ) 1) : ℝ) * jThreeTwo

/-- With a vanishing own defect and a nonnegative cross term, the affine face
gain of the first trailing coordinate is nonnegative. -/
theorem gain_two_nonneg_of_affineFaceGain_deltaTwo_zero
    (problem : BoxComplementarityProblem (Fin 4))
    (region : Set (UnitCube (Fin 4)))
    (jTwoThree deltaThree jThreeTwo : ℝ)
    (haffine : problem.HasAffineFaceGain region 0 jTwoThree deltaThree jThreeTwo)
    (hcross : 0 ≤ jTwoThree)
    (point : UnitCube (Fin 4)) (hmem : point ∈ region)
    (hzero : ((point 0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0)
    (hone : ((point 1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0) :
    0 ≤ problem.gain point 2 := by
  have hnonneg : (0 : ℝ) ≤ ((point 3 : Set.Icc (0 : ℝ) 1) : ℝ) :=
    (point 3).property.1
  rw [(haffine point hmem hzero hone).1]
  have hexpand : -(1 - ((point 3 : Set.Icc (0 : ℝ) 1) : ℝ)) * 0 +
      ((point 3 : Set.Icc (0 : ℝ) 1) : ℝ) * jTwoThree =
        ((point 3 : Set.Icc (0 : ℝ) 1) : ℝ) * jTwoThree := by ring
  rw [hexpand]
  exact mul_nonneg hnonneg hcross

/-- With a vanishing own defect and a nonnegative cross term, the affine face
gain of the second trailing coordinate is nonnegative. -/
theorem gain_three_nonneg_of_affineFaceGain_deltaThree_zero
    (problem : BoxComplementarityProblem (Fin 4))
    (region : Set (UnitCube (Fin 4)))
    (deltaTwo jTwoThree jThreeTwo : ℝ)
    (haffine : problem.HasAffineFaceGain region deltaTwo jTwoThree 0 jThreeTwo)
    (hcross : 0 ≤ jThreeTwo)
    (point : UnitCube (Fin 4)) (hmem : point ∈ region)
    (hzero : ((point 0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0)
    (hone : ((point 1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0) :
    0 ≤ problem.gain point 3 := by
  have hnonneg : (0 : ℝ) ≤ ((point 2 : Set.Icc (0 : ℝ) 1) : ℝ) :=
    (point 2).property.1
  rw [(haffine point hmem hzero hone).2]
  have hexpand : -(1 - ((point 2 : Set.Icc (0 : ℝ) 1) : ℝ)) * 0 +
      ((point 2 : Set.Icc (0 : ℝ) 1) : ℝ) * jThreeTwo =
        ((point 2 : Set.Icc (0 : ℝ) 1) : ℝ) * jThreeTwo := by ring
  rw [hexpand]
  exact mul_nonneg hnonneg hcross

/-! ## The degenerate binding face has zero local count -/

/-- The first trailing coordinate is the degenerate one: its own defect
vanishes and its cross term is nonnegative.  Then the local
complete-simplex count is zero. -/
theorem boxComplementarityLocalCompleteSimplexParity_eq_zero_of_soloTwo
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (jTwoThree deltaThree jThreeTwo : ℝ)
    (haffine : problem.HasAffineFaceGain region 0 jTwoThree deltaThree jThreeTwo)
    (hcross : 0 ≤ jTwoThree)
    (target : Set (UnitCube (Fin 4)))
    (hthicken : ∀ vertices (hcomplete : complete_simplex
        (boxComplementaritySpernerCube problem p hp) 4 vertices),
      boxComplementarityCompleteSimplexAnchorPoint problem p hp vertices
          hcomplete ∈ target →
        ∀ index, boxComplementarityGridPoint p (vertices index) ∈ region) :
    boxComplementarityLocalCompleteSimplexParity problem p hp target = 0 :=
  boxComplementarityLocalCompleteSimplexParity_eq_zero_of_face_gain_nonneg
    problem p hp region hregion (2 : Fin 4) (by decide)
    (fun point hmem hzero hone ↦
      gain_two_nonneg_of_affineFaceGain_deltaTwo_zero problem region jTwoThree
        deltaThree jThreeTwo haffine hcross point hmem hzero hone)
    target hthicken

/-- The second trailing coordinate is the degenerate one.  Then the local
complete-simplex count is zero. -/
theorem boxComplementarityLocalCompleteSimplexParity_eq_zero_of_soloThree
    (problem : BoxComplementarityProblem (Fin 4)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin 4)))
    (hregion : problem.IsLeadingNegativeRegion region)
    (deltaTwo jTwoThree jThreeTwo : ℝ)
    (haffine : problem.HasAffineFaceGain region deltaTwo jTwoThree 0 jThreeTwo)
    (hcross : 0 ≤ jThreeTwo)
    (target : Set (UnitCube (Fin 4)))
    (hthicken : ∀ vertices (hcomplete : complete_simplex
        (boxComplementaritySpernerCube problem p hp) 4 vertices),
      boxComplementarityCompleteSimplexAnchorPoint problem p hp vertices
          hcomplete ∈ target →
        ∀ index, boxComplementarityGridPoint p (vertices index) ∈ region) :
    boxComplementarityLocalCompleteSimplexParity problem p hp target = 0 :=
  boxComplementarityLocalCompleteSimplexParity_eq_zero_of_face_gain_nonneg
    problem p hp region hregion (3 : Fin 4) (by decide)
    (fun point hmem hzero hone ↦
      gain_three_nonneg_of_affineFaceGain_deltaThree_zero problem region
        deltaTwo jTwoThree jThreeTwo haffine hcross point hmem hzero hone)
    target hthicken

/-! ## Satisfiability of the hypothesis bundle -/

/-- The four-coordinate problem whose leading gains are constantly negative
and whose trailing gains vanish. -/
def constantLeadingNegativeProblem : BoxComplementarityProblem (Fin 4) where
  gain := fun _ who ↦ if (who : ℕ) < 2 then -1 else 0
  continuous_gain := fun _ ↦ continuous_const

/-- The part of the cube strictly below every upper face. -/
def unitCubeBelowTop : Set (UnitCube (Fin 4)) :=
  {point | ∀ who : Fin 4, ((point who : Set.Icc (0 : ℝ) 1) : ℝ) < 1}

theorem unitCubeBelowTop_nonempty : unitCubeBelowTop.Nonempty :=
  ⟨fun _ ↦ ⟨0, by constructor <;> norm_num⟩, fun _ ↦ by norm_num⟩

theorem constantLeadingNegativeProblem_isLeadingNegativeRegion :
    constantLeadingNegativeProblem.IsLeadingNegativeRegion unitCubeBelowTop where
  lt_one := fun _ hmem who ↦ hmem who
  gain_neg := fun _ _ _ hwho ↦ by
    simp only [constantLeadingNegativeProblem, if_pos hwho]
    norm_num

theorem constantLeadingNegativeProblem_hasAffineFaceGain :
    constantLeadingNegativeProblem.HasAffineFaceGain unitCubeBelowTop 0 0 0 0 := by
  intro point _ _ _
  constructor <;> simp [constantLeadingNegativeProblem]

/-- The negative leading gain and the degenerate affine face gains hold
together on a nonempty region. -/
theorem exists_isLeadingNegativeRegion_hasAffineFaceGain :
    ∃ (problem : BoxComplementarityProblem (Fin 4))
      (region : Set (UnitCube (Fin 4))),
      region.Nonempty ∧ problem.IsLeadingNegativeRegion region ∧
        problem.HasAffineFaceGain region 0 0 0 0 :=
  ⟨constantLeadingNegativeProblem, unitCubeBelowTop, unitCubeBelowTop_nonempty,
    constantLeadingNegativeProblem_isLeadingNegativeRegion,
    constantLeadingNegativeProblem_hasAffineFaceGain⟩

end Math
