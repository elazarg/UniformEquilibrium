/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import FixedPointTheorems.cubical_sperner
import Research.Topology.ModTwoBoxComplementarityParity

/-!
# Finite-grid Sperner labeling for box complementarity

This module is the first concrete layer below
`ModTwoBoxComplementarityParitySpec`.  It labels a rational cubical grid by
the first coordinate at which the projected complementarity direction points
down, with the upper boundary included as in the reduced-label convention of
the pinned cubical Sperner theorem.

The result here is global and finite: the number of complete grid simplices is
odd at every positive resolution.  No local parity, mesh-stability,
regularity, or `ModTwoBoxComplementarityParitySpec` inhabitant is constructed.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

/-- The rational unit-cube point represented by a positive-resolution grid
vertex. -/
def boxComplementarityGridPoint
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) : UnitCube (Fin n) :=
  fun who ↦ ⟨((vertex who).1 : ℝ) / p, by
    constructor
    · positivity
    · apply div_le_one_of_le₀
      · exact_mod_cast Fin.is_le (vertex who)
      · positivity⟩

@[simp] theorem boxComplementarityGridPoint_eq_zero
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) (who : Fin n)
    (hzero : vertex who = 0) :
    ((boxComplementarityGridPoint p vertex who : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by
  simp [boxComplementarityGridPoint, hzero]

@[simp] theorem boxComplementarityGridPoint_eq_one
    (p : ℕ) (hp : 0 < p) (vertex : Fin n → Fin (p + 1)) (who : Fin n)
    (htop : (vertex who).1 = p) :
    ((boxComplementarityGridPoint p vertex who : Set.Icc (0 : ℝ) 1) : ℝ) = 1 := by
  simp [boxComplementarityGridPoint, htop, Nat.ne_of_gt hp]

/-- The coordinate condition used by the reduced grid label.  Away from the
upper face it says that the coordinate is positive and its gain is negative;
at the upper face it is automatically active. -/
def BoxComplementarityProblem.IsGridViolation
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) (who : Fin n) : Prop :=
  let point := boxComplementarityGridPoint p vertex
  (0 < (point who : ℝ) ∧ problem.gain point who < 0) ∨
    (point who : ℝ) = 1

/-- Coordinates eligible to label one grid vertex. -/
def boxComplementarityGridViolationSet
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) : Finset (Fin n) := by
  classical
  exact {who | problem.IsGridViolation p vertex who}

/-- The first violating coordinate, or the extra label `n` when no coordinate
violates. -/
def boxComplementarityReducedLabel
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) : ℕ :=
  match (boxComplementarityGridViolationSet problem p vertex).min with
  | some who => who.1
  | none => n

/-- The reduced label is bounded by the cube dimension; a coordinate carrying
the label is a grid violation, and every grid violation bounds the label from
above. -/
theorem boxComplementarityReducedLabel_properties
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) :
    boxComplementarityReducedLabel problem p vertex ≤ n ∧
      ∀ who,
        (boxComplementarityReducedLabel problem p vertex = who.1 →
          problem.IsGridViolation p vertex who) ∧
        (problem.IsGridViolation p vertex who →
          boxComplementarityReducedLabel problem p vertex ≤ who.1) := by
  let violations := boxComplementarityGridViolationSet problem p vertex
  by_cases hempty : violations = ∅
  · have hlabel : boxComplementarityReducedLabel problem p vertex = n := by
      simp [boxComplementarityReducedLabel, violations, hempty]
    rw [hlabel]
    refine ⟨le_rfl, fun who ↦ ⟨?_, ?_⟩⟩
    · intro heq
      omega
    · intro hviolation
      have hmem : who ∈ violations := by
        change who ∈ boxComplementarityGridViolationSet problem p vertex
        simp only [boxComplementarityGridViolationSet, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hviolation
      rw [hempty] at hmem
      simp at hmem
  · have hnonempty : violations.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨minimum, hminimum⟩ := Finset.min_of_nonempty hnonempty
    have hlabel : boxComplementarityReducedLabel problem p vertex = minimum.1 := by
      simp [boxComplementarityReducedLabel, violations, hminimum]
    rw [hlabel]
    refine ⟨Nat.le_of_lt minimum.isLt, fun who ↦ ⟨?_, ?_⟩⟩
    · intro heq
      have hmem : who ∈ violations := by
        apply Finset.mem_of_min
        rw [hminimum]
        simp only [WithTop.coe_eq_coe]
        ext
        exact heq
      simpa [violations, boxComplementarityGridViolationSet] using hmem
    · intro hviolation
      have hmem : who ∈ violations := by
        change who ∈ boxComplementarityGridViolationSet problem p vertex
        simp only [boxComplementarityGridViolationSet, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hviolation
      have hle : minimum ≤ who :=
        Finset.min_le_of_eq (s := violations) hmem hminimum
      exact Fin.val_fin_le.mpr hle

/-- A zero grid coordinate cannot carry its own reduced label. -/
theorem boxComplementarityReducedLabel_ne_of_eq_zero
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (vertex : Fin n → Fin (p + 1)) (who : Fin n)
    (hzero : vertex who = 0) :
    boxComplementarityReducedLabel problem p vertex ≠ who.1 := by
  intro hlabel
  have hviolation :=
    (boxComplementarityReducedLabel_properties problem p vertex).2 who |>.1 hlabel
  rw [BoxComplementarityProblem.IsGridViolation] at hviolation
  have hpoint := boxComplementarityGridPoint_eq_zero p vertex who hzero
  rw [hpoint] at hviolation
  norm_num at hviolation

/-- At an upper-face grid coordinate, the reduced label is no larger than
that coordinate. -/
theorem boxComplementarityReducedLabel_le_of_eq_last
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) (vertex : Fin n → Fin (p + 1)) (who : Fin n)
    (htop : (vertex who).1 = p) :
    boxComplementarityReducedLabel problem p vertex ≤ who.1 := by
  apply (boxComplementarityReducedLabel_properties problem p vertex).2 who |>.2
  rw [BoxComplementarityProblem.IsGridViolation]
  exact Or.inr (boxComplementarityGridPoint_eq_one p hp vertex who htop)

/-- The concrete cubical Sperner instance associated with one box
complementarity problem and one positive grid resolution. -/
def boxComplementaritySpernerCube
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) : SpernerCube where
  n := n
  p := p
  RL := boxComplementarityReducedLabel problem p
  rl_proper := by
    intro vertex
    refine ⟨(boxComplementarityReducedLabel_properties problem p vertex).1,
      fun who ↦ ⟨?_, ?_⟩⟩
    · exact boxComplementarityReducedLabel_ne_of_eq_zero
        problem p vertex who
    · exact boxComplementarityReducedLabel_le_of_eq_last
        problem p hp vertex who

/-- Boundary admissibility of the concrete complementarity grid labeling. -/
theorem boxComplementaritySpernerCube_rl_proper
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) :
    ∀ vertex,
      boxComplementarityReducedLabel problem p vertex ≤ n ∧
        ∀ who,
          (vertex who = 0 →
            boxComplementarityReducedLabel problem p vertex ≠ who.1) ∧
          ((vertex who).1 = p →
            boxComplementarityReducedLabel problem p vertex ≤ who.1) :=
  (boxComplementaritySpernerCube problem p hp).rl_proper

/-- At every positive grid resolution, the number of complete top-dimensional
simplices for the concrete complementarity labeling is odd. -/
theorem boxComplementarity_completeSimplex_card_odd
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) :
    Odd (Finset.card {
      simplexVertices : Fin ((boxComplementaritySpernerCube problem p hp).n + 1) →
        (boxComplementaritySpernerCube problem p hp).G |
      complete_simplex (boxComplementaritySpernerCube problem p hp)
        (boxComplementaritySpernerCube problem p hp).n simplexVertices}) :=
  strong_cubical_sperner (boxComplementaritySpernerCube problem p hp).n
    (boxComplementaritySpernerCube problem p hp) rfl

/-- The odd finite count in particular supplies a complete labeled simplex. -/
theorem exists_boxComplementarity_completeSimplex
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) :
    ∃ simplexVertices :
        Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G,
      complete_simplex (boxComplementaritySpernerCube problem p hp) n
        simplexVertices :=
  weaker_cubical_sperner (boxComplementaritySpernerCube problem p hp)

end Math
