/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous box-complementarity problems

Neutral finite-cube gain fields, their exact solutions and isolating regions,
and jointly continuous one-parameter families. No parity or integer-degree
implementation is part of this foundation.
-/

noncomputable section

namespace Math

open Set

/-- The finite product of closed unit intervals. -/
abbrev UnitCube (ι : Type*) [Fintype ι] := ∀ _ : ι, Set.Icc (0 : ℝ) 1

variable (ι : Type*) [Fintype ι]

/-- A continuous gain field on a finite unit cube.  Positive gain means that
the upper action is preferred to the lower action. -/
structure BoxComplementarityProblem where
  gain : UnitCube ι → ι → ℝ
  continuous_gain : ∀ who, Continuous fun point ↦ gain point who

namespace BoxComplementarityProblem

variable {ι}

/-- Exact coordinatewise complementarity on the closed unit cube. -/
def IsSolution (problem : BoxComplementarityProblem ι) (point : UnitCube ι) : Prop :=
  ∀ who,
    ((point who : ℝ) = 0 → problem.gain point who ≤ 0) ∧
    ((point who : ℝ) = 1 → 0 ≤ problem.gain point who) ∧
    (0 < (point who : ℝ) → (point who : ℝ) < 1 → problem.gain point who = 0)

/-- A vanishing gain field satisfies complementarity, including on cube faces. -/
theorem isSolution_of_gain_eq_zero (problem : Math.BoxComplementarityProblem ι)
    (point : Math.UnitCube ι) (hzero : problem.gain point = 0) :
    problem.IsSolution point := by
  simp [IsSolution, hzero]

/-- At a coordinate-interior point, complementarity is exactly vanishing gain. -/
theorem isSolution_iff_gain_eq_zero_of_coordinateInterior
    (problem : Math.BoxComplementarityProblem ι) (point : Math.UnitCube ι)
    (hpoint : ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1) :
    problem.IsSolution point ↔ problem.gain point = 0 := by
  constructor
  · intro hsolution
    funext who
    exact (hsolution who).2.2 (hpoint who).1 (hpoint who).2
  · exact problem.isSolution_of_gain_eq_zero point

/-- All box-complementarity solutions. -/
def solutionSet (problem : BoxComplementarityProblem ι) : Set (UnitCube ι) :=
  {point | problem.IsSolution point}

/-- Solutions lying in a displayed relative neighborhood. -/
def solutionsIn (problem : BoxComplementarityProblem ι)
    (neighborhood : Set (UnitCube ι)) : Set (UnitCube ι) :=
  problem.solutionSet ∩ neighborhood

/-- A relative open set isolates the solutions it contains when no solution
lies on its relative frontier in the compact cube. -/
def IsIsolating (problem : BoxComplementarityProblem ι)
    (neighborhood : Set (UnitCube ι)) : Prop :=
  IsOpen neighborhood ∧ problem.solutionSet ∩ frontier neighborhood = ∅

end BoxComplementarityProblem

/-- Joint continuity of a one-parameter family of box-complementarity
problems. -/
def IsContinuousBoxComplementarityFamily
    (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem ι) : Prop :=
  ∀ who, Continuous fun data : Set.Icc (0 : ℝ) 1 × UnitCube ι ↦
    (family data.1).gain data.2 who

/-- The zero endpoint of the unit parameter interval. -/
def unitIntervalZero : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩

/-- The one endpoint of the unit parameter interval. -/
def unitIntervalOne : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

end Math

