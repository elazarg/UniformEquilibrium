/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# An open mod-two parity interface for box complementarity

This module states the smallest topological interface needed by the strict-ray
binding-cardinality argument.  It deliberately does not assert that the parity
implementation exists.  A future boundary-degree development can construct the
interface without changing its quitting-game consumers.

Isolation is relative to the compact unit cube.  There is no redundant ambient
boundedness hypothesis.  `IsRegular` remains an API predicate: no derivative
notion is selected until a concrete degree construction needs one.

## Construction seam

The pinned fixed-point dependency already proves `strong_cubical_sperner` in
`FixedPointTheorems/cubical_sperner.lean`: every proper labeling of a finite
cubical grid has an odd number of complete top-dimensional simplices.  A
concrete implementation of this interface can use that theorem as follows.

1. Uniformly discretize the continuous gain field on the cube and label each
   grid vertex by the first violated complementarity coordinate and sign.
   Boundary complementarity gives `SpernerCube.rl_proper`.
2. Define local parity as the eventual parity of complete simplices whose
   cells meet the relative isolating neighborhood.  Absence of a frontier
   solution makes this stable for fine meshes.
3. Apply the same double-counting argument to a parameter-times-cube grid for
   common-isolating-neighborhood homotopy invariance.  Partitioning complete
   simplices proves excision.
4. Near finitely many regular solutions, local affine signs identify exactly
   one complete simplex modulo two, yielding the finite-regular cardinal law.

Those steps construct the four fields below.  They are not carried out or
claimed in this specification module.
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

/-- Open contract for a mod-two local parity on box-complementarity problems.

The four laws are exactly the ones used downstream: global oddness, excision,
common-neighborhood homotopy invariance, and counting of finitely many regular
solutions.  The structure is data supplied to conditional theorems; this file
does not construct an inhabitant. -/
structure ModTwoBoxComplementarityParitySpec where
  IsRegular : BoxComplementarityProblem ι → UnitCube ι → Prop
  regular_isSolution : ∀ problem point,
    IsRegular problem point → problem.IsSolution point
  localParity : BoxComplementarityProblem ι → Set (UnitCube ι) → ZMod 2
  globalParity_eq_one : ∀ problem, localParity problem Set.univ = 1
  localParity_eq_global_of_solutionSet_subset : ∀ problem neighborhood,
    problem.IsIsolating neighborhood →
    problem.solutionSet ⊆ neighborhood →
    localParity problem neighborhood = localParity problem Set.univ
  localParity_eq_of_common_isolating_homotopy :
    ∀ (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem ι) neighborhood,
      IsContinuousBoxComplementarityFamily ι family →
      (∀ parameter, (family parameter).IsIsolating neighborhood) →
      localParity (family unitIntervalZero) neighborhood =
        localParity (family unitIntervalOne) neighborhood
  localParity_eq_card_of_finite_regular : ∀ problem neighborhood,
    problem.IsIsolating neighborhood →
    (problem.solutionsIn neighborhood).Finite →
    (∀ point ∈ problem.solutionsIn neighborhood, IsRegular problem point) →
    localParity problem neighborhood =
      ((problem.solutionsIn neighborhood).ncard : ZMod 2)

namespace ModTwoBoxComplementarityParitySpec

variable {ι}

/-- A local parity different from the global odd parity forces a solution
outside the displayed isolating neighborhood. -/
theorem exists_solution_not_mem_of_localParity_ne_one
    (spec : ModTwoBoxComplementarityParitySpec ι)
    (problem : BoxComplementarityProblem ι)
    (neighborhood : Set (UnitCube ι))
    (hisolating : problem.IsIsolating neighborhood)
    (hparity : spec.localParity problem neighborhood ≠ 1) :
    ∃ point, problem.IsSolution point ∧ point ∉ neighborhood := by
  by_contra hnone
  have hsubset : problem.solutionSet ⊆ neighborhood := by
    intro point hpoint
    by_contra houtside
    exact hnone ⟨point, hpoint, houtside⟩
  have hexcision := spec.localParity_eq_global_of_solutionSet_subset
    problem neighborhood hisolating hsubset
  rw [spec.globalParity_eq_one] at hexcision
  exact hparity hexcision

/-- A finite even collection of regular solutions in an isolating
neighborhood has zero local parity. -/
theorem localParity_eq_zero_of_finite_regular_even
    (spec : ModTwoBoxComplementarityParitySpec ι)
    (problem : BoxComplementarityProblem ι)
    (neighborhood : Set (UnitCube ι))
    (hisolating : problem.IsIsolating neighborhood)
    (hfinite : (problem.solutionsIn neighborhood).Finite)
    (hregular : ∀ point ∈ problem.solutionsIn neighborhood,
      spec.IsRegular problem point)
    (heven : Even (problem.solutionsIn neighborhood).ncard) :
    spec.localParity problem neighborhood = 0 := by
  rw [spec.localParity_eq_card_of_finite_regular problem neighborhood
    hisolating hfinite hregular]
  obtain ⟨half, hhalf⟩ := heven
  rw [hhalf, Nat.cast_add]
  change (half : ZMod 2) + half = 0
  rw [← two_mul]
  rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2, zero_mul]

/-- The generic parity consumer: an isolating neighborhood containing a
finite even collection of regular solutions cannot contain every solution. -/
theorem exists_solution_not_mem_of_finite_regular_even
    (spec : ModTwoBoxComplementarityParitySpec ι)
    (problem : BoxComplementarityProblem ι)
    (neighborhood : Set (UnitCube ι))
    (hisolating : problem.IsIsolating neighborhood)
    (hfinite : (problem.solutionsIn neighborhood).Finite)
    (hregular : ∀ point ∈ problem.solutionsIn neighborhood,
      spec.IsRegular problem point)
    (heven : Even (problem.solutionsIn neighborhood).ncard) :
    ∃ point, problem.IsSolution point ∧ point ∉ neighborhood := by
  apply spec.exists_solution_not_mem_of_localParity_ne_one problem neighborhood
    hisolating
  rw [spec.localParity_eq_zero_of_finite_regular_even problem neighborhood
    hisolating hfinite hregular heven]
  exact zero_ne_one

end ModTwoBoxComplementarityParitySpec

end Math
