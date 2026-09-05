/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.LinearProgramming.SingletonLCP

/-! # A two-point obstruction to homogeneous singleton-LCP infeasibility -/

noncomputable section

namespace Math.LinearProgramming

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If a simplex supported on at most two coordinates has zero residual on
both named coordinates and the homogeneous singleton LCP is infeasible, some
coordinate outside that pair has strictly negative residual. -/
theorem exists_negative_residual_outside_pair_of_noHomogeneous
    (matrix : ι → ι → ℝ) (first second : ι)
    (firstWeight secondWeight : ℝ)
    (hfirstWeight : 0 ≤ firstWeight) (hsecondWeight : 0 ≤ secondWeight)
    (hweight : firstWeight + secondWeight = 1)
    (hfirstResidual :
      matrix first first * firstWeight + matrix first second * secondWeight = 0)
    (hsecondResidual :
      matrix second first * firstWeight + matrix second second * secondWeight = 0)
    (hno : ¬SingletonLCPFeasible matrix) :
    ∃ outsider, outsider ∉ ({first, second} : Finset ι) ∧
      matrix outsider first * firstWeight +
        matrix outsider second * secondWeight < 0 := by
  by_contra hnone
  apply hno
  let weight : ι → ℝ := fun who =>
    (Pi.single first firstWeight : ι → ℝ) who +
      (Pi.single second secondWeight : ι → ℝ) who
  have hweightNonneg : ∀ who, 0 ≤ weight who := by
    intro who
    simp only [weight, Pi.single_apply]
    split_ifs <;> positivity
  have hweightSum : ∑ who, weight who = 1 := by
    simp only [weight, Finset.sum_add_distrib, Fintype.sum_pi_single']
    exact hweight
  let simplex : stdSimplex ℝ ι :=
    ⟨weight, hweightNonneg, hweightSum⟩
  have hresidual (who : ι) : singletonLCPResidual matrix simplex who =
      matrix who first * firstWeight + matrix who second * secondWeight := by
    change (∑ x, weight x * matrix who x) = _
    dsimp only [weight]
    simp_rw [add_mul]
    simp only [Finset.sum_add_distrib, Pi.single_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  refine ⟨simplex, ?_, ?_⟩
  · intro who
    rw [hresidual who]
    by_cases hwho : who ∈ ({first, second} : Finset ι)
    · simp only [mem_insert, mem_singleton] at hwho
      rcases hwho with rfl | rfl
      · simpa [mul_comm] using hfirstResidual.ge
      · simpa [mul_comm] using hsecondResidual.ge
    · have hnonneg : 0 ≤ matrix who first * firstWeight +
          matrix who second * secondWeight := by
        exact le_of_not_gt fun hnegative => hnone ⟨who, hwho, hnegative⟩
      simpa [mul_comm] using hnonneg
  · intro who
    by_cases hwhoFirst : who = first
    · subst who
      rw [hresidual first, hfirstResidual]
      simp
    by_cases hwhoSecond : who = second
    · subst who
      rw [hresidual second, hsecondResidual]
      simp
    · simp [simplex, weight, hwhoFirst, hwhoSecond]

end Math.LinearProgramming

namespace Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exhaustive sign exits for a simplex supported on at most two
coordinates. -/
inductive TwoPointMatrixExit
    (matrix : ι → ι → ℝ) (first second : ι)
    (firstWeight secondWeight : ℝ) : Prop
  | firstPositive (hcross : 0 < matrix first second)
  | firstNegative (hcross : matrix first second < 0)
  | secondPositive (hcross : 0 < matrix second first)
  | secondNegative (hcross : matrix second first < 0)
  | outsiderNegative (outsider : ι)
      (houtside : outsider ∉ ({first, second} : Finset ι))
      (hresidual : matrix outsider first * firstWeight +
        matrix outsider second * secondWeight < 0)

/-- If neither cross entry has a strict sign, homogeneous infeasibility
derives the negative removed coordinate in the zero-cross branch. -/
theorem twoPointMatrixExit_of_noHomogeneous
    (matrix : ι → ι → ℝ) (first second : ι)
    (firstWeight secondWeight : ℝ)
    (hfirstWeight : 0 ≤ firstWeight) (hsecondWeight : 0 ≤ secondWeight)
    (hweight : firstWeight + secondWeight = 1)
    (hdiag : ∀ who, matrix who who = 0)
    (hno : ¬SingletonLCPFeasible matrix) :
    TwoPointMatrixExit matrix first second firstWeight secondWeight := by
  rcases lt_trichotomy (matrix first second) 0 with hnegative | hzero | hpositive
  · exact .firstNegative hnegative
  · rcases lt_trichotomy (matrix second first) 0 with hnegative' | hzero' | hpositive'
    · exact .secondNegative hnegative'
    · obtain ⟨outsider, houtside, hresidual⟩ :=
        exists_negative_residual_outside_pair_of_noHomogeneous matrix first second
          firstWeight secondWeight hfirstWeight hsecondWeight hweight
          (by rw [hdiag first, hzero]; ring)
          (by rw [hdiag second, hzero']; ring) hno
      exact .outsiderNegative outsider houtside hresidual
    · exact .secondPositive hpositive'
  · exact .firstPositive hpositive

end Math.LinearProgramming
