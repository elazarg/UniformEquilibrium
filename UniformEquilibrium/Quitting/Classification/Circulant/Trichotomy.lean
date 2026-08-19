/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import MathUE.CubicAnchorRoot
import MathUE.LinearProgramming.ColumnSumQ
import UniformEquilibrium.Quitting.Classification.LCP.CopositiveQBridge
import UniformEquilibrium.Quitting.Classification.LCP.CounterexampleNecessary

/-!
# Rotation-symmetric quitting tables of nonpositive surplus

Fix a finite additive group of players and a quitting reward table whose
normalized solo matrix is the circulant matrix of a margin vector `m`: the
payoff to player `i` when player `j` quits alone, measured from `i`'s own solo
payoff, depends only on the difference `j - i`.  The **surplus** is the total
margin `∑ d, m d`; the diagonal margin `m 0` vanishes because the normalized
solo matrix has zero diagonal, so the surplus is the sum of the off-diagonal
margins.

Nonpositive surplus collapses the LCP gate of
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
in two independent ways.

* Every column of a circulant matrix sums to the surplus, so a nonpositive
  surplus makes the matrix fail textbook standard `Q`
  (`Math.LinearProgramming.not_isStandardQ_rowCirculant`).
* A vanishing surplus additionally makes every row sum vanish, so the uniform
  simplex point solves the homogeneous simplex LCP
  (`Math.LinearProgramming.singletonLCPFeasible_rowCirculant`).

Both facts are about the normal-player principal matrix rather than
the full normalized matrix, and the passage is exact: a nonpositive surplus
forces some off-diagonal margin to be nonpositive, and one such margin gives
every player a distinct nonpositive comparison at every normality
layer, so the normal core is the whole player set.

The gate then runs backwards.  `StandardQMatrixSide` asserts both that the
normal-player matrix is standard `Q` and that its homogeneous branch
is absent, and either failure contradicts
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`.  So such a table
has an ordinary uniform-equilibrium payoff and lies in no counterexample
regime.

The last section reads the margins along the arithmetic progression of a
fixed step as the coefficients of an anchor cubic and applies the root and
patience facts of `MathUE/CubicAnchorRoot.lean` to it.  Positivity of the
backward partial sum at an anchor root is the constant-step, uniform-survival
reading of the sign condition that the anchored cyclic patience system imposes
on the margin from each quitter to its successor.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.LinearProgramming StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup ι]

/-! ## Circulant tables -/

/-- The normalized solo matrix of `reward` is the circulant matrix of the
margin vector `m`: the normalized payoff to a receiver when a single other
player quits depends only on their difference in the player group. -/
def HasCirculantSoloMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (m : ι → ℝ) : Prop :=
  normalizedSoloMatrix reward = rowCirculant m

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {m : ι → ℝ}

/-- The margin at the group identity vanishes, because the normalized solo
matrix has zero diagonal. -/
theorem HasCirculantSoloMatrix.margin_zero [Nonempty ι]
    (h : HasCirculantSoloMatrix reward m) : m 0 = 0 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hdiag := normalizedSoloMatrix_diagonal reward i
  rw [h] at hdiag
  simpa using hdiag

/-- Every column of the normalized solo matrix of a circulant table sums to
the surplus. -/
theorem HasCirculantSoloMatrix.column_sum
    (h : HasCirculantSoloMatrix reward m) (c : ι) :
    (∑ i, normalizedSoloMatrix reward i c) = ∑ d, m d := by
  rw [h, sum_rowCirculant_column]

/-- Every row of the normalized solo matrix of a circulant table sums to the
surplus. -/
theorem HasCirculantSoloMatrix.row_sum
    (h : HasCirculantSoloMatrix reward m) (c : ι) :
    (∑ j, normalizedSoloMatrix reward c j) = ∑ d, m d := by
  rw [h, sum_rowCirculant_row]

/-! ## The normal core of a circulant table of nonpositive surplus -/

omit [AddCommGroup ι] in
/-- A matrix with a distinct nonpositive comparison in every row keeps every
player at every normality layer. -/
theorem normalLayer_eq_univ_of_forall_exists_ne_nonpos {M : ι → ι → ℝ}
    (hrow : ∀ i : ι, ∃ j, j ≠ i ∧ M i j ≤ 0) (n : ℕ) :
    normalLayer M n = Finset.univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [normalLayer, ih]
      refine Finset.filter_eq_self.mpr fun i _ => ?_
      obtain ⟨j, hne, hentry⟩ := hrow i
      exact ⟨j, Finset.mem_univ j, hne, hentry⟩

omit [AddCommGroup ι] in
/-- A matrix with a distinct nonpositive comparison in every row has the whole
player set as its normal core. -/
theorem normalCore_eq_univ_of_forall_exists_ne_nonpos {M : ι → ι → ℝ}
    (hrow : ∀ i : ι, ∃ j, j ≠ i ∧ M i j ≤ 0) : normalCore M = Finset.univ := by
  classical
  ext i
  simp [normalCore, normalLayer_eq_univ_of_forall_exists_ne_nonpos hrow]

omit [AddCommGroup ι] in
/-- Sums over a normal core that exhausts the player set are sums
over all players. -/
theorem sum_coe_normalCore_of_eq_univ {M : ι → ι → ℝ}
    (hcore : normalCore M = Finset.univ) (g : ι → ℝ) :
    (∑ i : normalCore M, g i.1) = ∑ i : ι, g i := by
  rw [Finset.sum_coe_sort (normalCore M) g, hcore]

/-- A nonpositive surplus makes some off-diagonal margin nonpositive, and the
shifted player `d + i` is then a distinct nonpositive comparison for every
receiver `i`. -/
theorem HasCirculantSoloMatrix.exists_ne_nonpos [Nontrivial ι]
    (h : HasCirculantSoloMatrix reward m) (hσ : (∑ d, m d) ≤ 0) (i : ι) :
    ∃ j, j ≠ i ∧ normalizedSoloMatrix reward i j ≤ 0 := by
  obtain ⟨d, hd, hmd⟩ := exists_ne_zero_margin_nonpos h.margin_zero hσ
  refine ⟨d + i, fun heq => hd (by simpa using heq), ?_⟩
  rw [h]
  simpa using hmd

/-- A circulant table of nonpositive surplus has the whole player set as its
normal core. -/
theorem HasCirculantSoloMatrix.normalCore_eq_univ [Nontrivial ι]
    (h : HasCirculantSoloMatrix reward m) (hσ : (∑ d, m d) ≤ 0) :
    normalCore (normalizedSoloMatrix reward) = Finset.univ :=
  normalCore_eq_univ_of_forall_exists_ne_nonpos (h.exists_ne_nonpos hσ)

/-- The normal core of a circulant table of nonpositive surplus is
inhabited. -/
theorem HasCirculantSoloMatrix.nonempty_normalCore [Nontrivial ι]
    (h : HasCirculantSoloMatrix reward m) (hσ : (∑ d, m d) ≤ 0) :
    Nonempty (normalCore (normalizedSoloMatrix reward)) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact ⟨⟨i, by rw [h.normalCore_eq_univ hσ]; exact Finset.mem_univ i⟩⟩

/-! ## The two LCP branches -/

/-- **Nonpositive surplus fails standard `Q`.**  Every column of the
normal-player matrix of a circulant table of nonpositive surplus sums to the
surplus, so the all-ones right-hand side has no complementary solution. -/
theorem HasCirculantSoloMatrix.not_isStandardQMatrix [Nontrivial ι]
    (h : HasCirculantSoloMatrix reward m) (hσ : (∑ d, m d) ≤ 0) :
    ¬IsStandardQMatrix (normalizedNormalPlayerMatrix reward) := by
  classical
  have hcore := h.normalCore_eq_univ hσ
  haveI := h.nonempty_normalCore hσ
  rw [← isStandardQ_iff_isStandardQMatrix]
  refine not_isStandardQ_of_forall_column_sum_nonpos _ fun j => ?_
  have hsum := sum_coe_normalCore_of_eq_univ hcore
    (fun i => normalizedSoloMatrix reward i j.1)
  show (∑ i : normalCore (normalizedSoloMatrix reward),
      normalizedSoloMatrix reward i.1 j.1) ≤ 0
  rw [hsum, h.column_sum j.1]
  exact hσ

/-- **Vanishing surplus is homogeneous.**  Every row of the
normal-player matrix of a circulant table of vanishing surplus sums to zero,
so the uniform simplex point solves the homogeneous simplex LCP. -/
theorem HasCirculantSoloMatrix.hasHomogeneousSimplexSolution [Nontrivial ι]
    (h : HasCirculantSoloMatrix reward m) (hσ : (∑ d, m d) = 0) :
    HasHomogeneousSimplexSolution (normalizedNormalPlayerMatrix reward) := by
  classical
  have hcore := h.normalCore_eq_univ hσ.le
  haveI := h.nonempty_normalCore hσ.le
  refine singletonLCPFeasible_of_forall_row_sum_eq_zero _ fun i => ?_
  have hsum := sum_coe_normalCore_of_eq_univ hcore
    (fun j => normalizedSoloMatrix reward i.1 j)
  show (∑ j : normalCore (normalizedSoloMatrix reward),
      normalizedSoloMatrix reward i.1 j.1) = 0
  rw [hsum, h.row_sum i.1]
  exact hσ

/-! ## Collapsing the counterexample gate -/

/-- A circulant table of nonpositive surplus is off the standard-`Q` side of
the normal-player split, its normal-player matrix failing standard
`Q`. -/
theorem HasCirculantSoloMatrix.not_standardQMatrixSide [Nontrivial ι]
    (h : HasCirculantSoloMatrix reward m) (hσ : (∑ d, m d) ≤ 0) :
    ¬StandardQMatrixSide reward :=
  fun hside => h.not_isStandardQMatrix hσ hside.normal_standardQ

/-- A circulant table of vanishing surplus is off the standard-`Q` side of the
normal-player split, its homogeneous branch being present. -/
theorem HasCirculantSoloMatrix.not_standardQMatrixSide_of_eq_zero [Nontrivial ι]
    (h : HasCirculantSoloMatrix reward m) (hσ : (∑ d, m d) = 0) :
    ¬StandardQMatrixSide reward :=
  fun hside => hside.no_homogeneous (h.hasHomogeneousSimplexSolution hσ)

/-- **Nonpositive surplus resolves the game.**  A quitting game whose
normalized solo matrix is circulant with nonpositive surplus has an ordinary
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos
    [Nontrivial ι] (h : HasCirculantSoloMatrix reward m)
    (hσ : (∑ d, m d) ≤ 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hnot
  exact h.not_standardQMatrixSide hσ
    (standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hnot)

/-- **Vanishing surplus resolves the game through the homogeneous branch.**
The conclusion repeats the nonpositive-surplus one, but the witness supplied to
the gate is the uniform homogeneous simplex solution rather than the failure of
standard `Q`. -/
theorem exists_uniformEquilibriumPayoff_of_circulant_surplus_eq_zero
    [Nontrivial ι] (h : HasCirculantSoloMatrix reward m)
    (hσ : (∑ d, m d) = 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hnot
  exact h.not_standardQMatrixSide_of_eq_zero hσ
    (standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hnot)

/-! ## The constant-step anchor polynomial -/

/-- The constant-step anchor of a margin vector: the margins read along the
arithmetic progression `d, 2d, 3d, 4d` of step `d`, discounted by a common
phase survival factor. -/
def constantStepAnchor (margin : ι → ℝ) (d : ι) (β : ℝ) : ℝ :=
  Math.cubicAnchor (margin d) (margin (2 • d)) (margin (3 • d)) (margin (4 • d)) β

/-- The backward partial sum of the constant-step anchor: the anchor with its
first margin dropped and the remaining margins advanced one step. -/
def constantStepAnchorTail (margin : ι → ℝ) (d : ι) (β : ℝ) : ℝ :=
  Math.cubicAnchorTail (margin (2 • d)) (margin (3 • d)) (margin (4 • d)) β

omit [Fintype ι] [DecidableEq ι] in
/-- A step whose own margin is negative while the four margins along its
progression total positive has a constant-step anchor root strictly between
zero and one. -/
theorem exists_constantStepAnchor_root {margin : ι → ℝ} {d : ι}
    (hneg : margin d < 0)
    (htotal : 0 < margin d + margin (2 • d) + margin (3 • d) + margin (4 • d)) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, constantStepAnchor margin d β = 0 :=
  Math.exists_cubicAnchor_root_mem_Ioo hneg htotal

omit [Fintype ι] [DecidableEq ι] in
/-- **Automatic patience along a constant step.**  At a positive root of the
constant-step anchor of a step with negative margin, the backward partial sum
of the later margins is positive; no sign hypothesis on those later margins is
used. -/
theorem constantStepAnchorTail_pos_of_root {margin : ι → ℝ} {d : ι} {β : ℝ}
    (hβ : 0 < β) (hneg : margin d < 0)
    (hroot : constantStepAnchor margin d β = 0) :
    0 < constantStepAnchorTail margin d β :=
  Math.cubicAnchorTail_pos_of_root hβ hneg hroot

/-! ## Five players -/

section FivePlayers

/-- The four margins along the progression of a nonzero step of the
five-element cyclic group total the surplus, the margin at the identity being
zero. -/
theorem sum_stepMargins_zmod_five (margin : ZMod 5 → ℝ) (hm0 : margin 0 = 0)
    {d : ZMod 5} (hd : d ≠ 0) :
    margin d + margin (2 • d) + margin (3 • d) + margin (4 • d) =
      ∑ e, margin e := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hbij : (∑ e : ZMod 5, margin (d * e)) = ∑ e, margin e :=
    Fintype.sum_equiv (Equiv.mulLeft₀ d hd) _ _ fun _ => rfl
  have henum : (∑ e : ZMod 5, margin (d * e)) =
      margin (d * 0) + margin (d * 1) + margin (d * 2) + margin (d * 3) +
        margin (d * 4) :=
    Fin.sum_univ_five (fun e : ZMod 5 => margin (d * e))
  rw [← hbij, henum]
  simp only [mul_zero, mul_one, hm0, zero_add]
  have h2 : d * 2 = 2 • d := by rw [nsmul_eq_mul]; push_cast; ring
  have h3 : d * 3 = 3 • d := by rw [nsmul_eq_mul]; push_cast; ring
  have h4 : d * 4 = 4 • d := by rw [nsmul_eq_mul]; push_cast; ring
  rw [h2, h3, h4]

/-- **The constant-step root of a five-player circulant table.**  A positive
surplus and a nonzero step of negative margin produce a phase survival factor
strictly between zero and one at which the constant-step anchor vanishes, and
at that factor the backward partial sum of the later margins is positive. -/
theorem exists_constantStepAnchor_root_zmod_five (margin : ZMod 5 → ℝ)
    (hm0 : margin 0 = 0) {d : ZMod 5} (hd : d ≠ 0) (hneg : margin d < 0)
    (hσ : 0 < ∑ e, margin e) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1,
      constantStepAnchor margin d β = 0 ∧
        0 < constantStepAnchorTail margin d β := by
  have htotal : 0 < margin d + margin (2 • d) + margin (3 • d) + margin (4 • d) := by
    rw [sum_stepMargins_zmod_five margin hm0 hd]
    exact hσ
  obtain ⟨β, hβ, hroot⟩ := exists_constantStepAnchor_root hneg htotal
  exact ⟨β, hβ, hroot, constantStepAnchorTail_pos_of_root hβ.1 hneg hroot⟩

/-- **Nonpositive surplus, five players.**  A five-player quitting game whose
normalized solo matrix is circulant with nonpositive surplus has an ordinary
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_pentagonCirculant_surplus_nonpos
    {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}
    {margin : ZMod 5 → ℝ} (h : HasCirculantSoloMatrix reward margin)
    (hσ : (∑ d, margin d) ≤ 0) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  haveI : Nontrivial (ZMod 5) := ⟨⟨0, 1, by decide⟩⟩
  exact exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos h hσ

/-- **Vanishing surplus, five players.**  The same conclusion for vanishing
surplus, drawn from the uniform homogeneous simplex solution. -/
theorem exists_uniformEquilibriumPayoff_of_pentagonCirculant_surplus_eq_zero
    {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}
    {margin : ZMod 5 → ℝ} (h : HasCirculantSoloMatrix reward margin)
    (hσ : (∑ d, margin d) = 0) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  haveI : Nontrivial (ZMod 5) := ⟨⟨0, 1, by decide⟩⟩
  exact exists_uniformEquilibriumPayoff_of_circulant_surplus_eq_zero h hσ

end FivePlayers

end QuittingLCPClassification
end GameTheory
