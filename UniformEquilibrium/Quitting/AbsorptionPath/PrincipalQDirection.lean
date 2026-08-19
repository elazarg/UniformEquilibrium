/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Principal-Q directions on active faces

This file formalizes Step 1 in the proof of Ashkenazi-Golan--Krasikov--Rainer--Solan,
*Absorption paths and equilibria in quitting games*, Theorem 5.2.

For a zero-diagonal matrix whose restriction to a nonempty finite face is a
projective `Q`-matrix, it constructs a probability vector on that face whose
matrix residual is nonnegative on the face and vanishes in at least one face
coordinate.  The proof uses the paper's inhomogeneous projective LCP with
`q i₀ = -1` and `q i = 0` elsewhere, then normalizes the non-cemetery mass.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Finset Math.LinearProgramming

/-- A probability direction on a principal face, with inward residual at
all active coordinates and tangency at at least one active coordinate. -/
structure PrincipalQDirection {ι : Type} (M : ι → ι → ℝ)
    (players : Finset ι) where
  weight : stdSimplex ℝ players
  residual_nonneg : ∀ who : players,
    0 ≤ singletonLCPResidual (principalMatrix M players) weight who
  residual_zero : ∃ who : players,
    singletonLCPResidual (principalMatrix M players) weight who = 0

private theorem sum_eq_zero_of_nonneg_of_add_eq_one
    {κ : Type} [Fintype κ] (c : ℝ) (z : κ → ℝ)
    (hz : ∀ i, 0 ≤ z i) (htotal : c + ∑ i, z i = 1) (hc1 : c = 1) :
    ∀ i, z i = 0 := by
  have hsum : ∑ i, z i = 0 := by linarith
  intro i
  have hle : z i ≤ ∑ j, z j :=
    Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  linarith [hz i]

private theorem projective_cemetery_lt_one
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : κ → κ → ℝ) (i0 : κ)
    (solution : ProjectiveLCPSolution M (fun i => if i = i0 then -1 else 0)) :
    solution.cemetery < 1 := by
  have hsum : 0 ≤ ∑ i, solution.singleton i :=
    Finset.sum_nonneg fun i _ => solution.singleton_nonneg i
  have hle : solution.cemetery ≤ 1 := by linarith [solution.total]
  apply lt_of_le_of_ne hle
  intro heq
  have hallzero : ∀ i, solution.singleton i = 0 :=
    sum_eq_zero_of_nonneg_of_add_eq_one solution.cemetery solution.singleton
      solution.singleton_nonneg solution.total heq
  have hres := solution.residual_nonneg i0
  simp [heq, hallzero] at hres
  linarith

private def normalizeProjectiveSingleton
    {κ : Type} [Fintype κ]
    {M : κ → κ → ℝ} {q : κ → ℝ}
    (solution : ProjectiveLCPSolution M q)
    (hc : solution.cemetery < 1) : stdSimplex ℝ κ where
  val := fun i => solution.singleton i / (1 - solution.cemetery)
  property := by
    constructor
    · intro i
      exact div_nonneg (solution.singleton_nonneg i) (sub_nonneg.mpr hc.le)
    · rw [← Finset.sum_div]
      have hden : 1 - solution.cemetery ≠ 0 := ne_of_gt (sub_pos.mpr hc)
      apply (div_eq_iff hden).2
      linarith [solution.total]

private theorem normalizeProjectiveSingleton_residual
    {κ : Type} [Fintype κ]
    {M : κ → κ → ℝ} {q : κ → ℝ}
    (solution : ProjectiveLCPSolution M q)
    (hc : solution.cemetery < 1) (who : κ) :
    singletonLCPResidual M (normalizeProjectiveSingleton solution hc) who =
      (∑ owner, solution.singleton owner * M who owner) /
        (1 - solution.cemetery) := by
  change (∑ owner, (solution.singleton owner / (1 - solution.cemetery)) *
      M who owner) = _
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro owner _
  ring

private theorem exists_positive_singleton
    {κ : Type} [Fintype κ]
    {M : κ → κ → ℝ} {q : κ → ℝ}
    (solution : ProjectiveLCPSolution M q)
    (hc : solution.cemetery < 1) :
    ∃ i, 0 < solution.singleton i := by
  by_contra hnone
  have hzero : ∀ i, solution.singleton i = 0 := by
    intro i
    have hnonpos : solution.singleton i ≤ 0 := le_of_not_gt fun hpos =>
      hnone ⟨i, hpos⟩
    exact le_antisymm hnonpos (solution.singleton_nonneg i)
  have : solution.cemetery = 1 := by
    simpa [hzero] using solution.total
  linarith

private theorem principalMatrix_diagonal
    {ι : Type} (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (players : Finset ι) (who : players) :
    principalMatrix M players who who = 0 := hdiag who.1

/-- **AKRS Theorem 5.2, Step 1.** Every nonempty projective-Q principal face
of a zero-diagonal matrix has a simplex direction with nonnegative residual
on the face and at least one tight residual coordinate. -/
theorem exists_principalQDirection
    {ι : Type} (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (players : Finset ι) (hplayers : players.Nonempty)
    (hQ : IsProjectiveQMatrix (principalMatrix M players)) :
    Nonempty (PrincipalQDirection M players) := by
  classical
  let i0 : players := ⟨hplayers.choose, hplayers.choose_spec⟩
  let q : players → ℝ := fun i => if i = i0 then -1 else 0
  obtain ⟨solution⟩ := hQ q
  have hc : solution.cemetery < 1 :=
    projective_cemetery_lt_one (principalMatrix M players) i0 solution
  let weight : stdSimplex ℝ players := normalizeProjectiveSingleton solution hc
  have hresFormula (who : players) :
      singletonLCPResidual (principalMatrix M players) weight who =
        (∑ owner, solution.singleton owner *
          principalMatrix M players who owner) / (1 - solution.cemetery) :=
    normalizeProjectiveSingleton_residual solution hc who
  have hq_nonpos (who : players) : q who ≤ 0 := by
    dsimp [q]
    split <;> norm_num
  have hresNonneg (who : players) :
      0 ≤ singletonLCPResidual (principalMatrix M players) weight who := by
    rw [hresFormula]
    apply div_nonneg
    · have hprojective := solution.residual_nonneg who
      have : solution.cemetery * q who ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos solution.cemetery_nonneg (hq_nonpos who)
      linarith
    · exact sub_nonneg.mpr hc.le
  obtain ⟨support, hsupport⟩ := exists_positive_singleton solution hc
  have hzero : ∃ who : players,
      singletonLCPResidual (principalMatrix M players) weight who = 0 := by
    by_cases hs0 : support = i0
    · by_cases hother : ∃ other : players,
          other ≠ i0 ∧ 0 < solution.singleton other
      · obtain ⟨other, hne, hotherpos⟩ := hother
        refine ⟨other, ?_⟩
        rw [hresFormula]
        have hcomp := solution.complementary other
        have hq0 : q other = 0 := by simp [q, hne]
        rw [hq0, mul_zero, zero_add] at hcomp
        have hsumzero :
            (∑ owner, solution.singleton owner *
              principalMatrix M players other owner) = 0 :=
          (mul_eq_zero.mp hcomp).resolve_left (ne_of_gt hotherpos)
        rw [hsumzero, zero_div]
      · refine ⟨i0, ?_⟩
        rw [hresFormula]
        have hallzero : ∀ other, other ≠ i0 → solution.singleton other = 0 := by
          intro other hne
          have hnotpos : ¬ 0 < solution.singleton other := fun hpos =>
            hother ⟨other, hne, hpos⟩
          exact le_antisymm (le_of_not_gt hnotpos) (solution.singleton_nonneg other)
        have hsumzero :
            (∑ owner, solution.singleton owner *
              principalMatrix M players i0 owner) = 0 := by
          rw [Finset.sum_eq_single i0]
          · simp [principalMatrix_diagonal M hdiag players i0]
          · intro other _ hne
            simp [hallzero other hne]
          · simp
        rw [hsumzero, zero_div]
    · refine ⟨support, ?_⟩
      rw [hresFormula]
      have hcomp := solution.complementary support
      have hq0 : q support = 0 := by simp [q, hs0]
      rw [hq0, mul_zero, zero_add] at hcomp
      have hsumzero :
          (∑ owner, solution.singleton owner *
            principalMatrix M players support owner) = 0 :=
        (mul_eq_zero.mp hcomp).resolve_left (ne_of_gt hsupport)
      rw [hsumzero, zero_div]
  exact ⟨⟨weight, hresNonneg, hzero⟩⟩

end GameTheory.QuittingLCPClassification
