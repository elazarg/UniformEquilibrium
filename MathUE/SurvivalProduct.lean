/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The canonical telescoping survival product

A census of `UniformEquilibrium.ProofView.Concepts.Stochastic` found the finite product of a
per-stage "continue mass" over a window reinvented under (at least) four
names: `quittingFiniteContinueWeight` (a recursion, closed by a separate
theorem), `blockSurvival` (a direct product, entangled with one file's own
seam-price development), `quittingJointSurvivalWeight` and
`quittingSurvivalPrefix` (thin game-specific wrappers), plus a "deleted"
(opponent-restricted) sibling `quittingOpponentSurvivalWeight` and a
best-response variant `quittingFiniteFullSurvivalWeight`.  The identity
between two of these was proved twice, independently, in the same wave.

This file supplies the one canonical, dependency-free name, `survivalProduct`,
with a minimal telescoping API.  It does **not** replace or delete any of the
existing names -- each keeps its own file, its own bounds lemmas, and its own
call sites -- it only gives every one of them a common target to be proved
equal to, by a single bridging lemma living next to each original
definition.
-/

namespace Math

/-- The product of `C` over the half-open window `[start, start + fuel)`,
written as a shift by `start` over `Finset.range fuel`.  The canonical name
for what `GameTheory.quittingFiniteContinueWeight`, `GameTheory.blockSurvival`,
`GameTheory.quittingJointSurvivalWeight`, `GameTheory.quittingSurvivalPrefix`
(at `start = 0`), `GameTheory.quittingOpponentSurvivalWeight` (at the deleted
continue mass), and `GameTheory.quittingFiniteFullSurvivalWeight` (at its own
hazard) each independently reinvent -- see the bridging lemma next to each of
those definitions. -/
def survivalProduct (C : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  ∏ offset ∈ Finset.range fuel, C (start + offset)

@[simp] theorem survivalProduct_zero (C : ℕ → ℝ) (start : ℕ) :
    survivalProduct C start 0 = 1 := by
  simp [survivalProduct]

/-- Appending one more stage at the far end multiplies survival by that
stage's coefficient. -/
theorem survivalProduct_succ (C : ℕ → ℝ) (start fuel : ℕ) :
    survivalProduct C start (fuel + 1) =
      survivalProduct C start fuel * C (start + fuel) := by
  simp [survivalProduct, Finset.prod_range_succ]

/-- Survival over a concatenated window splits multiplicatively into the
survival of its two pieces: the telescoping law. -/
theorem survivalProduct_add (C : ℕ → ℝ) (start a b : ℕ) :
    survivalProduct C start (a + b) =
      survivalProduct C start a * survivalProduct C (start + a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega, survivalProduct_succ, ih,
        survivalProduct_succ, show start + a + b = start + (a + b) by omega]
      ring

/-- Survival over a window peels its first stage: the opening coefficient
times the survival of the shifted remainder. -/
theorem survivalProduct_succ_left (C : ℕ → ℝ) (start fuel : ℕ) :
    survivalProduct C start (fuel + 1) =
      C start * survivalProduct C (start + 1) fuel := by
  rw [show fuel + 1 = 1 + fuel from by omega, survivalProduct_add]
  congr 1
  simpa using survivalProduct_succ C start 0

/-- **The absorbed-mass telescope.**  Each stage's complementary coefficient,
discounted by the survival that precedes it, together exhaust the complement
of the window's survival.  No sign or size hypothesis on `C` is used. -/
theorem sum_survivalProduct_mul_one_sub (C : ℕ → ℝ) (start fuel : ℕ) :
    (∑ offset ∈ Finset.range fuel,
        survivalProduct C start offset * (1 - C (start + offset))) =
      1 - survivalProduct C start fuel := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih, survivalProduct_succ]
      ring

theorem survivalProduct_nonneg (C : ℕ → ℝ) (hC : ∀ time, 0 ≤ C time)
    (start fuel : ℕ) : 0 ≤ survivalProduct C start fuel :=
  Finset.prod_nonneg fun offset _ => hC (start + offset)

theorem survivalProduct_le_one (C : ℕ → ℝ) (hC0 : ∀ time, 0 ≤ C time)
    (hC1 : ∀ time, C time ≤ 1) (start fuel : ℕ) :
    survivalProduct C start fuel ≤ 1 :=
  Finset.prod_le_one (fun offset _ => hC0 (start + offset))
    (fun offset _ => hC1 (start + offset))

/-- Increasing finitely many factors in `[0,1]` changes their product by at
most the sum of the coordinate increases. -/
theorem prod_sub_prod_le_sum_sub_of_le
    {κ : Type} [DecidableEq κ] (s : Finset κ) (first second : κ → ℝ)
    (hfirst0 : ∀ index ∈ s, 0 ≤ first index)
    (hfirst1 : ∀ index ∈ s, first index ≤ 1)
    (hsecond0 : ∀ index ∈ s, 0 ≤ second index)
    (hsecond1 : ∀ index ∈ s, second index ≤ 1)
    (hle : ∀ index ∈ s, first index ≤ second index) :
    (∏ index ∈ s, second index) - (∏ index ∈ s, first index) ≤
      ∑ index ∈ s, (second index - first index) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons index s hindex ih =>
      rw [Finset.prod_cons, Finset.prod_cons, Finset.sum_cons]
      have hfirst0s : ∀ other ∈ s, 0 ≤ first other :=
        fun other hother => hfirst0 other (Finset.mem_cons_of_mem hother)
      have hfirst1s : ∀ other ∈ s, first other ≤ 1 :=
        fun other hother => hfirst1 other (Finset.mem_cons_of_mem hother)
      have hsecond0s : ∀ other ∈ s, 0 ≤ second other :=
        fun other hother => hsecond0 other (Finset.mem_cons_of_mem hother)
      have hsecond1s : ∀ other ∈ s, second other ≤ 1 :=
        fun other hother => hsecond1 other (Finset.mem_cons_of_mem hother)
      have hles : ∀ other ∈ s, first other ≤ second other :=
        fun other hother => hle other (Finset.mem_cons_of_mem hother)
      have hih := ih hfirst0s hfirst1s hsecond0s hsecond1s hles
      have hprodSecond0 : 0 ≤ ∏ other ∈ s, second other :=
        Finset.prod_nonneg hsecond0s
      have hprodSecond1 : (∏ other ∈ s, second other) ≤ 1 :=
        Finset.prod_le_one hsecond0s hsecond1s
      have hprodLe : (∏ other ∈ s, first other) ≤
          ∏ other ∈ s, second other :=
        Finset.prod_le_prod hfirst0s hles
      have hcoordinate0 : 0 ≤ second index - first index :=
        sub_nonneg.mpr (hle index (Finset.mem_cons_self index s))
      have hfirstIndex1 := hfirst1 index (Finset.mem_cons_self index s)
      have hleft : (second index - first index) *
          (∏ other ∈ s, second other) ≤ second index - first index :=
        mul_le_of_le_one_right hcoordinate0 hprodSecond1
      have hright : first index *
          ((∏ other ∈ s, second other) - ∏ other ∈ s, first other) ≤
          (∏ other ∈ s, second other) - ∏ other ∈ s, first other :=
        mul_le_of_le_one_left (sub_nonneg.mpr hprodLe) hfirstIndex1
      nlinarith

end Math
