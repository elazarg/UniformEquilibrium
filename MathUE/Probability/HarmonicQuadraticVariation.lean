/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Chebyshev
import MathUE.Probability.HarmonicPeriodicCore

/-!
# Quadratic variation of a finite backward-harmonic orbit

The absolute-variation cardinality bound cannot be obtained by assigning an independent renewal
budget to each state.  The squared increments do have a completely coupled account: their
expected sum telescopes to the change in the second moment of the backward-harmonic value.
Consequently a `[0,1]`-valued orbit has total expected quadratic variation at most one.

This does not imply the horizon-free `L¹` cardinality bound.  It isolates that remaining theorem
as an `L²`-to-`L¹` conversion using the finite homogeneous transition structure.
-/

namespace Math.Probability

noncomputable section

variable {Omega : Type*} [Finite Omega]

theorem sq_expect_abs_le_expect_sq (law : PMF Omega) (f : Omega → ℝ) :
    expect law (fun state ↦ |f state|) ^ 2 ≤
      expect law (fun state ↦ f state ^ 2) := by
  let mean := expect law (fun state ↦ |f state|)
  have hnonneg : 0 ≤ expect law (fun state ↦ (|f state| - mean) ^ 2) :=
    expect_nonneg _ _ fun state => sq_nonneg _
  have hexpand : expect law (fun state ↦ (|f state| - mean) ^ 2) =
      expect law (fun state ↦ f state ^ 2) - mean ^ 2 := by
    rw [show (fun state ↦ (|f state| - mean) ^ 2) =
        fun state ↦ f state ^ 2 - 2 * mean * |f state| + mean ^ 2 by
      funext state
      calc
        (|f state| - mean) ^ 2 = |f state| ^ 2 -
            2 * mean * |f state| + mean ^ 2 := by ring
        _ = f state ^ 2 - 2 * mean * |f state| + mean ^ 2 := by rw [sq_abs]]
    rw [expect_add, expect_sub, expect_const, expect_const_mul]
    ring
  rw [hexpand] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Expected squared space-time increments through a finite horizon. -/
def finiteExpectedSpaceTimeMarkovQuadraticVariation
    (initial : Omega) (kernel : Omega → PMF Omega)
    (value : Omega → ℕ → ℝ) (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    expect (Math.PMFIter.iter kernel time initial) (fun source ↦
      expect (kernel source) (fun successor ↦
        (value successor (time + 1) - value source time) ^ 2))

theorem expect_sq_increment_eq_secondMoment_sub
    (law : PMF Omega) (kernel : Omega → PMF Omega)
    (current next : Omega → ℝ)
    (harmonic : ∀ state, current state = expect (kernel state) next) :
    expect law (fun source ↦
        expect (kernel source) (fun successor ↦
          (next successor - current source) ^ 2)) =
      expect (law.bind kernel) (fun state ↦ next state ^ 2) -
        expect law (fun state ↦ current state ^ 2) := by
  rw [expect_bind, ← expect_sub]
  apply congrArg
  funext source
  rw [show (fun successor ↦ (next successor - current source) ^ 2) =
      fun successor ↦ next successor ^ 2 -
        2 * current source * next successor + current source ^ 2 by
    funext successor
    ring]
  rw [expect_add, expect_sub, expect_const, expect_const_mul, ← harmonic source]
  ring

/-- The finite expected quadratic variation telescopes exactly between endpoint second moments. -/
theorem finiteExpectedSpaceTimeMarkovQuadraticVariation_eq
    (initial : Omega) (kernel : Omega → PMF Omega)
    (value : Omega → ℕ → ℝ)
    (harmonic : ∀ state time,
      value state time = expect (kernel state) (fun successor ↦
        value successor (time + 1)))
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovQuadraticVariation initial kernel value horizon =
      expect (Math.PMFIter.iter kernel horizon initial)
          (fun state ↦ value state horizon ^ 2) -
        value initial 0 ^ 2 := by
  induction horizon with
  | zero => simp [finiteExpectedSpaceTimeMarkovQuadraticVariation]
  | succ horizon ih =>
      rw [finiteExpectedSpaceTimeMarkovQuadraticVariation, Finset.sum_range_succ,
        ← finiteExpectedSpaceTimeMarkovQuadraticVariation, ih]
      have hstep := expect_sq_increment_eq_secondMoment_sub
        (Math.PMFIter.iter kernel horizon initial) kernel
        (fun state ↦ value state horizon)
        (fun state ↦ value state (horizon + 1))
        (fun state ↦ harmonic state horizon)
      rw [Math.PMFIter.iter_succ']
      linarith

/-- A unit-interval backward-harmonic orbit has at most one unit of expected quadratic
variation, uniformly in the horizon and independently of the number of states. -/
theorem finiteExpectedSpaceTimeMarkovQuadraticVariation_le_one
    (initial : Omega) (kernel : Omega → PMF Omega)
    (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    (harmonic : ∀ state time,
      value state time = expect (kernel state) (fun successor ↦
        value successor (time + 1)))
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovQuadraticVariation initial kernel value horizon ≤ 1 := by
  rw [finiteExpectedSpaceTimeMarkovQuadraticVariation_eq initial kernel value harmonic]
  have hterminal : expect (Math.PMFIter.iter kernel horizon initial)
      (fun state ↦ value state horizon ^ 2) ≤ 1 := by
    calc
      expect (Math.PMFIter.iter kernel horizon initial)
          (fun state ↦ value state horizon ^ 2) ≤
          expect (Math.PMFIter.iter kernel horizon initial) (fun _ ↦ (1 : ℝ)) := by
        apply expect_mono
        intro state
        nlinarith [(bounded state horizon).1, (bounded state horizon).2]
      _ = 1 := expect_const _ _
  nlinarith [sq_nonneg (value initial 0)]

/-- Finite-horizon Cauchy--Schwarz conversion from the coupled quadratic account to absolute
variation.  Its horizon factor is genuine; removing it using homogeneity and the finite transient
state structure is the remaining cardinality theorem. -/
theorem sq_finiteExpectedSpaceTimeMarkovVariation_le_mul_quadraticVariation
    (initial : Omega) (kernel : Omega → PMF Omega)
    (value : Omega → ℕ → ℝ) (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ^ 2 ≤
      (horizon : ℝ) *
        finiteExpectedSpaceTimeMarkovQuadraticVariation initial kernel value horizon := by
  letI : Fintype Omega := Fintype.ofFinite Omega
  let absoluteAt : ℕ → ℝ := fun time =>
    expect (Math.PMFIter.iter kernel time initial) (fun source ↦
      expect (kernel source) (fun successor ↦
        |value successor (time + 1) - value source time|))
  let squareAt : ℕ → ℝ := fun time =>
    expect (Math.PMFIter.iter kernel time initial) (fun source ↦
      expect (kernel source) (fun successor ↦
        (value successor (time + 1) - value source time) ^ 2))
  have htime (time : ℕ) : absoluteAt time ^ 2 ≤ squareAt time := by
    have houter := sq_expect_abs_le_expect_sq
      (Math.PMFIter.iter kernel time initial)
      (fun source ↦ expect (kernel source) (fun successor ↦
        |value successor (time + 1) - value source time|))
    have habs : (fun source ↦
        |expect (kernel source) (fun successor ↦
          |value successor (time + 1) - value source time|)|) =
        fun source ↦ expect (kernel source) (fun successor ↦
          |value successor (time + 1) - value source time|) := by
      funext source
      rw [abs_of_nonneg]
      exact expect_nonneg _ _ fun successor => abs_nonneg _
    rw [habs] at houter
    have hinner : expect (Math.PMFIter.iter kernel time initial) (fun source ↦
        expect (kernel source) (fun successor ↦
          |value successor (time + 1) - value source time|) ^ 2) ≤
        squareAt time := by
      apply expect_mono
      intro source
      exact sq_expect_abs_le_expect_sq (kernel source)
        (fun successor ↦ value successor (time + 1) - value source time)
    exact houter.trans hinner
  rw [finiteExpectedSpaceTimeMarkovVariation_eq_sum_iter_conditional]
  change (∑ time ∈ Finset.range horizon, absoluteAt time) ^ 2 ≤ _
  calc
    (∑ time ∈ Finset.range horizon, absoluteAt time) ^ 2 ≤
        (Finset.card (Finset.range horizon) : ℝ) *
          ∑ time ∈ Finset.range horizon, absoluteAt time ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (Finset.card (Finset.range horizon) : ℝ) *
          ∑ time ∈ Finset.range horizon, squareAt time := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun time _ => htime time
      · positivity
    _ = (horizon : ℝ) *
        finiteExpectedSpaceTimeMarkovQuadraticVariation initial kernel value horizon := by
      simp [finiteExpectedSpaceTimeMarkovQuadraticVariation, squareAt]

/-- The unit quadratic budget yields the universal finite-horizon estimate `L¹² ≤ horizon`. -/
theorem sq_finiteExpectedSpaceTimeMarkovVariation_le_horizon
    (initial : Omega) (kernel : Omega → PMF Omega)
    (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    (harmonic : ∀ state time,
      value state time = expect (kernel state) (fun successor ↦
        value successor (time + 1)))
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ^ 2 ≤ horizon := by
  exact (sq_finiteExpectedSpaceTimeMarkovVariation_le_mul_quadraticVariation
    initial kernel value horizon).trans (by
      have hquad := finiteExpectedSpaceTimeMarkovQuadraticVariation_le_one
        initial kernel value bounded harmonic horizon
      have hhorizon : (0 : ℝ) ≤ horizon := Nat.cast_nonneg horizon
      nlinarith)

end

end Math.Probability
