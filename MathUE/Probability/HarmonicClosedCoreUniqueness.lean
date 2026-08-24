/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicRecurrentCoreBound

/-!
# Uniqueness of bounded backward-harmonic extensions from a closed core

A closed core which is reached with a uniform positive probability in one fixed block determines
every bounded backward-harmonic orbit on the whole finite state space.  The proof is genuinely
coupled: the killed kernel contracts the probability of remaining outside the core geometrically.

This transports arbitrary recurrent phase data through the transient region.  It does not itself
give Simon's sharp bound on the total expected absolute variation of that extension.
-/

namespace Math.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Uniform one-block core reach gives a pointwise substochastic contraction of the off-core
indicator. -/
theorem expect_iter_transientCharge_le_mul
    {kernel : Omega → PMF Omega} {core : Set Omega}
    (closed : IsClosedCore kernel core) {block : ℕ} {δ : ℝ}
    (reach : HasUniformCoreReach kernel core block δ) (source : Omega) :
    expect (Math.PMFIter.iter kernel block source) (transientCharge core) ≤
      (1 - δ) * transientCharge core source := by
  by_cases source_core : source ∈ core
  · rw [transientCharge_of_mem source_core, mul_zero]
    have hpad := expect_iter_add_transientCharge_le closed 0 block source
    simpa [Math.PMFIter.iter_zero, transientCharge_of_mem source_core] using hpad
  · rw [transientCharge_of_not_mem source_core, mul_one]
    exact reach source

/-- The probability of avoiding the core for repeated reach blocks decays geometrically. -/
theorem expect_iter_mul_transientCharge_le_pow
    {kernel : Omega → PMF Omega} {core : Set Omega}
    (closed : IsClosedCore kernel core) {block : ℕ} {δ : ℝ}
    (delta_le_one : δ ≤ 1)
    (reach : HasUniformCoreReach kernel core block δ)
    (rounds : ℕ) (source : Omega) :
    expect (Math.PMFIter.iter kernel (rounds * block) source) (transientCharge core) ≤
      (1 - δ) ^ rounds * transientCharge core source := by
  induction rounds with
  | zero => simp [Math.PMFIter.iter_zero]
  | succ rounds ih =>
      rw [Nat.succ_mul, Math.PMFIter.iter_add, expect_bind]
      calc
        expect (Math.PMFIter.iter kernel (rounds * block) source)
            (fun state ↦ expect (Math.PMFIter.iter kernel block state)
              (transientCharge core)) ≤
            expect (Math.PMFIter.iter kernel (rounds * block) source)
              (fun state ↦ (1 - δ) * transientCharge core state) := by
          apply expect_mono
          exact expect_iter_transientCharge_le_mul closed reach
        _ = (1 - δ) * expect (Math.PMFIter.iter kernel (rounds * block) source)
              (transientCharge core) :=
          expect_const_mul _ _ _
        _ ≤ (1 - δ) * ((1 - δ) ^ rounds * transientCharge core source) :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr delta_le_one)
        _ = (1 - δ) ^ (rounds + 1) * transientCharge core source := by
          rw [pow_succ]
          ring

/-- Two unit-interval backward-harmonic orbits agreeing on a uniformly reachable closed core
agree everywhere.  Thus transient values contain no independent bounded backward-orbit data. -/
theorem backwardHarmonic_eq_of_eq_on_closedCore
    (kernel : Omega → PMF Omega) (core : Set Omega)
    (closed : IsClosedCore kernel core)
    {block : ℕ} {δ : ℝ} (delta_pos : 0 < δ) (delta_le_one : δ ≤ 1)
    (reach : HasUniformCoreReach kernel core block δ)
    (first second : Omega → ℕ → ℝ)
    (first_harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel first)
    (second_harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel second)
    (agree_core : ∀ {state}, state ∈ core → ∀ time, first state time = second state time)
    (state : Omega) (time : ℕ) :
    first state time = second state time := by
  have difference_iter (rounds : ℕ) :
      first state time - second state time =
        expect (Math.PMFIter.iter kernel (rounds * block) state)
          (fun successor ↦
            first successor (time + rounds * block) -
              second successor (time + rounds * block)) := by
    rw [expect_sub, ← backwardHarmonic_eq_expect_iter
      kernel first first_harmonic.2 state time (rounds * block),
      ← backwardHarmonic_eq_expect_iter
        kernel second second_harmonic.2 state time (rounds * block)]
  have difference_le (rounds : ℕ) :
      |first state time - second state time| ≤ (1 - δ) ^ rounds := by
    rw [difference_iter rounds]
    calc
      |expect (Math.PMFIter.iter kernel (rounds * block) state)
          (fun successor ↦ first successor (time + rounds * block) -
            second successor (time + rounds * block))| ≤
          expect (Math.PMFIter.iter kernel (rounds * block) state)
            (fun successor ↦ |first successor (time + rounds * block) -
              second successor (time + rounds * block)|) :=
        abs_expect_le_expect_abs _ _
      _ ≤ expect (Math.PMFIter.iter kernel (rounds * block) state)
            (transientCharge core) := by
        apply expect_mono
        intro successor
        by_cases successor_core : successor ∈ core
        · rw [agree_core successor_core, sub_self, abs_zero,
            transientCharge_of_mem successor_core]
        · rw [transientCharge_of_not_mem successor_core]
          rw [abs_le]
          constructor <;>
            linarith [(first_harmonic.1 successor (time + rounds * block)).1,
              (first_harmonic.1 successor (time + rounds * block)).2,
              (second_harmonic.1 successor (time + rounds * block)).1,
              (second_harmonic.1 successor (time + rounds * block)).2]
      _ ≤ (1 - δ) ^ rounds * transientCharge core state :=
        expect_iter_mul_transientCharge_le_pow closed delta_le_one reach rounds state
      _ ≤ (1 - δ) ^ rounds := by
        exact mul_le_of_le_one_right (pow_nonneg (sub_nonneg.mpr delta_le_one) rounds)
          (transientCharge_le_one core state)
  have hzero : |first state time - second state time| ≤ 0 := by
    apply ge_of_tendsto'
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (sub_nonneg.mpr delta_le_one) (by linarith))
    exact difference_le
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

/-- Source-native finite-kernel form: agreement on the union of all recurrent communication
classes determines a bounded backward-harmonic orbit everywhere. -/
theorem backwardHarmonic_eq_of_eq_on_finiteRecurrentCore
    [DecidableEq Omega] [Nonempty Omega]
    (kernel : Omega → PMF Omega) (first second : Omega → ℕ → ℝ)
    (first_harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel first)
    (second_harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel second)
    (agree_core : ∀ {state}, state ∈ finiteRecurrentCore kernel →
      ∀ time, first state time = second state time) :
    first = second := by
  obtain ⟨certificate⟩ := exists_closedCoreTransienceCertificate
    kernel (finiteRecurrentCore kernel : Set Omega)
      (finiteRecurrentCore_closed kernel)
      (exists_reachable_finiteRecurrentCore kernel)
  funext state time
  exact backwardHarmonic_eq_of_eq_on_closedCore
    kernel (finiteRecurrentCore kernel : Set Omega)
    (finiteRecurrentCore_closed kernel)
    certificate.minorization_pos certificate.minorization_le_one
    certificate.uniform_reach first second first_harmonic second_harmonic
    agree_core state time

end

end Math.Probability
