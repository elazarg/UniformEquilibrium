/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Niven
import Mathlib.Tactic

/-!
# The rational three-four-fifths rotation has infinite order

The unit complex number `(3 + 4i) / 5` gives a rational plane rotation.  It
has infinite multiplicative order: finite order would make it and its
conjugate algebraic integers, hence would make their rational trace `6/5` an
integer.
-/

noncomputable section

namespace Math
namespace Topology

open scoped ComplexConjugate

/-- The unit complex multiplier encoding the rational rotation matrix with
rows `(3/5, -4/5)` and `(4/5, 3/5)`. -/
def threeFourFifthsMultiplier : ℂ :=
  (3 : ℂ) / 5 + (4 : ℂ) / 5 * Complex.I

@[simp] theorem threeFourFifthsMultiplier_re :
    threeFourFifthsMultiplier.re = 3 / 5 := by
  norm_num [threeFourFifthsMultiplier]

@[simp] theorem threeFourFifthsMultiplier_im :
    threeFourFifthsMultiplier.im = 4 / 5 := by
  norm_num [threeFourFifthsMultiplier]

@[simp] theorem threeFourFifthsMultiplier_normSq :
    Complex.normSq threeFourFifthsMultiplier = 1 := by
  norm_num [Complex.normSq, threeFourFifthsMultiplier]

@[simp] theorem threeFourFifthsMultiplier_norm :
    ‖threeFourFifthsMultiplier‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
  rw [← Complex.normSq_eq_norm_sq]
  simp

theorem threeFourFifthsMultiplier_ne_zero :
    threeFourFifthsMultiplier ≠ 0 := by
  intro hzero
  have := congrArg Complex.re hzero
  norm_num at this

@[simp] theorem threeFourFifthsMultiplier_mul_re (phase : ℂ) :
    (threeFourFifthsMultiplier * phase).re =
      (3 / 5 : ℝ) * phase.re - (4 / 5 : ℝ) * phase.im := by
  simp [Complex.mul_re]

@[simp] theorem threeFourFifthsMultiplier_mul_im (phase : ℂ) :
    (threeFourFifthsMultiplier * phase).im =
      (4 / 5 : ℝ) * phase.re + (3 / 5 : ℝ) * phase.im := by
  simp [Complex.mul_im]
  ring

/-- The rational unit multiplier is not a root of unity. -/
theorem threeFourFifthsMultiplier_not_isOfFinOrder :
    ¬IsOfFinOrder threeFourFifthsMultiplier := by
  intro hfinite
  obtain ⟨period, hperiodPos, hperiod⟩ := hfinite.exists_pow_eq_one
  have hintegral : IsIntegral ℤ threeFourFifthsMultiplier :=
    IsIntegral.of_pow hperiodPos (hperiod ▸ isIntegral_one)
  have hconjPow : conj threeFourFifthsMultiplier ^ period = 1 := by
    rw [← map_pow]
    rw [hperiod]
    simp
  have hconjIntegral : IsIntegral ℤ
      (conj threeFourFifthsMultiplier) :=
    IsIntegral.of_pow hperiodPos (hconjPow ▸ isIntegral_one)
  have htraceIntegral : IsIntegral ℤ
      (threeFourFifthsMultiplier +
        conj threeFourFifthsMultiplier) :=
    hintegral.add hconjIntegral
  have htraceRat : ∃ value : ℚ,
      threeFourFifthsMultiplier +
          conj threeFourFifthsMultiplier = value := by
    refine ⟨6 / 5, ?_⟩
    rw [Complex.add_conj]
    norm_num
  obtain ⟨integer, hinteger⟩ :=
    htraceIntegral.exists_int_iff_exists_rat.mp htraceRat
  have hreal := congrArg Complex.re hinteger
  have hintegerReal : (integer : ℝ) = 6 / 5 := by
    rw [Complex.add_conj] at hreal
    norm_num at hreal ⊢
    linarith
  have hintegerEquation : 5 * integer = 6 := by
    exact_mod_cast (show (5 : ℝ) * integer = 6 by
      rw [hintegerReal]
      norm_num)
  omega

/-- No positive power of the rational rotation fixes a nonzero phase. -/
theorem threeFourFifthsMultiplier_pow_mul_ne
    {period : ℕ} (hperiod : 0 < period) {phase : ℂ}
    (hphase : phase ≠ 0) :
    threeFourFifthsMultiplier ^ period * phase ≠ phase := by
  intro heq
  have hpower : threeFourFifthsMultiplier ^ period = 1 := by
    apply mul_right_cancel₀ hphase
    simpa using heq
  exact threeFourFifthsMultiplier_not_isOfFinOrder
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨period, hperiod, hpower⟩)

end Topology
end Math
