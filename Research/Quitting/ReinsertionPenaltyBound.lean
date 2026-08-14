/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.CertifiedBoundaryReinsertion

/-!
# The depth-free mismatch penalty of certified reinsertion

Question 131's quantitative core: if the certified terminal payoff is off by
`error` in the deviator's coordinate, then reinsertion exploitability exceeds
the propagated dynamic debt by at most

  `(χ - P) * error⁺ + P * (-error)⁺ ≤ |error|`,

where `P` is full prescribed survival and `χ ≥ P` is opponent-only survival.
There is no dependence on the prefix length.  This closes the scalar
consumer: any certified terminal tail splices into any exact prefix with
total exploitability `debt + mismatch`, independent of depth.
-/


noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A maximum moves by at most the positive part of the perturbation of one
branch. -/
private theorem max_add_le_max_add_posPart (a b x : ℝ) :
    max a (b + x) ≤ max a b + max x 0 :=
  max_le (le_add_of_le_of_nonneg (le_max_left a b) (le_max_right x 0))
    (add_le_add (le_max_right a b) (le_max_left x 0))

/-- **Depth-free penalty bound.**  Reinsertion exploitability at boundary
mismatch `error` exceeds the exact propagated debt by at most
`(χ - P) * error⁺ + P * (-error)⁺`. -/
theorem quittingFiniteRelativeBoundaryExploitability_le_debt_add_penalty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (terminalDebt error : ℝ) (start fuel : ℕ) :
    quittingFiniteRelativeBoundaryExploitability reward roots who prescribed
        terminalDebt error start fuel ≤
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel +
        ((quittingOpponentSurvivalWeight roots who start fuel -
            quittingFiniteFullSurvivalWeight roots who
              (fun time => roots time who) start fuel) * max error 0 +
          quittingFiniteFullSurvivalWeight roots who
              (fun time => roots time who) start fuel * max (-error) 0) := by
  set χ := quittingOpponentSurvivalWeight roots who start fuel with hχ
  set P := quittingFiniteFullSurvivalWeight roots who
    (fun time => roots time who) start fuel with hP
  have hPχ : P ≤ χ := by
    rw [hP, hχ]
    exact quittingFiniteFullSurvivalWeight_le_opponentSurvivalWeight
      roots who (fun time => roots time who) start fuel
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact quittingFiniteFullSurvivalWeight_nonneg
      roots who (fun time => roots time who) start fuel
  have hχ0 : 0 ≤ χ := le_trans hP0 hPχ
  have hPe : P * error = P * max error 0 - P * max (-error) 0 := by
    rcases le_total error 0 with he | he
    · rw [max_eq_right he, max_eq_left (by linarith)]
      ring_nf
    · rw [max_eq_left he, max_eq_right (by linarith)]
      ring
  cases fuel with
  | zero =>
      rw [quittingFiniteRelativeBoundaryExploitability_zeroFuel]
      simp only [quittingFiniteDynamicDebt_zero]
      have hterm1 : 0 ≤ (χ - P) * max error 0 :=
        mul_nonneg (by linarith) (le_max_right error 0)
      have hterm2 : 0 ≤ P * max (-error) 0 :=
        mul_nonneg hP0 (le_max_right (-error) 0)
      linarith
  | succ fuel =>
      have hsucc := quittingFiniteRelativeBoundaryExploitability_succ_eq
        reward roots who prescribed hprescribed terminalDebt error start fuel
      have hzero := quittingFiniteRelativeBoundaryExploitability_succ_eq
        reward roots who prescribed hprescribed terminalDebt 0 start fuel
      have hdebt := quittingFiniteRelativeBoundaryExploitability_zero
        reward roots who prescribed hprescribed terminalDebt start (fuel + 1)
      rw [hzero] at hdebt
      simp only [mul_zero, add_zero] at hdebt
      rw [hsucc, ← hχ, ← hP]
      rw [← hdebt]
      have hmax := max_add_le_max_add_posPart
        (quittingFiniteEarlyBestResponseValue reward roots who start fuel)
        (quittingFiniteContinueToBoundaryValue reward roots who
          (prescribed (start + (fuel + 1)) + terminalDebt) start (fuel + 1))
        (χ * error)
      have hχe : max (χ * error) 0 = χ * max error 0 := by
        rcases le_total error 0 with he | he
        · rw [max_eq_right he, max_eq_right
            (mul_nonpos_of_nonneg_of_nonpos hχ0 he), mul_zero]
        · rw [max_eq_left he, max_eq_left (mul_nonneg hχ0 he)]
      rw [hχe] at hmax
      have hexpand : χ * max error 0 - P * error =
          (χ - P) * max error 0 + P * max (-error) 0 := by
        rw [hPe]
        ring
      linarith

/-- The mismatch penalty is depth-free and at most the mismatch itself. -/
theorem quittingFiniteRelativeBoundaryExploitability_le_debt_add_abs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (terminalDebt error : ℝ) (start fuel : ℕ) :
    quittingFiniteRelativeBoundaryExploitability reward roots who prescribed
        terminalDebt error start fuel ≤
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel + |error| := by
  set χ := quittingOpponentSurvivalWeight roots who start fuel with hχ
  set P := quittingFiniteFullSurvivalWeight roots who
    (fun time => roots time who) start fuel with hP
  have hPχ : P ≤ χ := by
    rw [hP, hχ]
    exact quittingFiniteFullSurvivalWeight_le_opponentSurvivalWeight
      roots who (fun time => roots time who) start fuel
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact quittingFiniteFullSurvivalWeight_nonneg
      roots who (fun time => roots time who) start fuel
  have hχ1 : χ ≤ 1 := by
    rw [hχ]
    exact quittingOpponentSurvivalWeight_le_one roots who start fuel
  refine (quittingFiniteRelativeBoundaryExploitability_le_debt_add_penalty
    reward roots who prescribed hprescribed terminalDebt error start
      fuel).trans ?_
  rw [← hχ, ← hP]
  have hpenalty : (χ - P) * max error 0 + P * max (-error) 0 ≤ |error| := by
    rcases le_total error 0 with he | he
    · rw [max_eq_right he, max_eq_left (by linarith), abs_of_nonpos he]
      nlinarith
    · rw [max_eq_left he, max_eq_right (by linarith), abs_of_nonneg he]
      nlinarith
  linarith


end GameTheory
