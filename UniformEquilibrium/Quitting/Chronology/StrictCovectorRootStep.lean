/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Chronology.StrictCovectorCharge
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockTangentObstruction

/-!
# One-row strict-covector delivery

A normalized singleton separator gives a literal product root a positive
Bellman drift once its quadratic collision remainder is within the separator
margin.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Raw Quit rates normalized by their positive total mass. -/
def quittingNormalizedQuitRates (root : ι → PMF Bool)
    (_hpositive : 0 < ∑ owner, quittingRootQuitRates root owner) : ι → ℝ :=
  fun owner ↦ quittingRootQuitRates root owner /
    ∑ player, quittingRootQuitRates root player

omit [DecidableEq ι] in
theorem quittingNormalizedQuitRates_nonneg (root : ι → PMF Bool)
    (hpositive : 0 < ∑ owner, quittingRootQuitRates root owner) (owner : ι) :
    0 ≤ quittingNormalizedQuitRates root hpositive owner := by
  exact div_nonneg ENNReal.toReal_nonneg hpositive.le

omit [DecidableEq ι] in
theorem sum_quittingNormalizedQuitRates (root : ι → PMF Bool)
    (hpositive : 0 < ∑ owner, quittingRootQuitRates root owner) :
    ∑ owner, quittingNormalizedQuitRates root hpositive owner = 1 := by
  unfold quittingNormalizedQuitRates
  rw [← Finset.sum_div]
  exact div_self hpositive.ne'

omit [DecidableEq ι] in
theorem quitRate_eq_sum_mul_normalizedQuitRate (root : ι → PMF Bool)
    (hpositive : 0 < ∑ owner, quittingRootQuitRates root owner) (owner : ι) :
    quittingRootQuitRates root owner =
      (∑ player, quittingRootQuitRates root player) *
        quittingNormalizedQuitRates root hpositive owner := by
  rw [quittingNormalizedQuitRates, mul_div_cancel₀]
  exact hpositive.ne'

omit [DecidableEq ι] in
/-- A columnwise separator remains strict on every probability mixture whose
positive support uses only separated columns. -/
theorem strictSeparator_le_singletonMixturePairing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary covector : Payoff ι) (weights : ι → ℝ) {κ : ℝ}
    (hweights : ∀ owner, 0 ≤ weights owner)
    (hmass : (∑ owner, weights owner) = 1)
    (hcolumn : ∀ owner, 0 < weights owner →
      κ ≤ quittingCovectorPairing covector (fun who ↦
        boundary who - reward (quittingSingletonTerminal owner) who)) :
    κ ≤ quittingCovectorPairing covector (fun who ↦
      boundary who - ∑ owner, weights owner *
        reward (quittingSingletonTerminal owner) who) := by
  have hweighted : κ * (∑ owner, weights owner) ≤
      ∑ owner, weights owner * quittingCovectorPairing covector (fun who ↦
        boundary who - reward (quittingSingletonTerminal owner) who) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro owner _
    by_cases hzero : weights owner = 0
    · simp [hzero]
    · simpa only [mul_comm κ] using mul_le_mul_of_nonneg_left
        (hcolumn owner (lt_of_le_of_ne (hweights owner) (Ne.symm hzero)))
          (hweights owner)
  rw [hmass, mul_one] at hweighted
  calc
    κ ≤ ∑ owner, weights owner * quittingCovectorPairing covector (fun who ↦
        boundary who - reward (quittingSingletonTerminal owner) who) := hweighted
    _ = quittingCovectorPairing covector (fun who ↦
        boundary who - ∑ owner, weights owner *
          reward (quittingSingletonTerminal owner) who) := by
      unfold quittingCovectorPairing
      simp only
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro who _
      rw [mul_sub, Finset.mul_sum]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
      ring_nf

/-- The exact product-law linearization bounds the error between one Bellman
drift and any explicitly normalized singleton drift. -/
theorem abs_bellmanDrift_sub_normalizedSingletonDrift_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current tail boundary mixture : Payoff ι) (root : ι → PMF Bool)
    (weights : ι → ℝ) {M ε : ℝ}
    (hbellman : current = quittingRootSuccessorPayoff reward tail root)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htail : ∀ who, |tail who| ≤ M)
    (hclose : ∀ who, |tail who - boundary who| ≤ ε)
    (hrate : ∀ owner, quittingRootQuitRates root owner =
      (∑ player, quittingRootQuitRates root player) * weights owner)
    (hmixture : ∀ who, mixture who = boundary who -
      ∑ owner, weights owner *
        reward (quittingSingletonTerminal owner) who)
    (who : ι) :
    |(tail who - current who) -
        (∑ owner, quittingRootQuitRates root owner) * mixture who| ≤
      (∑ owner, quittingRootQuitRates root owner) *
        (ε + 2 * M * ∑ owner, quittingRootQuitRates root owner) := by
  let total := ∑ owner, quittingRootQuitRates root owner
  let linearization := ∑ owner, quittingRootQuitRates root owner *
    (reward (quittingSingletonTerminal owner) who - tail who)
  have htotal : 0 ≤ total :=
    Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  have hrate' : ∀ owner, quittingRootQuitRates root owner =
      total * weights owner := by
    intro owner
    simpa only [total] using hrate owner
  have hmass : ∑ owner, total * weights owner = total := by
    calc
      (∑ owner, total * weights owner) =
          ∑ owner, quittingRootQuitRates root owner := by
        apply Finset.sum_congr rfl
        intro owner _
        exact (hrate' owner).symm
      _ = total := rfl
  have hlinear :=
    abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le
      reward tail root who hreward (htail who)
  have heq : (tail who - current who) - total * mixture who =
      -(quittingRootSuccessorPayoff reward tail root who - tail who -
          linearization) + total * (tail who - boundary who) := by
    rw [hbellman, hmixture]
    unfold linearization
    simp_rw [hrate', mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hmass]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  rw [heq]
  calc
    |-(quittingRootSuccessorPayoff reward tail root who - tail who -
          linearization) + total * (tail who - boundary who)| ≤
        |quittingRootSuccessorPayoff reward tail root who - tail who -
          linearization| + total * |tail who - boundary who| := by
      calc
        |-(quittingRootSuccessorPayoff reward tail root who - tail who -
              linearization) + total * (tail who - boundary who)| ≤
            |-(quittingRootSuccessorPayoff reward tail root who - tail who -
              linearization)| + |total * (tail who - boundary who)| :=
          abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_mul, abs_of_nonneg htotal]
    _ ≤ 2 * M * total ^ 2 + total * ε := by
      exact add_le_add
        (by simpa only [linearization, total] using hlinear)
        (mul_le_mul_of_nonneg_left (hclose who) htotal)
    _ = total * (ε + 2 * M * total) := by ring

omit [DecidableEq ι] in
/-- A coordinatewise first-order approximation transfers a strict separator
to an exact one-row absorption-charge inequality. -/
theorem strictCovector_mul_absorptionMass_le_drift_of_approximation
    (root : ι → PMF Bool) (drift mixture covector : Payoff ι)
    {κ error : ℝ}
    (hκ : 0 < κ)
    (hseparator : κ ≤ quittingCovectorPairing covector mixture)
    (happrox : ∀ who,
      |drift who -
        (∑ owner, quittingRootQuitRates root owner) * mixture who| ≤
          (∑ owner, quittingRootQuitRates root owner) * error)
    (hmargin : (∑ who, |covector who|) * error ≤ κ / 2) :
    κ / 2 * quittingRootAbsorptionMass root ≤
      quittingCovectorPairing covector drift := by
  let total := ∑ owner, quittingRootQuitRates root owner
  let remainder : Payoff ι := fun who ↦ drift who - total * mixture who
  have htotal : 0 ≤ total := Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  have hremainder : |quittingCovectorPairing covector remainder| ≤
      total * (κ / 2) := by
    calc
      |quittingCovectorPairing covector remainder| ≤
          (∑ who, |covector who|) * (total * error) := by
        apply abs_quittingCovectorPairing_le
        intro who
        simpa only [remainder, total] using happrox who
      _ = total * ((∑ who, |covector who|) * error) := by ring
      _ ≤ total * (κ / 2) :=
        mul_le_mul_of_nonneg_left hmargin htotal
  have hdecompose : quittingCovectorPairing covector drift =
      total * quittingCovectorPairing covector mixture +
        quittingCovectorPairing covector remainder := by
    unfold quittingCovectorPairing remainder
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro who _
    ring
  have habsorption := quittingRootAbsorptionMass_le_sum_quitRates root
  change quittingRootAbsorptionMass root ≤ total at habsorption
  rw [hdecompose]
  have hremainderLower : -(total * (κ / 2)) ≤
      quittingCovectorPairing covector remainder := neg_le_of_abs_le hremainder
  have hcharge : κ / 2 * quittingRootAbsorptionMass root ≤
      κ / 2 * total := mul_le_mul_of_nonneg_left habsorption (by linarith)
  have hmain : total * κ ≤
      total * quittingCovectorPairing covector mixture :=
    mul_le_mul_of_nonneg_left hseparator htotal
  nlinarith

/-- Literal product-root version of the strict-covector step: the only error
term is the exact quadratic simultaneous-quitting remainder. -/
theorem strictCovector_mul_absorptionMass_le_bellmanDrift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current tail boundary mixture covector : Payoff ι)
    (root : ι → PMF Bool) (weights : ι → ℝ) {κ M ε : ℝ}
    (hbellman : current = quittingRootSuccessorPayoff reward tail root)
    (hκ : 0 < κ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htail : ∀ who, |tail who| ≤ M)
    (hclose : ∀ who, |tail who - boundary who| ≤ ε)
    (hrate : ∀ owner, quittingRootQuitRates root owner =
      (∑ player, quittingRootQuitRates root player) * weights owner)
    (hmixture : ∀ who, mixture who = boundary who -
      ∑ owner, weights owner *
        reward (quittingSingletonTerminal owner) who)
    (hseparator : κ ≤ quittingCovectorPairing covector mixture)
    (hmargin : (∑ who, |covector who|) *
      (ε + 2 * M * ∑ owner, quittingRootQuitRates root owner) ≤ κ / 2) :
    κ / 2 * quittingRootAbsorptionMass root ≤
      quittingCovectorPairing covector (tail - current) := by
  apply strictCovector_mul_absorptionMass_le_drift_of_approximation
    root (tail - current) mixture covector hκ hseparator
  · intro who
    simpa only [Pi.sub_apply] using
      abs_bellmanDrift_sub_normalizedSingletonDrift_le
        reward current tail boundary mixture root weights hbellman hreward
          htail hclose hrate hmixture who
  · exact hmargin

end GameTheory
