/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite two-by-two dispatch for a large persistent base

This file isolates the finite normal-form algebra behind the four-player
large-base residual. A product Nash point is represented by the two Quit
rates and the two endpoint-difference rows. The theorem eliminates the full
rate continuum into a paid pure cell or one of the two strict
matching-pennies chambers with a division-free paid numerator.
-/

namespace GameTheory

noncomputable section

/-- Convert a Boolean action to its deterministic Quit rate. -/
def binaryPureRate : Bool → ℝ
  | false => 0
  | true => 1

/-- Expected Quit-minus-Continue difference for the first free player. -/
def binaryFirstDifference (alpha : Bool → ℝ) (secondRate : ℝ) : ℝ :=
  (1 - secondRate) * alpha false + secondRate * alpha true

/-- Expected Quit-minus-Continue difference for the second free player. -/
def binarySecondDifference (beta : Bool → ℝ) (firstRate : ℝ) : ℝ :=
  (1 - firstRate) * beta false + firstRate * beta true

/-- Complementarity form of product mixed Nash for a two-player binary game.
`alpha j` is the first player's Quit-minus-Continue difference against `j`,
and `beta i` is the analogous difference for the second player. -/
def IsBinaryDifferenceNash (alpha beta : Bool → ℝ)
    (firstRate secondRate : ℝ) : Prop :=
  firstRate ∈ Set.Icc (0 : ℝ) 1 ∧
    secondRate ∈ Set.Icc (0 : ℝ) 1 ∧
    (1 - firstRate) * binaryFirstDifference alpha secondRate ≤ 0 ∧
    0 ≤ firstRate * binaryFirstDifference alpha secondRate ∧
    (1 - secondRate) * binarySecondDifference beta firstRate ≤ 0 ∧
    0 ≤ secondRate * binarySecondDifference beta firstRate

/-- Pure best-response cell in endpoint-difference coordinates. -/
def IsPureBinaryDifferenceNash (alpha beta : Bool → ℝ)
    (first second : Bool) : Prop :=
  (if first then 0 ≤ alpha second else alpha second ≤ 0) ∧
    (if second then 0 ≤ beta first else beta first ≤ 0)

/-- Product expectation of a four-cell observable. -/
def binaryProductExpectation (observable : Bool → Bool → ℝ)
    (firstRate secondRate : ℝ) : ℝ :=
  (1 - firstRate) * (1 - secondRate) * observable false false +
    firstRate * (1 - secondRate) * observable true false +
    (1 - firstRate) * secondRate * observable false true +
    firstRate * secondRate * observable true true

/-- The two strict matching-pennies orientations. -/
def IsStrictMatchingPenniesOrientation (alpha beta : Bool → ℝ) : Prop :=
  (0 < alpha false ∧ alpha true < 0 ∧
      0 < beta true ∧ beta false < 0) ∨
    (0 < alpha true ∧ alpha false < 0 ∧
      0 < beta false ∧ beta true < 0)

/-- Cleared denominator for the unique interior product equilibrium. -/
def binaryClearedDenominator (alpha beta : Bool → ℝ) : ℝ :=
  (alpha false - alpha true) * (beta true - beta false)

/-- Cleared numerator of a four-cell observable at the interior equilibrium. -/
def binaryClearedObservable (alpha beta : Bool → ℝ)
    (observable : Bool → Bool → ℝ) : ℝ :=
  (-beta true * alpha true) * observable false false +
    (beta false * alpha true) * observable true false +
    (beta true * alpha false) * observable false true +
    (-beta false * alpha false) * observable true true

/-- A paid pure equilibrium cell. -/
def HasPaidPureBinaryCell (gamma : ℝ) (alpha beta : Bool → ℝ)
    (observable : Fin 2 → Bool → Bool → ℝ) : Prop :=
  ∃ first second owner,
    IsPureBinaryDifferenceNash alpha beta first second ∧
      gamma ≤ observable owner first second

/-- A strict matching-pennies cell with one paid cleared observable. -/
def HasPaidMixedBinaryCell (gamma : ℝ) (alpha beta : Bool → ℝ)
    (observable : Fin 2 → Bool → Bool → ℝ) : Prop :=
  IsStrictMatchingPenniesOrientation alpha beta ∧
    0 < binaryClearedDenominator alpha beta ∧
    ∃ owner,
      gamma * binaryClearedDenominator alpha beta ≤
        binaryClearedObservable alpha beta (observable owner)

theorem isBinaryDifferenceNash_pure_iff
    (alpha beta : Bool → ℝ) (first second : Bool) :
    IsBinaryDifferenceNash alpha beta
        (binaryPureRate first) (binaryPureRate second) ↔
      IsPureBinaryDifferenceNash alpha beta first second := by
  cases first <;> cases second <;>
    simp [IsBinaryDifferenceNash, IsPureBinaryDifferenceNash,
      binaryPureRate, binaryFirstDifference, binarySecondDifference]

/-- With no pure cell, all equality faces are excluded and exactly one strict
matching-pennies orientation remains. -/
theorem strictMatchingPenniesOrientation_of_no_pure
    (alpha beta : Bool → ℝ)
    (noPure : ¬ ∃ first second,
      IsPureBinaryDifferenceNash alpha beta first second) :
    IsStrictMatchingPenniesOrientation alpha beta := by
  have h00 : 0 < alpha false ∨ 0 < beta false := by
    by_contra h
    push Not at h
    exact noPure ⟨false, false, by
      simpa [IsPureBinaryDifferenceNash] using h⟩
  rcases h00 with ha0 | hb0
  · have hb1 : 0 < beta true := by
      by_contra h
      exact noPure ⟨true, false, by
        simp only [IsPureBinaryDifferenceNash, Bool.false_eq_true,
          if_false, if_true]
        exact ⟨ha0.le, le_of_not_gt h⟩⟩
    have ha1 : alpha true < 0 := by
      by_contra h
      exact noPure ⟨true, true, by
        simp only [IsPureBinaryDifferenceNash, if_true]
        exact ⟨le_of_not_gt h, hb1.le⟩⟩
    have hb0 : beta false < 0 := by
      by_contra h
      exact noPure ⟨false, true, by
        simp only [IsPureBinaryDifferenceNash, Bool.false_eq_true, if_false,
          if_true]
        exact ⟨ha1.le, le_of_not_gt h⟩⟩
    exact Or.inl ⟨ha0, ha1, hb1, hb0⟩
  · have ha1 : 0 < alpha true := by
      by_contra h
      exact noPure ⟨false, true, by
        simp only [IsPureBinaryDifferenceNash, Bool.false_eq_true, if_false,
          if_true]
        exact ⟨le_of_not_gt h, hb0.le⟩⟩
    have hb1 : beta true < 0 := by
      by_contra h
      exact noPure ⟨true, true, by
        simp only [IsPureBinaryDifferenceNash, if_true]
        exact ⟨ha1.le, le_of_not_gt h⟩⟩
    have ha0 : alpha false < 0 := by
      by_contra h
      exact noPure ⟨true, false, by
        simp only [IsPureBinaryDifferenceNash, Bool.false_eq_true,
          if_false, if_true]
        exact ⟨le_of_not_gt h, hb1.le⟩⟩
    exact Or.inr ⟨ha1, ha0, hb0, hb1⟩

theorem binaryClearedDenominator_pos
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    0 < binaryClearedDenominator alpha beta := by
  rcases orientation with h | h <;>
    simp only [binaryClearedDenominator] <;> nlinarith

/-- The unique rates solving the two indifference equations. -/
def binaryMixedFirstRate (beta : Bool → ℝ) : ℝ :=
  -beta false / (beta true - beta false)

def binaryMixedSecondRate (alpha : Bool → ℝ) : ℝ :=
  alpha false / (alpha false - alpha true)

theorem isBinaryDifferenceNash_mixed
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    IsBinaryDifferenceNash alpha beta
      (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha) := by
  rcases orientation with h | h
  · have halpha : 0 < alpha false - alpha true := by linarith
    have hbeta : 0 < beta true - beta false := by linarith
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact (div_nonneg (by linarith) hbeta.le)
    · apply (div_le_one hbeta).mpr
      linarith
    · exact div_nonneg h.1.le halpha.le
    · apply (div_le_one halpha).mpr
      linarith
    · rw [show binaryFirstDifference alpha (binaryMixedSecondRate alpha) = 0 by
        simp only [binaryFirstDifference, binaryMixedSecondRate]
        field_simp [ne_of_gt halpha]
        ring]
      simp
    · rw [show binaryFirstDifference alpha (binaryMixedSecondRate alpha) = 0 by
        simp only [binaryFirstDifference, binaryMixedSecondRate]
        field_simp [ne_of_gt halpha]
        ring]
      simp
    · rw [show binarySecondDifference beta (binaryMixedFirstRate beta) = 0 by
        simp only [binarySecondDifference, binaryMixedFirstRate]
        field_simp [ne_of_gt hbeta]
        ring]
      simp
    · rw [show binarySecondDifference beta (binaryMixedFirstRate beta) = 0 by
        simp only [binarySecondDifference, binaryMixedFirstRate]
        field_simp [ne_of_gt hbeta]
        ring]
      simp
  · have halpha : alpha false - alpha true < 0 := by linarith
    have hbeta : beta true - beta false < 0 := by linarith
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, hbeta.le⟩)
    · apply (div_le_one_of_neg hbeta).mpr
      linarith
    · exact div_nonneg_iff.mpr (Or.inr ⟨h.2.1.le, halpha.le⟩)
    · apply (div_le_one_of_neg halpha).mpr
      linarith
    · rw [show binaryFirstDifference alpha (binaryMixedSecondRate alpha) = 0 by
        simp only [binaryFirstDifference, binaryMixedSecondRate]
        field_simp [ne_of_lt halpha]
        ring]
      simp
    · rw [show binaryFirstDifference alpha (binaryMixedSecondRate alpha) = 0 by
        simp only [binaryFirstDifference, binaryMixedSecondRate]
        field_simp [ne_of_lt halpha]
        ring]
      simp
    · rw [show binarySecondDifference beta (binaryMixedFirstRate beta) = 0 by
        simp only [binarySecondDifference, binaryMixedFirstRate]
        field_simp [ne_of_lt hbeta]
        ring]
      simp
    · rw [show binarySecondDifference beta (binaryMixedFirstRate beta) = 0 by
        simp only [binarySecondDifference, binaryMixedFirstRate]
        field_simp [ne_of_lt hbeta]
        ring]
      simp

theorem binaryProductExpectation_mixed
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (observable : Bool → Bool → ℝ) :
    binaryProductExpectation observable
        (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha) =
      binaryClearedObservable alpha beta observable /
      binaryClearedDenominator alpha beta := by
  have hden := binaryClearedDenominator_pos orientation
  have halpha : alpha false - alpha true ≠ 0 := by
    intro hzero
    simp [binaryClearedDenominator, hzero] at hden
  have hbeta : beta true - beta false ≠ 0 := by
    intro hzero
    simp [binaryClearedDenominator, hzero] at hden
  simp only [binaryProductExpectation, binaryMixedFirstRate,
    binaryMixedSecondRate, binaryClearedObservable,
    binaryClearedDenominator]
  field_simp [halpha, hbeta]
  ring

/-- **Finite large-base Nash dispatch.** A uniform positive lower bound on
the maximum of two four-cell observables over the complete binary product
Nash set yields either a paid pure Nash cell or a strict matching-pennies
cell with one division-free paid numerator. -/
theorem paidPure_or_paidMixed_of_forall_binaryNash
    (gamma : ℝ) (alpha beta : Bool → ℝ)
    (observable : Fin 2 → Bool → Bool → ℝ)
    (gap : ∀ firstRate secondRate,
      IsBinaryDifferenceNash alpha beta firstRate secondRate →
        gamma ≤ max
          (binaryProductExpectation (observable 0) firstRate secondRate)
          (binaryProductExpectation (observable 1) firstRate secondRate)) :
    HasPaidPureBinaryCell gamma alpha beta observable ∨
      HasPaidMixedBinaryCell gamma alpha beta observable := by
  by_cases hpure : ∃ first second,
      IsPureBinaryDifferenceNash alpha beta first second
  · obtain ⟨first, second, hnash⟩ := hpure
    have hpaid := gap (binaryPureRate first) (binaryPureRate second)
      ((isBinaryDifferenceNash_pure_iff alpha beta first second).mpr hnash)
    have hexpect (owner : Fin 2) :
        binaryProductExpectation (observable owner)
            (binaryPureRate first) (binaryPureRate second) =
          observable owner first second := by
      cases first <;> cases second <;>
        simp [binaryProductExpectation, binaryPureRate]
    rw [hexpect 0, hexpect 1] at hpaid
    rcases (le_max_iff.mp hpaid) with hpaid | hpaid
    · exact Or.inl ⟨first, second, 0, hnash, hpaid⟩
    · exact Or.inl ⟨first, second, 1, hnash, hpaid⟩
  · right
    have orientation :=
      strictMatchingPenniesOrientation_of_no_pure alpha beta hpure
    have hden := binaryClearedDenominator_pos orientation
    have hpaid := gap (binaryMixedFirstRate beta) (binaryMixedSecondRate alpha)
      (isBinaryDifferenceNash_mixed orientation)
    rw [binaryProductExpectation_mixed orientation,
      binaryProductExpectation_mixed orientation] at hpaid
    have hcleared :
        gamma * binaryClearedDenominator alpha beta ≤
          max (binaryClearedObservable alpha beta (observable 0))
            (binaryClearedObservable alpha beta (observable 1)) := by
      rw [max_div_div_right hden.le] at hpaid
      exact (le_div_iff₀ hden).mp hpaid
    rcases (le_max_iff.mp hcleared) with hpaid | hpaid
    · exact ⟨orientation, hden, 0, hpaid⟩
    · exact ⟨orientation, hden, 1, hpaid⟩

/-! ## Same-rate deletion identities -/

/-- Cleared first-player indifference residual after changing the endpoint
difference row but retaining the original interior rate. -/
def binaryDeletedFirstResidual (alpha deletedAlpha : Bool → ℝ) : ℝ :=
  -alpha true * deletedAlpha false + alpha false * deletedAlpha true

/-- Cleared second-player indifference residual after the same deletion. -/
def binaryDeletedSecondResidual (beta deletedBeta : Bool → ℝ) : ℝ :=
  beta true * deletedBeta false - beta false * deletedBeta true

theorem binaryFirstDifference_mixed_eq_deletedResidual_div
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (deletedAlpha : Bool → ℝ) :
    binaryFirstDifference deletedAlpha (binaryMixedSecondRate alpha) =
      binaryDeletedFirstResidual alpha deletedAlpha /
        (alpha false - alpha true) := by
  have halpha : alpha false - alpha true ≠ 0 := by
    rcases orientation with h | h <;> linarith
  simp only [binaryFirstDifference, binaryMixedSecondRate,
    binaryDeletedFirstResidual]
  field_simp [halpha]
  ring

theorem binarySecondDifference_mixed_eq_deletedResidual_div
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (deletedBeta : Bool → ℝ) :
    binarySecondDifference deletedBeta (binaryMixedFirstRate beta) =
      binaryDeletedSecondResidual beta deletedBeta /
        (beta true - beta false) := by
  have hbeta : beta true - beta false ≠ 0 := by
    rcases orientation with h | h <;> linarith
  simp only [binarySecondDifference, binaryMixedFirstRate,
    binaryDeletedSecondResidual]
  field_simp [hbeta]
  ring

theorem binaryFirstDifference_mixed_eq_zero_iff_deletedResidual_eq_zero
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (deletedAlpha : Bool → ℝ) :
    binaryFirstDifference deletedAlpha (binaryMixedSecondRate alpha) = 0 ↔
      binaryDeletedFirstResidual alpha deletedAlpha = 0 := by
  rw [binaryFirstDifference_mixed_eq_deletedResidual_div orientation]
  have halpha : alpha false - alpha true ≠ 0 := by
    rcases orientation with h | h <;> linarith
  simp [halpha]

theorem binarySecondDifference_mixed_eq_zero_iff_deletedResidual_eq_zero
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (deletedBeta : Bool → ℝ) :
    binarySecondDifference deletedBeta (binaryMixedFirstRate beta) = 0 ↔
      binaryDeletedSecondResidual beta deletedBeta = 0 := by
  rw [binarySecondDifference_mixed_eq_deletedResidual_div orientation]
  have hbeta : beta true - beta false ≠ 0 := by
    rcases orientation with h | h <;> linarith
  simp [hbeta]

/-- The four cleared product weights sum to the cleared denominator. -/
theorem binaryClearedWeights_sum (alpha beta : Bool → ℝ) :
    -beta true * alpha true + beta false * alpha true +
        beta true * alpha false + -beta false * alpha false =
      binaryClearedDenominator alpha beta := by
  simp only [binaryClearedDenominator]
  ring

/-- Cleared owner Continue-minus-Quit numerator. The joint-Continue cell is
priced separately because it is the punishment-tail cell. -/
def binaryClearedOwnerFloorNumerator (alpha beta : Bool → ℝ)
    (jointContinueValue : ℝ) (continueAbsorbing : Bool → Bool → ℝ)
    (quitValue : Bool → Bool → ℝ) : ℝ :=
  (-beta true * alpha true) * jointContinueValue +
    (beta false * alpha true) * continueAbsorbing true false +
    (beta true * alpha false) * continueAbsorbing false true +
    (-beta false * alpha false) * continueAbsorbing true true -
    binaryClearedObservable alpha beta quitValue

/-- The owner numerator is the cleared observable of the exact cellwise
Continue-minus-Quit excess, with the punishment value in cell `(0,0)`. -/
theorem binaryClearedOwnerFloorNumerator_eq_clearedObservable
    (alpha beta : Bool → ℝ) (jointContinueValue : ℝ)
    (continueAbsorbing quitValue : Bool → Bool → ℝ) :
    binaryClearedOwnerFloorNumerator alpha beta jointContinueValue
        continueAbsorbing quitValue =
      binaryClearedObservable alpha beta (fun first second =>
        (if first = false ∧ second = false then jointContinueValue
          else continueAbsorbing first second) - quitValue first second) := by
  simp [binaryClearedOwnerFloorNumerator, binaryClearedObservable]
  ring

end

end GameTheory
