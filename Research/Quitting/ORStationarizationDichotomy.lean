/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# Fixed-table stationarization dichotomy for the OR rank reduction

`QuittingORRankReduction` gives an exact one-root `1 + 3` compiler but its
conditional target reward generally changes with the hidden
spectator-only/host-only/joint law.  This file isolates that variation as a
two-dimensional affine problem.

Two payoff channels have one affine determinant.

* If the determinant is nonzero, their conditional values identify the
  hidden law.  A recurrent family on which both target table entries stay
  fixed must therefore have one common hidden law.
* If the determinant is zero, an explicit nonzero hidden-law tangent is
  invisible to both channels (unless the first channel is itself constant).

The file also computes the exceptional OR host's exact endpoint debt.  At an
interior merged marginal it is zero exactly when its active and inactive
values agree, and it quantitatively prices their difference.  Combining
this with affine separation gives a literal local alternative: hidden-law
motion changes a protected table entry or creates positive calibrated host
debt.

## Deliberate fence

A changing required table entry is not yet a Nash defect in one stationary
four-player quitting game.  Turning recurrent table mismatch into a
state-matched deviation, blocker, or punishment charge remains the global
producer.  This experiment formalizes the finite-dimensional interface that
such a producer may consume; it does not assert that the producer exists.
-/


noncomputable section

namespace Research.QuittingORStationarizationDichotomy

open scoped BigOperators

/-- Prescribed mixture, best endpoint, and endpoint debt are repeated here
so this ignored experiment compiles independently of another ignored file. -/
def prescribedBinaryValue (ownQuit : ℝ) (value : Bool → ℝ) : ℝ :=
  (1 - ownQuit) * value false + ownQuit * value true

def bestBinaryValue (value : Bool → ℝ) : ℝ :=
  max (value false) (value true)

def binaryDebt (ownQuit : ℝ) (value : Bool → ℝ) : ℝ :=
  bestBinaryValue value - prescribedBinaryValue ownQuit value

/-! ## Affine coordinates of the three hidden active causes -/

/-- Coordinates of a normalized law on spectator-only, host-only, and joint
activation.  The joint coordinate is implicit.  Positivity is deliberately
not required for the affine identities. -/
@[ext] structure HiddenCoordinates where
  spectatorOnly : ℝ
  hostOnly : ℝ

namespace HiddenCoordinates

def joint (theta : HiddenCoordinates) : ℝ :=
  1 - theta.spectatorOnly - theta.hostOnly

def asLaw (theta : HiddenCoordinates) : Fin 3 → ℝ :=
  ![theta.spectatorOnly, theta.hostOnly, theta.joint]

@[simp] theorem sum_asLaw (theta : HiddenCoordinates) :
    ∑ cause, theta.asLaw cause = 1 := by
  simp [asLaw, joint, Fin.sum_univ_succ]

end HiddenCoordinates

/-- Conditional value of one payoff channel under the hidden active law. -/
def hiddenEvaluation (theta : HiddenCoordinates)
    (feature : Fin 3 → ℝ) : ℝ :=
  theta.spectatorOnly * feature 0 +
    theta.hostOnly * feature 1 +
      theta.joint * feature 2

/-- The two affine contrasts of a feature relative to the joint cause. -/
def contrastX (feature : Fin 3 → ℝ) : ℝ :=
  feature 0 - feature 2

def contrastY (feature : Fin 3 → ℝ) : ℝ :=
  feature 1 - feature 2

/-- Oriented affine area of two payoff channels on the hidden simplex. -/
def affineFeatureDeterminant
    (first second : Fin 3 → ℝ) : ℝ :=
  contrastX first * contrastY second -
    contrastY first * contrastX second

theorem hiddenEvaluation_sub
    (theta eta : HiddenCoordinates) (feature : Fin 3 → ℝ) :
    hiddenEvaluation theta feature - hiddenEvaluation eta feature =
      contrastX feature *
          (theta.spectatorOnly - eta.spectatorOnly) +
        contrastY feature * (theta.hostOnly - eta.hostOnly) := by
  simp only [hiddenEvaluation, HiddenCoordinates.joint, contrastX, contrastY]
  ring

/-! ## Exact Cramer identities and separation -/

theorem determinant_mul_spectatorDifference
    (theta eta : HiddenCoordinates) (first second : Fin 3 → ℝ) :
    affineFeatureDeterminant first second *
        (theta.spectatorOnly - eta.spectatorOnly) =
      contrastY second *
          (hiddenEvaluation theta first - hiddenEvaluation eta first) -
        contrastY first *
          (hiddenEvaluation theta second - hiddenEvaluation eta second) := by
  rw [hiddenEvaluation_sub, hiddenEvaluation_sub]
  unfold affineFeatureDeterminant
  ring

theorem determinant_mul_hostDifference
    (theta eta : HiddenCoordinates) (first second : Fin 3 → ℝ) :
    affineFeatureDeterminant first second *
        (theta.hostOnly - eta.hostOnly) =
      contrastX first *
          (hiddenEvaluation theta second - hiddenEvaluation eta second) -
        contrastX second *
          (hiddenEvaluation theta first - hiddenEvaluation eta first) := by
  rw [hiddenEvaluation_sub, hiddenEvaluation_sub]
  unfold affineFeatureDeterminant
  ring

/-- Coordinate displacement of two normalized hidden laws. -/
def hiddenCoordinateVariation
    (theta eta : HiddenCoordinates) : ℝ :=
  |theta.spectatorOnly - eta.spectatorOnly| +
    |theta.hostOnly - eta.hostOnly|

/-- Largest table mismatch seen by two payoff channels. -/
def twoChannelMismatch (theta eta : HiddenCoordinates)
    (first second : Fin 3 → ℝ) : ℝ :=
  max
    |hiddenEvaluation theta first - hiddenEvaluation eta first|
    |hiddenEvaluation theta second - hiddenEvaluation eta second|

/-- `l1` size of the two channels' affine contrasts. -/
def featureContrastBudget (first second : Fin 3 → ℝ) : ℝ :=
  |contrastX first| + |contrastY first| +
    |contrastX second| + |contrastY second|

/-- **Quantitative table-variation charge.**  The affine determinant times
hidden-law displacement is controlled by the largest mismatch in the two
observed table entries. -/
theorem abs_determinant_mul_variation_le_contrast_mul_mismatch
    (theta eta : HiddenCoordinates) (first second : Fin 3 → ℝ) :
    |affineFeatureDeterminant first second| *
        hiddenCoordinateVariation theta eta ≤
      featureContrastBudget first second *
        twoChannelMismatch theta eta first second := by
  let firstMismatch :=
    hiddenEvaluation theta first - hiddenEvaluation eta first
  let secondMismatch :=
    hiddenEvaluation theta second - hiddenEvaluation eta second
  let mismatch := max |firstMismatch| |secondMismatch|
  have hfirst : |firstMismatch| ≤ mismatch := le_max_left _ _
  have hsecond : |secondMismatch| ≤ mismatch := le_max_right _ _
  have hx : |affineFeatureDeterminant first second| *
      |theta.spectatorOnly - eta.spectatorOnly| ≤
      (|contrastY second| + |contrastY first|) * mismatch := by
    calc
      |affineFeatureDeterminant first second| *
          |theta.spectatorOnly - eta.spectatorOnly| =
        |affineFeatureDeterminant first second *
          (theta.spectatorOnly - eta.spectatorOnly)| := by
            rw [abs_mul]
      _ = |contrastY second * firstMismatch -
          contrastY first * secondMismatch| := by
            rw [determinant_mul_spectatorDifference]
      _ ≤ |contrastY second * firstMismatch| +
          |contrastY first * secondMismatch| := abs_sub _ _
      _ = |contrastY second| * |firstMismatch| +
          |contrastY first| * |secondMismatch| := by
            rw [abs_mul, abs_mul]
      _ ≤ |contrastY second| * mismatch +
          |contrastY first| * mismatch := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hfirst (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hsecond (abs_nonneg _))
      _ = (|contrastY second| + |contrastY first|) * mismatch := by ring
  have hy : |affineFeatureDeterminant first second| *
      |theta.hostOnly - eta.hostOnly| ≤
      (|contrastX first| + |contrastX second|) * mismatch := by
    calc
      |affineFeatureDeterminant first second| *
          |theta.hostOnly - eta.hostOnly| =
        |affineFeatureDeterminant first second *
          (theta.hostOnly - eta.hostOnly)| := by
            rw [abs_mul]
      _ = |contrastX first * secondMismatch -
          contrastX second * firstMismatch| := by
            rw [determinant_mul_hostDifference]
      _ ≤ |contrastX first * secondMismatch| +
          |contrastX second * firstMismatch| := abs_sub _ _
      _ = |contrastX first| * |secondMismatch| +
          |contrastX second| * |firstMismatch| := by
            rw [abs_mul, abs_mul]
      _ ≤ |contrastX first| * mismatch +
          |contrastX second| * mismatch := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hsecond (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hfirst (abs_nonneg _))
      _ = (|contrastX first| + |contrastX second|) * mismatch := by ring
  change |affineFeatureDeterminant first second| *
      (|theta.spectatorOnly - eta.spectatorOnly| +
        |theta.hostOnly - eta.hostOnly|) ≤
    (|contrastX first| + |contrastY first| +
      |contrastX second| + |contrastY second|) *
        max |firstMismatch| |secondMismatch|
  change _ ≤ _ * mismatch
  calc
    |affineFeatureDeterminant first second| *
        (|theta.spectatorOnly - eta.spectatorOnly| +
          |theta.hostOnly - eta.hostOnly|) =
      |affineFeatureDeterminant first second| *
          |theta.spectatorOnly - eta.spectatorOnly| +
        |affineFeatureDeterminant first second| *
          |theta.hostOnly - eta.hostOnly| := by ring
    _ ≤ (|contrastY second| + |contrastY first|) * mismatch +
        (|contrastX first| + |contrastX second|) * mismatch :=
      add_le_add hx hy
    _ = (|contrastX first| + |contrastY first| +
        |contrastX second| + |contrastY second|) * mismatch := by ring

/-- In inverse form, a positive contrast budget gives an explicit lower
bound on the required table mismatch. -/
theorem determinant_div_contrast_mul_variation_le_mismatch
    (theta eta : HiddenCoordinates) (first second : Fin 3 → ℝ)
    (hbudget : 0 < featureContrastBudget first second) :
    (|affineFeatureDeterminant first second| /
        featureContrastBudget first second) *
        hiddenCoordinateVariation theta eta ≤
      twoChannelMismatch theta eta first second := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hbudget).2
  simpa [mul_comm] using
    (abs_determinant_mul_variation_le_contrast_mul_mismatch
      theta eta first second)

/-- Two non-collinear payoff channels identify the full hidden law. -/
theorem eq_of_two_fixed_evaluations
    (theta eta : HiddenCoordinates) (first second : Fin 3 → ℝ)
    (hdet : affineFeatureDeterminant first second ≠ 0)
    (hfirst : hiddenEvaluation theta first = hiddenEvaluation eta first)
    (hsecond : hiddenEvaluation theta second = hiddenEvaluation eta second) :
    theta = eta := by
  have hxProduct : affineFeatureDeterminant first second *
      (theta.spectatorOnly - eta.spectatorOnly) = 0 := by
    rw [determinant_mul_spectatorDifference, hfirst, hsecond]
    ring
  have hyProduct : affineFeatureDeterminant first second *
      (theta.hostOnly - eta.hostOnly) = 0 := by
    rw [determinant_mul_hostDifference, hfirst, hsecond]
    ring
  have hx : theta.spectatorOnly = eta.spectatorOnly := by
    have := (mul_eq_zero.mp hxProduct).resolve_left hdet
    linarith
  have hy : theta.hostOnly = eta.hostOnly := by
    have := (mul_eq_zero.mp hyProduct).resolve_left hdet
    linarith
  exact HiddenCoordinates.ext hx hy

/-- If the hidden laws differ, at least one separating table entry differs. -/
theorem evaluation_mismatch_or_evaluation_mismatch
    (theta eta : HiddenCoordinates) (first second : Fin 3 → ℝ)
    (hdet : affineFeatureDeterminant first second ≠ 0)
    (hne : theta ≠ eta) :
    hiddenEvaluation theta first ≠ hiddenEvaluation eta first ∨
      hiddenEvaluation theta second ≠ hiddenEvaluation eta second := by
  by_contra hfixed
  push Not at hfixed
  exact hne (eq_of_two_fixed_evaluations theta eta first second hdet
    hfixed.1 hfixed.2)

/-- A recurrent family with two fixed separating table entries has one common
hidden conditional law. -/
theorem recurrent_fixedTable_forces_commonHiddenLaw
    {phase : Type} (hidden : phase → HiddenCoordinates) (anchor : phase)
    (first second : Fin 3 → ℝ)
    (hdet : affineFeatureDeterminant first second ≠ 0)
    (hfirst : ∀ p, hiddenEvaluation (hidden p) first =
      hiddenEvaluation (hidden anchor) first)
    (hsecond : ∀ p, hiddenEvaluation (hidden p) second =
      hiddenEvaluation (hidden anchor) second) :
    ∀ p, hidden p = hidden anchor := by
  intro p
  exact eq_of_two_fixed_evaluations (hidden p) (hidden anchor) first second
    hdet (hfirst p) (hsecond p)

/-! ## The rank-one alternative has an explicit invisible direction -/

/-- Tangent coordinates on the normalized hidden-law simplex.  The implicit
joint displacement is `-spectatorOnly-hostOnly`. -/
@[ext] structure HiddenTangent where
  spectatorOnly : ℝ
  hostOnly : ℝ

instance : Zero HiddenTangent where
  zero := ⟨0, 0⟩

@[simp] theorem zero_spectatorOnly :
    (0 : HiddenTangent).spectatorOnly = 0 := rfl

@[simp] theorem zero_hostOnly :
    (0 : HiddenTangent).hostOnly = 0 := rfl

def tangentEvaluation (direction : HiddenTangent)
    (feature : Fin 3 → ℝ) : ℝ :=
  contrastX feature * direction.spectatorOnly +
    contrastY feature * direction.hostOnly

/-- Canonical tangent perpendicular to one payoff channel. -/
def canonicalInvisibleDirection (feature : Fin 3 → ℝ) : HiddenTangent where
  spectatorOnly := contrastY feature
  hostOnly := -contrastX feature

@[simp] theorem canonicalInvisibleDirection_first
    (feature : Fin 3 → ℝ) :
    tangentEvaluation (canonicalInvisibleDirection feature) feature = 0 := by
  simp [tangentEvaluation, canonicalInvisibleDirection]
  ring

/-- Zero determinant means the same canonical tangent is invisible to the
second channel as well. -/
theorem canonicalInvisibleDirection_second
    (first second : Fin 3 → ℝ)
    (hdet : affineFeatureDeterminant first second = 0) :
    tangentEvaluation (canonicalInvisibleDirection first) second = 0 := by
  simp only [tangentEvaluation, canonicalInvisibleDirection]
  unfold affineFeatureDeterminant at hdet
  linarith

theorem canonicalInvisibleDirection_ne_zero
    (feature : Fin 3 → ℝ)
    (hcontrast : contrastX feature ≠ 0 ∨ contrastY feature ≠ 0) :
    canonicalInvisibleDirection feature ≠ 0 := by
  intro hzero
  have hx := congrArg HiddenTangent.spectatorOnly hzero
  have hy := congrArg HiddenTangent.hostOnly hzero
  simp only [canonicalInvisibleDirection, zero_spectatorOnly, zero_hostOnly,
    neg_eq_zero] at hx hy
  rcases hcontrast with hcontrast | hcontrast
  · exact hcontrast (by linarith)
  · exact hcontrast hx

/-- Complete two-channel affine-rank dichotomy. -/
theorem separating_or_nonzeroInvisibleDirection
    (first second : Fin 3 → ℝ)
    (hcontrast : contrastX first ≠ 0 ∨ contrastY first ≠ 0) :
    affineFeatureDeterminant first second ≠ 0 ∨
      ∃ direction : HiddenTangent,
        direction ≠ 0 ∧
        tangentEvaluation direction first = 0 ∧
        tangentEvaluation direction second = 0 := by
  by_cases hdet : affineFeatureDeterminant first second = 0
  · right
    refine ⟨canonicalInvisibleDirection first,
      canonicalInvisibleDirection_ne_zero first hcontrast,
      canonicalInvisibleDirection_first first, ?_⟩
    exact canonicalInvisibleDirection_second first second hdet
  · exact Or.inl hdet

/-! ## Exact debt of the exceptional OR host -/

def hostActionValues (inactive active : ℝ) : Bool → ℝ :=
  fun action => if action then active else inactive

def hostORDebt (mergedQuit inactive active : ℝ) : ℝ :=
  binaryDebt mergedQuit (hostActionValues inactive active)

theorem hostORDebt_of_inactive_le_active
    (mergedQuit inactive active : ℝ) (horder : inactive ≤ active) :
    hostORDebt mergedQuit inactive active =
      (1 - mergedQuit) * (active - inactive) := by
  simp [hostORDebt, binaryDebt, bestBinaryValue, prescribedBinaryValue,
    hostActionValues, max_eq_right horder]
  ring

theorem hostORDebt_of_active_le_inactive
    (mergedQuit inactive active : ℝ) (horder : active ≤ inactive) :
    hostORDebt mergedQuit inactive active =
      mergedQuit * (inactive - active) := by
  simp [hostORDebt, binaryDebt, bestBinaryValue, prescribedBinaryValue,
    hostActionValues, max_eq_left horder]
  ring

theorem hostORDebt_nonneg
    (mergedQuit inactive active : ℝ)
    (hzero : 0 ≤ mergedQuit) (hone : mergedQuit ≤ 1) :
    0 ≤ hostORDebt mergedQuit inactive active := by
  rcases le_total inactive active with horder | horder
  · rw [hostORDebt_of_inactive_le_active _ _ _ horder]
    exact mul_nonneg (sub_nonneg.mpr hone) (sub_nonneg.mpr horder)
  · rw [hostORDebt_of_active_le_inactive _ _ _ horder]
    exact mul_nonneg hzero (sub_nonneg.mpr horder)

/-- At an interior OR marginal, zero host debt is exactly equality between
the active conditional value and the inactive value. -/
theorem hostORDebt_eq_zero_iff
    (mergedQuit inactive active : ℝ)
    (hzero : 0 < mergedQuit) (hone : mergedQuit < 1) :
    hostORDebt mergedQuit inactive active = 0 ↔ inactive = active := by
  constructor
  · intro hdebt
    rcases le_total inactive active with horder | horder
    · rw [hostORDebt_of_inactive_le_active _ _ _ horder] at hdebt
      nlinarith
    · rw [hostORDebt_of_active_le_inactive _ _ _ horder] at hdebt
      nlinarith
  · rintro rfl
    rw [hostORDebt_of_inactive_le_active]
    · ring
    · rfl

/-- Quantitative pricing of active/inactive mismatch by the host debt. -/
theorem min_boundaryMass_mul_abs_sub_le_hostORDebt
    (mergedQuit inactive active : ℝ) :
    min mergedQuit (1 - mergedQuit) * |active - inactive| ≤
      hostORDebt mergedQuit inactive active := by
  rcases le_total inactive active with horder | horder
  · rw [hostORDebt_of_inactive_le_active _ _ _ horder,
      abs_of_nonneg (sub_nonneg.mpr horder)]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _)
      (sub_nonneg.mpr horder)
  · rw [hostORDebt_of_active_le_inactive _ _ _ horder,
      abs_of_nonpos (sub_nonpos.mpr horder)]
    have hdiff : -(active - inactive) = inactive - active := by ring
    rw [hdiff]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _)
      (sub_nonneg.mpr horder)

/-! ## Recurrent common-slot table mismatch is paid by endpoint debt -/

/-- One protected payoff channel observed at two recurrent phases which must
share one fixed target Quit reward. -/
structure RecurrentTableChannel where
  fixedQuit : ℝ
  firstContinue : ℝ
  secondContinue : ℝ
  firstOwnQuit : ℝ
  secondOwnQuit : ℝ

namespace RecurrentTableChannel

/-- Endpoint debt in the two source rows, using their individually required
Quit values. -/
def sourceDebt (channel : RecurrentTableChannel)
    (firstRequired secondRequired : ℝ) : ℝ :=
  hostORDebt channel.firstOwnQuit channel.firstContinue firstRequired +
    hostORDebt channel.secondOwnQuit channel.secondContinue secondRequired

/-- Endpoint debt in the target rows after both use one fixed table entry. -/
def fixedTableDebt (channel : RecurrentTableChannel) : ℝ :=
  hostORDebt channel.firstOwnQuit channel.firstContinue channel.fixedQuit +
    hostORDebt channel.secondOwnQuit channel.secondContinue channel.fixedQuit

def totalDebt (channel : RecurrentTableChannel)
    (firstRequired secondRequired : ℝ) : ℝ :=
  channel.sourceDebt firstRequired secondRequired + channel.fixedTableDebt

/-- Both recurrent prescribed marginals are genuine probabilities and stay
at least `kappa` from the two pure endpoints. -/
structure HasMixingFloor (channel : RecurrentTableChannel)
    (kappa : ℝ) : Prop where
  first_nonneg : 0 ≤ channel.firstOwnQuit
  first_le_one : channel.firstOwnQuit ≤ 1
  second_nonneg : 0 ≤ channel.secondOwnQuit
  second_le_one : channel.secondOwnQuit ≤ 1
  first_floor : kappa ≤
    min channel.firstOwnQuit (1 - channel.firstOwnQuit)
  second_floor : kappa ≤
    min channel.secondOwnQuit (1 - channel.secondOwnQuit)

structure HasProbabilityMarginals (channel : RecurrentTableChannel) : Prop where
  first_nonneg : 0 ≤ channel.firstOwnQuit
  first_le_one : channel.firstOwnQuit ≤ 1
  second_nonneg : 0 ≤ channel.secondOwnQuit
  second_le_one : channel.secondOwnQuit ≤ 1

/-- The explicit boundary escape from a common interior mixing floor. -/
def NearPureEscape (channel : RecurrentTableChannel) (kappa : ℝ) : Prop :=
  channel.firstOwnQuit < kappa ∨
    1 - kappa < channel.firstOwnQuit ∨
    channel.secondOwnQuit < kappa ∨
    1 - kappa < channel.secondOwnQuit

theorem mixingFloor_or_nearPure
    (channel : RecurrentTableChannel) (kappa : ℝ)
    (hprobability : channel.HasProbabilityMarginals) :
    channel.HasMixingFloor kappa ∨ channel.NearPureEscape kappa := by
  by_cases hfirst : kappa ≤
      min channel.firstOwnQuit (1 - channel.firstOwnQuit)
  · by_cases hsecond : kappa ≤
        min channel.secondOwnQuit (1 - channel.secondOwnQuit)
    · left
      exact ⟨hprobability.first_nonneg, hprobability.first_le_one,
        hprobability.second_nonneg, hprobability.second_le_one,
        hfirst, hsecond⟩
    · right
      have hlt : min channel.secondOwnQuit
          (1 - channel.secondOwnQuit) < kappa := lt_of_not_ge hsecond
      rcases (min_lt_iff.mp hlt) with hnear | hnear
      · exact Or.inr (Or.inr (Or.inl hnear))
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · right
    have hlt : min channel.firstOwnQuit
        (1 - channel.firstOwnQuit) < kappa := lt_of_not_ge hfirst
    rcases (min_lt_iff.mp hlt) with hnear | hnear
    · exact Or.inl hnear
    · exact Or.inr (Or.inl (by linarith))

/-- At one row, changing the required Quit value to a fixed table value is
paid by the sum of the source and target endpoint debts. -/
theorem minBoundary_mul_tableMismatch_le_debtSum
    (ownQuit continueValue requiredQuit fixedQuit : ℝ)
    (hzero : 0 ≤ ownQuit) (hone : ownQuit ≤ 1) :
    min ownQuit (1 - ownQuit) * |fixedQuit - requiredQuit| ≤
      hostORDebt ownQuit continueValue requiredQuit +
        hostORDebt ownQuit continueValue fixedQuit := by
  have hmin : 0 ≤ min ownQuit (1 - ownQuit) :=
    le_min hzero (sub_nonneg.mpr hone)
  have htriangle : |fixedQuit - requiredQuit| ≤
      |fixedQuit - continueValue| + |requiredQuit - continueValue| := by
    calc
      |fixedQuit - requiredQuit| =
          |(fixedQuit - continueValue) -
            (requiredQuit - continueValue)| := by
              congr 1
              ring
      _ ≤ |fixedQuit - continueValue| +
          |requiredQuit - continueValue| := abs_sub _ _
  calc
    min ownQuit (1 - ownQuit) * |fixedQuit - requiredQuit| ≤
        min ownQuit (1 - ownQuit) *
          (|fixedQuit - continueValue| +
            |requiredQuit - continueValue|) :=
      mul_le_mul_of_nonneg_left htriangle hmin
    _ = min ownQuit (1 - ownQuit) * |fixedQuit - continueValue| +
        min ownQuit (1 - ownQuit) * |requiredQuit - continueValue| := by ring
    _ ≤ hostORDebt ownQuit continueValue fixedQuit +
        hostORDebt ownQuit continueValue requiredQuit :=
      add_le_add
        (min_boundaryMass_mul_abs_sub_le_hostORDebt
          ownQuit continueValue fixedQuit)
        (min_boundaryMass_mul_abs_sub_le_hostORDebt
          ownQuit continueValue requiredQuit)
    _ = hostORDebt ownQuit continueValue requiredQuit +
        hostORDebt ownQuit continueValue fixedQuit := by ring

/-- **Two-phase fixed-slot charge.**  If two recurrent phases require
different Quit rewards in the same table slot, their source and target debts
pay the variation at the mixing-floor scale. -/
theorem mixingFloor_mul_requiredVariation_le_totalDebt
    (channel : RecurrentTableChannel) (kappa : ℝ)
    (firstRequired secondRequired : ℝ)
    (hfloor : channel.HasMixingFloor kappa)
    (hkappa : 0 ≤ kappa) :
    kappa * |firstRequired - secondRequired| ≤
      channel.totalDebt firstRequired secondRequired := by
  have hfirstBase := minBoundary_mul_tableMismatch_le_debtSum
    channel.firstOwnQuit channel.firstContinue firstRequired channel.fixedQuit
    hfloor.first_nonneg hfloor.first_le_one
  have hsecondBase := minBoundary_mul_tableMismatch_le_debtSum
    channel.secondOwnQuit channel.secondContinue secondRequired channel.fixedQuit
    hfloor.second_nonneg hfloor.second_le_one
  have hfirst : kappa * |channel.fixedQuit - firstRequired| ≤
      hostORDebt channel.firstOwnQuit channel.firstContinue firstRequired +
        hostORDebt channel.firstOwnQuit channel.firstContinue
          channel.fixedQuit := by
    exact (mul_le_mul_of_nonneg_right hfloor.first_floor (abs_nonneg _)).trans
      hfirstBase
  have hsecond : kappa * |channel.fixedQuit - secondRequired| ≤
      hostORDebt channel.secondOwnQuit channel.secondContinue secondRequired +
        hostORDebt channel.secondOwnQuit channel.secondContinue
          channel.fixedQuit := by
    exact (mul_le_mul_of_nonneg_right hfloor.second_floor (abs_nonneg _)).trans
      hsecondBase
  have htriangle : |firstRequired - secondRequired| ≤
      |channel.fixedQuit - firstRequired| +
        |channel.fixedQuit - secondRequired| := by
    calc
      |firstRequired - secondRequired| =
          |-(channel.fixedQuit - firstRequired) +
            (channel.fixedQuit - secondRequired)| := by
              congr 1
              ring
      _ ≤ |-(channel.fixedQuit - firstRequired)| +
          |channel.fixedQuit - secondRequired| := abs_add_le _ _
      _ = |channel.fixedQuit - firstRequired| +
          |channel.fixedQuit - secondRequired| := by rw [abs_neg]
  calc
    kappa * |firstRequired - secondRequired| ≤
        kappa * (|channel.fixedQuit - firstRequired| +
          |channel.fixedQuit - secondRequired|) :=
      mul_le_mul_of_nonneg_left htriangle hkappa
    _ = kappa * |channel.fixedQuit - firstRequired| +
        kappa * |channel.fixedQuit - secondRequired| := by ring
    _ ≤ (hostORDebt channel.firstOwnQuit channel.firstContinue firstRequired +
          hostORDebt channel.firstOwnQuit channel.firstContinue
            channel.fixedQuit) +
        (hostORDebt channel.secondOwnQuit channel.secondContinue secondRequired +
          hostORDebt channel.secondOwnQuit channel.secondContinue
            channel.fixedQuit) := add_le_add hfirst hsecond
    _ = channel.totalDebt firstRequired secondRequired := by
      unfold totalDebt sourceDebt fixedTableDebt
      ring

end RecurrentTableChannel

/-- **Hidden-law motion is debt or boundary.**  For two separating payoff
channels sharing recurrent fixed table slots, determinant-controlled motion
of the hidden conditional law is paid by the four source/target endpoint
debts, provided both channels have a common interior mixing floor. -/
theorem hiddenMotion_le_twoChannelRecurrentDebt
    (firstHidden secondHidden : HiddenCoordinates)
    (firstFeature secondFeature : Fin 3 → ℝ)
    (firstChannel secondChannel : RecurrentTableChannel)
    (kappa : ℝ)
    (hfirstFloor : firstChannel.HasMixingFloor kappa)
    (hsecondFloor : secondChannel.HasMixingFloor kappa)
    (hkappa : 0 ≤ kappa)
    (hbudget : 0 < featureContrastBudget firstFeature secondFeature) :
    kappa *
        (|affineFeatureDeterminant firstFeature secondFeature| /
          featureContrastBudget firstFeature secondFeature) *
        hiddenCoordinateVariation firstHidden secondHidden ≤
      firstChannel.totalDebt
          (hiddenEvaluation firstHidden firstFeature)
          (hiddenEvaluation secondHidden firstFeature) +
        secondChannel.totalDebt
          (hiddenEvaluation firstHidden secondFeature)
          (hiddenEvaluation secondHidden secondFeature) := by
  let firstMismatch := |hiddenEvaluation firstHidden firstFeature -
    hiddenEvaluation secondHidden firstFeature|
  let secondMismatch := |hiddenEvaluation firstHidden secondFeature -
    hiddenEvaluation secondHidden secondFeature|
  have hseparation := determinant_div_contrast_mul_variation_le_mismatch
    firstHidden secondHidden firstFeature secondFeature hbudget
  have hfirstCharge :=
    RecurrentTableChannel.mixingFloor_mul_requiredVariation_le_totalDebt
      firstChannel kappa
      (hiddenEvaluation firstHidden firstFeature)
      (hiddenEvaluation secondHidden firstFeature) hfirstFloor hkappa
  have hsecondCharge :=
    RecurrentTableChannel.mixingFloor_mul_requiredVariation_le_totalDebt
      secondChannel kappa
      (hiddenEvaluation firstHidden secondFeature)
      (hiddenEvaluation secondHidden secondFeature) hsecondFloor hkappa
  have hmismatchSum :
      twoChannelMismatch firstHidden secondHidden firstFeature secondFeature ≤
        firstMismatch + secondMismatch := by
    unfold twoChannelMismatch firstMismatch secondMismatch
    exact max_le
      (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))
  calc
    kappa *
        (|affineFeatureDeterminant firstFeature secondFeature| /
          featureContrastBudget firstFeature secondFeature) *
        hiddenCoordinateVariation firstHidden secondHidden =
      kappa *
        ((|affineFeatureDeterminant firstFeature secondFeature| /
          featureContrastBudget firstFeature secondFeature) *
        hiddenCoordinateVariation firstHidden secondHidden) := by ring
    _ ≤ kappa *
        twoChannelMismatch firstHidden secondHidden firstFeature secondFeature :=
      mul_le_mul_of_nonneg_left hseparation hkappa
    _ ≤ kappa * (firstMismatch + secondMismatch) :=
      mul_le_mul_of_nonneg_left hmismatchSum hkappa
    _ = kappa * firstMismatch + kappa * secondMismatch := by ring
    _ ≤ firstChannel.totalDebt
          (hiddenEvaluation firstHidden firstFeature)
          (hiddenEvaluation secondHidden firstFeature) +
        secondChannel.totalDebt
          (hiddenEvaluation firstHidden secondFeature)
          (hiddenEvaluation secondHidden secondFeature) :=
      add_le_add hfirstCharge hsecondCharge

/-- Complete finite stationarization alternative.  Hidden-law motion is
quantitatively charged by recurrent endpoint debts, or one of the four
protected marginals lies within `kappa` of a pure endpoint. -/
theorem hiddenMotion_charged_or_nearPure
    (firstHidden secondHidden : HiddenCoordinates)
    (firstFeature secondFeature : Fin 3 → ℝ)
    (firstChannel secondChannel : RecurrentTableChannel)
    (kappa : ℝ)
    (hfirstProbability : firstChannel.HasProbabilityMarginals)
    (hsecondProbability : secondChannel.HasProbabilityMarginals)
    (hkappa : 0 ≤ kappa)
    (hbudget : 0 < featureContrastBudget firstFeature secondFeature) :
    (kappa *
        (|affineFeatureDeterminant firstFeature secondFeature| /
          featureContrastBudget firstFeature secondFeature) *
        hiddenCoordinateVariation firstHidden secondHidden ≤
      firstChannel.totalDebt
          (hiddenEvaluation firstHidden firstFeature)
          (hiddenEvaluation secondHidden firstFeature) +
        secondChannel.totalDebt
          (hiddenEvaluation firstHidden secondFeature)
          (hiddenEvaluation secondHidden secondFeature)) ∨
      firstChannel.NearPureEscape kappa ∨
      secondChannel.NearPureEscape kappa := by
  rcases firstChannel.mixingFloor_or_nearPure kappa hfirstProbability with
      hfirstFloor | hfirstNear
  · rcases secondChannel.mixingFloor_or_nearPure kappa hsecondProbability with
        hsecondFloor | hsecondNear
    · exact Or.inl (hiddenMotion_le_twoChannelRecurrentDebt
        firstHidden secondHidden firstFeature secondFeature
        firstChannel secondChannel kappa hfirstFloor hsecondFloor
        hkappa hbudget)
    · exact Or.inr (Or.inr hsecondNear)
  · exact Or.inr (Or.inl hfirstNear)

/-! ## Stationary-table charge around a finite recurrence -/

/-- One occurrence of a fixed target-table slot along a recurrent family.
`requiredQuit` is the conditional reward demanded by the source lift, whereas
the target game must use one phase-independent `fixedQuit`. -/
structure StationaryTableRow where
  ownQuit : ℝ
  continueValue : ℝ
  requiredQuit : ℝ

namespace StationaryTableRow

/-- The source endpoint debt plus the debt created by replacing the required
Quit entry with the stationary table entry. -/
def endpointDebt (row : StationaryTableRow) (fixedQuit : ℝ) : ℝ :=
  hostORDebt row.ownQuit row.continueValue row.requiredQuit +
    hostORDebt row.ownQuit row.continueValue fixedQuit

/-- The row stays at least `kappa` away from both pure host endpoints. -/
def HasMixingFloor (row : StationaryTableRow) (kappa : ℝ) : Prop :=
  0 ≤ row.ownQuit ∧ row.ownQuit ≤ 1 ∧
    kappa ≤ min row.ownQuit (1 - row.ownQuit)

/-- The complementary endpoint escape. -/
def NearPureEscape (row : StationaryTableRow) (kappa : ℝ) : Prop :=
  row.ownQuit < kappa ∨ 1 - kappa < row.ownQuit

theorem mixingFloor_or_nearPure (row : StationaryTableRow) (kappa : ℝ)
    (hzero : 0 ≤ row.ownQuit) (hone : row.ownQuit ≤ 1) :
    row.HasMixingFloor kappa ∨ row.NearPureEscape kappa := by
  by_cases hfloor : kappa ≤ min row.ownQuit (1 - row.ownQuit)
  · exact Or.inl ⟨hzero, hone, hfloor⟩
  · right
    have hlt : min row.ownQuit (1 - row.ownQuit) < kappa :=
      lt_of_not_ge hfloor
    rcases min_lt_iff.mp hlt with hnear | hnear
    · exact Or.inl hnear
    · exact Or.inr (by linarith)

/-- At an interior row, failure to use the required table entry is paid by
the two endpoint debts at that same row. -/
theorem mixingFloor_mul_fixedMismatch_le_endpointDebt
    (row : StationaryTableRow) (fixedQuit kappa : ℝ)
    (hfloor : row.HasMixingFloor kappa) (_hkappa : 0 ≤ kappa) :
    kappa * |fixedQuit - row.requiredQuit| ≤ row.endpointDebt fixedQuit := by
  have hbase := RecurrentTableChannel.minBoundary_mul_tableMismatch_le_debtSum
    row.ownQuit row.continueValue row.requiredQuit fixedQuit
    hfloor.1 hfloor.2.1
  exact (mul_le_mul_of_nonneg_right hfloor.2.2 (abs_nonneg _)).trans hbase

end StationaryTableRow

section FiniteRecurrence

variable {phase : Type} [Fintype phase]

/-- Total variation of the source-required entry around a finite recurrence. -/
def cyclicRequiredVariation (rows : phase → StationaryTableRow)
    (next : Equiv.Perm phase) : ℝ :=
  ∑ index, |(rows index).requiredQuit - (rows (next index)).requiredQuit|

/-- Total source-plus-stationarization endpoint debt in one fixed table slot. -/
def stationaryTableDebt (rows : phase → StationaryTableRow)
    (fixedQuit : ℝ) : ℝ :=
  ∑ index, (rows index).endpointDebt fixedQuit

/-- **Cyclic stationarization inequality.**  If every recurrent occurrence of
one table slot is interior, twice its accumulated endpoint debt pays the full
cyclic variation of the conditional reward required by the source lifts.

The factor two is the exact incidence degree of a cycle: every row is charged
once by the incoming edge and once by the outgoing edge. -/
theorem mixingFloor_mul_cyclicRequiredVariation_le_two_stationaryTableDebt
    (rows : phase → StationaryTableRow) (next : Equiv.Perm phase)
    (fixedQuit kappa : ℝ)
    (hfloor : ∀ index, (rows index).HasMixingFloor kappa)
    (hkappa : 0 ≤ kappa) :
    kappa * cyclicRequiredVariation rows next ≤
      2 * stationaryTableDebt rows fixedQuit := by
  have hedge : ∀ index,
      kappa * |(rows index).requiredQuit -
          (rows (next index)).requiredQuit| ≤
        (rows index).endpointDebt fixedQuit +
          (rows (next index)).endpointDebt fixedQuit := by
    intro index
    have hleft := StationaryTableRow.mixingFloor_mul_fixedMismatch_le_endpointDebt
      (rows index) fixedQuit kappa (hfloor index) hkappa
    have hright := StationaryTableRow.mixingFloor_mul_fixedMismatch_le_endpointDebt
      (rows (next index)) fixedQuit kappa (hfloor (next index)) hkappa
    have htriangle : |(rows index).requiredQuit -
        (rows (next index)).requiredQuit| ≤
        |fixedQuit - (rows index).requiredQuit| +
          |fixedQuit - (rows (next index)).requiredQuit| := by
      calc
        |(rows index).requiredQuit - (rows (next index)).requiredQuit| =
            |-(fixedQuit - (rows index).requiredQuit) +
              (fixedQuit - (rows (next index)).requiredQuit)| := by
                congr 1
                ring
        _ ≤ |-(fixedQuit - (rows index).requiredQuit)| +
            |fixedQuit - (rows (next index)).requiredQuit| := abs_add_le _ _
        _ = |fixedQuit - (rows index).requiredQuit| +
            |fixedQuit - (rows (next index)).requiredQuit| := by rw [abs_neg]
    calc
      kappa * |(rows index).requiredQuit -
          (rows (next index)).requiredQuit| ≤
          kappa * (|fixedQuit - (rows index).requiredQuit| +
            |fixedQuit - (rows (next index)).requiredQuit|) :=
        mul_le_mul_of_nonneg_left htriangle hkappa
      _ = kappa * |fixedQuit - (rows index).requiredQuit| +
          kappa * |fixedQuit - (rows (next index)).requiredQuit| := by ring
      _ ≤ (rows index).endpointDebt fixedQuit +
          (rows (next index)).endpointDebt fixedQuit := add_le_add hleft hright
  have hsum := Finset.sum_le_sum fun index (_ : index ∈ Finset.univ) =>
    hedge index
  have hreindex : (∑ index, (rows (next index)).endpointDebt fixedQuit) =
      ∑ index, (rows index).endpointDebt fixedQuit := by
    simpa using Equiv.sum_comp next
      (fun index => (rows index).endpointDebt fixedQuit)
  unfold cyclicRequiredVariation stationaryTableDebt
  rw [Finset.mul_sum]
  calc
    ∑ index, kappa * |(rows index).requiredQuit -
        (rows (next index)).requiredQuit| ≤
        ∑ index, ((rows index).endpointDebt fixedQuit +
          (rows (next index)).endpointDebt fixedQuit) := hsum
    _ = (∑ index, (rows index).endpointDebt fixedQuit) +
        ∑ index, (rows (next index)).endpointDebt fixedQuit := by
          rw [Finset.sum_add_distrib]
    _ = 2 * ∑ index, (rows index).endpointDebt fixedQuit := by
      rw [hreindex]
      ring

/-- Complete cycle-level alternative: table variation is charged, or the
recurrence contains an explicit near-pure host occurrence. -/
theorem cyclicRequiredVariation_charged_or_nearPure
    (rows : phase → StationaryTableRow) (next : Equiv.Perm phase)
    (fixedQuit kappa : ℝ)
    (hprobability : ∀ index,
      0 ≤ (rows index).ownQuit ∧ (rows index).ownQuit ≤ 1)
    (hkappa : 0 ≤ kappa) :
    (kappa * cyclicRequiredVariation rows next ≤
      2 * stationaryTableDebt rows fixedQuit) ∨
      ∃ index, (rows index).NearPureEscape kappa := by
  by_cases hall : ∀ index, (rows index).HasMixingFloor kappa
  · exact Or.inl
      (mixingFloor_mul_cyclicRequiredVariation_le_two_stationaryTableDebt
        rows next fixedQuit kappa hall hkappa)
  · right
    push Not at hall
    obtain ⟨index, hnotFloor⟩ := hall
    rcases (rows index).mixingFloor_or_nearPure kappa
        (hprobability index).1 (hprobability index).2 with hfloor | hnear
    · exact False.elim (hnotFloor hfloor)
    · exact ⟨index, hnear⟩

/-- **Finite recurrent hidden-law stationarization.**  Two payoff channels
separating the hidden OR law turn the whole cyclic path length of that law
into stationary-table endpoint debt.  The only alternative is a concrete
phase/channel whose host marginal is within `kappa` of a pure endpoint.

This is the cycle-level version of `hiddenMotion_charged_or_nearPure`: there
is no selected pair of phases and no loss depending on the number of phases.
The factor two is solely the cycle's incoming/outgoing incidence degree. -/
theorem hiddenCyclicVariation_charged_or_nearPure
    (hidden : phase → HiddenCoordinates)
    (firstRows secondRows : phase → StationaryTableRow)
    (next : Equiv.Perm phase)
    (firstFeature secondFeature : Fin 3 → ℝ)
    (firstFixedQuit secondFixedQuit kappa : ℝ)
    (hfirstRequired : ∀ index, (firstRows index).requiredQuit =
      hiddenEvaluation (hidden index) firstFeature)
    (hsecondRequired : ∀ index, (secondRows index).requiredQuit =
      hiddenEvaluation (hidden index) secondFeature)
    (hfirstProbability : ∀ index,
      0 ≤ (firstRows index).ownQuit ∧ (firstRows index).ownQuit ≤ 1)
    (hsecondProbability : ∀ index,
      0 ≤ (secondRows index).ownQuit ∧ (secondRows index).ownQuit ≤ 1)
    (hkappa : 0 ≤ kappa)
    (hbudget : 0 < featureContrastBudget firstFeature secondFeature) :
    (kappa *
        (|affineFeatureDeterminant firstFeature secondFeature| /
          featureContrastBudget firstFeature secondFeature) *
        (∑ index, hiddenCoordinateVariation
          (hidden index) (hidden (next index))) ≤
      2 * (stationaryTableDebt firstRows firstFixedQuit +
        stationaryTableDebt secondRows secondFixedQuit)) ∨
      (∃ index, (firstRows index).NearPureEscape kappa) ∨
      ∃ index, (secondRows index).NearPureEscape kappa := by
  by_cases hfirstFloor : ∀ index,
      (firstRows index).HasMixingFloor kappa
  · by_cases hsecondFloor : ∀ index,
        (secondRows index).HasMixingFloor kappa
    · left
      have hseparation :
          (|affineFeatureDeterminant firstFeature secondFeature| /
              featureContrastBudget firstFeature secondFeature) *
              (∑ index, hiddenCoordinateVariation
                (hidden index) (hidden (next index))) ≤
            cyclicRequiredVariation firstRows next +
              cyclicRequiredVariation secondRows next := by
        rw [Finset.mul_sum]
        calc
          ∑ index,
              (|affineFeatureDeterminant firstFeature secondFeature| /
                  featureContrastBudget firstFeature secondFeature) *
                hiddenCoordinateVariation
                  (hidden index) (hidden (next index)) ≤
              ∑ index,
                (|(firstRows index).requiredQuit -
                    (firstRows (next index)).requiredQuit| +
                  |(secondRows index).requiredQuit -
                    (secondRows (next index)).requiredQuit|) := by
            apply Finset.sum_le_sum
            intro index _
            have hpoint := determinant_div_contrast_mul_variation_le_mismatch
              (hidden index) (hidden (next index)) firstFeature secondFeature
              hbudget
            have hmax : twoChannelMismatch
                (hidden index) (hidden (next index))
                firstFeature secondFeature ≤
                |hiddenEvaluation (hidden index) firstFeature -
                    hiddenEvaluation (hidden (next index)) firstFeature| +
                  |hiddenEvaluation (hidden index) secondFeature -
                    hiddenEvaluation (hidden (next index)) secondFeature| := by
              unfold twoChannelMismatch
              exact max_le
                (le_add_of_nonneg_right (abs_nonneg _))
                (le_add_of_nonneg_left (abs_nonneg _))
            calc
              (|affineFeatureDeterminant firstFeature secondFeature| /
                  featureContrastBudget firstFeature secondFeature) *
                  hiddenCoordinateVariation
                    (hidden index) (hidden (next index)) ≤
                twoChannelMismatch
                  (hidden index) (hidden (next index))
                  firstFeature secondFeature := hpoint
              _ ≤ |hiddenEvaluation (hidden index) firstFeature -
                    hiddenEvaluation (hidden (next index)) firstFeature| +
                  |hiddenEvaluation (hidden index) secondFeature -
                    hiddenEvaluation (hidden (next index)) secondFeature| := hmax
              _ = |(firstRows index).requiredQuit -
                    (firstRows (next index)).requiredQuit| +
                  |(secondRows index).requiredQuit -
                    (secondRows (next index)).requiredQuit| := by
                rw [hfirstRequired index, hfirstRequired (next index),
                  hsecondRequired index, hsecondRequired (next index)]
          _ = cyclicRequiredVariation firstRows next +
              cyclicRequiredVariation secondRows next := by
            unfold cyclicRequiredVariation
            rw [Finset.sum_add_distrib]
      have hfirstCharge :=
        mixingFloor_mul_cyclicRequiredVariation_le_two_stationaryTableDebt
          firstRows next firstFixedQuit kappa hfirstFloor hkappa
      have hsecondCharge :=
        mixingFloor_mul_cyclicRequiredVariation_le_two_stationaryTableDebt
          secondRows next secondFixedQuit kappa hsecondFloor hkappa
      calc
        kappa *
            (|affineFeatureDeterminant firstFeature secondFeature| /
              featureContrastBudget firstFeature secondFeature) *
            (∑ index, hiddenCoordinateVariation
              (hidden index) (hidden (next index))) =
          kappa *
            ((|affineFeatureDeterminant firstFeature secondFeature| /
                featureContrastBudget firstFeature secondFeature) *
              (∑ index, hiddenCoordinateVariation
                (hidden index) (hidden (next index)))) := by ring
        _ ≤ kappa * (cyclicRequiredVariation firstRows next +
              cyclicRequiredVariation secondRows next) :=
          mul_le_mul_of_nonneg_left hseparation hkappa
        _ = kappa * cyclicRequiredVariation firstRows next +
              kappa * cyclicRequiredVariation secondRows next := by ring
        _ ≤ 2 * stationaryTableDebt firstRows firstFixedQuit +
              2 * stationaryTableDebt secondRows secondFixedQuit :=
          add_le_add hfirstCharge hsecondCharge
        _ = 2 * (stationaryTableDebt firstRows firstFixedQuit +
              stationaryTableDebt secondRows secondFixedQuit) := by ring
    · right
      right
      push Not at hsecondFloor
      obtain ⟨index, hnotFloor⟩ := hsecondFloor
      rcases (secondRows index).mixingFloor_or_nearPure kappa
          (hsecondProbability index).1 (hsecondProbability index).2 with
          hfloor | hnear
      · exact False.elim (hnotFloor hfloor)
      · exact ⟨index, hnear⟩
  · right
    left
    push Not at hfirstFloor
    obtain ⟨index, hnotFloor⟩ := hfirstFloor
    rcases (firstRows index).mixingFloor_or_nearPure kappa
        (hfirstProbability index).1 (hfirstProbability index).2 with
        hfloor | hnear
    · exact False.elim (hnotFloor hfloor)
    · exact ⟨index, hnear⟩

end FiniteRecurrence

/-! ## A literal local table-mismatch/host-debt alternative -/

/-- Use one payoff feature as a calibrated host test against a reference
hidden law. -/
def calibratedHostDebt (mergedQuit : ℝ)
    (reference current : HiddenCoordinates) (feature : Fin 3 → ℝ) : ℝ :=
  hostORDebt mergedQuit
    (hiddenEvaluation reference feature)
    (hiddenEvaluation current feature)

/-- If two channels separate hidden laws, motion away from a reference law
either changes the first (protected) table entry or creates strictly positive
calibrated host debt in the second channel. -/
theorem protectedTableMismatch_or_positiveCalibratedHostDebt
    (mergedQuit : ℝ) (reference current : HiddenCoordinates)
    (protectedFeature hostFeature : Fin 3 → ℝ)
    (hdet : affineFeatureDeterminant protectedFeature hostFeature ≠ 0)
    (hcurrent : current ≠ reference)
    (hzero : 0 < mergedQuit) (hone : mergedQuit < 1) :
    hiddenEvaluation current protectedFeature ≠
        hiddenEvaluation reference protectedFeature ∨
      0 < calibratedHostDebt mergedQuit reference current hostFeature := by
  rcases evaluation_mismatch_or_evaluation_mismatch current reference
      protectedFeature hostFeature hdet hcurrent with hmismatch | hmismatch
  · exact Or.inl hmismatch
  · right
    have hnonneg : 0 ≤ calibratedHostDebt mergedQuit reference current
        hostFeature :=
      hostORDebt_nonneg _ _ _ hzero.le hone.le
    have hne : calibratedHostDebt mergedQuit reference current hostFeature ≠
        0 := by
      intro hdebt
      have heq := (hostORDebt_eq_zero_iff mergedQuit
        (hiddenEvaluation reference hostFeature)
        (hiddenEvaluation current hostFeature) hzero hone).mp hdebt
      exact hmismatch heq.symm
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end Research.QuittingORStationarizationDichotomy
