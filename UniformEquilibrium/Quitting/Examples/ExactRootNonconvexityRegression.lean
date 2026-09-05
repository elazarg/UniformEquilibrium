/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.ExactSuccessorClosure
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import Mathlib.Analysis.Convex.Basic

/-! # Nonconvexity of the exact-root payoff image

For the displayed two-player game and zero continuation payoff, every exact
product Nash root has quitting rates `(0, 0)`, `(1/3, 1/3)`, or `(1, 1)`.
The corresponding three-point Bellman payoff image is not convex.
-/

noncomputable section

namespace GameTheory.ExactRootNonconvexityRegression

open GameTheory Math.ProbabilityMassFunction

abbrev Player := Fin 2

/-- Both players receive `1` at joint quitting and `-1` at either singleton. -/
def reward (_terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun _who => if _terminal.1 = Finset.univ then 1 else -1

def continuation : Payoff Player := fun _ => 0

/-- Symmetric independent root with common quitting probability `q`. -/
def symmetricRoot (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Player → PMF Bool := fun _ => bernoulliBool q hq0 hq1

private theorem pair_active (root : Player → PMF Bool) :
    IsQuittingActiveRoot {0, 1} root := by
  intro who hwho
  fin_cases who <;> simp at hwho

@[simp] theorem symmetricRoot_hazard (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (who : Player) : hazardOfRoot (symmetricRoot q hq0 hq1) who = q := by
  simp [hazardOfRoot, symmetricRoot]

private theorem endpointDifference_eq (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (who : Player) :
    quittingRootEndpointDifference reward continuation
      (symmetricRoot q hq0 hq1) who = -1 + 3 * q := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_pair_active reward continuation _ 0 1 who
      (by decide) (pair_active _),
    quittingRootExpectedPayoff_pair_active reward continuation _ 0 1 who
      (by decide) (pair_active _)]
  fin_cases who <;>
    simp [hazardOfRoot, symmetricRoot, continuation, reward] <;>
      norm_num +decide <;> ring

/-- The scalar mutual-best-reply system after substituting the symmetric
binary root.  Its pure Quit-minus-Continue difference is `-1 + 3*q`. -/
def IsSymmetricExactRootRate (q : ℝ) : Prop :=
  q ∈ Set.Icc (0 : ℝ) 1 ∧
    ((q = 0 ∧ -1 + 3 * q ≤ 0) ∨
      (q = 1 ∧ 0 ≤ -1 + 3 * q) ∨
      (0 < q ∧ q < 1 ∧ -1 + 3 * q = 0))

theorem isSymmetricExactRootRate_iff (q : ℝ) :
    IsSymmetricExactRootRate q ↔ q = 0 ∨ q = 1 / 3 ∨ q = 1 := by
  constructor
  · rintro ⟨_, hreply⟩
    rcases hreply with hzero | hone | hinterior
    · exact Or.inl hzero.1
    · exact Or.inr (Or.inr hone.1)
    · right; left; linarith [hinterior.2.2]
  · rintro (rfl | rfl | rfl) <;>
      constructor
    · exact ⟨by norm_num, by norm_num⟩
    · exact Or.inl ⟨rfl, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
    · exact Or.inr (Or.inr ⟨by norm_num, by norm_num, by norm_num⟩)
    · exact ⟨by norm_num, by norm_num⟩
    · exact Or.inr (Or.inl ⟨rfl, by norm_num⟩)

theorem symmetricRoot_isZeroNash_iff
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsεQuittingRootNash reward continuation 0 (symmetricRoot q hq0 hq1) ↔
      IsSymmetricExactRootRate q := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  unfold IsεQuittingRootEndpointNash
  simp only [endpointDifference_eq]
  constructor
  · intro hnash
    have hcoordinate := hnash 0
    constructor
    · exact ⟨hq0, hq1⟩
    · by_cases hqzero : q = 0
      · exact Or.inl ⟨hqzero, by linarith⟩
      by_cases hqone : q = 1
      · exact Or.inr (Or.inl ⟨hqone, by linarith⟩)
      · right; right
        refine ⟨lt_of_le_of_ne hq0 (Ne.symm hqzero),
          lt_of_le_of_ne hq1 hqone, ?_⟩
        rcases hcoordinate with ⟨hcontinue, hquit⟩
        simp [symmetricRoot] at hcontinue hquit
        have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqzero)
        have hcontinuePos : 0 < 1 - q := sub_pos.mpr (lt_of_le_of_ne hq1 hqone)
        nlinarith
  · rintro ⟨_, hreply⟩ who
    simp only [symmetricRoot]
    rcases hreply with ⟨rfl, hdiff⟩ | ⟨rfl, hdiff⟩ | ⟨_, _, hdiff⟩
    · simp
    · simp
    · simp [hdiff]

theorem symmetricRoot_isZeroNash_iff_rate
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsεQuittingRootNash reward continuation 0 (symmetricRoot q hq0 hq1) ↔
      q = 0 ∨ q = 1 / 3 ∨ q = 1 := by
  rw [symmetricRoot_isZeroNash_iff, isSymmetricExactRootRate_iff]

theorem symmetricRoot_successorPayoff
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (who : Player) :
    quittingRootSuccessorPayoff reward continuation
        (symmetricRoot q hq0 hq1) who = 3 * q ^ 2 - 2 * q := by
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_pair_active reward continuation _ 0 1 who
    (by decide) (pair_active _)]
  fin_cases who <;>
    simp [hazardOfRoot, symmetricRoot, continuation, reward] <;>
      norm_num +decide <;> ring

theorem exact_symmetric_successor_values :
    quittingRootSuccessorPayoff reward continuation
          (symmetricRoot 0 (by norm_num) (by norm_num)) = continuation ∧
      quittingRootSuccessorPayoff reward continuation
          (symmetricRoot (1 / 3) (by norm_num) (by norm_num)) =
            (fun _ => -(1 / 3 : ℝ)) ∧
      quittingRootSuccessorPayoff reward continuation
          (symmetricRoot 1 (by norm_num) (by norm_num)) = fun _ => 1 := by
  constructor
  · funext who
    rw [symmetricRoot_successorPayoff]
    simp [continuation]
  constructor <;> funext who <;> rw [symmetricRoot_successorPayoff] <;> norm_num

def displayedImage : Set (Payoff Player) :=
  {continuation, fun _ => -(1 / 3 : ℝ), fun _ => 1}

theorem exact_symmetric_root_successor_range :
    {payoff | ∃ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1),
      IsεQuittingRootNash reward continuation 0 (symmetricRoot q hq0 hq1) ∧
      payoff = quittingRootSuccessorPayoff reward continuation
        (symmetricRoot q hq0 hq1)} = displayedImage := by
  ext payoff
  constructor
  · rintro ⟨q, hq0, hq1, hnash, rfl⟩
    rw [symmetricRoot_isZeroNash_iff_rate q hq0 hq1] at hnash
    rcases hnash with rfl | rfl | rfl
    · simp [displayedImage, exact_symmetric_successor_values.1]
    · simp [displayedImage, exact_symmetric_successor_values.2.1]
    · simp [displayedImage, exact_symmetric_successor_values.2.2]
  · intro hpayoff
    rcases hpayoff with rfl | rfl | rfl
    · refine ⟨0, by norm_num, by norm_num, ?_, ?_⟩
      · exact (symmetricRoot_isZeroNash_iff_rate 0 (by norm_num) (by norm_num)).2
          (Or.inl rfl)
      · exact exact_symmetric_successor_values.1.symm
    · refine ⟨1 / 3, by norm_num, by norm_num, ?_, ?_⟩
      · exact (symmetricRoot_isZeroNash_iff_rate (1 / 3)
          (by norm_num) (by norm_num)).2 (Or.inr (Or.inl rfl))
      · exact exact_symmetric_successor_values.2.1.symm
    · refine ⟨1, by norm_num, by norm_num, ?_, ?_⟩
      · exact (symmetricRoot_isZeroNash_iff_rate 1 (by norm_num) (by norm_num)).2
          (Or.inr (Or.inr rfl))
      · exact exact_symmetric_successor_values.2.2.symm

/-- For an arbitrary product root, each player's endpoint difference depends
only on the opponent's Quit probability. -/
theorem endpointDifference_eq_otherHazard (root : Player → PMF Bool) :
    quittingRootEndpointDifference reward continuation root 0 =
        -1 + 3 * hazardOfRoot root 1 ∧
      quittingRootEndpointDifference reward continuation root 1 =
        -1 + 3 * hazardOfRoot root 0 := by
  constructor <;>
    unfold quittingRootEndpointDifference quittingRootQuitPayoff
      quittingRootContinuePayoff <;>
    rw [quittingRootExpectedPayoff_pair_active reward continuation _ 0 1 _
        (by decide) (pair_active _),
      quittingRootExpectedPayoff_pair_active reward continuation _ 0 1 _
        (by decide) (pair_active _)] <;>
    simp [hazardOfRoot, continuation, reward] <;>
    norm_num +decide <;> ring

/-- Exact endpoint complementarity classifies every product root, not merely
the symmetric slice: both Quit rates are simultaneously `0`, `1 / 3`, or
`1`. -/
theorem exactRoot_hazards_classification (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward continuation 0 root) :
    (hazardOfRoot root 0 = 0 ∧ hazardOfRoot root 1 = 0) ∨
      (hazardOfRoot root 0 = 1 / 3 ∧ hazardOfRoot root 1 = 1 / 3) ∨
      (hazardOfRoot root 0 = 1 ∧ hazardOfRoot root 1 = 1) := by
  let p0 := hazardOfRoot root 0
  let p1 := hazardOfRoot root 1
  have hp0nonneg : 0 ≤ p0 := ENNReal.toReal_nonneg
  have hp1nonneg : 0 ≤ p1 := ENNReal.toReal_nonneg
  have hp0le : p0 ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top ((root 0).coe_le_one true)
  have hp1le : p1 ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top ((root 1).coe_le_one true)
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward continuation root).2 hnash
  have h0 := hendpoint 0
  have h1 := hendpoint 1
  rw [endpointDifference_eq_otherHazard root |>.1] at h0
  rw [endpointDifference_eq_otherHazard root |>.2] at h1
  rw [Math.PMFProduct.pmfBool_false_toReal] at h0 h1
  have h0' : (1 - p0) * (-1 + 3 * p1) ≤ 0 ∧
      0 ≤ p0 * (-1 + 3 * p1) := by
    simpa [p0, p1, hazardOfRoot] using h0
  have h1' : (1 - p1) * (-1 + 3 * p0) ≤ 0 ∧
      0 ≤ p1 * (-1 + 3 * p0) := by
    simpa [p0, p1, hazardOfRoot] using h1
  by_cases hp0zero : p0 = 0
  · left
    refine ⟨hp0zero, ?_⟩
    have hp1zero : p1 = 0 := by
      rw [hp0zero] at h1'
      nlinarith [h1'.1, h1'.2]
    simpa [p1] using hp1zero
  by_cases hp0one : p0 = 1
  · right; right
    refine ⟨hp0one, ?_⟩
    have hp1one : p1 = 1 := by
      rw [hp0one] at h1'
      nlinarith [h1'.1, h1'.2]
    simpa [p1] using hp1one
  · right; left
    have hp0pos : 0 < p0 := lt_of_le_of_ne hp0nonneg (Ne.symm hp0zero)
    have hp0lt : p0 < 1 := lt_of_le_of_ne hp0le hp0one
    have hp1eq : p1 = 1 / 3 := by nlinarith [h0'.1, h0'.2]
    refine ⟨?_, by simpa [p1] using hp1eq⟩
    rw [hp1eq] at h1'
    norm_num at h1'
    have hp0third : p0 = 1 / 3 := by nlinarith [h1'.1, h1'.2]
    simpa [p0] using hp0third

/-- The successor payoff of an arbitrary product root in the regression is
the elementary two-rate polynomial. -/
theorem arbitraryRoot_successorPayoff (root : Player → PMF Bool) :
    quittingRootSuccessorPayoff reward continuation root =
      fun _ => 3 * hazardOfRoot root 0 * hazardOfRoot root 1 -
        hazardOfRoot root 0 - hazardOfRoot root 1 := by
  funext who
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_pair_active reward continuation _ 0 1 who
    (by decide) (pair_active _)]
  fin_cases who <;>
    simp [hazardOfRoot, continuation, reward] <;>
      norm_num +decide <;> ring

/-- The full exact-root successor image equals the displayed three points. -/
theorem exact_root_successor_range :
    {payoff | ∃ root : Player → PMF Bool,
      IsεQuittingRootNash reward continuation 0 root ∧
        payoff = quittingRootSuccessorPayoff reward continuation root} =
      displayedImage := by
  ext payoff
  constructor
  · rintro ⟨root, hnash, rfl⟩
    rcases exactRoot_hazards_classification root hnash with hzero | hthird | hone
    · rw [arbitraryRoot_successorPayoff]
      exact Or.inl (by funext who; simp [hzero.1, hzero.2, continuation])
    · rw [arbitraryRoot_successorPayoff]
      simp [displayedImage, hthird.1, hthird.2]
    · rw [arbitraryRoot_successorPayoff]
      exact Or.inr (Or.inr (by funext who; simp [hone.1, hone.2]; norm_num))
  · intro hpayoff
    rw [← exact_symmetric_root_successor_range] at hpayoff
    rcases hpayoff with ⟨q, hq0, hq1, hnash, rfl⟩
    exact ⟨symmetricRoot q hq0 hq1, hnash, rfl⟩

/-- The three payoffs displayed by the scalar exact-root calculation form a
nonconvex set.  This is not a statement about the full uniform-payoff set. -/
theorem not_convex_displayedImage : ¬ Convex ℝ displayedImage := by
  intro hconvex
  have hzero : continuation ∈ displayedImage := by simp [displayedImage]
  have hone : (fun _ : Player => (1 : ℝ)) ∈ displayedImage := by
    simp [displayedImage]
  have hhalf := hconvex hzero hone (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rcases hhalf with hhalf | hhalf | hhalf
  · have := congrFun hhalf 0
    norm_num [continuation] at this
  · have := congrFun hhalf 0
    norm_num [continuation] at this
  · have := congrFun hhalf 0
    norm_num [continuation] at this

/-- Consequently, the successor image of all exact product roots against the
fixed continuation is nonconvex. -/
theorem not_convex_exact_root_successor_range :
    ¬ Convex ℝ {payoff | ∃ root : Player → PMF Bool,
      IsεQuittingRootNash reward continuation 0 root ∧
        payoff = quittingRootSuccessorPayoff reward continuation root} := by
  rw [exact_root_successor_range]
  exact not_convex_displayedImage

end GameTheory.ExactRootNonconvexityRegression
