import MathUE.Probability.OverlappingFirstStoppingInfiniteRecurrence
import UniformEquilibrium.Quitting.Paths.OverlappingPairSharpProfiles

/-! # Exact boundary and false-generalization examples for overlapping first quitters -/

noncomputable section

namespace GameTheory.OverlappingFirstStoppingBoundary

open Math.Probability.DiscreteHazard
open Math.Probability.DiscreteHazard.StoppingLaw
open OverlappingPairSharpProfiles

/-- Three independent stationary clocks with stopping probability one half. -/
def halfHazard : ScalarHazard where
  stop _ := 1 / 2
  stop_nonneg _ := by norm_num
  stop_le_one _ := by norm_num

theorem halfHazard_shift (start : ℕ) : halfHazard.shift start = halfHazard := by
  apply ScalarHazard.eq_of_stop_eq
  rfl

/-- The infinite law is computed by the exact recurrence, not a truncated sum. -/
theorem stationary_halfHazard_firstMass :
    equalFirstSecondBeforeThirdMass halfHazard.stoppingLaw
      halfHazard.stoppingLaw halfHazard.stoppingLaw = 1 / 7 := by
  have h := ScalarHazard.equalFirstSecondBeforeThirdTailMass_succ
    halfHazard halfHazard halfHazard 0
  simp only [ScalarHazard.equalFirstSecondBeforeThirdTailMass, halfHazard_shift] at h
  norm_num [halfHazard] at h ⊢
  linarith

theorem stationary_halfHazard_secondMass :
    equalFirstThirdBeforeSecondMass halfHazard.stoppingLaw
      halfHazard.stoppingLaw halfHazard.stoppingLaw = 1 / 7 :=
  stationary_halfHazard_firstMass

theorem stationary_halfHazard_sqrt_sum_lt_one :
    Real.sqrt (equalFirstSecondBeforeThirdMass halfHazard.stoppingLaw
        halfHazard.stoppingLaw halfHazard.stoppingLaw) +
      Real.sqrt (equalFirstThirdBeforeSecondMass halfHazard.stoppingLaw
        halfHazard.stoppingLaw halfHazard.stoppingLaw) < 1 := by
  rw [stationary_halfHazard_firstMass, stationary_halfHazard_secondMass]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hn := Real.sqrt_nonneg (1 / 7 : ℝ)
  nlinarith

/-- The immediate two winning masses and the all-Continue mass are all one eighth. -/
theorem halfHazard_current_row :
    ((1 / 2 : ℝ) * (1 / 2) * (1 - 1 / 2),
      (1 / 2 : ℝ) * (1 / 2) * (1 - 1 / 2),
      (1 - 1 / 2 : ℝ) * (1 - 1 / 2) * (1 - 1 / 2)) =
        (1 / 8, 1 / 8, 1 / 8) := by norm_num

/-- Taking a separate square root of the continuation mass breaks the naive ledger. -/
theorem naive_three_root_ledger_fails :
    1 < Real.sqrt (1 / 8 : ℝ) + Real.sqrt (1 / 8 : ℝ) + Real.sqrt (1 / 8 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hn := Real.sqrt_nonneg (1 / 8 : ℝ)
  nlinarith

/-- Denominator-twelve clocks on dates zero, one, two, and Never. -/
def denominatorTwelveLaws : Fin 4 → PMF (Option ℕ)
  | 0 => PMF.pure (some 2)
  | 1 => stopOrNever 2 (1 / 12) (by norm_num) (by norm_num)
  | 2 => stopOrNever 2 (11 / 12) (by norm_num) (by norm_num)
  | 3 => PMF.pure none

theorem denominatorTwelve_finite_and_never_atoms :
    finiteMass (denominatorTwelveLaws 0) 2 = 1 ∧
      finiteMass (denominatorTwelveLaws 1) 2 = 1 / 12 ∧
      (denominatorTwelveLaws 1 none).toReal = 11 / 12 ∧
      finiteMass (denominatorTwelveLaws 2) 2 = 11 / 12 ∧
      (denominatorTwelveLaws 2 none).toReal = 1 / 12 := by
  simp [denominatorTwelveLaws, finiteMass, stopOrNever, PMF.map_apply]
  norm_num

theorem denominatorTwelve_firstMass :
    exactFiniteFirstStoppingCoalitionMass denominatorTwelveLaws firstPair = 1 / 144 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  rw [tsum_eq_single 2]
  · simp only [firstPair]
    have hout : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    rw [hout]
    simp [denominatorTwelveLaws, stopOrNever, finiteMass, survival,
      PMF.map_apply, Finset.sum_range_succ]
    norm_num
  · intro time htime
    simp [denominatorTwelveLaws, firstPair, stopOrNever, finiteMass, PMF.map_apply, htime]

theorem denominatorTwelve_secondMass :
    exactFiniteFirstStoppingCoalitionMass denominatorTwelveLaws secondPair = 121 / 144 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  rw [tsum_eq_single 2]
  · simp only [secondPair]
    have hout : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
    rw [hout]
    simp [denominatorTwelveLaws, stopOrNever, finiteMass, survival,
      PMF.map_apply, Finset.sum_range_succ]
    norm_num
  · intro time htime
    simp [denominatorTwelveLaws, secondPair, stopOrNever, finiteMass, PMF.map_apply, htime]

theorem denominatorTwelve_sqrt_sum_eq_one :
    Real.sqrt (exactFiniteFirstStoppingCoalitionMass denominatorTwelveLaws firstPair) +
      Real.sqrt (exactFiniteFirstStoppingCoalitionMass denominatorTwelveLaws secondPair) = 1 := by
  rw [denominatorTwelve_firstMass, denominatorTwelve_secondMass]
  norm_num [Real.sqrt_div]

/-- One sure quitter and one independent half-probability quitter at the same date. -/
def nestedCoalitionLaws : Fin 2 → PMF (Option ℕ)
  | 0 => PMF.pure (some 0)
  | 1 => stopOrNever 0 (1 / 2) (by norm_num) (by norm_num)

def singletonCoalition : {C : Finset (Fin 2) // C.Nonempty} := ⟨{0}, by simp⟩

def doubleCoalition : {C : Finset (Fin 2) // C.Nonempty} := ⟨{0, 1}, by simp⟩

theorem nestedCoalition_strict_subset :
    singletonCoalition.1 ⊂ doubleCoalition.1 := by decide

theorem nestedCoalition_singletonMass :
    exactFiniteFirstStoppingCoalitionMass nestedCoalitionLaws singletonCoalition = 1 / 2 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  rw [tsum_eq_single 0]
  · simp only [singletonCoalition]
    have hout : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
    rw [hout]
    simp [nestedCoalitionLaws, stopOrNever, finiteMass, survival, PMF.map_apply]
    norm_num
  · intro time htime
    simp [nestedCoalitionLaws, singletonCoalition, finiteMass, htime]

theorem nestedCoalition_doubleMass :
    exactFiniteFirstStoppingCoalitionMass nestedCoalitionLaws doubleCoalition = 1 / 2 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  rw [tsum_eq_single 0]
  · simp only [doubleCoalition]
    have hout : ({0, 1} : Finset (Fin 2))ᶜ = ∅ := by decide
    rw [hout]
    simp [nestedCoalitionLaws, stopOrNever, finiteMass, survival, PMF.map_apply]
  · intro time htime
    simp [nestedCoalitionLaws, doubleCoalition, finiteMass, htime]

/-- Incomparability cannot be removed from the coalition square-root law. -/
theorem nestedCoalition_sqrt_sum_gt_one :
    1 < Real.sqrt (exactFiniteFirstStoppingCoalitionMass
        nestedCoalitionLaws singletonCoalition) +
      Real.sqrt (exactFiniteFirstStoppingCoalitionMass
        nestedCoalitionLaws doubleCoalition) := by
  rw [nestedCoalition_singletonMass, nestedCoalition_doubleMass]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hn := Real.sqrt_nonneg (1 / 2 : ℝ)
  nlinarith

/-- The exact one-row objective, including its residual event split. -/
def rowRootSum (first second third futureFirst futureSecond : ℝ) : ℝ :=
  Real.sqrt (first * second * (1 - third) +
      (1 - first) * (1 - second) * (1 - third) * futureFirst) +
    Real.sqrt (first * third * (1 - second) +
      (1 - first) * (1 - second) * (1 - third) * futureSecond)

/-- The all-zero row preserves every future boundary point, including the interior. -/
theorem all_zero_row_boundary (futureFirst futureSecond : ℝ)
    (hboundary : Real.sqrt futureFirst + Real.sqrt futureSecond = 1) :
    rowRootSum 0 0 0 futureFirst futureSecond = 1 := by
  simpa [rowRootSum] using hboundary

/-- A zero common hazard alone does not preserve boundary equality. -/
theorem zero_common_hazard_strict_loss : rowRootSum 0 (1 / 2) 0 1 0 < 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hn := Real.sqrt_nonneg (1 / 2 : ℝ)
  have hroot : Real.sqrt (1 / 2 : ℝ) < 1 := by nlinarith
  convert hroot using 1
  norm_num [rowRootSum]

/-- Nor do zero exclusive hazards with a nonzero common hazard preserve equality. -/
theorem zero_exclusive_hazards_strict_loss : rowRootSum (1 / 2) 0 0 1 0 < 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hn := Real.sqrt_nonneg (1 / 2 : ℝ)
  have hroot : Real.sqrt (1 / 2 : ℝ) < 1 := by nlinarith
  convert hroot using 1
  norm_num [rowRootSum]

end GameTheory.OverlappingFirstStoppingBoundary
