import UniformEquilibrium.Quitting.Root.RationalFiniteWordSemantics

/-! # Executable rational quitting-root grid selection

This module specializes the executable finite Boolean-game grid search to a
rational quitting row.  Its output remains a `RationalQuittingRoot`; the real
`PMF` interpretation is used only by the semantic correctness theorems.
-/

namespace GameTheory

open GameTheory.Finite

variable {players : ℕ}

/-- Package the probability vector returned by the Boolean grid search as a
rational quitting root. -/
def rationalQuittingRootGridSelector
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (accuracy : ℚ)
    (hsuccess : (rationalBooleanRootGridSearch?
      (rationalQuittingBooleanPayoff reward tail) accuracy).isSome = true) :
    RationalQuittingRoot players where
  probability := rationalBooleanRootGridSelector
    (rationalQuittingBooleanPayoff reward tail) accuracy hsuccess
  nonnegative := by
    intro who
    exact (rationalBooleanGridProbability_mem_unitInterval
      (rationalBooleanGridResolution
        (rationalQuittingBooleanPayoff reward tail) accuracy)
      ((rationalBooleanRootGridSearch?
        (rationalQuittingBooleanPayoff reward tail) accuracy).get hsuccess) who).1
  le_one := by
    intro who
    exact (rationalBooleanGridProbability_mem_unitInterval
      (rationalBooleanGridResolution
        (rationalQuittingBooleanPayoff reward tail) accuracy)
      ((rationalBooleanRootGridSearch?
        (rationalQuittingBooleanPayoff reward tail) accuracy).get hsuccess) who).2

/-- Positive rational accuracy proves that the executable quitting-root search
has a result.  Finite-game Nash existence is used only in this erased proof. -/
theorem rationalQuittingRootGridSearch_isSome_of_pos
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    (rationalBooleanRootGridSearch?
      (rationalQuittingBooleanPayoff reward tail) accuracy).isSome = true :=
  rationalBooleanRootGridSearch_isSome_of_pos
    (rationalQuittingBooleanPayoff reward tail) accuracy haccuracy

/-- Rational Boolean regret is exactly the actual quitting-root coordinate
Nash defect after casting to the real semantics. -/
theorem quittingRootCoordinateNashDefect_rationalQuitting_eq_cast
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (root : RationalQuittingRoot players) (who : Fin players) :
    quittingRootCoordinateNashDefect (rationalQuittingRewardToReal reward)
        (fun player => (tail player : ℝ)) root.toPMF who =
      (rationalBooleanNashRegret (rationalQuittingBooleanPayoff reward tail)
        root.probability who : ℝ) := by
  have hquit := quittingRootPurePayoff_rationalQuitting_eq_cast
    reward tail root who true
  have hcontinue := quittingRootPurePayoff_rationalQuitting_eq_cast
    reward tail root who false
  have hprescribed := quittingRootExpectedPayoff_rationalQuitting_eq_cast
    reward tail root who
  simp only [if_true] at hquit
  simp only [Bool.false_eq_true, if_false] at hcontinue
  rw [quittingRootCoordinateNashDefect, quittingRootSuccessorPayoff,
    hquit, hcontinue, hprescribed]
  simp only [rationalBooleanNashRegret, Rat.cast_sub, Rat.cast_max]
  rw [max_comm]
  rfl

/-- Exact cast bridge for the total acceptance quantity used by the auxiliary
debt ledger. -/
theorem quittingRootTotalNashDefect_rationalQuitting_eq_cast
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (root : RationalQuittingRoot players) :
    quittingRootTotalNashDefect (rationalQuittingRewardToReal reward)
        (fun player => (tail player : ℝ)) root.toPMF =
      (rationalBooleanTotalNashDefect
        (rationalQuittingBooleanPayoff reward tail) root.probability : ℝ) := by
  have hregretNonnegative (who : Fin players) :
      0 ≤ rationalBooleanNashRegret
        (rationalQuittingBooleanPayoff reward tail) root.probability who := by
    have hactual := quittingRootCoordinateNashDefect_nonneg
      (rationalQuittingRewardToReal reward)
      (fun player => (tail player : ℝ)) root.toPMF who
    rw [quittingRootCoordinateNashDefect_rationalQuitting_eq_cast] at hactual
    exact_mod_cast hactual
  rw [quittingRootTotalNashDefect, rationalBooleanTotalNashDefect]
  push_cast
  apply Finset.sum_congr rfl
  intro who _
  rw [quittingRootCoordinateNashDefect_rationalQuitting_eq_cast]
  apply Eq.symm
  rw [max_eq_left]
  exact_mod_cast hregretNonnegative who

/-- The selected executable grid root has actual total Nash defect at most the
requested rational accuracy. -/
theorem rationalQuittingRootGridSelector_totalNashDefect_le
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (accuracy : ℚ)
    (hsuccess : (rationalBooleanRootGridSearch?
      (rationalQuittingBooleanPayoff reward tail) accuracy).isSome = true) :
    quittingRootTotalNashDefect (rationalQuittingRewardToReal reward)
        (fun player => (tail player : ℝ))
        (rationalQuittingRootGridSelector reward tail accuracy hsuccess).toPMF ≤
      (accuracy : ℝ) := by
  rw [quittingRootTotalNashDefect_rationalQuitting_eq_cast]
  exact_mod_cast rationalBooleanRootGridSelector_totalNashDefect_le
    (rationalQuittingBooleanPayoff reward tail) accuracy hsuccess

end GameTheory
