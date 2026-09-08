import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.BehaviorFirstStoppingPairLaw
import UniformEquilibrium.Quitting.Terminal.PairAverageSurplus

/-! # Two-pair reward bounds imply nonconcentrated group exclusion -/

noncomputable section

namespace GameTheory

section FourPlayers

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

private def firstPair : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨{0, 1}, by simp⟩

private def secondPair : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨{2, 3}, by simp⟩

private def firstPairWeight : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 0]

private def secondPairWeight : Fin 4 → ℝ := ![0, 0, 1 / 2, 1 / 2]

private theorem firstPairWeight_nonneg (who : Fin 4) :
    0 ≤ firstPairWeight who := by
  fin_cases who <;> norm_num [firstPairWeight]

private theorem secondPairWeight_nonneg (who : Fin 4) :
    0 ≤ secondPairWeight who := by
  fin_cases who <;> norm_num [secondPairWeight]

private theorem sum_firstPairWeight : ∑ who, firstPairWeight who = 1 := by
  norm_num [firstPairWeight, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three]

private theorem sum_secondPairWeight : ∑ who, secondPairWeight who = 1 := by
  norm_num [secondPairWeight, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three]

private theorem firstPairWeight_le_half (who : Fin 4) :
    firstPairWeight who ≤ (1 : ℝ) / 2 := by
  fin_cases who <;> norm_num [firstPairWeight]

private theorem secondPairWeight_le_half (who : Fin 4) :
    secondPairWeight who ≤ (1 : ℝ) / 2 := by
  fin_cases who <;> norm_num [secondPairWeight]

/-- The reward-table entrance reduces group exclusion to the literal
finite-leftover inequality for the two complementary pair masses. -/
private theorem hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairFiniteLeftover
    (a b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (habL : a ≤ b + 2 * L)
    (hfirstSingletonSum :
      0 ≤ reward (quittingSingletonTerminal 0) 0 +
        reward (quittingSingletonTerminal 1) 1)
    (hsecondSingletonSum :
      0 ≤ reward (quittingSingletonTerminal 2) 2 +
        reward (quittingSingletonTerminal 3) 3)
    (hfirstAtFirst : quittingTwoCoordinateAverageSurplus reward 0 1
      (reward firstPair) ≤ a)
    (hsecondAtFirst : quittingTwoCoordinateAverageSurplus reward 2 3
      (reward firstPair) ≤ -b)
    (hfirstAtSecond : quittingTwoCoordinateAverageSurplus reward 0 1
      (reward secondPair) ≤ -b)
    (hsecondAtSecond : quittingTwoCoordinateAverageSurplus reward 2 3
      (reward secondPair) ≤ a)
    (hother : ∀ terminal, terminal ≠ firstPair → terminal ≠ secondPair →
      quittingTwoCoordinateAverageSurplus reward 0 1 (reward terminal) ≤ -L ∧
        quittingTwoCoordinateAverageSurplus reward 2 3 (reward terminal) ≤ -L)
    (hfiniteLeftover : ∀ profile : (quittingGame reward).BehaviorProfile,
      2 * Real.sqrt
          (quittingBehaviorExactFiniteFirstCoalitionMass profile firstPair *
            quittingBehaviorExactFiniteFirstCoalitionMass profile secondPair) ≤
        1 - quittingBehaviorExactFiniteFirstCoalitionMass profile firstPair -
          quittingBehaviorExactFiniteFirstCoalitionMass profile secondPair -
          quittingTerminalOutcomeMass reward profile none) :
    HasQuittingActualNonconcentratedGroupExclusion reward ((1 : ℝ) / 2) := by
  intro profile
  let x := quittingBehaviorExactFiniteFirstCoalitionMass profile firstPair
  let y := quittingBehaviorExactFiniteFirstCoalitionMass profile secondPair
  let ν := quittingTerminalOutcomeMass reward profile none
  have hx : 0 ≤ x := quittingBehaviorExactFiniteFirstCoalitionMass_nonneg profile firstPair
  have hy : 0 ≤ y := quittingBehaviorExactFiniteFirstCoalitionMass_nonneg profile secondPair
  have hν : 0 ≤ ν := (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 none
  have hleftover : 2 * Real.sqrt (x * y) ≤ 1 - x - y - ν := hfiniteLeftover profile
  have hfirstBound := quittingTwoCoordinateAverageSurplus_terminalPayoff_le
    profile 0 1 firstPair secondPair (by norm_num +decide [firstPair, secondPair])
      a (-b) (-L) hfirstAtFirst hfirstAtSecond (fun terminal hp hs => (hother terminal hp hs).1)
  have hsecondBound := quittingTwoCoordinateAverageSurplus_terminalPayoff_le
    profile 2 3 firstPair secondPair (by norm_num +decide [firstPair, secondPair])
      (-b) a (-L) hsecondAtFirst hsecondAtSecond
      (fun terminal hp hs => (hother terminal hp hs).2)
  simp_rw [← quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass]
    at hfirstBound hsecondBound
  dsimp only [x, y, ν] at hfirstBound hsecondBound hleftover hx hy hν
  by_cases hxy : x ≤ y
  · refine ⟨firstPairWeight, firstPairWeight_nonneg, sum_firstPairWeight,
      firstPairWeight_le_half, ?_⟩
    rw [show (∑ who, firstPairWeight who *
        (quittingTerminalPayoff reward profile who -
          reward (quittingSingletonTerminal who) who)) =
        quittingTwoCoordinateAverageSurplus reward 0 1
          (quittingTerminalPayoff reward profile) by
      simp [firstPairWeight, Fin.sum_univ_four,
        quittingTwoCoordinateAverageSurplus]
      ring]
    have hxSq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have hySq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    have hrootOrder : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
    have hrootProduct : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y :=
      Real.sqrt_mul hx y
    have hxRoot : x ≤ Real.sqrt (x * y) := by
      rw [hrootProduct]
      nlinarith [Real.sqrt_nonneg x]
    nlinarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    refine ⟨secondPairWeight, secondPairWeight_nonneg, sum_secondPairWeight,
      secondPairWeight_le_half, ?_⟩
    rw [show (∑ who, secondPairWeight who *
        (quittingTerminalPayoff reward profile who -
          reward (quittingSingletonTerminal who) who)) =
        quittingTwoCoordinateAverageSurplus reward 2 3
          (quittingTerminalPayoff reward profile) by
      simp [secondPairWeight, Fin.sum_univ_four,
        quittingTwoCoordinateAverageSurplus]
      ring]
    have hxSq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have hySq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    have hrootOrder : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx
    have hrootProduct : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y :=
      Real.sqrt_mul hx y
    have hyRoot : y ≤ Real.sqrt (x * y) := by
      rw [hrootProduct]
      nlinarith [Real.sqrt_nonneg y]
    nlinarith

/-- The complete raw two-pair reward inequalities imply actual group
exclusion with the uniform coordinate cap one half. -/
theorem hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds
    (a b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (habL : a ≤ b + 2 * L)
    (hfirstSingletonSum :
      0 ≤ reward (quittingSingletonTerminal 0) 0 +
        reward (quittingSingletonTerminal 1) 1)
    (hsecondSingletonSum :
      0 ≤ reward (quittingSingletonTerminal 2) 2 +
        reward (quittingSingletonTerminal 3) 3)
    (hfirstAtFirst : quittingTwoCoordinateAverageSurplus reward 0 1
      (reward ⟨{0, 1}, by simp⟩) ≤ a)
    (hsecondAtFirst : quittingTwoCoordinateAverageSurplus reward 2 3
      (reward ⟨{0, 1}, by simp⟩) ≤ -b)
    (hfirstAtSecond : quittingTwoCoordinateAverageSurplus reward 0 1
      (reward ⟨{2, 3}, by simp⟩) ≤ -b)
    (hsecondAtSecond : quittingTwoCoordinateAverageSurplus reward 2 3
      (reward ⟨{2, 3}, by simp⟩) ≤ a)
    (hother : ∀ terminal,
      terminal ≠ (⟨{0, 1}, by simp⟩ : {S : Finset (Fin 4) // S.Nonempty}) →
      terminal ≠ (⟨{2, 3}, by simp⟩ : {S : Finset (Fin 4) // S.Nonempty}) →
      quittingTwoCoordinateAverageSurplus reward 0 1 (reward terminal) ≤ -L ∧
        quittingTwoCoordinateAverageSurplus reward 2 3 (reward terminal) ≤ -L) :
    HasQuittingActualNonconcentratedGroupExclusion reward ((1 : ℝ) / 2) := by
  exact hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairFiniteLeftover
    a b L hb hL habL hfirstSingletonSum hsecondSingletonSum hfirstAtFirst
      hsecondAtFirst hfirstAtSecond hsecondAtSecond hother
      quittingBehaviorTwoDisjointPairMasses_finiteLeftover_ge_two_sqrt_mul

/-- The same reward-table inequalities imply the equivalent bounded-calendar
raw group-exclusion predicate. -/
theorem hasQuittingFiniteCalendarRawNonconcentratedGroupExclusion_half_of_twoPairRewardBounds
    (a b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (habL : a ≤ b + 2 * L)
    (hfirstSingletonSum :
      0 ≤ reward (quittingSingletonTerminal 0) 0 +
        reward (quittingSingletonTerminal 1) 1)
    (hsecondSingletonSum :
      0 ≤ reward (quittingSingletonTerminal 2) 2 +
        reward (quittingSingletonTerminal 3) 3)
    (hfirstAtFirst : quittingTwoCoordinateAverageSurplus reward 0 1
      (reward ⟨{0, 1}, by simp⟩) ≤ a)
    (hsecondAtFirst : quittingTwoCoordinateAverageSurplus reward 2 3
      (reward ⟨{0, 1}, by simp⟩) ≤ -b)
    (hfirstAtSecond : quittingTwoCoordinateAverageSurplus reward 0 1
      (reward ⟨{2, 3}, by simp⟩) ≤ -b)
    (hsecondAtSecond : quittingTwoCoordinateAverageSurplus reward 2 3
      (reward ⟨{2, 3}, by simp⟩) ≤ a)
    (hother : ∀ terminal,
      terminal ≠ (⟨{0, 1}, by simp⟩ : {S : Finset (Fin 4) // S.Nonempty}) →
      terminal ≠ (⟨{2, 3}, by simp⟩ : {S : Finset (Fin 4) // S.Nonempty}) →
      quittingTwoCoordinateAverageSurplus reward 0 1 (reward terminal) ≤ -L ∧
        quittingTwoCoordinateAverageSurplus reward 2 3 (reward terminal) ≤ -L) :
    HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
      reward ((1 : ℝ) / 2) := by
  rw [hasQuittingFiniteCalendarRawNonconcentratedGroupExclusion_iff_actual]
  exact hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds
    a b L hb hL habL hfirstSingletonSum hsecondSingletonSum hfirstAtFirst
      hsecondAtFirst hfirstAtSecond hsecondAtSecond hother

end FourPlayers

end GameTheory
