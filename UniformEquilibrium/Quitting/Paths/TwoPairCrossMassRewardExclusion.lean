import UniformEquilibrium.Quitting.Paths.TwoPairCrossMassDeterminant
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates

/-! # Reward-table entrance from the two-pair cross-mass determinant -/

noncomputable section

namespace GameTheory

private theorem quittingTerminalPayoff_sub_le_positiveMass_sub_threeMass
    {players : Type} [Fintype players] [DecidableEq players]
    {reward : {S : Finset players // S.Nonempty} → Payoff players}
    (profile : (quittingGame reward).BehaviorProfile) (who : players)
    (positive negativeFirst negativeSecond negativeThird :
      {S : Finset players // S.Nonempty})
    (a loss : ℝ) (hsingleton : 0 ≤ reward (quittingSingletonTerminal who) who)
    (hrow : ∀ terminal,
      reward terminal who - reward (quittingSingletonTerminal who) who ≤
        a * (if terminal = positive then 1 else 0) -
          loss * ((if terminal = negativeFirst then 1 else 0) +
            (if terminal = negativeSecond then 1 else 0) +
            (if terminal = negativeThird then 1 else 0))) :
    quittingTerminalPayoff reward profile who -
        reward (quittingSingletonTerminal who) who ≤
      a * quittingTerminalOutcomeMass reward profile (some positive) -
        loss * (quittingTerminalOutcomeMass reward profile (some negativeFirst) +
          quittingTerminalOutcomeMass reward profile (some negativeSecond) +
          quittingTerminalOutcomeMass reward profile (some negativeThird)) := by
  let mass := quittingTerminalOutcomeMass reward profile
  let singleton := reward (quittingSingletonTerminal who) who
  have hmoment := congrFun (quittingTerminalRewardMoment_outcomeMass reward profile) who
  have htotal := (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).2
  change (∑ outcome, mass outcome) = 1 at htotal
  have hsurplus :
      quittingTerminalPayoff reward profile who - singleton =
        ∑ outcome, mass outcome *
          (quittingTerminalOutcomeReward reward outcome who - singleton) := by
    rw [← hmoment]
    unfold quittingTerminalRewardMoment
    calc
      (∑ outcome, mass outcome *
          quittingTerminalOutcomeReward reward outcome who) - singleton =
          (∑ outcome, mass outcome *
            quittingTerminalOutcomeReward reward outcome who) -
            (∑ outcome, mass outcome) * singleton := by rw [htotal, one_mul]
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro outcome _
        ring
  rw [hsurplus]
  calc
    _ ≤ ∑ outcome, mass outcome *
        (a * (if outcome = some positive then 1 else 0) -
          loss * ((if outcome = some negativeFirst then 1 else 0) +
            (if outcome = some negativeSecond then 1 else 0) +
            (if outcome = some negativeThird then 1 else 0))) := by
      apply Finset.sum_le_sum
      intro outcome _
      apply mul_le_mul_of_nonneg_left
      · cases outcome with
        | none =>
          simpa only [quittingTerminalOutcomeReward, Pi.zero_apply, reduceCtorEq,
            if_false, zero_add, mul_zero, sub_zero, zero_sub, singleton] using
              neg_nonpos.mpr hsingleton
        | some terminal =>
          simpa only [quittingTerminalOutcomeReward, Option.some.injEq] using
            hrow terminal
      · exact (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 outcome
    _ = _ := by
      classical
      simp only [mul_sub, Finset.sum_sub_distrib, mul_add,
        Finset.sum_add_distrib]
      simp_rw [mul_ite, mul_one, mul_zero]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

/-- The literal reward inequalities in the separate-cross determinant
criterion imply weak exclusion on the two designated owners. -/
theorem hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (a b lossMinus lossPlus : ℝ)
    (hlossMinus : 0 ≤ lossMinus) (hlossPlus : 0 ≤ lossPlus)
    (hproduct : a * b ≤ lossMinus * lossPlus)
    (hzeroSingleton : 0 ≤ reward (quittingSingletonTerminal 0) 0)
    (honeSingleton : 0 ≤ reward (quittingSingletonTerminal 1) 1)
    (hzero : ∀ terminal,
      reward terminal 0 - reward (quittingSingletonTerminal 0) 0 ≤
        a * (if terminal = (⟨{0, 1}, by simp⟩ :
          {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) -
        lossMinus *
          ((if terminal = (⟨{1}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) +
            (if terminal = (⟨{2}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) +
            (if terminal = (⟨{1, 2}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0)))
    (hone : ∀ terminal,
      reward terminal 1 - reward (quittingSingletonTerminal 1) 1 ≤
        b * (if terminal = (⟨{2, 3}, by simp⟩ :
          {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) -
        lossPlus *
          ((if terminal = (⟨{0}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) +
            (if terminal = (⟨{3}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) +
            (if terminal = (⟨{0, 3}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0))) :
    HasQuittingActualWeakSubsetExclusion reward {0, 1} := by
  constructor
  · intro who hwho
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
    rcases hwho with rfl | rfl
    · exact hzeroSingleton
    · exact honeSingleton
  · intro profile
    by_cases hzeroPayoff : quittingTerminalPayoff reward profile 0 ≤
        reward (quittingSingletonTerminal 0) 0
    · exact ⟨0, by simp, hzeroPayoff⟩
    by_cases honePayoff : quittingTerminalPayoff reward profile 1 ≤
        reward (quittingSingletonTerminal 1) 1
    · exact ⟨1, by simp, honePayoff⟩
    exfalso
    let x := quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{0, 1}, by simp⟩
    let y := quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{2, 3}, by simp⟩
    let zPlus := quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{0}, by simp⟩ +
      quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{3}, by simp⟩ +
      quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{0, 3}, by simp⟩
    let zMinus := quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{1}, by simp⟩ +
      quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{2}, by simp⟩ +
      quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{1, 2}, by simp⟩
    have hx : 0 ≤ x := quittingBehaviorExactFiniteFirstCoalitionMass_nonneg _ _
    have hy : 0 ≤ y := quittingBehaviorExactFiniteFirstCoalitionMass_nonneg _ _
    have hzPlus : 0 ≤ zPlus := by
      dsimp only [zPlus]
      exact add_nonneg
        (add_nonneg
          (quittingBehaviorExactFiniteFirstCoalitionMass_nonneg _ _)
          (quittingBehaviorExactFiniteFirstCoalitionMass_nonneg _ _))
        (quittingBehaviorExactFiniteFirstCoalitionMass_nonneg _ _)
    have hzMinus : 0 ≤ zMinus := by
      dsimp only [zMinus]
      exact add_nonneg
        (add_nonneg
          (quittingBehaviorExactFiniteFirstCoalitionMass_nonneg _ _)
          (quittingBehaviorExactFiniteFirstCoalitionMass_nonneg _ _))
        (quittingBehaviorExactFiniteFirstCoalitionMass_nonneg _ _)
    have hzeroUpper := quittingTerminalPayoff_sub_le_positiveMass_sub_threeMass
      profile 0 ⟨{0, 1}, by simp⟩ ⟨{1}, by simp⟩ ⟨{2}, by simp⟩
        ⟨{1, 2}, by simp⟩ a lossMinus hzeroSingleton hzero
    have honeUpper := quittingTerminalPayoff_sub_le_positiveMass_sub_threeMass
      profile 1 ⟨{2, 3}, by simp⟩ ⟨{0}, by simp⟩ ⟨{3}, by simp⟩
        ⟨{0, 3}, by simp⟩ b lossPlus honeSingleton hone
    simp_rw [← quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass]
      at hzeroUpper honeUpper
    have hzeroPositive : 0 < quittingTerminalPayoff reward profile 0 -
        reward (quittingSingletonTerminal 0) 0 :=
      sub_pos.mpr (lt_of_not_ge hzeroPayoff)
    have honePositive : 0 < quittingTerminalPayoff reward profile 1 -
        reward (quittingSingletonTerminal 1) 1 :=
      sub_pos.mpr (lt_of_not_ge honePayoff)
    have hzeroStrict : lossMinus * zMinus < a * x := by
      dsimp only [x, zMinus] at hzeroUpper ⊢
      linarith
    have honeStrict : lossPlus * zPlus < b * y := by
      dsimp only [y, zPlus] at honeUpper ⊢
      linarith
    have hstrict :
        (lossMinus * zMinus) * (lossPlus * zPlus) < (a * x) * (b * y) :=
      calc
        _ ≤ (a * x) * (lossPlus * zPlus) :=
          mul_le_mul_of_nonneg_right hzeroStrict.le
            (mul_nonneg hlossPlus hzPlus)
        _ < _ := mul_lt_mul_of_pos_left honeStrict
          (lt_of_le_of_lt (mul_nonneg hlossMinus hzMinus) hzeroStrict)
    have hdeterminant : x * y ≤ zPlus * zMinus := by
      exact quittingBehaviorTwoPair_crossMassDeterminant profile
    have hweak : (a * b) * (x * y) ≤
        (lossMinus * lossPlus) * (zMinus * zPlus) := by
      apply mul_le_mul hproduct
      · simpa [mul_comm] using hdeterminant
      · exact mul_nonneg hx hy
      · exact mul_nonneg hlossMinus hlossPlus
    have : (lossMinus * zMinus) * (lossPlus * zPlus) <
        (lossMinus * lossPlus) * (zMinus * zPlus) := by
      calc
        _ < (a * x) * (b * y) := hstrict
        _ = (a * b) * (x * y) := by ring
        _ ≤ _ := hweak
    nlinarith

/-- The same determinant reward inequalities imply the fixed-calendar raw
weak-exclusion predicate on owners `{0,1}`. -/
theorem hasQuittingFiniteCalendarRawWeakSubsetExclusion_zero_one_of_crossMassBounds
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (a b lossMinus lossPlus : ℝ)
    (hlossMinus : 0 ≤ lossMinus) (hlossPlus : 0 ≤ lossPlus)
    (hproduct : a * b ≤ lossMinus * lossPlus)
    (hzeroSingleton : 0 ≤ reward (quittingSingletonTerminal 0) 0)
    (honeSingleton : 0 ≤ reward (quittingSingletonTerminal 1) 1)
    (hzero : ∀ terminal,
      reward terminal 0 - reward (quittingSingletonTerminal 0) 0 ≤
        a * (if terminal = (⟨{0, 1}, by simp⟩ :
          {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) -
        lossMinus *
          ((if terminal = (⟨{1}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) +
            (if terminal = (⟨{2}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) +
            (if terminal = (⟨{1, 2}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0)))
    (hone : ∀ terminal,
      reward terminal 1 - reward (quittingSingletonTerminal 1) 1 ≤
        b * (if terminal = (⟨{2, 3}, by simp⟩ :
          {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) -
        lossPlus *
          ((if terminal = (⟨{0}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) +
            (if terminal = (⟨{3}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0) +
            (if terminal = (⟨{0, 3}, by simp⟩ :
              {S : Finset (Fin 4) // S.Nonempty}) then 1 else 0))) :
    HasQuittingFiniteCalendarRawWeakSubsetExclusion reward {0, 1} := by
  rw [hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_actual]
  exact hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds
    a b lossMinus lossPlus hlossMinus hlossPlus hproduct
      hzeroSingleton honeSingleton hzero hone

end GameTheory
