/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-!
# Coherent pure-time cap selection across one root prefix

If a suffix's complete behavioral cap is attained by a deterministic quit
time or by `Never`, the cap after prepending one product root is attained
either by quitting immediately or by shifting that same suffix time forward
one date.  In particular, `Never` shifts to `Never`.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Shifting a pure quit time through a new root means Continue now and use
the old pure quit time in the reached suffix. -/
theorem quittingPureTimeBehaviorStrategy_optionMap_succ_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (choice : Option ℕ) :
    quittingPureTimeBehaviorStrategy reward who (choice.map Nat.succ) =
      quittingRootAndContinuationDeviation reward (PMF.pure false)
        (quittingPureTimeBehaviorStrategy reward who choice) := by
  cases choice with
  | none =>
      funext time history
      cases time <;>
        simp [quittingPureTimeBehaviorStrategy,
          quittingRootAndContinuationDeviation, quittingPureTimeHazard]
  | some choice =>
      funext time history
      cases time with
      | zero =>
          simp [quittingPureTimeBehaviorStrategy,
            quittingRootAndContinuationDeviation, quittingPureTimeHazard]
      | succ time =>
          simp [quittingPureTimeBehaviorStrategy,
            quittingRootAndContinuationDeviation, quittingPureTimeHazard]

omit [DecidableEq ι] in
/-- Quitting at the new root is immediate Quit followed by the irrelevant
`Never` suffix strategy. -/
theorem quittingPureTimeBehaviorStrategy_zero_eq_rootAndNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) :
    quittingPureTimeBehaviorStrategy reward who (some 0) =
      quittingRootAndContinuationDeviation reward (PMF.pure true)
        (quittingPureTimeBehaviorStrategy reward who none) := by
  funext time history
  cases time <;>
    simp [quittingPureTimeBehaviorStrategy,
      quittingRootAndContinuationDeviation, quittingPureTimeHazard]

/-- The pure-time payoff after shifting a suffix response through one root is
the pure-Continue endpoint evaluated at that suffix response's payoff. -/
theorem quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who
            (quittingPureTimeBehaviorStrategy reward who
              (choice.map Nat.succ))) who =
      quittingRootContinuePayoff reward
        (Function.update
          (fun player => quittingTerminalPayoff reward continuation player)
          who
          (quittingTerminalPayoff reward
            (Function.update continuation who
              (quittingPureTimeBehaviorStrategy reward who choice)) who))
        root who := by
  rw [quittingPureTimeBehaviorStrategy_optionMap_succ_eq,
    quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
  rfl

/-- The pure-time response `Quit0` has exactly the root Quit endpoint payoff.
-/
theorem quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
      quittingRootQuitPayoff reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who := by
  rw [quittingPureTimeBehaviorStrategy_zero_eq_rootAndNever,
    quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
  exact quittingRootQuitPayoff_continuation_invariant reward _ _ root who

/-- Replacing a player's displayed strategy by a complete cap attainer makes
that player's literal terminal deviation debt exactly zero. -/
theorem quittingTerminalDeviationDebt_update_eq_zero_of_attainsCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (strategy : (quittingGame reward).BehaviorStrategy who)
    (hattains : quittingTerminalPayoff reward
        (Function.update profile who strategy) who =
      quittingContinuationBestResponseValue reward profile who) :
    quittingTerminalDeviationDebt reward
        (Function.update profile who strategy) who = 0 := by
  unfold quittingTerminalDeviationDebt
  rw [quittingContinuationBestResponseValue_update_self, hattains]
  ring

/-- Installing a pure-time cap after prepending one root gives a literal
nested child: the owner Continues at the new root and uses the old time in
the unchanged suffix. -/
theorem update_quittingRootThenContinuationProfile_pureTime_succ_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (owner : ι) (deadline : ℕ) :
    Function.update
        (quittingRootThenContinuationProfile reward root continuation)
        owner
        (quittingPureTimeBehaviorStrategy reward owner
          (some (deadline + 1))) =
      quittingRootThenContinuationProfile reward
        (Function.update root owner (PMF.pure false))
        (Function.update continuation owner
          (quittingPureTimeBehaviorStrategy reward owner
            (some deadline))) := by
  have hshift := quittingPureTimeBehaviorStrategy_optionMap_succ_eq
    reward owner (some deadline)
  simp only [Option.map_some, Nat.succ_eq_add_one] at hshift
  rw [hshift, update_quittingRootThenContinuationProfile_eq]

/-- A pure-time suffix cap attainer extends coherently across one literal
root: the new cap attainer is either `Quit0` or the shifted old time. -/
theorem exists_pureTimeCap_zero_or_map_succ_of_suffixAttainer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ)
    (hchoice : quittingTerminalPayoff reward
        (Function.update continuation who
          (quittingPureTimeBehaviorStrategy reward who choice)) who =
      quittingContinuationBestResponseValue reward continuation who) :
    ∃ nextChoice : Option ℕ,
      (nextChoice = some 0 ∨ nextChoice = choice.map Nat.succ) ∧
        quittingTerminalPayoff reward
            (Function.update
              (quittingRootThenContinuationProfile reward root continuation)
              who
              (quittingPureTimeBehaviorStrategy reward who nextChoice)) who =
          quittingContinuationBestResponseValue reward
            (quittingRootThenContinuationProfile reward root continuation) who := by
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let quitValue := quittingRootQuitPayoff reward base root who
  let continueValue := quittingRootContinuePayoff reward
    (Function.update base who
      (quittingContinuationBestResponseValue reward continuation who)) root who
  have hcap : quittingContinuationBestResponseValue reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      max quitValue continueValue := by
    exact quittingContinuationBestResponseValue_rootThenContinuation_eq_max
      reward root continuation who
  by_cases hcompare : continueValue ≤ quitValue
  · refine ⟨some 0, Or.inl rfl, ?_⟩
    rw [hcap, max_eq_left hcompare]
    exact quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff
      reward root continuation who
  · refine ⟨choice.map Nat.succ, Or.inr rfl, ?_⟩
    rw [hcap, max_eq_right (le_of_not_ge hcompare),
      quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff,
      hchoice]

end GameTheory
