/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.NashBellmanChronologicalForcing
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel

/-!
# Two-player obstruction to persistent exact Nash--Bellman labels

This scratch module develops the explicit two-player counterexample used to
refute universal persistent-two-label selection.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

/-- Player `true` gets `-1` whenever they quit and `1` whenever only opponents
quit. Player `false` is payoff-neutral. -/
def persistentTwoLabelCounterexampleReward
    (terminal : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if who = true then
      if true ∈ terminal.1 then -1 else 1
    else 0

private def persistentTwoLabelAction
    (observerQuits otherQuits : Bool) : Bool → Bool
  | false => otherQuits
  | true => observerQuits

private theorem expect_update_true_pure
    (root : Bool → PMF Bool) (observerAction : Bool)
    (payoff : (Bool → Bool) → ℝ) :
    expect (pmfPi (Function.update root true (PMF.pure observerAction))) payoff =
      expect (root false) (fun otherAction =>
        payoff (persistentTwoLabelAction observerAction otherAction)) := by
  have hfamily :
      Function.update root true (PMF.pure observerAction) =
        Function.update
          (Function.update root true (PMF.pure observerAction))
          false (root false) := by
    funext player
    cases player <;> simp
  rw [hfamily, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (root false))
  funext otherAction
  have hpure :
      Function.update
          (Function.update root true (PMF.pure observerAction))
          false (PMF.pure otherAction) =
        fun player =>
          PMF.pure
            (persistentTwoLabelAction observerAction otherAction player) := by
    funext player
    cases player <;> simp [persistentTwoLabelAction]
  rw [hpure, pmfPi_pure, expect_pure]

@[simp] theorem quittingRootQuitPayoff_persistentTwoLabelCounterexample
    (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff persistentTwoLabelCounterexampleReward
        tail root true = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_update_true_pure]
  calc
    expect (root false) (fun otherAction =>
        quittingRootPayoff persistentTwoLabelCounterexampleReward tail
          (persistentTwoLabelAction true otherAction) true) =
      expect (root false) (fun _ => (-1 : ℝ)) := by
        apply congrArg (expect (root false))
        funext otherAction
        cases otherAction <;>
          simp [quittingRootPayoff, quittingQuitters,
            persistentTwoLabelCounterexampleReward,
            persistentTwoLabelAction]
    _ = -1 := expect_const _ _

@[simp] theorem quittingRootContinuePayoff_persistentTwoLabelCounterexample
    (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff persistentTwoLabelCounterexampleReward
        tail root true =
      (root false false).toReal * tail true +
        (root false true).toReal := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_update_true_pure]
  calc
    expect (root false) (fun otherAction =>
        quittingRootPayoff persistentTwoLabelCounterexampleReward tail
          (persistentTwoLabelAction false otherAction) true) =
      expect (root false) (fun otherAction =>
        if otherAction = true then 1 else tail true) := by
          apply congrArg (expect (root false))
          funext otherAction
          cases otherAction <;>
            simp [quittingRootPayoff, quittingQuitters,
              persistentTwoLabelCounterexampleReward,
              persistentTwoLabelAction]
    _ = (root false false).toReal * tail true +
        (root false true).toReal := by
      rw [expect_eq_sum, Fintype.sum_bool]
      simp

/-- The designated observer's continuation premium is the sum of twice the
other player's Quit mass and the surviving shifted continuation value. -/
theorem quittingRootContinuePayoff_add_one_persistentTwoLabelCounterexample
    (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff persistentTwoLabelCounterexampleReward
          tail root true + 1 =
      2 * (root false true).toReal +
        (root false false).toReal * (tail true + 1) := by
  rw [quittingRootContinuePayoff_persistentTwoLabelCounterexample]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  rw [← hsum]
  ring

/-- No exact Nash--Bellman spine for this two-player game can carry two
persistent marginal labels. Boundedness is not needed. -/
theorem not_exists_persistentTwoLabelExactNashBellmanSpine :
    ¬ ∃ (value : ℕ → Payoff Bool)
        (roots : ℕ → Bool → PMF Bool),
      (∀ time,
        value time = quittingRootSuccessorPayoff
          persistentTwoLabelCounterexampleReward
          (value (time + 1)) (roots time)) ∧
      (∀ time,
        IsεQuittingRootNash persistentTwoLabelCounterexampleReward
          (value (time + 1)) 0 (roots time)) ∧
      HasTwoPersistentQuittingMarginals roots := by
  rintro ⟨value, roots, hbellman, hnash, hpersistent⟩
  have hvalueLower : ∀ time, -1 ≤ value time true := by
    intro time
    calc
      (-1 : ℝ) = quittingRootQuitPayoff
          persistentTwoLabelCounterexampleReward
          (value (time + 1)) (roots time) true := by simp
      _ ≤ quittingRootSuccessorPayoff
          persistentTwoLabelCounterexampleReward
          (value (time + 1)) (roots time) true :=
        quittingRootQuitPayoff_le_successor_of_isZeroNash
          persistentTwoLabelCounterexampleReward
          (value (time + 1)) (roots time) true (hnash time)
      _ = value time true := (congrFun (hbellman time) true).symm
  have hcontinueNonneg : ∀ time,
      0 ≤ quittingRootContinuePayoff
          persistentTwoLabelCounterexampleReward
          (value (time + 1)) (roots time) true + 1 := by
    intro time
    rw [quittingRootContinuePayoff_add_one_persistentTwoLabelCounterexample]
    exact add_nonneg
      (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      (mul_nonneg ENNReal.toReal_nonneg (by
        linarith [hvalueLower (time + 1)]))
  have hzeroContinue : ∀ time,
      quittingRootContinuePayoff
            persistentTwoLabelCounterexampleReward
            (value (time + 1)) (roots time) true + 1 = 0 →
        (roots time false true).toReal = 0 ∧
          value (time + 1) true + 1 = 0 := by
    intro time hzero
    have hshift :=
      quittingRootContinuePayoff_add_one_persistentTwoLabelCounterexample
        (value (time + 1)) (roots time)
    have hquitNonneg : 0 ≤ (roots time false true).toReal :=
      ENNReal.toReal_nonneg
    have hcontinueNonneg' : 0 ≤ (roots time false false).toReal :=
      ENNReal.toReal_nonneg
    have hnextNonneg : 0 ≤ value (time + 1) true + 1 := by
      linarith [hvalueLower (time + 1)]
    have hproductNonneg :
        0 ≤ (roots time false false).toReal *
          (value (time + 1) true + 1) :=
      mul_nonneg hcontinueNonneg' hnextNonneg
    have hquitZero : (roots time false true).toReal = 0 := by
      nlinarith
    have hsum :=
      quittingRoot_continueProbability_add_quitProbability
        (roots time) false
    have hcontinueOne : (roots time false false).toReal = 1 := by
      nlinarith
    have hnextZero : value (time + 1) true + 1 = 0 := by
      nlinarith
    exact ⟨hquitZero, hnextZero⟩
  have hstepOfObserverQuit : ∀ time,
      0 < quittingMarginalQuitHazard roots true time →
        (roots time false true).toReal = 0 ∧
          value (time + 1) true + 1 = 0 := by
    intro time hpositive
    have hendpoint :
        IsεQuittingRootEndpointNash
          persistentTwoLabelCounterexampleReward
          (value (time + 1)) 0 (roots time) :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        persistentTwoLabelCounterexampleReward
        (value (time + 1)) (roots time)).2 (hnash time)
    have hdifference := (hendpoint true).2
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_persistentTwoLabelCounterexample] at hdifference
    have hpositive' : 0 < (roots time true true).toReal := by
      simpa [quittingMarginalQuitHazard] using hpositive
    have hupper :
        quittingRootContinuePayoff
            persistentTwoLabelCounterexampleReward
            (value (time + 1)) (roots time) true + 1 ≤ 0 := by
      nlinarith
    have hzero :
        quittingRootContinuePayoff
            persistentTwoLabelCounterexampleReward
            (value (time + 1)) (roots time) true + 1 = 0 :=
      le_antisymm hupper (hcontinueNonneg time)
    exact hzeroContinue time hzero
  have hstepOfZeroValue : ∀ time,
      value time true + 1 = 0 →
        (roots time false true).toReal = 0 ∧
          value (time + 1) true + 1 = 0 := by
    intro time hvalueZero
    by_cases hquitZero : (roots time true true).toReal = 0
    · have hmix :=
        quittingRootSuccessorPayoff_eq_endpointMix
          persistentTwoLabelCounterexampleReward
          (value (time + 1)) (roots time) true
      rw [quittingRootQuitPayoff_persistentTwoLabelCounterexample] at hmix
      have hcurrent := congrFun (hbellman time) true
      have hsum :=
        quittingRoot_continueProbability_add_quitProbability
          (roots time) true
      have hcontinueZero :
          quittingRootContinuePayoff
              persistentTwoLabelCounterexampleReward
              (value (time + 1)) (roots time) true + 1 = 0 := by
        nlinarith
      exact hzeroContinue time hcontinueZero
    · have hpositive : 0 < (roots time true true).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg hquitZero.symm
      exact hstepOfObserverQuit time (by
        simpa [quittingMarginalQuitHazard] using hpositive)
  obtain ⟨first, second, hne, hfirst, hsecond⟩ := hpersistent
  have hboth :
      (¬Summable (quittingMarginalQuitHazard roots false)) ∧
        ¬Summable (quittingMarginalQuitHazard roots true) := by
    cases first with
    | false =>
        cases second with
        | false => exact False.elim (hne rfl)
        | true => exact ⟨hfirst, hsecond⟩
    | true =>
        cases second with
        | false => exact ⟨hsecond, hfirst⟩
        | true => exact False.elim (hne rfl)
  have hexistsPositive :
      ∃ time, 0 < quittingMarginalQuitHazard roots true time := by
    by_contra hnone
    push_neg at hnone
    apply hboth.2
    have hzero : quittingMarginalQuitHazard roots true = 0 := by
      funext time
      exact le_antisymm (le_of_not_gt (hnone time))
        (quittingMarginalQuitHazard_nonneg roots true time)
    rw [hzero]
    exact summable_zero
  obtain ⟨time, hpositive⟩ := hexistsPositive
  have hnextZero := (hstepOfObserverQuit time hpositive).2
  have hvalueTail : ∀ offset,
      value (time + 1 + offset) true + 1 = 0 := by
    intro offset
    induction offset with
    | zero => simpa using hnextZero
    | succ offset ih =>
        simpa [Nat.add_assoc] using
          (hstepOfZeroValue (time + 1 + offset) ih).2
  have hotherTail : ∀ offset,
      quittingMarginalQuitHazard roots false
        (time + 1 + offset) = 0 := by
    intro offset
    change (roots (time + 1 + offset) false true).toReal = 0
    exact (hstepOfZeroValue (time + 1 + offset)
      (hvalueTail offset)).1
  apply hboth.1
  have hsuffix : Summable (fun offset =>
      quittingMarginalQuitHazard roots false (offset + (time + 1))) := by
    have hzero :
        (fun offset =>
          quittingMarginalQuitHazard roots false (offset + (time + 1))) = 0 := by
      funext offset
      rw [Nat.add_comm]
      exact hotherTail offset
    rw [hzero]
    exact summable_zero
  exact (summable_nat_add_iff (time + 1)).1 hsuffix

end GameTheory
