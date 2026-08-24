/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.HazardSummability
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel

/-!
# A two-player obstruction to persistent exact Nash--Bellman selection

Two persistent marginal Quit streams cannot be selected on every exact
Nash--Bellman spine, even when there are exactly two players.

For the reward table below, player `true` receives `-1` whenever it belongs to
the terminal quitting coalition and `1` when player `false` quits alone.
Player `false` receives zero.  Vanishing joint survival identifies every
bounded exact Bellman value with the literal terminal payoff, hence keeps
player `true`'s continuation value above `-1`.  At any date where player
`true` quits with positive probability, exact Nash forces player `false`'s
Quit probability to vanish and pins the next value of `true` to `-1`.  Once
that lower boundary is reached, the same conclusion propagates forever.
Thus the `false` hazard has finite support, contradicting persistence of both
labels.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped BigOperators Topology

/-- Exact bounded Nash--Bellman data whose same literal roots carry two
persistent marginal labels. -/
structure PersistentTwoLabelNashBellmanAnswer
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  value : ℕ → Payoff ι
  roots : ℕ → ι → PMF Bool
  value_bound : ∀ time who,
    |value time who| ≤ quittingRewardBound reward
  bellman : ∀ time,
    value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time)
  nash : ∀ time,
    IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)
  persistent : HasTwoPersistentQuittingMarginals roots

/-- Player `true` loses whenever it quits; it gains when only player `false`
quits.  Player `false` is strategically irrelevant. -/
def persistentTwoLabelCounterexampleReward :
    {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun terminal who =>
    if who then
      if true ∈ terminal.1 then -1 else 1
    else 0

private theorem abs_persistentTwoLabelCounterexampleReward_le_one
    (terminal : {S : Finset Bool // S.Nonempty}) (who : Bool) :
    |persistentTwoLabelCounterexampleReward terminal who| ≤ 1 := by
  cases who
  · simp [persistentTwoLabelCounterexampleReward]
  · by_cases hmem : true ∈ terminal.1 <;>
      simp [persistentTwoLabelCounterexampleReward, hmem]

private theorem persistentTwoLabelCounterexample_quitPayoff
    (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff persistentTwoLabelCounterexampleReward tail root true = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [quittingRootPayoff, persistentTwoLabelCounterexampleReward]

private theorem persistentTwoLabelCounterexample_continuePayoff
    (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff persistentTwoLabelCounterexampleReward tail root true =
      (root false true).toReal + (root false false).toReal * tail true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [quittingRootPayoff, persistentTwoLabelCounterexampleReward,
    expect_eq_sum]

private theorem persistentTwoLabelCounterexample_continuePayoff_ge_neg_one
    (tail : Payoff Bool) (root : Bool → PMF Bool)
    (htail : -1 ≤ tail true) :
    -1 ≤ quittingRootContinuePayoff
      persistentTwoLabelCounterexampleReward tail root true := by
  rw [persistentTwoLabelCounterexample_continuePayoff]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hquit : 0 ≤ (root false true).toReal := ENNReal.toReal_nonneg
  have hcontinue : 0 ≤ (root false false).toReal := ENNReal.toReal_nonneg
  have hscaled :
      0 ≤ (root false false).toReal * (tail true + 1) :=
    mul_nonneg hcontinue (by linarith)
  nlinarith

private theorem persistentTwoLabelCounterexample_forced_boundary
    (tail : Payoff Bool) (root : Bool → PMF Bool)
    (htail : -1 ≤ tail true)
    (hle : quittingRootContinuePayoff
      persistentTwoLabelCounterexampleReward tail root true ≤ -1) :
    (root false true).toReal = 0 ∧ tail true = -1 := by
  rw [persistentTwoLabelCounterexample_continuePayoff] at hle
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hquit : 0 ≤ (root false true).toReal := ENNReal.toReal_nonneg
  have hcontinue : 0 ≤ (root false false).toReal := ENNReal.toReal_nonneg
  have hscaled :
      0 ≤ (root false false).toReal * (tail true + 1) :=
    mul_nonneg hcontinue (by linarith)
  constructor
  · nlinarith
  · have hquitZero : (root false true).toReal = 0 := by nlinarith
    nlinarith

/-- The two-player reward table above admits no bounded exact Nash--Bellman
spine on which both marginal Quit streams are persistent. -/
theorem not_nonempty_persistentTwoLabelNashBellmanAnswer_counterexample :
    ¬ Nonempty
      (PersistentTwoLabelNashBellmanAnswer
        persistentTwoLabelCounterexampleReward) := by
  rintro ⟨answer⟩
  let hazard : Bool → ℕ → ℝ :=
    fun who time => quittingMarginalQuitHazard answer.roots who time
  have hpersistent := answer.persistent
  obtain ⟨hopponent, hjoint⟩ := hpersistent.survival (by decide)
  obtain ⟨first, second, hne, hfirst, hsecond⟩ := hpersistent
  have hboth :
      (¬Summable (hazard false)) ∧ (¬Summable (hazard true)) := by
    cases first <;> cases second <;> simp_all [hazard]
  have hsemantic : ∀ time,
      answer.value time true =
        quittingRootSequenceTerminalValue
          persistentTwoLabelCounterexampleReward answer.roots true time := by
    intro time
    apply quittingValue_eq_rootSequenceTerminalValue_of_tendsto_jointSurvival
      (reward := persistentTwoLabelCounterexampleReward)
      answer.roots answer.value answer.bellman true time
      (bound := quittingRewardBound persistentTwoLabelCounterexampleReward)
      (fun later => answer.value_bound later true)
      (rewardBound := 1)
      abs_persistentTwoLabelCounterexampleReward_le_one
    have heq :
        quittingRootSequenceJointSurvival answer.roots time =
          Math.survivalProduct
            (fun later => quittingStationaryContinueMass (answer.roots later))
            time := by
      funext length
      unfold quittingRootSequenceJointSurvival
      congr 1
      funext later
      unfold quittingRootSequenceAbsorptionCharge quittingRootAbsorptionMass
      ring
    rw [heq]
    exact hjoint time
  have hvalueLower : ∀ time, -1 ≤ answer.value time true := by
    intro time
    rw [hsemantic time]
    have hbound := abs_quittingRootSequenceTerminalValue_le
      persistentTwoLabelCounterexampleReward answer.roots true time
      (by norm_num) abs_persistentTwoLabelCounterexampleReward_le_one
    exact (abs_le.mp hbound).1
  have hboundaryStep : ∀ time,
      answer.value time true = -1 →
        (answer.roots time false true).toReal = 0 ∧
          answer.value (time + 1) true = -1 := by
    intro time hvalue
    have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
      persistentTwoLabelCounterexampleReward (answer.value (time + 1))
      (answer.roots time) true (answer.nash time)
    rw [← congrFun (answer.bellman time) true, hvalue] at hcontinue
    exact persistentTwoLabelCounterexample_forced_boundary
      (answer.value (time + 1)) (answer.roots time)
      (hvalueLower (time + 1)) hcontinue
  have htriggerStep : ∀ time,
      0 < (answer.roots time true true).toReal →
        (answer.roots time false true).toReal = 0 ∧
          answer.value (time + 1) true = -1 := by
    intro time hpositive
    let continueValue := quittingRootContinuePayoff
      persistentTwoLabelCounterexampleReward (answer.value (time + 1))
        (answer.roots time) true
    have hcontinueLower : -1 ≤ continueValue :=
      persistentTwoLabelCounterexample_continuePayoff_ge_neg_one
        (answer.value (time + 1)) (answer.roots time)
        (hvalueLower (time + 1))
    have hcontinueLe := quittingRootContinuePayoff_le_successor_of_isZeroNash
      persistentTwoLabelCounterexampleReward (answer.value (time + 1))
      (answer.roots time) true (answer.nash time)
    have hmix := quittingRootSuccessorPayoff_eq_endpointMix
      persistentTwoLabelCounterexampleReward (answer.value (time + 1))
      (answer.roots time) true
    rw [persistentTwoLabelCounterexample_quitPayoff] at hmix
    change quittingRootSuccessorPayoff
        persistentTwoLabelCounterexampleReward (answer.value (time + 1))
          (answer.roots time) true =
      (answer.roots time true true).toReal * -1 +
        (answer.roots time true false).toReal * continueValue at hmix
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (answer.roots time) true
    have hcontinueProbability :
        (answer.roots time true false).toReal =
          1 - (answer.roots time true true).toReal := by
      linarith
    rw [hcontinueProbability] at hmix
    have hscaled :
        0 ≤ (answer.roots time true true).toReal * (continueValue + 1) :=
      mul_nonneg hpositive.le (by linarith)
    have hgap :
        (answer.roots time true true).toReal * (continueValue + 1) ≤ 0 := by
      nlinarith
    have hcontinueUpper : continueValue ≤ -1 := by
      nlinarith
    exact persistentTwoLabelCounterexample_forced_boundary
      (answer.value (time + 1)) (answer.roots time)
      (hvalueLower (time + 1)) hcontinueUpper
  have hexists : ∃ time,
      0 < (answer.roots time true true).toReal := by
    by_contra hnot
    have hnonpos : ∀ time,
        (answer.roots time true true).toReal ≤ 0 := by
      intro time
      exact not_lt.mp (not_exists.mp hnot time)
    have hzero : hazard true = 0 := by
      funext time
      apply le_antisymm
      · exact hnonpos time
      · exact quittingMarginalQuitHazard_nonneg answer.roots true time
    exact hboth.2 (by rw [hzero]; exact summable_zero)
  obtain ⟨start, hstart⟩ := hexists
  have hnext := (htriggerStep start hstart).2
  let base := start + 1
  have hvalueTail : ∀ offset,
      answer.value (base + offset) true = -1 := by
    intro offset
    induction offset with
    | zero => simpa [base] using hnext
    | succ offset ih =>
        have hstep := (hboundaryStep (base + offset) ih).2
        simpa [Nat.add_assoc] using hstep
  have hzeroTail : ∀ offset,
      hazard false (offset + base) = 0 := by
    intro offset
    have hstep := (hboundaryStep (base + offset) (hvalueTail offset)).1
    simpa [hazard, quittingMarginalQuitHazard, Nat.add_comm] using hstep
  have hsuffix : Summable (fun offset => hazard false (offset + base)) := by
    have hfun : (fun offset => hazard false (offset + base)) = 0 := by
      funext offset
      exact hzeroTail offset
    rw [hfun]
    exact summable_zero
  exact hboth.1 ((summable_nat_add_iff base).1 hsuffix)

/-- Consequently, the proposed universal persistent-selector statement is
false even after imposing the necessary cardinality hypothesis. -/
theorem not_forall_persistentTwoLabelNashBellmanAnswer :
    ¬ (∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      2 ≤ Fintype.card ι →
      ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
        Nonempty (PersistentTwoLabelNashBellmanAnswer reward)) := by
  intro hall
  exact not_nonempty_persistentTwoLabelNashBellmanAnswer_counterexample
    (hall Bool (by decide) persistentTwoLabelCounterexampleReward)

end GameTheory
