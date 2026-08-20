/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling
import MathUE.Topology.FiniteLimitDecomposition

/-!
# Solo preemption and its two-rate stationary probe

For players `owner` and `other`, say that `other` preempts `owner` at margin
`gap` when `other` gains at least `gap` by quitting alone before `owner` exits
alone:

`r_other({owner}) + gap <= r_other({other})`.

The two-rate probe lets a current owner quit at rate `rate` and its supplied
predecessor at rate `rate²`.  Exact payoff and unilateral-cap formulas identify
the zero-rate limit while retaining the incoming preemption edge.  The module
contains no counterexample-regime assumption; diagnostic producers supply the
terminal gap and stationary exploitability inequality.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

/-- `other` preempts `owner` by `gap` when its own solo exit improves by at
least `gap` over receiving the payoff from `owner`'s solo exit. -/
def QuittingSoloPreempts
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (gap : ℝ) (owner other : player) : Prop :=
  other ≠ owner ∧
    quittingSoloReward reward owner other + gap ≤
      quittingSoloReward reward other other

/-- A positive-period closed directed walk in the strict solo-preemption
relation. -/
structure QuittingSoloPreemptionCycle
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (gap : ℝ) where
  period : ℕ
  period_pos : 0 < period
  vertex : ℕ → player
  vertex_periodic : ∀ time, vertex (time + period) = vertex time
  edge : ∀ time, QuittingSoloPreempts reward gap (vertex time) (vertex (time + 1))

namespace QuittingSoloPreemptionCycle

omit [Fintype player] [DecidableEq player] in
/-- Strictness rules out a one-vertex preemption cycle. -/
theorem two_le_period
    {gap : ℝ} (cycle : QuittingSoloPreemptionCycle reward gap) :
    2 ≤ cycle.period := by
  by_contra hperiod
  have hpos := cycle.period_pos
  have hone : cycle.period = 1 := by omega
  have hne := (cycle.edge 0).1
  have hperiodic := cycle.vertex_periodic 0
  rw [hone] at hperiodic
  simp only [zero_add] at hperiodic
  exact hne hperiodic

end QuittingSoloPreemptionCycle

omit [Fintype player] [DecidableEq player] in
/-- Exact algebraic defect of a convex value supported on two solo rows. -/
theorem quittingSoloRotationDefect_eq
    (preempted preemptor : player) (lam : ℝ) :
    quittingSoloReward reward preemptor preemptor -
        (lam * quittingSoloReward reward preempted preemptor +
          (1 - lam) * quittingSoloReward reward preemptor preemptor) =
      lam * (quittingSoloReward reward preemptor preemptor -
        quittingSoloReward reward preempted preemptor) := by
  ring

omit [Fintype player] [DecidableEq player] in
/-- Against a strict preemption edge, a convex value with nonnegative weight
`lam` on the preemptor's solo row under-serves the preempted player's solo
payoff by at least `lam * gap`. -/
theorem QuittingSoloPreempts.rotation_indifference_defect
    {gap : ℝ} {preempted preemptor : player}
    (hedge : QuittingSoloPreempts reward gap preempted preemptor)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    lam * gap ≤
      quittingSoloReward reward preemptor preemptor -
        (lam * quittingSoloReward reward preempted preemptor +
          (1 - lam) * quittingSoloReward reward preemptor preemptor) := by
  rw [quittingSoloRotationDefect_eq]
  have hgap : gap ≤ quittingSoloReward reward preemptor preemptor -
      quittingSoloReward reward preempted preemptor := by
    linarith [hedge.2]
  exact mul_le_mul_of_nonneg_left hgap hlam

/-! ## The two-rate preemption probe -/

/-- The hazard vector used to propagate a preemption edge.  `current` quits
at rate `rate`, its supplied predecessor at the smaller rate `rate²`, and every
other player surely Continues. -/
def quittingPreemptionHazard
    (predecessor current : player) (rate : ℝ) (who : player) : ℝ :=
  if who = current then rate
  else if who = predecessor then rate ^ 2
  else 0

omit [Fintype player] in
theorem quittingPreemptionHazard_nonneg
    (predecessor current : player) {rate : ℝ} (hrate : 0 ≤ rate) :
    ∀ who, 0 ≤ quittingPreemptionHazard predecessor current rate who := by
  intro who
  simp only [quittingPreemptionHazard]
  split_ifs <;> positivity

omit [Fintype player] in
theorem quittingPreemptionHazard_le_one
    (predecessor current : player) {rate : ℝ}
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ∀ who, quittingPreemptionHazard predecessor current rate who ≤ 1 := by
  intro who
  simp only [quittingPreemptionHazard]
  split_ifs
  · exact hrate1
  · nlinarith
  · norm_num

/-- Product root for the two-rate preemption probe. -/
def quittingPreemptionRoot
    (predecessor current : player) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) : player → PMF Bool :=
  rootOfHazard (quittingPreemptionHazard predecessor current rate)
    (quittingPreemptionHazard_nonneg predecessor current hrate0)
    (quittingPreemptionHazard_le_one predecessor current hrate0 hrate1)

omit [Fintype player] in
@[simp] theorem hazardOfRoot_quittingPreemptionRoot
    (predecessor current : player) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    hazardOfRoot
        (quittingPreemptionRoot predecessor current rate hrate0 hrate1) =
      quittingPreemptionHazard predecessor current rate := by
  exact hazardOfRoot_rootOfHazard _ _ _

omit [Fintype player] in
@[simp] theorem quittingPreemptionHazard_current
    {predecessor current : player}
    (rate : ℝ) :
    quittingPreemptionHazard predecessor current rate current = rate := by
  simp [quittingPreemptionHazard]

omit [Fintype player] in
@[simp] theorem quittingPreemptionHazard_predecessor
    {predecessor current : player} (hne : predecessor ≠ current)
    (rate : ℝ) :
    quittingPreemptionHazard predecessor current rate predecessor = rate ^ 2 := by
  simp [quittingPreemptionHazard, hne]

omit [Fintype player] in
theorem quittingPreemptionHazard_eq_zero_of_ne
    {predecessor current who : player}
    (hcurrent : who ≠ current) (hpredecessor : who ≠ predecessor)
    (rate : ℝ) :
    quittingPreemptionHazard predecessor current rate who = 0 := by
  simp [quittingPreemptionHazard, hcurrent, hpredecessor]

omit [Fintype player] in
theorem isQuittingActiveRoot_quittingPreemptionRoot
    {predecessor current : player}
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    IsQuittingActiveRoot {current, predecessor}
      (quittingPreemptionRoot predecessor current rate hrate0 hrate1) := by
  intro who hwho
  have hcurrent : who ≠ current := by simpa using fun h => hwho (by simp [h])
  have hpredecessor : who ≠ predecessor := by
    simpa using fun h => hwho (by simp [h])
  unfold quittingPreemptionRoot rootOfHazard
  simp only [quittingPreemptionHazard, hcurrent, hpredecessor, if_false]
  apply PMF.ext
  intro action
  cases action <;> simp [quittingHazardCoin, PMF.ofFintype_apply]

/-- The probe's one-stage absorption probability. -/
theorem quittingPreemptionRoot_absorptionMass
    {predecessor current : player} (hne : predecessor ≠ current)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingRootAbsorptionMass
        (quittingPreemptionRoot predecessor current rate hrate0 hrate1) =
      1 - (1 - rate) * (1 - rate ^ 2) := by
  let root := quittingPreemptionRoot predecessor current rate hrate0 hrate1
  have hactive : IsQuittingActiveRoot {current, predecessor} root :=
    isQuittingActiveRoot_quittingPreemptionRoot rate hrate0 hrate1
  have hempty := coalitionMass_empty_of_pair_active hne.symm hactive
  have hcontinue : quittingStationaryContinueMass root =
      (1 - rate) * (1 - rate ^ 2) := by
    have hmass : continueMass (hazardOfRoot root) =
        quittingStationaryContinueMass root := by
      rw [continueMass,
        quittingStationaryContinueMass_eq_prod_continueProbability]
      apply Finset.prod_congr rfl
      intro who _
      exact (pmfBool_false_toReal (root who)).symm
    rw [← hmass, ← coalitionMass_empty, hempty]
    simp [root, hne]
  unfold quittingRootAbsorptionMass
  rw [hcontinue]

/-- Exact terminal payoff of the two-rate probe, with the common factor
`rate` cancelled. -/
theorem quittingTerminalPayoff_preemptionRoot
    {predecessor current : player} (hne : predecessor ≠ current)
    (rate : ℝ) (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (who : player) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward
          (quittingPreemptionRoot predecessor current rate hrate0.le hrate1))
        who =
      ((1 - rate ^ 2) * quittingSoloReward reward current who +
          rate * (1 - rate) * quittingSoloReward reward predecessor who +
          rate ^ 2 * reward ⟨{current, predecessor}, by simp⟩ who) /
        (1 + rate - rate ^ 2) := by
  let root := quittingPreemptionRoot predecessor current rate hrate0.le hrate1
  have hactive : IsQuittingActiveRoot {current, predecessor} root :=
    isQuittingActiveRoot_quittingPreemptionRoot rate hrate0.le hrate1
  have hrootCurrent : (root current true).toReal = rate := by
    change hazardOfRoot root current = rate
    simp [root]
  have hrootPredecessor : (root predecessor true).toReal = rate ^ 2 := by
    change hazardOfRoot root predecessor = rate ^ 2
    simp [root, hne]
  have hhazardCurrent : hazardOfRoot root current = rate := hrootCurrent
  have hhazardPredecessor : hazardOfRoot root predecessor = rate ^ 2 :=
    hrootPredecessor
  have habsorption : rate ≤ quittingRootAbsorptionMass root := by
    rw [← hrootCurrent]
    exact quittingRoot_quitProbability_le_absorptionMass root current
  have hcontracts : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hdenominator : 0 < 1 + rate - rate ^ 2 := by
    nlinarith [mul_nonneg hrate0.le (sub_nonneg.mpr hrate1)]
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward root who hcontracts]
  change quittingRootExpectedPayoff reward (0 : Payoff player) root who /
      quittingRootAbsorptionMass root = _
  rw [quittingRootExpectedPayoff_pair_active reward (0 : Payoff player)
      root current predecessor who hne.symm hactive,
    quittingPreemptionRoot_absorptionMass hne rate hrate0.le hrate1]
  rw [hhazardCurrent, hhazardPredecessor]
  simp only [Pi.zero_apply]
  have hfactor : 1 - (1 - rate) * (1 - rate ^ 2) =
      rate * (1 + rate - rate ^ 2) := by ring
  rw [hfactor]
  apply (div_eq_div_iff (mul_ne_zero (ne_of_gt hrate0)
    (ne_of_gt hdenominator)) (ne_of_gt hdenominator)).2
  simp only [quittingSoloReward]
  ring

/-- Along any positive two-rate probe whose principal rate tends to zero,
the prescribed payoff converges to the current player's solo payoff vector. -/
theorem tendsto_quittingTerminalPayoff_preemptionRoot
    {predecessor current : player} (hne : predecessor ≠ current)
    (rate : ℕ → ℝ) (hrate0 : ∀ n, 0 < rate n)
    (hrate1 : ∀ n, rate n ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds 0))
    (who : player) :
    Filter.Tendsto
      (fun n ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward
          (quittingPreemptionRoot predecessor current (rate n)
            (hrate0 n).le (hrate1 n))) who)
      Filter.atTop
      (nhds (quittingSoloReward reward current who)) := by
  let currentValue := quittingSoloReward reward current who
  let predecessorValue := quittingSoloReward reward predecessor who
  let collisionValue := reward ⟨{current, predecessor}, by simp⟩ who
  have hrateSq : Filter.Tendsto (fun n ↦ rate n ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using hrate.pow 2
  have hnumerator : Filter.Tendsto
      (fun n ↦
        (1 - rate n ^ 2) * currentValue +
          rate n * (1 - rate n) * predecessorValue +
          rate n ^ 2 * collisionValue)
      Filter.atTop (nhds currentValue) := by
    convert (((tendsto_const_nhds.sub hrateSq).mul tendsto_const_nhds).add
      ((hrate.mul (tendsto_const_nhds.sub hrate)).mul
        tendsto_const_nhds)).add
      (hrateSq.mul tendsto_const_nhds) using 1
    all_goals simp [currentValue, predecessorValue, collisionValue]
  have hdenominator : Filter.Tendsto
      (fun n ↦ 1 + rate n - rate n ^ 2)
      Filter.atTop (nhds 1) := by
    convert (tendsto_const_nhds.add hrate).sub hrateSq using 1
    all_goals norm_num
  have hquotient := hnumerator.div hdenominator (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun n ↦
      ((1 - rate n ^ 2) * currentValue +
          rate n * (1 - rate n) * predecessorValue +
          rate n ^ 2 * collisionValue) /
        (1 + rate n - rate n ^ 2)) =ᶠ[Filter.atTop]
      (fun n ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward
          (quittingPreemptionRoot predecessor current (rate n)
            (hrate0 n).le (hrate1 n))) who) := by
    filter_upwards [] with n
    exact (quittingTerminalPayoff_preemptionRoot
      (reward := reward) hne (rate n) (hrate0 n) (hrate1 n) who).symm
  simpa [currentValue] using hquotient.congr' heq

/-- Along the same probe, every player's immediate-Quit endpoint converges
to that player's own solo payoff. -/
theorem tendsto_quittingStationaryFixedOpponentsQuitValue_preemptionRoot
    {predecessor current : player} (hne : predecessor ≠ current)
    (rate : ℕ → ℝ) (hrate0 : ∀ n, 0 < rate n)
    (hrate1 : ∀ n, rate n ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds 0))
    (who : player) :
    Filter.Tendsto
      (fun n ↦ quittingStationaryFixedOpponentsQuitValue reward
        (quittingPreemptionRoot predecessor current (rate n)
          (hrate0 n).le (hrate1 n)) who)
      Filter.atTop
      (nhds (quittingSoloReward reward who who)) := by
  let root : ℕ → player → PMF Bool := fun n ↦
    quittingPreemptionRoot predecessor current (rate n)
      (hrate0 n).le (hrate1 n)
  have habsorption : Filter.Tendsto
      (fun n ↦ quittingRootAbsorptionMass (root n))
      Filter.atTop (nhds 0) := by
    have hrateSq : Filter.Tendsto (fun n ↦ rate n ^ 2)
        Filter.atTop (nhds 0) := by simpa using hrate.pow 2
    have hformula : ∀ n, quittingRootAbsorptionMass (root n) =
        1 - (1 - rate n) * (1 - rate n ^ 2) := by
      intro n
      exact quittingPreemptionRoot_absorptionMass
        hne (rate n) (hrate0 n).le (hrate1 n)
    have hpoly : Filter.Tendsto
        (fun n ↦ 1 - (1 - rate n) * (1 - rate n ^ 2))
        Filter.atTop (nhds 0) := by
      convert tendsto_const_nhds.sub
        ((tendsto_const_nhds.sub hrate).mul
          (tendsto_const_nhds.sub hrateSq)) using 1
      all_goals norm_num
    exact hpoly.congr' (Filter.Eventually.of_forall fun n ↦ (hformula n).symm)
  let bound := fun n ↦ 2 * quittingRewardBound reward *
    quittingRootAbsorptionMass (root n)
  have hbound : Filter.Tendsto bound Filter.atTop (nhds 0) := by
    simpa [bound, mul_comm] using
      habsorption.mul_const (2 * quittingRewardBound reward)
  have hdiff : Filter.Tendsto
      (fun n ↦ quittingStationaryFixedOpponentsQuitValue reward
          (root n) who - quittingSoloReward reward who who)
      Filter.atTop (nhds 0) := by
    apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _ bound hbound
    filter_upwards [] with n
    calc
      |quittingStationaryFixedOpponentsQuitValue reward (root n) who -
          quittingSoloReward reward who who| ≤
          2 * quittingRewardBound reward *
            quittingRootOpponentAbsorptionMass (root n) who :=
        abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
          (reward := reward) (root n) who
            (abs_reward_le_quittingRewardBound reward)
      _ ≤ 2 * quittingRewardBound reward *
          quittingRootAbsorptionMass (root n) :=
        mul_le_mul_of_nonneg_left
          (quittingRootOpponentAbsorptionMass_le_absorptionMass (root n) who)
          (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
  have hsum := hdiff.add
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ ↦ quittingSoloReward reward who who)
      Filter.atTop (nhds (quittingSoloReward reward who who)))
  simpa [root] using hsum

/-- The current player's cap on a two-rate probe is exactly its cap against
the predecessor's smaller solo clock. -/
theorem quittingStationaryUnilateralCap_preemptionRoot_current
    {predecessor current : player} (hne : predecessor ≠ current)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingStationaryUnilateralCap reward
        (quittingPreemptionRoot predecessor current rate hrate0 hrate1)
        current =
      quittingStationaryUnilateralCap reward
        (quittingSoloStationaryRoot predecessor
          (quittingHazardCoin (rate ^ 2) (sq_nonneg rate) (by nlinarith)))
        current := by
  apply quittingStationaryUnilateralCap_congr_of_opponents reward current
  intro who hwho
  by_cases hpredecessor : who = predecessor
  · subst who
    unfold quittingPreemptionRoot rootOfHazard quittingSoloStationaryRoot
    simp [quittingPreemptionHazard, hne]
  · unfold quittingPreemptionRoot rootOfHazard quittingSoloStationaryRoot
    simp [quittingPreemptionHazard, hwho, hpredecessor]
    apply PMF.ext
    intro action
    cases action <;> simp [quittingHazardCoin, PMF.ofFintype_apply]

/-- The predecessor's cap on a two-rate probe is exactly its cap against
the current player's principal solo clock. -/
theorem quittingStationaryUnilateralCap_preemptionRoot_predecessor
    {predecessor current : player}
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingStationaryUnilateralCap reward
        (quittingPreemptionRoot predecessor current rate hrate0 hrate1)
        predecessor =
      quittingStationaryUnilateralCap reward
        (quittingSoloStationaryRoot current
          (quittingHazardCoin rate hrate0 hrate1)) predecessor := by
  apply quittingStationaryUnilateralCap_congr_of_opponents reward predecessor
  intro who hwho
  by_cases hcurrent : who = current
  · subst who
    unfold quittingPreemptionRoot rootOfHazard quittingSoloStationaryRoot
    simp [quittingPreemptionHazard]
  · unfold quittingPreemptionRoot rootOfHazard quittingSoloStationaryRoot
    simp [quittingPreemptionHazard, hcurrent, hwho]
    apply PMF.ext
    intro action
    cases action <;> simp [quittingHazardCoin, PMF.ofFintype_apply]

/-- If the selected player surely Continues at an absorbing root, the
Continue endpoint of its stationary cap is the prescribed terminal payoff. -/
theorem quittingStationaryUnilateralCap_eq_max_terminalPayoff_of_continue
    (root : player → PMF Bool) (who : player)
    (hcontinue : root who = PMF.pure false)
    (hcontracts : quittingStationaryContinueMass root < 1) :
    quittingStationaryUnilateralCap reward root who =
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
        (quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who) := by
  have hupdate : Function.update root who (PMF.pure false) = root := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [hcontinue]
    · simp [Function.update_of_ne hplayer]
  have hreward : quittingStationaryFixedOpponentsContinueReward
      reward root who = quittingRootAbsorbingContribution reward root who := by
    unfold quittingStationaryFixedOpponentsContinueReward
      quittingFixedOpponentsContinueReward
    rw [hupdate]
  have hmass : quittingStationaryFixedOpponentsContinueMass root who =
      quittingStationaryContinueMass root := by
    unfold quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass
    rw [hupdate]
  rw [quittingStationaryUnilateralCap_eq_max_div, hreward, hmass,
    ← quittingTerminalPayoff_stationary_eq_absorbingContribution_div
      reward root who hcontracts]

/-- An incoming preemption edge controls the selected-cap limit of the
two-rate probe: every player's limiting cap is the better of quitting alone
and receiving the current player's solo-exit payoff. -/
theorem tendsto_quittingStationaryUnilateralCap_preemptionRoot
    {gap : ℝ} {predecessor current : player}
    (hedge : QuittingSoloPreempts reward gap predecessor current)
    (hgap0 : 0 ≤ gap)
    (rate : ℕ → ℝ) (hrate0 : ∀ n, 0 < rate n)
    (hrate1 : ∀ n, rate n ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds 0))
    (who : player) :
    Filter.Tendsto
      (fun n ↦ quittingStationaryUnilateralCap reward
        (quittingPreemptionRoot predecessor current (rate n)
          (hrate0 n).le (hrate1 n)) who)
      Filter.atTop
      (nhds (max (quittingSoloReward reward who who)
        (quittingSoloReward reward current who))) := by
  have hne : predecessor ≠ current := hedge.1.symm
  have hrateSq : Filter.Tendsto (fun n ↦ rate n ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using hrate.pow 2
  by_cases hcurrent : who = current
  · subst who
    have hmix : Filter.Tendsto
        (fun n ↦
          (1 - rate n ^ 2) * quittingSoloReward reward current current +
            rate n ^ 2 *
              quittingSingletonCollisionReward reward predecessor current)
        Filter.atTop
        (nhds (quittingSoloReward reward current current)) := by
      convert ((tendsto_const_nhds.sub hrateSq).mul
        tendsto_const_nhds).add (hrateSq.mul tendsto_const_nhds) using 1
      all_goals ring_nf
    have hcap := hmix.max
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ ↦ quittingSoloReward reward predecessor current)
        Filter.atTop (nhds (quittingSoloReward reward predecessor current)))
    have hlimit : max (quittingSoloReward reward current current)
        (quittingSoloReward reward predecessor current) =
        quittingSoloReward reward current current := by
      apply max_eq_left
      linarith [hedge.2]
    rw [max_self]
    rw [hlimit] at hcap
    apply hcap.congr'
    filter_upwards [] with n
    have hsq1 : rate n ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (hrate0 n).le (sub_nonneg.mpr (hrate1 n))]
    rw [quittingStationaryUnilateralCap_preemptionRoot_current
      (reward := reward) hne (rate n) (hrate0 n).le (hrate1 n),
      quittingStationaryUnilateralCap_solo_other reward hedge.1
        (quittingHazardCoin (rate n ^ 2) (sq_nonneg (rate n)) hsq1)
        (by simp [hrate0 n]),
      quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward hedge.1]
    simp only [quittingHazardCoin_false_toReal,
      quittingHazardCoin_true_toReal]
  · by_cases hpredecessor : who = predecessor
    · subst who
      have hmix : Filter.Tendsto
          (fun n ↦
            (1 - rate n) * quittingSoloReward reward predecessor predecessor +
              rate n *
                quittingSingletonCollisionReward reward current predecessor)
          Filter.atTop
          (nhds (quittingSoloReward reward predecessor predecessor)) := by
        convert ((tendsto_const_nhds.sub hrate).mul
          tendsto_const_nhds).add (hrate.mul tendsto_const_nhds) using 1
        all_goals ring_nf
      have hcap := hmix.max
        (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℕ ↦ quittingSoloReward reward current predecessor)
          Filter.atTop (nhds (quittingSoloReward reward current predecessor)))
      apply hcap.congr'
      filter_upwards [] with n
      rw [quittingStationaryUnilateralCap_preemptionRoot_predecessor
        (reward := reward) (rate n) (hrate0 n).le (hrate1 n),
        quittingStationaryUnilateralCap_solo_other reward hne
          (quittingHazardCoin (rate n) (hrate0 n).le (hrate1 n))
          (by simp [hrate0 n]),
        quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward hne]
      simp only [quittingHazardCoin_false_toReal,
        quittingHazardCoin_true_toReal]
    · let root : ℕ → player → PMF Bool := fun n ↦
        quittingPreemptionRoot predecessor current (rate n)
          (hrate0 n).le (hrate1 n)
      have hcontinue : ∀ n, root n who = PMF.pure false := by
        intro n
        unfold root quittingPreemptionRoot rootOfHazard
        simp [quittingPreemptionHazard, hcurrent, hpredecessor]
        apply PMF.ext
        intro action
        cases action <;> simp [quittingHazardCoin, PMF.ofFintype_apply]
      have hcontracts : ∀ n, quittingStationaryContinueMass (root n) < 1 := by
        intro n
        have habsorption : rate n ≤ quittingRootAbsorptionMass (root n) := by
          have hcurrentQuit : (root n current true).toReal = rate n := by
            change hazardOfRoot (root n) current = rate n
            simp [root]
          rw [← hcurrentQuit]
          exact quittingRoot_quitProbability_le_absorptionMass (root n) current
        unfold quittingRootAbsorptionMass at habsorption
        linarith [hrate0 n]
      have hquit :=
        tendsto_quittingStationaryFixedOpponentsQuitValue_preemptionRoot
          (reward := reward) hne rate hrate0 hrate1 hrate who
      have hprescribed := tendsto_quittingTerminalPayoff_preemptionRoot
        (reward := reward) hne rate hrate0 hrate1 hrate who
      have hcap := hquit.max hprescribed
      apply hcap.congr'
      filter_upwards [] with n
      exact (quittingStationaryUnilateralCap_eq_max_terminalPayoff_of_continue
        (reward := reward) (root n) who (hcontinue n) (hcontracts n)).symm

end GameTheory
