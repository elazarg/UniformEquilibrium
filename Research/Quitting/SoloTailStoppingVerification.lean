/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.SoloTailExactStructure
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality

/-!
# Verification of solo quitting tails against stopping deviations

A player deviating unilaterally in a quitting game may as well stop at a
deterministic date or never stop
(`quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy`), and the
value of such a deviation against a fixed root sequence satisfies the scalar
fixed-opponent recursion
(`quittingRootSequenceHazardTerminalValue_eq_hazardBellman`).  This file
verifies a prescribed value sequence against exactly those deviations by
backwards induction along the recursion.

The window shape needed is weaker than a solo tail: at each date either the
deviator surely continues, so its prescribed value obeys the fixed-opponent
recursion verbatim, or the deviator is the only coordinate that may quit, so
the opponents cannot absorb and the deviator's value is pinned across the
date up to the date's Nash slack (`QuittingSoloDeviationDate`).  A solo root
supplies this shape at every coordinate at once
(`quittingSoloDeviationDate_of_isQuittingSoloRoot`).

* **Stopping bound**
  (`quittingRootSequencePureTimeTerminalValue_le_value_add_slackBudget`): the
  value of stopping at a date inside the window exceeds the prescribed value
  by at most the survival-discounted sum of the Nash slacks up to that date.
  Exact roots give the clean cap
  (`quittingRootSequencePureTimeTerminalValue_le_value_of_exact`).
* **Refusal bound**
  (`quittingRootSequencePureTimeTerminalValue_none_sub_value_le`): never
  stopping is capped by the surviving displacement at the far end of the
  window plus the same slack budget, hence by the prescribed value alone once
  opponent survival vanishes
  (`quittingRootSequencePureTimeTerminalValue_none_le_value_of_exact`).
* **Financing inequality**
  (`le_slackBudget_of_stoppingGap`, `le_slackBudget_of_refusalGap`): a
  deviation exceeding the prescribed value by `gap` forces the discounted
  Nash slack of the window to be at least `gap`.  This prices any splice that
  buys a non-summable tail out of exactness.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The window shape seen by one deviator -/

/-- At `time`, either `who` surely continues, or `who` is the only coordinate
that may quit. -/
def QuittingSoloDeviationDate (roots : ℕ → ι → PMF Bool) (who : ι)
    (time : ℕ) : Prop :=
  roots time who = PMF.pure false ∨ IsQuittingSoloRoot (roots time) who

omit [Fintype ι] in
/-- A solo root presents the deviation shape to every coordinate at once: the
designated owner is the only possible quitter, and every other coordinate
surely continues. -/
theorem quittingSoloDeviationDate_of_isQuittingSoloRoot
    {roots : ℕ → ι → PMF Bool} {owner : ι} {time : ℕ}
    (hsolo : IsQuittingSoloRoot (roots time) owner) (who : ι) :
    QuittingSoloDeviationDate roots who time := by
  by_cases hwho : who = owner
  · subst who
    exact Or.inr hsolo
  · exact Or.inl (hsolo who hwho)

/-! ## Fixed-opponent coefficients under the two branches -/

/-- When `who` is the only coordinate that may quit, its opponents cannot
absorb: the fixed-opponent survival mass is one. -/
theorem quittingFixedOpponentsContinueMass_eq_one_of_soloRoot
    (roots : ℕ → ι → PMF Bool) {who : ι} {time : ℕ}
    (hsolo : IsQuittingSoloRoot (roots time) who) :
    quittingFixedOpponentsContinueMass roots who time = 1 := by
  have hshape : Function.update (roots time) who (PMF.pure false) =
      quittingSoloStationaryRoot who (PMF.pure false) := by
    have hothers : ∀ other, other ≠ who →
        Function.update (roots time) who (PMF.pure false) other =
          PMF.pure false := by
      intro other hother
      rw [Function.update_of_ne hother]
      exact hsolo other hother
    have hself := eq_quittingSoloStationaryRoot_of_others_continue hothers
    rwa [Function.update_self] at hself
  unfold quittingFixedOpponentsContinueMass
  rw [hshape, quittingStationaryContinueMass_solo]
  simp

/-- When `who` is the only coordinate that may quit, its opponents contribute
no absorbing reward. -/
theorem quittingFixedOpponentsContinueReward_eq_zero_of_soloRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {who : ι} {time : ℕ}
    (hsolo : IsQuittingSoloRoot (roots time) who) :
    quittingFixedOpponentsContinueReward reward roots who time = 0 := by
  have hshape : Function.update (roots time) who (PMF.pure false) =
      quittingSoloStationaryRoot who (PMF.pure false) := by
    have hothers : ∀ other, other ≠ who →
        Function.update (roots time) who (PMF.pure false) other =
          PMF.pure false := by
      intro other hother
      rw [Function.update_of_ne hother]
      exact hsolo other hother
    have hself := eq_quittingSoloStationaryRoot_of_others_continue hothers
    rwa [Function.update_self] at hself
  unfold quittingFixedOpponentsContinueReward
  rw [hshape, quittingRootAbsorbingContribution_solo]
  simp

/-- A surely continuing coordinate's prescribed value obeys the
fixed-opponent recursion verbatim. -/
theorem quittingValue_eq_fixedOpponents_of_continueSurely
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {who : ι} {time : ℕ} (hpure : roots time who = PMF.pure false) :
    value time who =
      quittingFixedOpponentsContinueReward reward roots who time +
        quittingFixedOpponentsContinueMass roots who time *
          value (time + 1) who := by
  have hquitMass : (roots time who true).toReal = 0 := by rw [hpure]; simp
  have hcontinueMass : (roots time who false).toReal = 1 := by rw [hpure]; simp
  conv_lhs => rw [hpolicy time]
  rw [quittingRootSuccessorPayoff_eq_endpointMix, hquitMass, hcontinueMass,
    zero_mul, one_mul, zero_add, quittingRootContinuePayoff_eq_fixedOpponents]

/-- A sole possible quitter's prescribed value falls by at most the date's
Nash slack across the date. -/
theorem quittingValue_succ_le_value_add_slack_of_soloRoot
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) {slack : ℝ}
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {who : ι} {time : ℕ} (hsolo : IsQuittingSoloRoot (roots time) who)
    (hnash : IsεQuittingRootEndpointNash reward (value (time + 1)) slack
      (roots time)) :
    value (time + 1) who ≤ value time who + slack := by
  have hpin := hsolo.tail_owner_le_successorPayoff_add reward hnash
  rw [← hpolicy time] at hpin
  exact hpin

/-! ## The discounted slack budget -/

/-- Survival-discounted total Nash slack of the `length` dates beginning at
`start`, as seen by `who`'s opponents. -/
def quittingDeviatorSlackBudget (roots : ℕ → ι → PMF Bool) (who : ι)
    (slack : ℕ → ℝ) (start length : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range length,
    quittingOpponentSurvivalWeight roots who start offset *
      slack (start + offset)

/-- The slack budget peels its first date. -/
theorem quittingDeviatorSlackBudget_succ
    (roots : ℕ → ι → PMF Bool) (who : ι) (slack : ℕ → ℝ)
    (start length : ℕ) :
    quittingDeviatorSlackBudget roots who slack start (length + 1) =
      slack start + quittingFixedOpponentsContinueMass roots who start *
        quittingDeviatorSlackBudget roots who slack (start + 1) length := by
  unfold quittingDeviatorSlackBudget
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have hshift : ∀ offset ∈ Finset.range length,
      quittingOpponentSurvivalWeight roots who start (offset + 1) *
          slack (start + (offset + 1)) =
        quittingFixedOpponentsContinueMass roots who start *
          (quittingOpponentSurvivalWeight roots who (start + 1) offset *
            slack (start + 1 + offset)) := by
    intro offset _
    rw [quittingOpponentSurvivalWeight_succ_left,
      show start + (offset + 1) = start + 1 + offset from by omega]
    ring
  rw [Finset.sum_congr rfl hshift, add_comm]
  simp [quittingOpponentSurvivalWeight]

/-- Every discounted slack budget of nonnegative slacks is nonnegative. -/
theorem quittingDeviatorSlackBudget_nonneg
    (roots : ℕ → ι → PMF Bool) (who : ι) {slack : ℕ → ℝ}
    (hslack : ∀ time, 0 ≤ slack time) (start length : ℕ) :
    0 ≤ quittingDeviatorSlackBudget roots who slack start length :=
  Finset.sum_nonneg fun offset _ =>
    mul_nonneg (quittingOpponentSurvivalWeight_nonneg roots who start offset)
      (hslack (start + offset))

/-! ## The stopping recursion -/

/-- Before its quit date, a deterministic stopper obeys the fixed-opponent
continue recursion. -/
theorem quittingRootSequencePureTimeTerminalValue_some_of_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {quitTime start : ℕ}
    (hne : start ≠ quitTime) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some quitTime) start =
      quittingFixedOpponentsContinueReward reward roots who start +
        quittingFixedOpponentsContinueMass roots who start *
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some quitTime) (start + 1) := by
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
    quittingPureTimeHazard_some_of_ne hne]
  simp

/-- **Stopping bound.**  Against a root sequence presenting the deviation
shape at every date of the window, stopping at the window's far end exceeds
the prescribed value by at most the window's survival-discounted Nash
slack. -/
theorem quittingRootSequencePureTimeTerminalValue_le_value_add_slackBudget
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (slack : ℕ → ℝ)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) (slack time)
        (roots time))
    (hslack : ∀ time, 0 ≤ slack time)
    (who : ι) (start length : ℕ)
    (hwindow : ∀ offset, offset < length →
      QuittingSoloDeviationDate roots who (start + offset)) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + length)) start ≤
      value start who +
        quittingDeviatorSlackBudget roots who slack start (length + 1) := by
  induction length generalizing start with
  | zero =>
      have hstop := quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents
        reward roots who start
      have hquit : quittingFixedOpponentsQuitValue reward roots who start =
          quittingRootQuitPayoff reward (value (start + 1)) (roots start) who :=
        (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots who
          (value (start + 1)) start).symm
      have hnashStart :=
        ((isεQuittingRootEndpointNash_iff_purePayoff_le reward
          (value (start + 1)) (slack start) (roots start)).1 (hnash start)
          who).1
      rw [← hpolicy start] at hnashStart
      have hbudget : quittingDeviatorSlackBudget roots who slack start 1 =
          slack start := by
        simp [quittingDeviatorSlackBudget, quittingOpponentSurvivalWeight]
      rw [Nat.add_zero, hstop, hquit, hbudget]
      exact hnashStart
  | succ length ih =>
      have hwindow0 : QuittingSoloDeviationDate roots who start := by
        simpa using hwindow 0 (Nat.succ_pos length)
      have hwindowTail : ∀ offset, offset < length →
          QuittingSoloDeviationDate roots who (start + 1 + offset) := by
        intro offset hoffset
        have hshift := hwindow (offset + 1) (by omega)
        rwa [show start + (offset + 1) = start + 1 + offset from by omega]
          at hshift
      have hIH := ih (start + 1) hwindowTail
      have hstep := quittingRootSequencePureTimeTerminalValue_some_of_ne reward
        roots who (quitTime := start + (length + 1)) (start := start)
        (by omega)
      have hshift : quittingRootSequencePureTimeTerminalValue reward roots who
          (some (start + (length + 1))) (start + 1) =
            quittingRootSequencePureTimeTerminalValue reward roots who
              (some (start + 1 + length)) (start + 1) := by
        rw [show start + (length + 1) = start + 1 + length from by omega]
      rw [hstep, hshift, quittingDeviatorSlackBudget_succ]
      have hmass := quittingStationaryContinueMass_nonneg
        (Function.update (roots start) who (PMF.pure false))
      have hmassLe := quittingStationaryContinueMass_le_one
        (Function.update (roots start) who (PMF.pure false))
      have hmass0 : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        hmass
      have hmass1 : quittingFixedOpponentsContinueMass roots who start ≤ 1 :=
        hmassLe
      rcases hwindow0 with hpure | hsolo
      · have hvalue := quittingValue_eq_fixedOpponents_of_continueSurely roots
          value hpolicy hpure
        nlinarith [hIH, hslack start]
      · have hcontinueMass :=
          quittingFixedOpponentsContinueMass_eq_one_of_soloRoot roots hsolo
        have hcontinueReward :=
          quittingFixedOpponentsContinueReward_eq_zero_of_soloRoot reward roots
            hsolo
        have hpin := quittingValue_succ_le_value_add_slack_of_soloRoot roots
          value hpolicy hsolo (hnash start)
        rw [hcontinueMass, hcontinueReward]
        have hbudget0 := quittingDeviatorSlackBudget_nonneg roots who hslack
          (start + 1) (length + 1)
        linarith [hIH, hpin]

/-- **Exact stopping cap.**  At accuracy zero every deterministic stopping
date inside the window is capped by the prescribed value. -/
theorem quittingRootSequencePureTimeTerminalValue_le_value_of_exact
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (who : ι) (start length : ℕ)
    (hwindow : ∀ offset, offset < length →
      QuittingSoloDeviationDate roots who (start + offset)) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + length)) start ≤ value start who := by
  have hmain := quittingRootSequencePureTimeTerminalValue_le_value_add_slackBudget
    roots value (fun _ => 0) hpolicy hnash (fun _ => le_rfl) who start length
    hwindow
  simpa [quittingDeviatorSlackBudget] using hmain

/-! ## The refusal branch -/

/-- **Refusal bound.**  Never stopping exceeds the prescribed value by at most
the surviving displacement at the far end of the window plus the window's
discounted Nash slack. -/
theorem quittingRootSequencePureTimeTerminalValue_none_sub_value_le
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (slack : ℕ → ℝ)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) (slack time)
        (roots time))
    (hslack : ∀ time, 0 ≤ slack time)
    (who : ι) (start length : ℕ)
    (hwindow : ∀ offset, offset < length →
      QuittingSoloDeviationDate roots who (start + offset)) :
    quittingRootSequencePureTimeTerminalValue reward roots who none start -
        value start who ≤
      quittingOpponentSurvivalWeight roots who start length *
          (quittingRootSequencePureTimeTerminalValue reward roots who none
              (start + length) - value (start + length) who) +
        quittingDeviatorSlackBudget roots who slack start length := by
  induction length generalizing start with
  | zero => simp [quittingDeviatorSlackBudget, quittingOpponentSurvivalWeight]
  | succ length ih =>
      have hwindow0 : QuittingSoloDeviationDate roots who start := by
        simpa using hwindow 0 (Nat.succ_pos length)
      have hwindowTail : ∀ offset, offset < length →
          QuittingSoloDeviationDate roots who (start + 1 + offset) := by
        intro offset hoffset
        have hshift := hwindow (offset + 1) (by omega)
        rwa [show start + (offset + 1) = start + 1 + offset from by omega]
          at hshift
      have hIH := ih (start + 1) hwindowTail
      have hstep :=
        quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents
          reward roots who start
      have hmass0 : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      rw [show start + (length + 1) = start + 1 + length from by omega,
        quittingOpponentSurvivalWeight_succ_left,
        quittingDeviatorSlackBudget_succ, hstep]
      rcases hwindow0 with hpure | hsolo
      · have hvalue := quittingValue_eq_fixedOpponents_of_continueSurely roots
          value hpolicy hpure
        nlinarith [hIH, hslack start]
      · have hcontinueMass :=
          quittingFixedOpponentsContinueMass_eq_one_of_soloRoot roots hsolo
        have hcontinueReward :=
          quittingFixedOpponentsContinueReward_eq_zero_of_soloRoot reward roots
            hsolo
        have hpin := quittingValue_succ_le_value_add_slack_of_soloRoot roots
          value hpolicy hsolo (hnash start)
        rw [hcontinueMass, hcontinueReward]
        linarith [hIH]

/-! ## Financing a deviation out of Nash slack -/

/-- **Financing inequality, stopping form.**  A deterministic stopping date
that beats the prescribed value by `gap` forces the window's discounted Nash
slack to be at least `gap`. -/
theorem le_slackBudget_of_stoppingGap
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (slack : ℕ → ℝ)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) (slack time)
        (roots time))
    (hslack : ∀ time, 0 ≤ slack time)
    (who : ι) (start length : ℕ) {gap : ℝ}
    (hwindow : ∀ offset, offset < length →
      QuittingSoloDeviationDate roots who (start + offset))
    (hgap : value start who + gap ≤
      quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + length)) start) :
    gap ≤ quittingDeviatorSlackBudget roots who slack start (length + 1) := by
  have hcap := quittingRootSequencePureTimeTerminalValue_le_value_add_slackBudget
    roots value slack hpolicy hnash hslack who start length hwindow
  linarith

/-- **Financing inequality, refusal form.**  Refusal that beats the prescribed
value by `gap` forces the window's discounted Nash slack, together with the
surviving displacement at the far end, to be at least `gap`. -/
theorem le_slackBudget_of_refusalGap
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (slack : ℕ → ℝ)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) (slack time)
        (roots time))
    (hslack : ∀ time, 0 ≤ slack time)
    (who : ι) (start length : ℕ) {gap : ℝ}
    (hwindow : ∀ offset, offset < length →
      QuittingSoloDeviationDate roots who (start + offset))
    (hgap : value start who + gap ≤
      quittingRootSequencePureTimeTerminalValue reward roots who none start) :
    gap ≤
      quittingOpponentSurvivalWeight roots who start length *
          (quittingRootSequencePureTimeTerminalValue reward roots who none
              (start + length) - value (start + length) who) +
        quittingDeviatorSlackBudget roots who slack start length := by
  have hcap := quittingRootSequencePureTimeTerminalValue_none_sub_value_le roots
    value slack hpolicy hnash hslack who start length hwindow
  linarith

end GameTheory
