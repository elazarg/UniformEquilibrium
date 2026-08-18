/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.SolanVieilleOneShotPerfection
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit
import UniformEquilibrium.Quitting.Cycles.InfinitePureTimeExtremality
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding

/-!
# The stage ledger of a pure-time deviation

Stage-local identities and bounds used by the block analysis of Solan and
Vieille, *Quitting games*, Math. Oper. Res. 26 (2001), Section 2.5, in this
development's root-sequence vocabulary.  Everything here concerns one stage
of one root sequence and one deviating player.

* The plan's value recursion in absorbing-contribution form, and the exact
  split of the absorbing contribution along the deviator's own action.
* The continue step of a deterministic pure-time deviation's value.
* **The deviation ledger**: the gap between a pure-time deviation's value
  and the plan's value evolves by exactly the deviator's own quit weight
  times the deviation's edge over quitting now, discounted by the full joint
  survival mass.  This is the identity behind the source's observation that
  deviation profits accrue proportionally to the deviator's own quit rate.
* Under unit solo exit, the one-stage quit value is within
  `2 * bound * opponent absorption` of `1`; combined with one-stage
  perfectness this floors the plan's value at every stage.
* The opponent-absorption reward is bounded by the payoff bound times the
  opponent absorption mass.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The plan recursion and the own-action split -/

omit [DecidableEq ι] in
/-- The plan's value recursion, in absorbing-contribution form. -/
theorem quittingRootSequenceTerminalValue_eq_absorbingContribution_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootSequenceTerminalValue reward roots who time =
      quittingRootAbsorbingContribution reward (roots time) who +
        quittingStationaryContinueMass (roots time) *
          quittingRootSequenceTerminalValue reward roots who (time + 1) := by
  rw [quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
  exact quittingRootExpectedPayoff_eq_absorbingContribution_add reward
    (quittingRootSequenceTailVector reward roots (time + 1)) (roots time) who

/-- The absorbing contribution splits along the selected player's own
action: own quit weight times the fixed-opponent quit value plus own
continue weight times the opponent-absorption reward. -/
theorem quittingRootAbsorbingContribution_eq_own_split
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootAbsorbingContribution reward (roots time) who =
      (roots time who true).toReal *
          quittingFixedOpponentsQuitValue reward roots who time +
        (roots time who false).toReal *
          quittingFixedOpponentsContinueReward reward roots who time := by
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix reward
    (0 : Payoff ι) (roots time) who
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    roots who (0 : Payoff ι) time
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents reward
    roots who (0 : Payoff ι) time
  have hzero : (0 : Payoff ι) who = 0 := rfl
  rw [hquit, hcontinue, hzero, mul_zero, add_zero] at hmix
  exact hmix

/-! ## The pure-time continue step -/

/-- Before its quit date — and always, for `Never` — a deterministic
pure-time deviation's value satisfies the fixed-opponent continue
recursion. -/
theorem quittingRootSequencePureTimeTerminalValue_continue_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (quitTime : Option ℕ) (time : ℕ) (hne : quitTime ≠ some time) :
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime time =
      quittingFixedOpponentsContinueReward reward roots who time +
        quittingFixedOpponentsContinueMass roots who time *
          quittingRootSequencePureTimeTerminalValue reward roots who quitTime
            (time + 1) := by
  cases quitTime with
  | none =>
      exact quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents
        reward roots who time
  | some target =>
      have htime : time ≠ target := fun heq => hne (by rw [heq])
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
        quittingPureTimeHazard_some_of_ne htime]
      simp

/-! ## The deviation ledger -/

/-- **The deviation ledger.**  Away from its quit date, the gap between a
pure-time deviation's value and the plan's value equals the deviator's own
quit weight times the deviation's edge over quitting now, plus the full
joint survival mass times the next stage's gap.

Deviation profits therefore accrue only in proportion to the deviator's own
prescribed quit rate, which is the source's key accounting device
(Solan and Vieille, *Quitting games*, Math. Oper. Res. 26 (2001),
Section 2.5.1). -/
theorem quittingPureTimeDeviationLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (quitTime : Option ℕ) (time : ℕ) (hne : quitTime ≠ some time) :
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime time -
        quittingRootSequenceTerminalValue reward roots who time =
      (roots time who true).toReal *
          (quittingRootSequencePureTimeTerminalValue reward roots who
              quitTime time -
            quittingFixedOpponentsQuitValue reward roots who time) +
        quittingStationaryContinueMass (roots time) *
          (quittingRootSequencePureTimeTerminalValue reward roots who
              quitTime (time + 1) -
            quittingRootSequenceTerminalValue reward roots who (time + 1)) := by
  have hplan := quittingRootSequenceTerminalValue_eq_absorbingContribution_add
    reward roots who time
  have hsplit := quittingRootAbsorbingContribution_eq_own_split reward roots
    who time
  have hstep := quittingRootSequencePureTimeTerminalValue_continue_step reward
    roots who quitTime time hne
  have hfactor := quittingStationaryContinueMass_eq_forcedContinue_mul_own
    (roots time) who
  have hCM : quittingFixedOpponentsContinueMass roots who time =
      quittingStationaryContinueMass
        (Function.update (roots time) who (PMF.pure false)) := rfl
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (roots time) who
  have hcontinue : (roots time who false).toReal =
      1 - (roots time who true).toReal := by linarith
  rw [hstep, hplan, hsplit, hfactor, hCM, hcontinue]
  ring

/-! ## Caps and floors from the solo-exit assumptions -/

/-- The fixed-opponent quit value never exceeds `1` under capped joint
exit. -/
theorem quittingFixedOpponentsQuitValue_le_one_of_cappedJointExit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcap : QuittingCappedJointExit reward)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward roots who time ≤ 1 := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots who
    (0 : Payoff ι) time]
  exact quittingRootQuitPayoff_le_one_of_cappedJointExit hcap
    (0 : Payoff ι) (roots time) who

/-- Under unit solo exit, the fixed-opponent quit value is within twice the
payoff bound times the opponent absorption mass of `1`. -/
theorem abs_quittingFixedOpponentsQuitValue_sub_one_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingFixedOpponentsQuitValue reward roots who time - 1| ≤
      2 * M * quittingRootOpponentAbsorptionMass (roots time) who := by
  have hsolo : reward (quittingSingletonTerminal who) who = 1 := hunit who
  have hcompare :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (0 : Payoff ι) (roots time) who M hreward
  rw [hsolo, quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots
    who (0 : Payoff ι) time] at hcompare
  exact hcompare

/-- **The plan-value floor.**  Under unit solo exit, a one-stage perfect row
keeps the plan's value at that stage above `1` minus the row tolerance and
twice the payoff bound times the stage's opponent absorption mass: quitting
now is worth almost the solo exit, and perfectness caps its edge over the
prescribed value. -/
theorem one_sub_le_quittingRootSequenceTerminalValue_of_rowPerfect
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) {M εr : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hperfect : QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (time + 1)) (roots time)
      εr) :
    1 - εr - 2 * M * quittingRootOpponentAbsorptionMass (roots time) who ≤
      quittingRootSequenceTerminalValue reward roots who time := by
  have hclause := (hperfect who).1
  have hrecursion :=
    quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector reward
      roots who time
  have hbridge := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    roots who (quittingRootSequenceTailVector reward roots (time + 1)) time
  rw [hbridge, ← hrecursion] at hclause
  have hnear := abs_quittingFixedOpponentsQuitValue_sub_one_le hunit roots
    who time hreward
  have hnear' := (abs_le.mp hnear).1
  linarith

/-! ## The opponent-absorption reward is small with the opponent hazard -/

omit [DecidableEq ι] in
/-- The all-continue action carries no quitters. -/
theorem quittingQuitters_nonempty_iff_ne_allContinue (action : ι → Bool) :
    (quittingQuitters action).Nonempty ↔
      action ≠ (quittingAllContinueAction : ι → Bool) := by
  constructor
  · rintro ⟨someone, hsomeone⟩ heq
    have htrue : action someone = true := by
      simpa [quittingQuitters] using hsomeone
    rw [heq] at htrue
    simp [quittingAllContinueAction] at htrue
  · intro hne
    obtain ⟨someone, hsomeone⟩ := Function.ne_iff.mp hne
    have htrue : action someone = true := by
      cases haction : action someone with
      | false =>
          exact absurd (by simp [haction, quittingAllContinueAction])
            hsomeone
      | true => rfl
    exact ⟨someone, by simpa [quittingQuitters] using htrue⟩

omit [DecidableEq ι] in
/-- The absorbing contribution is bounded by the payoff bound times the
absorption mass: only absorbing actions contribute, and each contributes a
bounded reward. -/
theorem abs_quittingRootAbsorbingContribution_le_mul_absorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootAbsorbingContribution reward root who| ≤
      M * quittingRootAbsorptionMass root := by
  classical
  have hpointwise : ∀ action : ι → Bool,
      |quittingRootPayoff reward (0 : Payoff ι) action who| ≤
        (if (quittingQuitters action).Nonempty then M else 0) := by
    intro action
    unfold quittingRootPayoff
    by_cases hquit : (quittingQuitters action).Nonempty
    · rw [dif_pos hquit, if_pos hquit]
      exact hreward _ who
    · rw [dif_neg hquit, if_neg hquit]
      simp
  have hcapSplit : (fun action : ι → Bool =>
      if (quittingQuitters action).Nonempty then M else 0) =
      fun action => M *
        (if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) := by
    funext action
    by_cases hquit : (quittingQuitters action).Nonempty <;> simp [hquit]
  have hcomplement : ∀ action : ι → Bool,
      (if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
        1 - (if action = (quittingAllContinueAction : ι → Bool)
          then (1 : ℝ) else 0) := by
    intro action
    by_cases heq : action = (quittingAllContinueAction : ι → Bool)
    · have hempty : ¬ (quittingQuitters action).Nonempty := fun hnonempty =>
        (quittingQuitters_nonempty_iff_ne_allContinue action).1 hnonempty heq
      rw [if_neg hempty, if_pos heq]
      norm_num
    · have hnonempty :=
        (quittingQuitters_nonempty_iff_ne_allContinue action).2 heq
      rw [if_pos hnonempty, if_neg heq]
      norm_num
  have hpoint : expect (pmfPi root) (fun action =>
      if action = (quittingAllContinueAction : ι → Bool)
        then (1 : ℝ) else 0) =
      quittingStationaryContinueMass root := by
    rw [expect_eq_sum]
    rw [Finset.sum_eq_single (quittingAllContinueAction : ι → Bool)]
    · simp [quittingStationaryContinueMass]
    · intro action _ hne
      simp [hne]
    · intro habsent
      exact absurd (Finset.mem_univ _) habsent
  have hindicatorExpect : expect (pmfPi root) (fun action =>
      if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
      quittingRootAbsorptionMass root := by
    have hrewrite : (fun action : ι → Bool =>
        if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
        fun action =>
          1 - (if action = (quittingAllContinueAction : ι → Bool)
            then (1 : ℝ) else 0) :=
      funext hcomplement
    rw [hrewrite, expect_sub, expect_const, hpoint]
    rfl
  have hcapExpect : expect (pmfPi root) (fun action =>
      if (quittingQuitters action).Nonempty then M else 0) =
      M * quittingRootAbsorptionMass root := by
    rw [hcapSplit, expect_const_mul, hindicatorExpect]
  have hupper : quittingRootAbsorbingContribution reward root who ≤
      M * quittingRootAbsorptionMass root := by
    rw [← hcapExpect]
    apply expect_mono
    intro action
    exact le_trans (le_abs_self _) (hpointwise action)
  have hlower : -(M * quittingRootAbsorptionMass root) ≤
      quittingRootAbsorbingContribution reward root who := by
    have hneg : expect (pmfPi root) (fun action =>
        (0 : ℝ) - quittingRootPayoff reward (0 : Payoff ι) action who) ≤
        expect (pmfPi root) (fun action =>
          if (quittingQuitters action).Nonempty then M else 0) := by
      apply expect_mono
      intro action
      calc (0 : ℝ) - quittingRootPayoff reward (0 : Payoff ι) action who ≤
          |quittingRootPayoff reward (0 : Payoff ι) action who| := by
            have := neg_abs_le
              (quittingRootPayoff reward (0 : Payoff ι) action who)
            linarith
        _ ≤ _ := hpointwise action
    rw [expect_sub, expect_const, hcapExpect] at hneg
    have hAC : expect (pmfPi root)
        (fun action => quittingRootPayoff reward (0 : Payoff ι) action who) =
        quittingRootAbsorbingContribution reward root who := rfl
    rw [hAC] at hneg
    linarith
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-- The opponent-absorption reward is bounded by the payoff bound times the
stage's opponent absorption mass. -/
theorem abs_quittingFixedOpponentsContinueReward_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingFixedOpponentsContinueReward reward roots who time| ≤
      M * quittingRootOpponentAbsorptionMass (roots time) who :=
  abs_quittingRootAbsorbingContribution_le_mul_absorptionMass reward
    (Function.update (roots time) who (PMF.pure false)) who hreward

end GameTheory
