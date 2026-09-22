/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Quitting.Paths.FirstStoppingOutcomeCoalition
import UniformEquilibrium.Quitting.Paths.PureTimeDeadlineSelection
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance

/-!
# Membership-toggle obstruction for complete pure clocks

A positive table-level membership-toggle gap rules out exact terminal Nash
within the complete pure-clock class.  The deviation produced below is an
actual behavioral deviation.  This module does not claim that the table-level
condition supplies a gap against arbitrary behavioral profiles.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A uniform gain from a solo exit at Never and from joining or leaving every
nonempty first coalition. -/
structure HasQuittingPureTimeMembershipToggleGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) : Prop where
  solo : ∃ who,
    gap ≤ reward ⟨{who}, Finset.singleton_nonempty who⟩ who
  toggle : ∀ coalition : {S : Finset ι // S.Nonempty},
    (∃ outsider, outsider ∉ coalition.1 ∧
      reward coalition outsider + gap ≤
        reward
          ⟨insert outsider coalition.1,
            Finset.insert_nonempty outsider coalition.1⟩ outsider) ∨
    ∃ member, member ∈ coalition.1 ∧
      ∃ hremaining : (coalition.1.erase member).Nonempty,
        reward coalition member + gap ≤
          reward ⟨coalition.1.erase member, hremaining⟩ member

omit [DecidableEq ι] in
private theorem quittingStoppingTimeValue_lt_of_firstCoalition_not_mem
    (times : QuittingPureTimeProfile ι) (deadline : ℕ)
    (hbefore : ∀ time < deadline,
      quittingPureTimeCoalitionAt times time = ∅)
    {who : ι} (hwho : who ∉ quittingPureTimeCoalitionAt times deadline) :
    quittingStoppingTimeValue (some deadline) <
      quittingStoppingTimeValue (times who) := by
  cases htime : times who with
  | none => simp [quittingStoppingTimeValue]
  | some time =>
      have htimeNe : time ≠ deadline := by
        intro heq
        subst time
        apply hwho
        simp [quittingPureTimeCoalitionAt, htime]
      have hnotLt : ¬ time < deadline := by
        intro hlt
        have hmem : who ∈ quittingPureTimeCoalitionAt times time := by
          simp [quittingPureTimeCoalitionAt, htime]
        rw [hbefore time hlt] at hmem
        simp at hmem
      have hdeadlineLt : deadline < time :=
        lt_of_le_of_ne (Nat.le_of_not_gt hnotLt) htimeNe.symm
      simpa [quittingStoppingTimeValue] using hdeadlineLt

namespace HasQuittingPureTimeMembershipToggleGap

/-- Every complete pure-clock profile admits an actual behavioral unilateral
deviation gaining at least the table-level toggle gap. -/
theorem exists_behaviorDeviation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gap : ℝ}
    (condition : HasQuittingPureTimeMembershipToggleGap reward gap)
    (times : QuittingPureTimeProfile ι) :
    ∃ (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who),
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward times) who + gap ≤
        quittingTerminalPayoff reward
          (Function.update (quittingPureTimeProfileBehavior reward times)
            who deviation) who := by
  classical
  let _ : Nonempty ι := ⟨condition.solo.choose⟩
  by_cases hsupport :
      (quittingPureTimeDeadlineSupport times).Nonempty
  · obtain ⟨deadline, hcoalition, hbefore⟩ :=
      exists_quittingPureTime_firstDeadline times hsupport
    let coalition : {S : Finset ι // S.Nonempty} :=
      ⟨quittingPureTimeCoalitionAt times deadline, hcoalition⟩
    have hinside : ∀ who ∈ coalition.1, times who = some deadline := by
      intro who hwho
      simpa [coalition, quittingPureTimeCoalitionAt] using hwho
    have hlater : ∀ who ∉ coalition.1,
        quittingStoppingTimeValue (some deadline) <
          quittingStoppingTimeValue (times who) := by
      intro who hwho
      exact quittingStoppingTimeValue_lt_of_firstCoalition_not_mem
        times deadline hbefore hwho
    have hcurrent : quittingFirstStoppingOutcome times = some coalition := by
      exact quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
        times coalition.1 coalition.2 deadline hinside hlater
    rcases condition.toggle coalition with hjoin | hleave
    · obtain ⟨who, hwho, hgain⟩ := hjoin
      have hnew :
          quittingFirstStoppingOutcome
              (Function.update times who (some deadline)) =
            some
              ⟨insert who coalition.1,
                Finset.insert_nonempty who coalition.1⟩ := by
        apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
          (time := deadline)
        · intro player hplayer
          by_cases heq : player = who
          · subst player
            simp
          · rw [Function.update_of_ne heq]
            exact hinside player
              ((Finset.mem_insert.mp hplayer).resolve_left heq)
        · intro player hplayer
          have hne : player ≠ who := by
            intro heq
            subst player
            exact hplayer (Finset.mem_insert_self who coalition.1)
          rw [Function.update_of_ne hne]
          apply hlater player
          intro hmem
          exact hplayer (Finset.mem_insert_of_mem hmem)
      refine ⟨who,
        quittingPureTimeBehaviorStrategy reward who (some deadline), ?_⟩
      rw [← quittingPureTimeProfileBehavior_update]
      rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
        quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
        hcurrent, hnew]
      simpa only [quittingTerminalOutcomeReward] using hgain
    · obtain ⟨who, -, hremaining, hgain⟩ := hleave
      have hnew :
          quittingFirstStoppingOutcome (Function.update times who none) =
            some ⟨coalition.1.erase who, hremaining⟩ := by
        apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
          (time := deadline)
        · intro player hplayer
          have hmem := Finset.mem_erase.mp hplayer
          rw [Function.update_of_ne hmem.1]
          exact hinside player hmem.2
        · intro player hplayer
          by_cases heq : player = who
          · subst player
            simp [quittingStoppingTimeValue]
          · rw [Function.update_of_ne heq]
            apply hlater player
            intro hmem
            exact hplayer (Finset.mem_erase.mpr ⟨heq, hmem⟩)
      refine ⟨who, quittingPureTimeBehaviorStrategy reward who none, ?_⟩
      rw [← quittingPureTimeProfileBehavior_update]
      rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
        quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
        hcurrent, hnew]
      simpa only [quittingTerminalOutcomeReward] using hgain
  · have htimes : times = fun _ : ι => none := by
      funext who
      cases htime : times who with
      | none => rfl
      | some deadline =>
          exfalso
          apply hsupport
          exact ⟨deadline,
            (mem_quittingPureTimeDeadlineSupport_iff times deadline).2
              ⟨who, htime⟩⟩
    subst times
    obtain ⟨who, hgain⟩ := condition.solo
    have hnew :
        quittingFirstStoppingOutcome
            (Function.update (fun _ : ι => none) who (some 0)) =
          some ⟨{who}, Finset.singleton_nonempty who⟩ := by
      apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
        (time := 0)
      · intro player hplayer
        have heq : player = who := Finset.mem_singleton.mp hplayer
        subst player
        simp
      · intro player hplayer
        have hne : player ≠ who := by simpa using hplayer
        rw [Function.update_of_ne hne]
        simp [quittingStoppingTimeValue]
    refine ⟨who, quittingPureTimeBehaviorStrategy reward who (some 0), ?_⟩
    rw [← quittingPureTimeProfileBehavior_update]
    rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
      quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
      quittingFirstStoppingOutcome_all_never, hnew]
    simpa only [quittingTerminalOutcomeReward, Pi.zero_apply, zero_add] using hgain

/-- A positive toggle gap rules out exact terminal Nash for every complete
pure-clock profile. -/
theorem not_isεAsymptoticNash_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gap : ℝ}
    (condition : HasQuittingPureTimeMembershipToggleGap reward gap)
    (hgap : 0 < gap) (times : QuittingPureTimeProfile ι) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingPureTimeProfileBehavior reward times) := by
  intro hnash
  obtain ⟨who, deviation, hgain⟩ := condition.exists_behaviorDeviation times
  have hupper := hnash who deviation
  linarith

end HasQuittingPureTimeMembershipToggleGap

end GameTheory
