import UniformEquilibrium.Diagnostics.Quitting.PureTimeScreenedMenu
import UniformEquilibrium.Quitting.Paths.PureTimeDeadlineSelection

/-!
# Exact pure-time cap attainment against canonical opponents

The first opponent deadline reduces the unrestricted behavioral cap to two
values at date zero and three values at a positive date.  If no opponent has
a finite deadline, the cap is attained by immediate Quit or `Never`.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- When the first opponent deadline is zero, the unrestricted cap is the
better of joining that coalition and passing it. -/
theorem quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι)
    (hat : (quittingPureTimeOpponentCoalitionAt times who 0).Nonempty) :
    quittingContinuationBestResponseValue reward
        (quittingPureTimeProfileBehavior reward times) who =
      max
        (reward ⟨insert who
          (quittingPureTimeOpponentCoalitionAt times who 0),
          Finset.insert_nonempty who _⟩ who)
        (reward ⟨quittingPureTimeOpponentCoalitionAt times who 0, hat⟩ who) := by
  let profile := quittingPureTimeProfileBehavior reward times
  let endpoint := max
    (reward ⟨insert who
      (quittingPureTimeOpponentCoalitionAt times who 0),
      Finset.insert_nonempty who _⟩ who)
    (reward ⟨quittingPureTimeOpponentCoalitionAt times who 0, hat⟩ who)
  let pureValues : Set ℝ := Set.range fun quitTime : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime)) who
  have hpureNonempty : pureValues.Nonempty := ⟨_, ⟨none, rfl⟩⟩
  have hpureBdd : BddAbove pureValues := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨quitTime, rfl⟩
    exact le_trans (le_abs_self _)
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who)
  have hbefore : ∀ time < 0,
      quittingPureTimeOpponentCoalitionAt times who time = ∅ := by omega
  have hpureUpper : ∀ value ∈ pureValues, value ≤ endpoint := by
    rintro value ⟨quitTime, rfl⟩
    rcases quitTime with _ | time
    · change quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who ≤ endpoint
      rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
        quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
          reward times who 0 hbefore hat]
      exact le_max_right _ _
    · rcases Nat.eq_zero_or_pos time with rfl | htime
      · change quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some 0))) who ≤ endpoint
        rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
          quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
            reward times who 0 hbefore]
        exact le_max_left _ _
      · change quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some time))) who ≤
            endpoint
        rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
          quittingTerminalPayoff_pureTimeProfile_update_late_eq_firstOpponent
            reward times who 0 time hbefore hat htime]
        exact le_max_right _ _
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  change sSup pureValues = endpoint
  apply le_antisymm
  · exact csSup_le hpureNonempty hpureUpper
  · apply max_le
    · rw [← quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
        reward times who 0 hbefore]
      exact le_csSup hpureBdd ⟨some 0, rfl⟩
    · rw [← quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
        reward times who 0 hbefore hat]
      exact le_csSup hpureBdd ⟨none, rfl⟩

/-- If one displayed owner is the only player with a finite deadline and its
solo reward is nonpositive, replacing that owner by `Never` produces the
literal all-`Never` profile, attains its unrestricted cap, and gains exactly
the owner's source semantic debt. -/
theorem pureTimeSingletonOwner_allOpponentsNever_never_eq_cap_and_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (owner : ι) (deadline : ℕ)
    (howner : times owner = some deadline)
    (hopponents : ∀ other, other ≠ owner → times other = none)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤ 0) :
    quittingPureTimeCoalitionAt times deadline = {owner} ∧
      quittingPureTimeProfileBehavior reward (Function.update times owner none) =
        quittingAlwaysContinueProfile reward ∧
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times owner none)) owner =
        quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward times) owner ∧
      quittingTerminalPayoff reward
            (quittingPureTimeProfileBehavior reward
              (Function.update times owner none)) owner -
          quittingTerminalPayoff reward
            (quittingPureTimeProfileBehavior reward times) owner =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward times)) owner := by
  have hsingleton : quittingPureTimeCoalitionAt times deadline = {owner} := by
    ext other
    by_cases heq : other = owner
    · subst other
      simp [quittingPureTimeCoalitionAt, howner]
    · simp [quittingPureTimeCoalitionAt, heq, hopponents other heq]
  have hprofileNever :
      quittingPureTimeProfileBehavior reward (Function.update times owner none) =
        quittingAlwaysContinueProfile reward := by
    funext other
    by_cases heq : other = owner
    · subst other
      rw [quittingPureTimeProfileBehavior_apply, Function.update_self,
        quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
      rfl
    · rw [quittingPureTimeProfileBehavior_apply, Function.update_of_ne heq,
        hopponents other heq,
        quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
      rfl
  have hcap : quittingContinuationBestResponseValue reward
        (quittingPureTimeProfileBehavior reward times) owner = 0 := by
    rw [← quittingContinuationBestResponseValue_update_self reward
      (quittingPureTimeProfileBehavior reward times) owner
      (quittingPureTimeBehaviorStrategy reward owner none),
      ← quittingPureTimeProfileBehavior_update, hprofileNever,
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      max_eq_left hsolo]
  have hpayoff : quittingTerminalPayoff reward
      (quittingPureTimeProfileBehavior reward
        (Function.update times owner none)) owner = 0 := by
    rw [hprofileNever, quittingTerminalPayoff_quittingAlwaysContinue]
  refine ⟨hsingleton, hprofileNever, hpayoff.trans hcap.symm, ?_⟩
  unfold quittingTerminalSemanticDebt
  dsimp only [quittingTerminalSemanticPair]
  rw [hpayoff, hcap]

/-- Against a canonical pure-time opponent profile, some pure finite time or
`Never` attains the unrestricted behavioral cap exactly. -/
theorem exists_quittingPureTime_capAttainer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) :
    ∃ response : Option ℕ,
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times who response)) who =
        quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward times) who := by
  by_cases hsupport :
      (quittingPureTimeOpponentDeadlineSupport times who).Nonempty
  · obtain ⟨deadline, hat, hbefore⟩ :=
      exists_quittingPureTime_firstOpponentDeadline times who hsupport
    rcases Nat.eq_zero_or_pos deadline with rfl | hpositive
    · have hcap :=
        quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
          reward times who hat
      by_cases hjoin :
          reward ⟨quittingPureTimeOpponentCoalitionAt times who 0, hat⟩ who ≤
            reward ⟨insert who
              (quittingPureTimeOpponentCoalitionAt times who 0),
              Finset.insert_nonempty who _⟩ who
      · refine ⟨some 0, ?_⟩
        rw [quittingPureTimeProfileBehavior_update,
          quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
            reward times who 0 hbefore,
          hcap, max_eq_left hjoin]
      · refine ⟨none, ?_⟩
        rw [quittingPureTimeProfileBehavior_update,
          quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
            reward times who 0 hbefore hat,
          hcap, max_eq_right (le_of_not_ge hjoin)]
    · have hcap := quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
        reward times who deadline hpositive hbefore hat
      let singleton := reward (quittingSingletonTerminal who) who
      let join := reward ⟨insert who
        (quittingPureTimeOpponentCoalitionAt times who deadline),
        Finset.insert_nonempty who _⟩ who
      let pass := reward
        ⟨quittingPureTimeOpponentCoalitionAt times who deadline, hat⟩ who
      by_cases hsingle : max join pass ≤ singleton
      · refine ⟨some 0, ?_⟩
        rw [quittingPureTimeProfileBehavior_update,
          quittingTerminalPayoff_pureTimeProfile_update_early_eq_singleton
            reward times who deadline 0 hbefore hpositive,
          hcap]
        change singleton = max singleton (max join pass)
        exact (max_eq_left hsingle).symm
      · by_cases hjoin : pass ≤ join
        · refine ⟨some deadline, ?_⟩
          rw [quittingPureTimeProfileBehavior_update,
            quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
              reward times who deadline hbefore,
            hcap]
          change join = max singleton (max join pass)
          rw [max_eq_left hjoin]
          have hnot : ¬join ≤ singleton := by
            intro hle
            exact hsingle (by simpa [max_eq_left hjoin] using hle)
          exact (max_eq_right (le_of_not_ge hnot)).symm
        · refine ⟨none, ?_⟩
          rw [quittingPureTimeProfileBehavior_update,
            quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
              reward times who deadline hbefore hat,
            hcap]
          change pass = max singleton (max join pass)
          rw [max_eq_right (le_of_not_ge hjoin)]
          have hnot : ¬pass ≤ singleton := by
            intro hle
            exact hsingle (by simpa [max_eq_right (le_of_not_ge hjoin)] using hle)
          exact (max_eq_right (le_of_not_ge hnot)).symm
  · have hallNever : ∀ other, other ≠ who → times other = none := by
      intro other hne
      cases htime : times other with
      | none => rfl
      | some time =>
          exfalso
          apply hsupport
          exact ⟨time, (mem_quittingPureTimeOpponentDeadlineSupport_iff
            times who time).2 ⟨other, hne, htime⟩⟩
    have hprofileNever :
        quittingPureTimeProfileBehavior reward (Function.update times who none) =
          quittingAlwaysContinueProfile reward := by
      funext other
      by_cases heq : other = who
      · subst other
        rw [quittingPureTimeProfileBehavior_apply, Function.update_self,
          quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
        rfl
      · rw [quittingPureTimeProfileBehavior_apply, Function.update_of_ne heq,
          hallNever other heq,
          quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
        rfl
    have hcap : quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward times) who =
        max 0 (reward (quittingSingletonTerminal who) who) := by
      rw [← quittingContinuationBestResponseValue_update_self reward
        (quittingPureTimeProfileBehavior reward times) who
        (quittingPureTimeBehaviorStrategy reward who none),
        ← quittingPureTimeProfileBehavior_update, hprofileNever,
        quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
    by_cases hsolo : 0 ≤ reward (quittingSingletonTerminal who) who
    · refine ⟨some 0, ?_⟩
      have hpayoff : quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times who (some 0))) who =
          reward (quittingSingletonTerminal who) who := by
        rw [quittingPureTimeProfileBehavior_update]
        apply quittingTerminalPayoff_pureTimeProfile_update_early_eq_singleton
          reward times who 1 0
        · intro offset hoffset
          rw [show offset = 0 by omega]
          ext other
          constructor
          · intro hmem
            have hne : other ≠ who := (Finset.mem_erase.mp hmem).1
            have htime : times other = some 0 := by
              simpa [quittingPureTimeCoalitionAt] using
                (Finset.mem_erase.mp hmem).2
            rw [hallNever other hne] at htime
            simp at htime
          · intro hmem
            simp at hmem
        · omega
      rw [hpayoff, hcap, max_eq_right hsolo]
    · refine ⟨none, ?_⟩
      rw [hprofileNever, quittingTerminalPayoff_quittingAlwaysContinue,
        hcap, max_eq_left (le_of_not_ge hsolo)]

end GameTheory
