import UniformEquilibrium.Diagnostics.Quitting.PureTimeDeadlineSemantics

/-!
# Screened pure-time response menus

Against canonical pure-time opponents, their first nonempty deadline screens
every later response.  These lemmas identify the resulting three payoff
values before taking the unrestricted behavioral cap.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem quittingPureTimeCoalitionAt_update_eq_opponents_of_ne
    (times : QuittingPureTimeProfile ι) (who : ι)
    (replacement : Option ℕ) (time : ℕ)
    (hne : replacement ≠ some time) :
    quittingPureTimeCoalitionAt (Function.update times who replacement) time =
      quittingPureTimeOpponentCoalitionAt times who time := by
  rw [quittingPureTimeCoalitionAt_update, if_neg hne]
  rfl

private theorem quittingPureTimeCoalitionAt_update_eq_insert_opponents
    (times : QuittingPureTimeProfile ι) (who : ι) (time : ℕ) :
    quittingPureTimeCoalitionAt (Function.update times who (some time)) time =
      insert who (quittingPureTimeOpponentCoalitionAt times who time) := by
  rw [quittingPureTimeCoalitionAt_update, if_pos rfl]
  rfl

/-- `Never` reaches the first nonempty opponent deadline and receives that
opponent coalition's reward. -/
theorem quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) (deadline : ℕ)
    (hbefore : ∀ time < deadline,
      quittingPureTimeOpponentCoalitionAt times who time = ∅)
    (hat : (quittingPureTimeOpponentCoalitionAt times who deadline).Nonempty) :
    quittingTerminalPayoff reward
        (Function.update (quittingPureTimeProfileBehavior reward times) who
          (quittingPureTimeBehaviorStrategy reward who none)) who =
      reward ⟨quittingPureTimeOpponentCoalitionAt times who deadline, hat⟩ who := by
  rw [← quittingPureTimeProfileBehavior_update]
  have hfirst : ∀ time < deadline,
      quittingPureTimeCoalitionAt
        (Function.update times who none) time = ∅ := by
    intro time htime
    rw [quittingPureTimeCoalitionAt_update_eq_opponents_of_ne]
    · exact hbefore time htime
    · simp
  have hat' : (quittingPureTimeCoalitionAt
      (Function.update times who none) deadline).Nonempty := by
    rw [quittingPureTimeCoalitionAt_update_eq_opponents_of_ne]
    · exact hat
    · simp
  have hpayoff := quittingTerminalPayoff_pureTimeProfileBehavior_eq
    reward (Function.update times who none) deadline hfirst hat'
  simpa [quittingPureTimeCoalitionAt_update_eq_opponents_of_ne] using
    congrFun hpayoff who

/-- Quitting strictly before the first opponent deadline receives the
singleton reward. -/
theorem quittingTerminalPayoff_pureTimeProfile_update_early_eq_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) (deadline time : ℕ)
    (hbefore : ∀ offset < deadline,
      quittingPureTimeOpponentCoalitionAt times who offset = ∅)
    (htime : time < deadline) :
    quittingTerminalPayoff reward
        (Function.update (quittingPureTimeProfileBehavior reward times) who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who =
      reward (quittingSingletonTerminal who) who := by
  rw [← quittingPureTimeProfileBehavior_update]
  have hcoalition : quittingPureTimeOpponentCoalitionAt times who time = ∅ :=
    hbefore time htime
  have hfirst : ∀ offset < time,
      quittingPureTimeCoalitionAt
        (Function.update times who (some time)) offset = ∅ := by
    intro offset hoffset
    rw [quittingPureTimeCoalitionAt_update_eq_opponents_of_ne]
    · exact hbefore offset (hoffset.trans htime)
    · intro heq
      have := Option.some.inj heq
      omega
  have hat : (quittingPureTimeCoalitionAt
      (Function.update times who (some time)) time).Nonempty := by
    rw [quittingPureTimeCoalitionAt_update_eq_insert_opponents, hcoalition]
    simp
  have hpayoff := quittingTerminalPayoff_pureTimeProfileBehavior_eq
    reward (Function.update times who (some time)) time hfirst hat
  simpa [quittingPureTimeCoalitionAt_update_eq_insert_opponents,
    hcoalition, quittingSingletonTerminal] using congrFun hpayoff who

/-- Quitting at the first opponent deadline joins that coalition. -/
theorem quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) (deadline : ℕ)
    (hbefore : ∀ time < deadline,
      quittingPureTimeOpponentCoalitionAt times who time = ∅) :
    quittingTerminalPayoff reward
        (Function.update (quittingPureTimeProfileBehavior reward times) who
          (quittingPureTimeBehaviorStrategy reward who (some deadline))) who =
      reward ⟨insert who
        (quittingPureTimeOpponentCoalitionAt times who deadline),
        Finset.insert_nonempty who _⟩ who := by
  rw [← quittingPureTimeProfileBehavior_update]
  have hfirst : ∀ time < deadline,
      quittingPureTimeCoalitionAt
        (Function.update times who (some deadline)) time = ∅ := by
    intro time htime
    rw [quittingPureTimeCoalitionAt_update_eq_opponents_of_ne]
    · exact hbefore time htime
    · exact fun heq => Nat.ne_of_lt htime (Option.some.inj heq).symm
  have hpayoff := quittingTerminalPayoff_pureTimeProfileBehavior_eq
    reward (Function.update times who (some deadline)) deadline hfirst
      (by rw [quittingPureTimeCoalitionAt_update_eq_insert_opponents]; simp)
  simpa [quittingPureTimeCoalitionAt_update_eq_insert_opponents] using
    congrFun hpayoff who

/-- Quitting after the first opponent deadline is screened just like Never. -/
theorem quittingTerminalPayoff_pureTimeProfile_update_late_eq_firstOpponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) (deadline time : ℕ)
    (hbefore : ∀ offset < deadline,
      quittingPureTimeOpponentCoalitionAt times who offset = ∅)
    (hat : (quittingPureTimeOpponentCoalitionAt times who deadline).Nonempty)
    (htime : deadline < time) :
    quittingTerminalPayoff reward
        (Function.update (quittingPureTimeProfileBehavior reward times) who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who =
      reward ⟨quittingPureTimeOpponentCoalitionAt times who deadline, hat⟩ who := by
  rw [← quittingPureTimeProfileBehavior_update]
  have hne : (some time : Option ℕ) ≠ some deadline := by
    intro heq
    have := Option.some.inj heq
    omega
  have hfirst : ∀ offset < deadline,
      quittingPureTimeCoalitionAt
        (Function.update times who (some time)) offset = ∅ := by
    intro offset hoffset
    rw [quittingPureTimeCoalitionAt_update_eq_opponents_of_ne]
    · exact hbefore offset hoffset
    · intro heq
      have := Option.some.inj heq
      omega
  have hAt : quittingPureTimeCoalitionAt
      (Function.update times who (some time)) deadline =
        quittingPureTimeOpponentCoalitionAt times who deadline :=
    quittingPureTimeCoalitionAt_update_eq_opponents_of_ne
      times who (some time) deadline hne
  have hpayoff := quittingTerminalPayoff_pureTimeProfileBehavior_eq
    reward (Function.update times who (some time)) deadline hfirst
      (by simpa only [hAt] using hat)
  simpa only [hAt] using congrFun hpayoff who

/-- When the singleton response is no better than the two screened endpoints,
the unrestricted behavioral cap is exactly the better endpoint.  This is the
three-value calculation; no stationarity or finite-horizon restriction is
placed on the deviating player. -/
theorem quittingContinuationBestResponseValue_pureTimeProfile_eq_max_screened
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) (deadline : ℕ)
    (hbefore : ∀ time < deadline,
      quittingPureTimeOpponentCoalitionAt times who time = ∅)
    (hat : (quittingPureTimeOpponentCoalitionAt times who deadline).Nonempty)
    (hsingleton : reward (quittingSingletonTerminal who) who ≤
      max
        (reward ⟨insert who
          (quittingPureTimeOpponentCoalitionAt times who deadline),
          Finset.insert_nonempty who _⟩ who)
        (reward ⟨quittingPureTimeOpponentCoalitionAt times who deadline,
          hat⟩ who)) :
    quittingContinuationBestResponseValue reward
        (quittingPureTimeProfileBehavior reward times) who =
      max
        (reward ⟨insert who
          (quittingPureTimeOpponentCoalitionAt times who deadline),
          Finset.insert_nonempty who _⟩ who)
        (reward ⟨quittingPureTimeOpponentCoalitionAt times who deadline,
          hat⟩ who) := by
  let profile := quittingPureTimeProfileBehavior reward times
  let endpoint := max
    (reward ⟨insert who
      (quittingPureTimeOpponentCoalitionAt times who deadline),
      Finset.insert_nonempty who _⟩ who)
    (reward ⟨quittingPureTimeOpponentCoalitionAt times who deadline, hat⟩ who)
  let pureValues : Set ℝ := Set.range fun quitTime : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime)) who
  have hpureNonempty : pureValues.Nonempty := by
    exact ⟨_, ⟨none, rfl⟩⟩
  have hpureBdd : BddAbove pureValues := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨quitTime, rfl⟩
    exact le_trans (le_abs_self _) (abs_quittingTerminalPayoff_le_quittingRewardBound
      reward _ who)
  have hpureUpper : ∀ value ∈ pureValues, value ≤ endpoint := by
    rintro value ⟨quitTime, rfl⟩
    rcases quitTime with _ | time
    · change quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who ≤ endpoint
      rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
        quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
          reward times who deadline hbefore hat]
      exact le_max_right _ _
    · rcases lt_trichotomy time deadline with htime | htime | htime
      · change quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some time))) who ≤
            endpoint
        rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
          quittingTerminalPayoff_pureTimeProfile_update_early_eq_singleton
            reward times who deadline time hbefore htime]
        exact hsingleton
      · subst time
        change quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some deadline))) who ≤
            endpoint
        rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
          quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
            reward times who deadline hbefore]
        exact le_max_left _ _
      · change quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some time))) who ≤
            endpoint
        rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
          quittingTerminalPayoff_pureTimeProfile_update_late_eq_firstOpponent
            reward times who deadline time hbefore hat htime]
        exact le_max_right _ _
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  change sSup pureValues = endpoint
  apply le_antisymm
  · exact csSup_le hpureNonempty hpureUpper
  · apply max_le
    · rw [← quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
        reward times who deadline hbefore]
      exact le_csSup hpureBdd ⟨some deadline, rfl⟩
    · rw [← quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
        reward times who deadline hbefore hat]
      exact le_csSup hpureBdd ⟨none, rfl⟩

/-- At a positive first-opponent deadline, the unrestricted behavioral cap is
the maximum of exactly three values: early singleton Quit, joining the first
opponent coalition, and passing that coalition (including `Never`). -/
theorem quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) (deadline : ℕ)
    (hdeadline : 0 < deadline)
    (hbefore : ∀ time < deadline,
      quittingPureTimeOpponentCoalitionAt times who time = ∅)
    (hat : (quittingPureTimeOpponentCoalitionAt times who deadline).Nonempty) :
    quittingContinuationBestResponseValue reward
        (quittingPureTimeProfileBehavior reward times) who =
      max (reward (quittingSingletonTerminal who) who)
        (max
          (reward ⟨insert who
            (quittingPureTimeOpponentCoalitionAt times who deadline),
            Finset.insert_nonempty who _⟩ who)
          (reward ⟨quittingPureTimeOpponentCoalitionAt times who deadline,
            hat⟩ who)) := by
  let profile := quittingPureTimeProfileBehavior reward times
  let endpoint := max
    (reward ⟨insert who
      (quittingPureTimeOpponentCoalitionAt times who deadline),
      Finset.insert_nonempty who _⟩ who)
    (reward ⟨quittingPureTimeOpponentCoalitionAt times who deadline, hat⟩ who)
  let cap := max (reward (quittingSingletonTerminal who) who) endpoint
  let pureValues : Set ℝ := Set.range fun quitTime : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime)) who
  have hpureNonempty : pureValues.Nonempty := ⟨_, ⟨none, rfl⟩⟩
  have hpureBdd : BddAbove pureValues := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨quitTime, rfl⟩
    exact le_trans (le_abs_self _) (abs_quittingTerminalPayoff_le_quittingRewardBound
      reward _ who)
  have hpureUpper : ∀ value ∈ pureValues, value ≤ cap := by
    rintro value ⟨quitTime, rfl⟩
    rcases quitTime with _ | time
    · change quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who ≤ cap
      rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
        quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
          reward times who deadline hbefore hat]
      exact le_max_of_le_right (le_max_right _ _)
    · rcases lt_trichotomy time deadline with htime | htime | htime
      · change quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some time))) who ≤ cap
        rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
          quittingTerminalPayoff_pureTimeProfile_update_early_eq_singleton
            reward times who deadline time hbefore htime]
        exact le_max_left _ _
      · subst time
        change quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some deadline))) who ≤
            cap
        rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
          quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
            reward times who deadline hbefore]
        exact le_max_of_le_right (le_max_left _ _)
      · change quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who (some time))) who ≤ cap
        rw [show profile = quittingPureTimeProfileBehavior reward times by rfl,
          quittingTerminalPayoff_pureTimeProfile_update_late_eq_firstOpponent
            reward times who deadline time hbefore hat htime]
        exact le_max_of_le_right (le_max_right _ _)
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  change sSup pureValues = cap
  apply le_antisymm
  · exact csSup_le hpureNonempty hpureUpper
  · apply max_le
    · rw [← quittingTerminalPayoff_pureTimeProfile_update_early_eq_singleton
        reward times who deadline 0 hbefore hdeadline]
      exact le_csSup hpureBdd ⟨some 0, rfl⟩
    · apply max_le
      · rw [← quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
          reward times who deadline hbefore]
        exact le_csSup hpureBdd ⟨some deadline, rfl⟩
      · rw [← quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
          reward times who deadline hbefore hat]
        exact le_csSup hpureBdd ⟨none, rfl⟩

end GameTheory
