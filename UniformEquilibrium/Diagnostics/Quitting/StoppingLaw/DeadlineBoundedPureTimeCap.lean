import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle

/-!
# Pure-time caps for deadline-bounded quitting profiles

This module contains only the finite-deadline kernel needed by the pure-clock
reduction: late pure quit dates have a common payoff, the unrestricted cap is
attained by `Never` or a bounded pure quit date, exact-cap replacement gain is
the source semantic debt, and such a replacement preserves deadline boundedness
with one step of slack.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- No player quits on the live path strictly after `deadline`. -/
def QuittingDeadlineBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (deadline : ℕ) : Prop :=
  ∀ (who : ι) (time : ℕ), deadline < time →
    quittingProfileLiveRoot reward profile time who = PMF.pure false

omit [DecidableEq ι] in
theorem quittingDeadlineBounded_liveRoot_eq_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline time : ℕ}
    (hbound : QuittingDeadlineBounded reward profile deadline)
    (htime : deadline < time) :
    quittingProfileLiveRoot reward profile time =
      (quittingAllContinueRoot : ι → PMF Bool) :=
  funext fun who => hbound who time htime

private theorem fixedOpponentsQuitValue_of_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {time : ℕ}
    (hroot : roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingFixedOpponentsQuitValue reward roots who time =
      reward (quittingSingletonTerminal who) who := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots who
      (0 : Payoff ι) time,
    hroot, quittingRootQuitPayoff_allContinueRoot]

private theorem fixedOpponentsContinueReward_of_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {time : ℕ}
    (hroot : roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingFixedOpponentsContinueReward reward roots who time = 0 := by
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents reward roots
    who (0 : Payoff ι) time
  rw [hroot, quittingRootContinuePayoff_allContinueRoot] at hcontinue
  simpa using hcontinue.symm

private theorem fixedOpponentsContinueMass_of_allContinueRoot
    (roots : ℕ → ι → PMF Bool) (who : ι) {time : ℕ}
    (hroot : roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingFixedOpponentsContinueMass roots who time = 1 := by
  have hupdate : Function.update (quittingAllContinueRoot : ι → PMF Bool) who
      (PMF.pure false) = (quittingAllContinueRoot : ι → PMF Bool) :=
    Function.update_eq_self who (quittingAllContinueRoot : ι → PMF Bool)
  unfold quittingFixedOpponentsContinueMass
  rw [hroot, hupdate,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [quittingAllContinueRoot]

private theorem rootSequencePureTimeTerminalValue_of_ne
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

private theorem rootSequencePureTimeTerminalValue_tail_eq_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {deadline : ℕ}
    (hall : ∀ time, deadline < time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∀ (gap start : ℕ), deadline < start →
      quittingRootSequencePureTimeTerminalValue reward roots who
          (some (start + gap)) start =
        reward (quittingSingletonTerminal who) who := by
  intro gap
  induction gap with
  | zero =>
      intro start hstart
      rw [Nat.add_zero,
        quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
        fixedOpponentsQuitValue_of_allContinueRoot reward roots who
          (hall start hstart)]
  | succ gap ih =>
      intro start hstart
      rw [rootSequencePureTimeTerminalValue_of_ne reward roots who
          (by omega : start ≠ start + (gap + 1)),
        fixedOpponentsContinueReward_of_allContinueRoot reward roots who
          (hall start hstart),
        fixedOpponentsContinueMass_of_allContinueRoot roots who
          (hall start hstart),
        show start + (gap + 1) = start + 1 + gap by omega,
        ih (start + 1) (by omega)]
      ring

private theorem rootSequenceHazardTerminalValue_congr_of_agree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (left right : ℕ → PMF Bool) :
    ∀ (span start : ℕ),
      (∀ time, start ≤ time → time < start + span → left time = right time) →
      quittingRootSequenceHazardTerminalValue reward roots who left
          (start + span) =
        quittingRootSequenceHazardTerminalValue reward roots who right
          (start + span) →
      quittingRootSequenceHazardTerminalValue reward roots who left start =
        quittingRootSequenceHazardTerminalValue reward roots who right start := by
  intro span
  induction span with
  | zero =>
      intro start _ hend
      simpa using hend
  | succ span ih =>
      intro start hagree hend
      have hstep : left start = right start := hagree start le_rfl (by omega)
      have htail :
          quittingRootSequenceHazardTerminalValue reward roots who left
              (start + 1) =
            quittingRootSequenceHazardTerminalValue reward roots who right
              (start + 1) := by
        refine ih (start + 1)
          (fun time htime hlt => hagree time (by omega) (by omega)) ?_
        rw [show start + 1 + span = start + (span + 1) by omega]
        exact hend
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman reward roots
          who left start,
        quittingRootSequenceHazardTerminalValue_eq_hazardBellman reward roots
          who right start,
        hstep, htail]

theorem quittingPureTimeDeviationPayoff_eq_rootSequencePureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward profile observer choice =
      quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) observer choice 0 :=
  quittingTerminalPayoff_update_pureTimeBehaviorStrategy reward profile
    observer choice

theorem quittingPureTimeDeviationPayoff_tail_const_of_deadlineBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    {deadline time : ℕ} (hbound : QuittingDeadlineBounded reward profile deadline)
    (htime : deadline + 1 ≤ time) :
    quittingPureTimeDeviationPayoff reward profile observer (some time) =
      quittingPureTimeDeviationPayoff reward profile observer
        (some (deadline + 1)) := by
  have hall : ∀ stage, deadline < stage →
      quittingProfileLiveRoot reward profile stage =
        (quittingAllContinueRoot : ι → PMF Bool) :=
    fun stage hstage => quittingDeadlineBounded_liveRoot_eq_allContinueRoot
      reward profile hbound hstage
  rw [quittingPureTimeDeviationPayoff_eq_rootSequencePureTime,
    quittingPureTimeDeviationPayoff_eq_rootSequencePureTime]
  unfold quittingRootSequencePureTimeTerminalValue
  refine rootSequenceHazardTerminalValue_congr_of_agree reward
    (quittingProfileLiveRoot reward profile) observer
    (quittingPureTimeHazard (some time))
    (quittingPureTimeHazard (some (deadline + 1))) (deadline + 1) 0 ?_ ?_
  · intro stage _ hstage
    rw [quittingPureTimeHazard_some_of_ne (by omega : stage ≠ time),
      quittingPureTimeHazard_some_of_ne (by omega : stage ≠ deadline + 1)]
  · have hleft : quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) observer (some time)
          (deadline + 1) =
      reward (quittingSingletonTerminal observer) observer := by
      have hvalue := rootSequencePureTimeTerminalValue_tail_eq_solo reward
        (quittingProfileLiveRoot reward profile) observer hall
        (time - (deadline + 1)) (deadline + 1) (by omega)
      rw [show deadline + 1 + (time - (deadline + 1)) = time by omega] at hvalue
      exact hvalue
    have hright : quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) observer (some (deadline + 1))
          (deadline + 1) =
      reward (quittingSingletonTerminal observer) observer := by
      have hvalue := rootSequencePureTimeTerminalValue_tail_eq_solo reward
        (quittingProfileLiveRoot reward profile) observer hall
        0 (deadline + 1) (by omega)
      rw [Nat.add_zero] at hvalue
      exact hvalue
    rw [Nat.zero_add]
    exact hleft.trans hright.symm

private theorem exists_mem_of_cover_csSup_range
    {cover : Finset (Option ℕ)} (value : Option ℕ → ℝ)
    (hcover : ∀ choice : Option ℕ, ∃ point ∈ cover, value point = value choice) :
    ∃ point ∈ cover, value point = sSup (Set.range value) := by
  classical
  have hrange : Set.range value = value '' (↑cover : Set (Option ℕ)) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro target ⟨choice, rfl⟩
      obtain ⟨point, hpoint, hvalue⟩ := hcover choice
      exact ⟨point, hpoint, hvalue⟩
    · rintro target ⟨point, -, rfl⟩
      exact ⟨point, rfl⟩
  have hfinite : (value '' (↑cover : Set (Option ℕ))).Finite :=
    cover.finite_toSet.image value
  have hnonempty : (value '' (↑cover : Set (Option ℕ))).Nonempty := by
    obtain ⟨point, hpoint, -⟩ := hcover none
    exact ⟨value point, ⟨point, hpoint, rfl⟩⟩
  rw [hrange]
  obtain ⟨point, hpoint, hvalue⟩ := hnonempty.csSup_mem hfinite
  exact ⟨point, Finset.mem_coe.mp hpoint, hvalue⟩

theorem exists_quittingDeadlineBounded_pureTime_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    {deadline : ℕ} (hbound : QuittingDeadlineBounded reward profile deadline) :
    ∃ choice : Option ℕ,
      quittingPureTimeDeviationPayoff reward profile observer choice =
          quittingContinuationBestResponseValue reward profile observer ∧
        (choice = none ∨ ∃ time, time ≤ deadline + 1 ∧ choice = some time) := by
  classical
  have hcover : ∀ choice : Option ℕ,
      ∃ point ∈ insert (none : Option ℕ)
          ((Finset.range (deadline + 2)).image some),
        quittingPureTimeDeviationPayoff reward profile observer point =
          quittingPureTimeDeviationPayoff reward profile observer choice := by
    intro choice
    match choice with
    | none => exact ⟨none, Finset.mem_insert_self _ _, rfl⟩
    | some date =>
        by_cases hdate : date ≤ deadline + 1
        · exact ⟨some date, Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨date, Finset.mem_range.mpr (by omega), rfl⟩),
            rfl⟩
        · exact ⟨some (deadline + 1), Finset.mem_insert_of_mem
            (Finset.mem_image.mpr
              ⟨deadline + 1, Finset.mem_range.mpr (by omega), rfl⟩),
            (quittingPureTimeDeviationPayoff_tail_const_of_deadlineBounded
              reward profile observer hbound (by omega)).symm⟩
  obtain ⟨choice, hmem, hvalue⟩ := exists_mem_of_cover_csSup_range
    (quittingPureTimeDeviationPayoff reward profile observer) hcover
  refine ⟨choice, ?_, ?_⟩
  · rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
    exact hvalue
  · rcases Finset.mem_insert.mp hmem with hnone | himage
    · exact Or.inl hnone
    · obtain ⟨date, hdate, rfl⟩ := Finset.mem_image.mp himage
      have hlt := Finset.mem_range.mp hdate
      exact Or.inr ⟨date, by omega, rfl⟩

theorem quittingTerminalPayoff_update_pureTime_sub_eq_semanticDebt_of_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (choice : Option ℕ)
    (hcap : quittingPureTimeDeviationPayoff reward profile observer choice =
      quittingContinuationBestResponseValue reward profile observer) :
    quittingTerminalPayoff reward
          (Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer choice)) observer -
        quittingTerminalPayoff reward profile observer =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer := by
  change quittingPureTimeDeviationPayoff reward profile observer choice -
      quittingTerminalPayoff reward profile observer = _
  rw [hcap]
  rfl

theorem quittingDeadlineBounded_update_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : QuittingDeadlineBounded reward profile deadline) (who : ι)
    {choice : Option ℕ}
    (hchoice : choice = none ∨
      ∃ time, time ≤ deadline + 1 ∧ choice = some time) :
    QuittingDeadlineBounded reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice))
      (deadline + 1) := by
  intro player time htime
  simp only [quittingProfileLiveRoot]
  by_cases hcase : player = who
  · subst player
    rw [Function.update_self]
    show quittingPureTimeHazard choice time = PMF.pure false
    rcases hchoice with rfl | ⟨date, hdate, rfl⟩
    · rfl
    · exact quittingPureTimeHazard_some_of_ne (by omega)
  · rw [Function.update_of_ne hcase]
    exact hbound player time (by omega)

end GameTheory
