/-
The finite-clock purification kernel.

A behavioral profile is *deadline bounded* at a date `T` when, on the unique
live history, every player's prescribed root after `T` is pure Continue.  Such
a profile leaves only finitely many genuinely different pure quit plans for a
fixed observer: quitting at any date past `T` meets an all-Continue tail, so
the pure-time deviation payoff has already stopped moving at `T + 1`.

Three consequences are recorded here.  The observer's behavioral cap is
attained by one literal pure plan, either `Never` or a quit date no later than
`T + 1`.  An observer carrying strictly positive terminal semantic debt
purifies to that plan, gaining exactly its debt and killing it.  And an
observer whose debt is already zero has every plan in the support of its own
behavioral stopping law sitting exactly at the cap, so purifying through any
support point moves no payoff at all and again leaves zero debt.

Nothing here fixes an equilibrium or claims that purification preserves the
other coordinates: only the observer's own coordinate is overwritten, and only
that coordinate's debt is computed.
-/
import FableOneSureOwnerResponse

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Deadline-bounded profiles -/

/-- A profile is *deadline bounded* at `deadline` when nobody quits on the
live path at any strictly later date. -/
def FableDeadlineBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (deadline : ℕ) : Prop :=
  ∀ (who : ι) (time : ℕ), deadline < time →
    quittingProfileLiveRoot reward profile time who = PMF.pure false

omit [DecidableEq ι] in
/-- Past the deadline, the whole live root is the all-Continue product row. -/
theorem fableDeadlineBounded_liveRoot_eq_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline)
    {time : ℕ} (htime : deadline < time) :
    quittingProfileLiveRoot reward profile time =
      (quittingAllContinueRoot : ι → PMF Bool) :=
  funext fun who => hbound who time htime

/-! ## All-Continue row coefficients -/

private theorem fable_quitValue_of_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {time : ℕ}
    (hroot : roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingFixedOpponentsQuitValue reward roots who time =
      reward (quittingSingletonTerminal who) who := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots who
      (0 : Payoff ι) time,
    hroot, quittingRootQuitPayoff_allContinueRoot]

private theorem fable_continueReward_of_allContinueRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {time : ℕ}
    (hroot : roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingFixedOpponentsContinueReward reward roots who time = 0 := by
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents reward roots
    who (0 : Payoff ι) time
  rw [hroot, quittingRootContinuePayoff_allContinueRoot] at hcontinue
  simpa using hcontinue.symm

private theorem fable_continueMass_of_allContinueRoot
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

/-! ## Pure-time values against an all-Continue tail -/

/-- One Bellman step of a pure quit plan at a date before its quit date. -/
private theorem fable_pureTimeValue_of_ne
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

/-- Started after the deadline, every finite pure quit date is worth exactly
the solo terminal reward: nothing absorbs before it, and the quit itself is
solo. -/
private theorem fable_pureTimeValue_tail_eq_solo
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
        fable_quitValue_of_allContinueRoot reward roots who (hall start hstart)]
  | succ gap ih =>
      intro start hstart
      rw [fable_pureTimeValue_of_ne reward roots who
          (by omega : start ≠ start + (gap + 1)),
        fable_continueReward_of_allContinueRoot reward roots who
          (hall start hstart),
        fable_continueMass_of_allContinueRoot roots who (hall start hstart),
        show start + (gap + 1) = start + 1 + gap by omega,
        ih (start + 1) (by omega)]
      ring

/-- Two hazards agreeing strictly before a common date, and agreeing in value
at that date, agree in value at every earlier date. -/
private theorem fable_hazardValue_congr_of_agree
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

/-! ## B1: tail constancy of the pure-time deviation payoff -/

/-- A pure-time deviation payoff is the corresponding root-sequence pure-time
value of the source profile's live roots. -/
theorem fable_pureTimeDeviationPayoff_eq_rootSequencePureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward profile observer choice =
      quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) observer choice 0 :=
  quittingTerminalPayoff_update_pureTimeBehaviorStrategy reward profile
    observer choice

/-- **Theorem B1.**  At a deadline-bounded profile every pure quit date past
the deadline has the same deviation payoff as the first such date. -/
theorem fable_pureTimeDeviationPayoff_tail_const
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    {deadline : ℕ} (hbound : FableDeadlineBounded reward profile deadline)
    {time : ℕ} (htime : deadline + 1 ≤ time) :
    quittingPureTimeDeviationPayoff reward profile observer (some time) =
      quittingPureTimeDeviationPayoff reward profile observer
        (some (deadline + 1)) := by
  have hall : ∀ stage, deadline < stage →
      quittingProfileLiveRoot reward profile stage =
        (quittingAllContinueRoot : ι → PMF Bool) :=
    fun stage hstage => fableDeadlineBounded_liveRoot_eq_allContinueRoot
      reward profile hbound hstage
  rw [fable_pureTimeDeviationPayoff_eq_rootSequencePureTime,
    fable_pureTimeDeviationPayoff_eq_rootSequencePureTime]
  unfold quittingRootSequencePureTimeTerminalValue
  refine fable_hazardValue_congr_of_agree reward
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
      have hvalue := fable_pureTimeValue_tail_eq_solo reward
        (quittingProfileLiveRoot reward profile) observer hall
        (time - (deadline + 1)) (deadline + 1) (by omega)
      rw [show deadline + 1 + (time - (deadline + 1)) = time by omega] at hvalue
      exact hvalue
    have hright : quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) observer (some (deadline + 1))
          (deadline + 1) =
      reward (quittingSingletonTerminal observer) observer := by
      have hvalue := fable_pureTimeValue_tail_eq_solo reward
        (quittingProfileLiveRoot reward profile) observer hall
        0 (deadline + 1) (by omega)
      rw [Nat.add_zero] at hvalue
      exact hvalue
    rw [Nat.zero_add]
    exact hleft.trans hright.symm

/-! ## B2: the cap is attained by a bounded pure plan -/

/-- A finite covering set of a real-valued family carries the family's
supremum, and carries it at one of its own points. -/
private theorem fable_exists_mem_of_cover_csSup_range
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

/-- **Theorem B2.**  At a deadline-bounded profile the observer's behavioral
cap is attained by a literal pure plan: either `Never`, or a quit date no
later than one step past the deadline. -/
theorem fable_exists_deadlineBounded_pureTime_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    {deadline : ℕ} (hbound : FableDeadlineBounded reward profile deadline) :
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
            (fable_pureTimeDeviationPayoff_tail_const reward profile observer
              hbound (by omega : deadline + 1 ≤ date)).symm⟩
  obtain ⟨choice, hmem, hvalue⟩ := fable_exists_mem_of_cover_csSup_range
    (quittingPureTimeDeviationPayoff reward profile observer) hcover
  refine ⟨choice, ?_, ?_⟩
  · rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
    exact hvalue
  · rcases Finset.mem_insert.mp hmem with hnone | himage
    · exact Or.inl hnone
    · obtain ⟨date, hdate, rfl⟩ := Finset.mem_image.mp himage
      have hlt := Finset.mem_range.mp hdate
      exact Or.inr ⟨date, by omega, rfl⟩

/-! ## B3: paid purification at strictly positive debt -/

/-- **Theorem B3.**  At a deadline-bounded profile, purifying the observer to
the cap-attaining pure plan of B2 raises the observer's own payoff by exactly
its terminal semantic debt, and leaves the observer's coordinate of the target
profile with zero debt.  No sign hypothesis on the debt is used. -/
theorem fable_deadlineBounded_purification
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    {deadline : ℕ} (hbound : FableDeadlineBounded reward profile deadline) :
    ∃ choice : Option ℕ,
      (choice = none ∨ ∃ time, time ≤ deadline + 1 ∧ choice = some time) ∧
        quittingTerminalPayoff reward
              (Function.update profile observer
                (quittingPureTimeBehaviorStrategy reward observer choice))
              observer -
            quittingTerminalPayoff reward profile observer =
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer ∧
        quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer choice)))
          observer = 0 := by
  obtain ⟨choice, hvalue, hshape⟩ := fable_exists_deadlineBounded_pureTime_eq_cap
    reward profile observer hbound
  have hpayoff : quittingTerminalPayoff reward
      (Function.update profile observer
        (quittingPureTimeBehaviorStrategy reward observer choice)) observer =
      quittingContinuationBestResponseValue reward profile observer := hvalue
  refine ⟨choice, hshape, ?_, ?_⟩
  · rw [hpayoff, fable_semanticDebt_profile_eq]
  · rw [fable_semanticDebt_profile_eq,
      fable_continuationBestResponseValue_update_self, hpayoff, sub_self]

/-- **Theorem B3, positive-debt form.**  When the observer's debt is strictly
positive, the same purification is a strict payoff improvement. -/
theorem fable_positiveDebt_purification
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    {deadline : ℕ} (hbound : FableDeadlineBounded reward profile deadline)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer) :
    ∃ choice : Option ℕ,
      (choice = none ∨ ∃ time, time ≤ deadline + 1 ∧ choice = some time) ∧
        quittingTerminalPayoff reward
              (Function.update profile observer
                (quittingPureTimeBehaviorStrategy reward observer choice))
              observer -
            quittingTerminalPayoff reward profile observer =
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer ∧
        quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer choice)))
            observer = 0 ∧
        quittingTerminalPayoff reward profile observer <
          quittingTerminalPayoff reward
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer choice))
            observer := by
  obtain ⟨choice, hshape, hgain, hkilled⟩ :=
    fable_deadlineBounded_purification reward profile observer hbound
  exact ⟨choice, hshape, hgain, hkilled, by linarith⟩

/-! ## B4 and B5: zero-debt purification through the own stopping law -/

/-- **Theorem B4.**  A zero-debt observer's own behavioral stopping law is
supported on pure plans that all attain the observer's cap exactly.  No
deadline hypothesis is needed. -/
theorem fable_zeroDebt_support_pureTimeDeviationPayoff_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (hdebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer = 0)
    {choice : Option ℕ}
    (hsupport : choice ∈
      (quittingBehaviorStoppingLaw reward (profile observer)).support) :
    quittingPureTimeDeviationPayoff reward profile observer choice =
      quittingContinuationBestResponseValue reward profile observer := by
  have hmixture : quittingTerminalPayoff reward profile observer =
      expect (quittingBehaviorStoppingLaw reward (profile observer))
        (quittingPureTimeDeviationPayoff reward profile observer) := by
    have hlaw := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile observer (profile observer)
    rw [Function.update_eq_self] at hlaw
    exact hlaw
  have hgap : quittingContinuationBestResponseValue reward profile observer -
      quittingTerminalPayoff reward profile observer = 0 :=
    (fable_semanticDebt_profile_eq reward profile observer).symm.trans hdebt
  have hnonpos : ∀ point : Option ℕ,
      quittingPureTimeDeviationPayoff reward profile observer point -
        quittingContinuationBestResponseValue reward profile observer ≤ 0 := by
    intro point
    have hle := le_csSup
      (bddAbove_range_quittingPureTimeDeviationPayoff reward profile observer)
      (Set.mem_range_self point)
    rw [← quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
      at hle
    linarith
  have habs : ∀ point : Option ℕ,
      |quittingPureTimeDeviationPayoff reward profile observer point| ≤
        quittingRewardBound reward := fun point =>
    abs_quittingTerminalPayoff_le reward _ observer
      (abs_reward_le_quittingRewardBound reward)
  have hsumValue : Summable (fun point : Option ℕ =>
      ((quittingBehaviorStoppingLaw reward (profile observer)) point).toReal *
        quittingPureTimeDeviationPayoff reward profile observer point) :=
    expect_summable_of_bounded _ _ habs
  have hsumConst : Summable (fun point : Option ℕ =>
      ((quittingBehaviorStoppingLaw reward (profile observer)) point).toReal *
        -quittingContinuationBestResponseValue reward profile observer) :=
    expect_summable_of_bounded _ _
      (C := |(-quittingContinuationBestResponseValue reward profile observer)|)
      (fun _ => le_rfl)
  have hsumGap : Summable (fun point : Option ℕ =>
      ((quittingBehaviorStoppingLaw reward (profile observer)) point).toReal *
        (quittingPureTimeDeviationPayoff reward profile observer point -
          quittingContinuationBestResponseValue reward profile observer)) := by
    refine expect_summable_of_bounded _ _
      (C := quittingRewardBound reward +
        |quittingContinuationBestResponseValue reward profile observer|)
      (fun point => ?_)
    have hsplit :
        |quittingPureTimeDeviationPayoff reward profile observer point -
            quittingContinuationBestResponseValue reward profile observer| ≤
          |quittingPureTimeDeviationPayoff reward profile observer point| +
            |quittingContinuationBestResponseValue reward profile observer| :=
      abs_sub _ _
    linarith [habs point]
  have hexpect :
      expect (quittingBehaviorStoppingLaw reward (profile observer))
        (fun point =>
          quittingPureTimeDeviationPayoff reward profile observer point -
            quittingContinuationBestResponseValue reward profile observer) =
        0 := by
    have hadd := expect_add_of_summable
      (quittingBehaviorStoppingLaw reward (profile observer))
      (quittingPureTimeDeviationPayoff reward profile observer)
      (fun _ => -quittingContinuationBestResponseValue reward profile observer)
      hsumValue hsumConst
    rw [expect_const] at hadd
    rw [show (fun point =>
          quittingPureTimeDeviationPayoff reward profile observer point -
            quittingContinuationBestResponseValue reward profile observer) =
        (fun point =>
          quittingPureTimeDeviationPayoff reward profile observer point +
            -quittingContinuationBestResponseValue reward profile observer) from
      funext fun point => sub_eq_add_neg _ _, hadd, ← hmixture]
    linarith
  have hzero :
      quittingPureTimeDeviationPayoff reward profile observer choice -
        quittingContinuationBestResponseValue reward profile observer = 0 :=
    Math.ProbabilityMassFunction.eq_zero_of_expect_eq_zero_of_nonpos_of_pos
      (quittingBehaviorStoppingLaw reward (profile observer)) _ hnonpos hexpect
      hsumGap ((PMF.mem_support_iff _ _).mp hsupport)
  linarith

/-- **Theorem B5.**  Purifying a zero-debt observer to any plan in the support
of its own behavioral stopping law changes no payoff and again leaves zero
debt in the observer's coordinate. -/
theorem fable_zeroDebt_support_purification
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (hdebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer = 0)
    {choice : Option ℕ}
    (hsupport : choice ∈
      (quittingBehaviorStoppingLaw reward (profile observer)).support) :
    quittingTerminalPayoff reward
          (Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer choice)) observer =
        quittingTerminalPayoff reward profile observer ∧
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer choice)))
        observer = 0 := by
  have hvalue := fable_zeroDebt_support_pureTimeDeviationPayoff_eq_cap
    reward profile observer hdebt hsupport
  have hpayoff : quittingTerminalPayoff reward
      (Function.update profile observer
        (quittingPureTimeBehaviorStrategy reward observer choice)) observer =
      quittingContinuationBestResponseValue reward profile observer := hvalue
  have hgap : quittingContinuationBestResponseValue reward profile observer -
      quittingTerminalPayoff reward profile observer = 0 :=
    (fable_semanticDebt_profile_eq reward profile observer).symm.trans hdebt
  refine ⟨?_, ?_⟩
  · rw [hpayoff]
    linarith
  · rw [fable_semanticDebt_profile_eq,
      fable_continuationBestResponseValue_update_self, hpayoff, sub_self]

end GameTheory
