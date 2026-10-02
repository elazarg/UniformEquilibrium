/-
The canonical pure-time value table and its deadline cap.

A *canonical pure-time profile* assigns every player one date in
`Option ℕ`: `some date` means Continue everywhere except a sure Quit at
`date`, and `none` means Never.  Such a profile is completely deterministic,
so its live root at every date is the pure coalition root of the players
whose date is exactly that date.

Fix an observer and suppose its opponents' finite dates have a minimum `u`,
realized by the nonempty coalition `A`.  Then the observer's own pure-time
deviation payoff takes exactly three values: quitting strictly before `u`
pays the solo terminal reward, quitting exactly at `u` pays the reward of
`insert observer A`, and quitting after `u` or never quitting pays the reward
of `A`.  The observer's whole behavioral cap is therefore the maximum of the
three, and drops to the maximum of the last two as soon as the solo reward
sits strictly below the cap.

The all-Never opponent case is recorded separately: every finite date pays
the solo reward, `Never` pays zero, and the cap is their maximum.

Finally, neither of the two surviving responses introduces a finite date that
the profile did not already use, which is what later feeds a descent rank.

Nothing here selects an equilibrium, fixes a global minimum, or claims that
the responses below preserve the other coordinates.
-/
import FableFiniteClockPurification
import UniformEquilibrium.Quitting.Paths.SureExitSet

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The canonical pure-time profile -/

/-- The profile in which every player follows its own canonical pure quit
date, `none` meaning Never. -/
def fableCanonicalProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) : (quittingGame reward).BehaviorProfile :=
  fun who => quittingPureTimeBehaviorStrategy reward who (tau who)

/-- The players whose canonical date is exactly `time`. -/
def fableCanonicalQuitSet (tau : ι → Option ℕ) (time : ℕ) : Finset ι :=
  Finset.univ.filter fun who => tau who = some time

/-- The observer's opponents whose canonical date is exactly `time`. -/
def fableCanonicalOpponentQuitSet
    (observer : ι) (tau : ι → Option ℕ) (time : ℕ) : Finset ι :=
  (fableCanonicalQuitSet tau time).erase observer

omit [DecidableEq ι] in
theorem fableCanonicalQuitSet_mem
    {tau : ι → Option ℕ} {time : ℕ} {who : ι} :
    who ∈ fableCanonicalQuitSet tau time ↔ tau who = some time := by
  simp [fableCanonicalQuitSet]

theorem fableCanonicalOpponentQuitSet_mem
    {observer : ι} {tau : ι → Option ℕ} {time : ℕ} {who : ι} :
    who ∈ fableCanonicalOpponentQuitSet observer tau time ↔
      (who ≠ observer ∧ tau who = some time) := by
  simp [fableCanonicalOpponentQuitSet, fableCanonicalQuitSet]

omit [DecidableEq ι] in
/-- Each coordinate of a canonical live root is the pure quit-time hazard of
that player's own date. -/
theorem fableCanonicalProfile_liveRoot_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (time : ℕ) (who : ι) :
    quittingProfileLiveRoot reward (fableCanonicalProfile reward tau) time
        who = quittingPureTimeHazard (tau who) time :=
  rfl

/-- **The canonical live root is a pure coalition root.**  At every date the
whole prescribed row is the sure-quit row of the players whose canonical date
is that date. -/
theorem fableCanonicalProfile_liveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (time : ℕ) :
    quittingProfileLiveRoot reward (fableCanonicalProfile reward tau) time =
      quittingPureSetRoot (fableCanonicalQuitSet tau time) := by
  funext who
  rw [fableCanonicalProfile_liveRoot_apply]
  by_cases hwho : tau who = some time
  · have hmem : who ∈ fableCanonicalQuitSet tau time :=
      fableCanonicalQuitSet_mem.mpr hwho
    rw [hwho, quittingPureTimeHazard_some_self]
    simp [quittingPureSetRoot, quittingSetAction, hmem]
  · have hmem : who ∉ fableCanonicalQuitSet tau time := fun hcontra =>
      hwho (fableCanonicalQuitSet_mem.mp hcontra)
    have hhazard : quittingPureTimeHazard (tau who) time = PMF.pure false := by
      cases hcase : tau who with
      | none => rfl
      | some date =>
          refine quittingPureTimeHazard_some_of_ne (fun hne => hwho ?_)
          rw [hcase, hne]
    rw [hhazard]
    simp [quittingPureSetRoot, quittingSetAction, hmem]

/-- Updating one coordinate of the date vector updates exactly that
coordinate of the canonical profile. -/
theorem fableCanonicalProfile_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) (choice : Option ℕ) :
    fableCanonicalProfile reward (Function.update tau observer choice) =
      Function.update (fableCanonicalProfile reward tau) observer
        (quittingPureTimeBehaviorStrategy reward observer choice) := by
  funext who
  by_cases hwho : who = observer
  · subst who
    simp [fableCanonicalProfile]
  · simp [fableCanonicalProfile, Function.update_of_ne hwho]

/-- The deviation payoff overwrites the observer's own coordinate, so it does
not see the observer's declared canonical date. -/
theorem fable_canonicalPureTimeDeviationPayoff_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) (own choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (fableCanonicalProfile reward (Function.update tau observer own))
        observer choice =
      quittingPureTimeDeviationPayoff reward
        (fableCanonicalProfile reward tau) observer choice := by
  unfold quittingPureTimeDeviationPayoff
  rw [fableCanonicalProfile_update, Function.update_idem]

omit [DecidableEq ι] in
/-- The canonical profile of a date vector bounded by `deadline` is deadline
bounded there. -/
theorem fableDeadlineBounded_canonicalProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) {deadline : ℕ}
    (hbound : ∀ who date, tau who = some date → date ≤ deadline) :
    FableDeadlineBounded reward (fableCanonicalProfile reward tau) deadline := by
  intro who time htime
  rw [fableCanonicalProfile_liveRoot_apply]
  cases hcase : tau who with
  | none => rfl
  | some date =>
      have hle := hbound who date hcase
      exact quittingPureTimeHazard_some_of_ne (by omega)

/-! ## Fixed-opponent coefficients of a canonical profile -/

omit [Fintype ι] in
private theorem fable_insert_erase (owner : ι) (S : Finset ι) :
    insert owner (S.erase owner) = insert owner S := by
  ext point
  simp only [Finset.mem_insert, Finset.mem_erase]
  tauto

/-- Quitting now against canonical opponents pays the reward of the observer
joined to that date's opponent coalition. -/
theorem fable_canonicalProfile_quitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward
        (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
        observer time =
      quittingSetReward reward
        (insert observer (fableCanonicalOpponentQuitSet observer tau time))
        observer := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
      (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
      observer (0 : Payoff ι) time,
    fableCanonicalProfile_liveRoot, quittingRootQuitPayoff_pureSetRoot_eq_insert,
    fableCanonicalOpponentQuitSet, fable_insert_erase]

/-- Continuing now against canonical opponents pays the reward of that date's
opponent coalition, whether or not it is empty. -/
theorem fable_canonicalProfile_continueReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) (time : ℕ) :
    quittingFixedOpponentsContinueReward reward
        (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
        observer time =
      quittingSetReward reward
        (fableCanonicalOpponentQuitSet observer tau time) observer := by
  unfold quittingFixedOpponentsContinueReward
  rw [fableCanonicalProfile_liveRoot, update_quittingPureSetRoot_false,
    quittingRootAbsorbingContribution_pureSetRoot]
  rfl

/-- A date at which some opponent surely quits kills the whole continuation
mass. -/
theorem fable_canonicalProfile_continueMass_of_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {time : ℕ}
    (hne : (fableCanonicalOpponentQuitSet observer tau time).Nonempty) :
    quittingFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
        observer time = 0 := by
  unfold quittingFixedOpponentsContinueMass
  rw [fableCanonicalProfile_liveRoot, update_quittingPureSetRoot_false]
  exact stationaryContinueMass_pureSetRoot_of_nonempty hne

/-- A date at which no opponent quits passes the whole continuation mass. -/
theorem fable_canonicalProfile_continueMass_of_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {time : ℕ}
    (hempty : fableCanonicalOpponentQuitSet observer tau time = ∅) :
    quittingFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
        observer time = 1 := by
  unfold quittingFixedOpponentsContinueMass
  rw [fableCanonicalProfile_liveRoot, update_quittingPureSetRoot_false,
    show (fableCanonicalQuitSet tau time).erase observer = ∅ from hempty]
  exact quittingStationaryContinueMass_pureSetRoot_empty

/-! ## Transparent descent to the earliest opponent deadline -/

private theorem fable_pureTimeHazard_eq_pure_false
    {choice : Option ℕ} {time : ℕ} (hne : choice ≠ some time) :
    quittingPureTimeHazard choice time = PMF.pure false := by
  cases hcase : choice with
  | none => rfl
  | some date =>
      refine quittingPureTimeHazard_some_of_ne (fun hcontra => hne ?_)
      rw [hcase, hcontra]

/-- One Bellman step at a date where the observer's hazard does not fire. -/
private theorem fable_hazardValue_step_of_pure_false
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) {start : ℕ}
    (hhazard : hazard start = PMF.pure false) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard start =
      quittingFixedOpponentsContinueReward reward roots who start +
        quittingFixedOpponentsContinueMass roots who start *
          quittingRootSequenceHazardTerminalValue reward roots who hazard
            (start + 1) := by
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman, hhazard]
  simp

/-- Dates at which neither the observer nor any opponent quits do not move
the hazard value. -/
private theorem fable_hazardValue_transparent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) :
    ∀ (span start : ℕ),
      (∀ time, start ≤ time → time < start + span →
        hazard time = PMF.pure false ∧
          quittingFixedOpponentsContinueReward reward roots who time = 0 ∧
          quittingFixedOpponentsContinueMass roots who time = 1) →
      quittingRootSequenceHazardTerminalValue reward roots who hazard start =
        quittingRootSequenceHazardTerminalValue reward roots who hazard
          (start + span) := by
  intro span
  induction span with
  | zero => intro start _; rw [Nat.add_zero]
  | succ span ih =>
      intro start hstep
      obtain ⟨hhazard, hreward, hmass⟩ := hstep start le_rfl (by omega)
      rw [fable_hazardValue_step_of_pure_false reward roots who hazard hhazard,
        hreward, hmass, one_mul, zero_add,
        ih (start + 1) (fun time hle hlt => hstep time (by omega) (by omega)),
        show start + 1 + span = start + (span + 1) by omega]

/-- Before the earliest opponent deadline no opponent quits. -/
theorem fable_canonicalOpponentQuitSet_eq_empty_of_lt
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    {time : ℕ} (htime : time < earliest) :
    fableCanonicalOpponentQuitSet observer tau time = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun other hother => ?_
  obtain ⟨hne, hdate⟩ := fableCanonicalOpponentQuitSet_mem.mp hother
  have := hearliest other hne time hdate
  omega

/-- Every date strictly before the earliest opponent deadline is transparent,
so a pure plan that does not fire there keeps its value. -/
private theorem fable_canonicalPureTimeValue_descend
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (choice : Option ℕ) {span : ℕ} (hspan : span ≤ earliest)
    (hchoice : ∀ time, time < span → choice ≠ some time) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
        observer choice 0 =
      quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
        observer choice span := by
  unfold quittingRootSequencePureTimeTerminalValue
  have hvalue := fable_hazardValue_transparent reward
    (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
    observer (quittingPureTimeHazard choice) span 0 ?_
  · rw [Nat.zero_add] at hvalue
    exact hvalue
  · intro time _ hlt
    rw [Nat.zero_add] at hlt
    have hempty : fableCanonicalOpponentQuitSet observer tau time = ∅ :=
      fable_canonicalOpponentQuitSet_eq_empty_of_lt tau observer hearliest
        (by omega)
    refine ⟨fable_pureTimeHazard_eq_pure_false (hchoice time hlt), ?_, ?_⟩
    · rw [fable_canonicalProfile_continueReward, hempty, quittingSetReward_empty]
    · exact fable_canonicalProfile_continueMass_of_empty reward tau observer
        hempty

/-! ## C1: the canonical pure-time value table -/

/-- **Value table, early quit.**  Quitting strictly before the earliest
opponent deadline is a solo quit: the observer pays the singleton reward. -/
theorem fable_canonicalPureTime_value_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    {date : ℕ} (hdate : date < earliest) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
        observer (some date) =
      reward (quittingSingletonTerminal observer) observer := by
  rw [fable_pureTimeDeviationPayoff_eq_rootSequencePureTime,
    fable_canonicalPureTimeValue_descend reward tau observer hearliest
      (some date) (by omega : date ≤ earliest)
      (fun time hlt hcontra => by
        rw [Option.some.injEq] at hcontra; omega),
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
    fable_canonicalProfile_quitValue,
    fable_canonicalOpponentQuitSet_eq_empty_of_lt tau observer hearliest hdate,
    Finset.insert_empty,
    quittingSetReward_of_nonempty reward
      (Finset.singleton_nonempty observer) observer]
  rfl

/-- **Value table, quit at the deadline.**  Quitting exactly at the earliest
opponent deadline joins that coalition. -/
theorem fable_canonicalPureTime_value_of_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest)) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
        observer (some earliest) =
      reward ⟨insert observer coalition,
        Finset.insert_nonempty observer coalition⟩ observer := by
  have hset : fableCanonicalOpponentQuitSet observer tau earliest = coalition := by
    ext other
    rw [fableCanonicalOpponentQuitSet_mem, hcoalition other]
  rw [fable_pureTimeDeviationPayoff_eq_rootSequencePureTime,
    fable_canonicalPureTimeValue_descend reward tau observer hearliest
      (some earliest) le_rfl
      (fun time hlt hcontra => by
        rw [Option.some.injEq] at hcontra; omega),
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
    fable_canonicalProfile_quitValue, hset,
    quittingSetReward_of_nonempty reward
      (Finset.insert_nonempty observer coalition) observer]

/-- Any plan that has not fired by the earliest opponent deadline is
screened by that coalition. -/
private theorem fable_canonicalPureTime_value_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty)
    (choice : Option ℕ) (hchoice : ∀ time, time ≤ earliest → choice ≠ some time) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
        observer choice = reward ⟨coalition, hne⟩ observer := by
  have hset : fableCanonicalOpponentQuitSet observer tau earliest = coalition := by
    ext other
    rw [fableCanonicalOpponentQuitSet_mem, hcoalition other]
  have hmass : quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
      observer earliest = 0 :=
    fable_canonicalProfile_continueMass_of_nonempty reward tau observer
      (by rw [hset]; exact hne)
  rw [fable_pureTimeDeviationPayoff_eq_rootSequencePureTime,
    fable_canonicalPureTimeValue_descend reward tau observer hearliest choice
      le_rfl (fun time hlt => hchoice time (by omega))]
  unfold quittingRootSequencePureTimeTerminalValue
  rw [fable_hazardValue_step_of_pure_false reward
      (quittingProfileLiveRoot reward (fableCanonicalProfile reward tau))
      observer (quittingPureTimeHazard choice)
      (fable_pureTimeHazard_eq_pure_false (hchoice earliest le_rfl)),
    hmass, fable_canonicalProfile_continueReward, hset,
    quittingSetReward_of_nonempty reward hne observer]
  ring

/-- **Value table, late quit.**  Quitting strictly after the earliest
opponent deadline never happens: that coalition has already absorbed. -/
theorem fable_canonicalPureTime_value_of_gt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) {date : ℕ} (hdate : earliest < date) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
        observer (some date) = reward ⟨coalition, hne⟩ observer :=
  fable_canonicalPureTime_value_after reward tau observer hearliest hcoalition
    hne (some date) fun time hle hcontra => by
      rw [Option.some.injEq] at hcontra; omega

/-- **Value table, never.**  Never quitting pays the same as any late quit. -/
theorem fable_canonicalPureTime_value_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
        observer none = reward ⟨coalition, hne⟩ observer :=
  fable_canonicalPureTime_value_after reward tau observer hearliest hcoalition
    hne none fun _ _ => by simp

/-- **The table is exhaustive.**  Every pure plan takes one of the three
listed values. -/
theorem fable_canonicalPureTime_value_trichotomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
          observer choice =
        reward (quittingSingletonTerminal observer) observer ∨
      quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
            observer choice =
          reward ⟨insert observer coalition,
            Finset.insert_nonempty observer coalition⟩ observer ∨
        quittingPureTimeDeviationPayoff reward
            (fableCanonicalProfile reward tau) observer choice =
          reward ⟨coalition, hne⟩ observer := by
  match choice with
  | none =>
      exact Or.inr (Or.inr (fable_canonicalPureTime_value_never reward tau
        observer hearliest hcoalition hne))
  | some date =>
      rcases lt_trichotomy date earliest with hlt | heq | hgt
      · exact Or.inl (fable_canonicalPureTime_value_of_lt reward tau observer
          hearliest hlt)
      · subst heq
        exact Or.inr (Or.inl (fable_canonicalPureTime_value_of_eq reward tau
          observer hearliest hcoalition))
      · exact Or.inr (Or.inr (fable_canonicalPureTime_value_of_gt reward tau
          observer hearliest hcoalition hne hgt))

/-! ## C2: the cap against an opponent deadline -/

private theorem fable_isGreatest_of_three
    {value : Option ℕ → ℝ} {left middle right : ℝ}
    (hleft : ∃ choice, value choice = left)
    (hmiddle : ∃ choice, value choice = middle)
    (hright : ∃ choice, value choice = right)
    (hall : ∀ choice, value choice = left ∨ value choice = middle ∨
      value choice = right) :
    IsGreatest (Set.range value) (max left (max middle right)) := by
  refine ⟨?_, ?_⟩
  · rcases le_total left (max middle right) with hcase | hcase
    · rw [max_eq_right hcase]
      rcases le_total middle right with hinner | hinner
      · rw [max_eq_right hinner]
        obtain ⟨choice, hchoice⟩ := hright
        exact ⟨choice, hchoice⟩
      · rw [max_eq_left hinner]
        obtain ⟨choice, hchoice⟩ := hmiddle
        exact ⟨choice, hchoice⟩
    · rw [max_eq_left hcase]
      obtain ⟨choice, hchoice⟩ := hleft
      exact ⟨choice, hchoice⟩
  · rintro point ⟨choice, rfl⟩
    rcases hall choice with hcase | hcase | hcase
    · rw [hcase]; exact le_max_left _ _
    · rw [hcase]; exact (le_max_left _ _).trans (le_max_right _ _)
    · rw [hcase]; exact (le_max_right _ _).trans (le_max_right _ _)

private theorem fable_isGreatest_of_two
    {value : Option ℕ → ℝ} {left right : ℝ}
    (hleft : ∃ choice, value choice = left)
    (hright : ∃ choice, value choice = right)
    (hall : ∀ choice, value choice = left ∨ value choice = right) :
    IsGreatest (Set.range value) (max left right) := by
  refine ⟨?_, ?_⟩
  · rcases le_total left right with hcase | hcase
    · rw [max_eq_right hcase]
      obtain ⟨choice, hchoice⟩ := hright
      exact ⟨choice, hchoice⟩
    · rw [max_eq_left hcase]
      obtain ⟨choice, hchoice⟩ := hleft
      exact ⟨choice, hchoice⟩
  · rintro point ⟨choice, rfl⟩
    rcases hall choice with hcase | hcase
    · rw [hcase]; exact le_max_left _ _
    · rw [hcase]; exact le_max_right _ _

/-- **The cap at a positive opponent deadline.**  All three table values are
available, so the observer's whole behavioral cap is their maximum. -/
theorem fable_canonicalPureTime_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) (hpos : 0 < earliest) :
    quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer =
      max (reward (quittingSingletonTerminal observer) observer)
        (max (reward ⟨insert observer coalition,
              Finset.insert_nonempty observer coalition⟩ observer)
          (reward ⟨coalition, hne⟩ observer)) := by
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  refine IsGreatest.csSup_eq (fable_isGreatest_of_three ?_ ?_ ?_ ?_)
  · exact ⟨some 0, fable_canonicalPureTime_value_of_lt reward tau observer
      hearliest hpos⟩
  · exact ⟨some earliest, fable_canonicalPureTime_value_of_eq reward tau
      observer hearliest hcoalition⟩
  · exact ⟨none, fable_canonicalPureTime_value_never reward tau observer
      hearliest hcoalition hne⟩
  · exact fable_canonicalPureTime_value_trichotomy reward tau observer
      hearliest hcoalition hne

/-- **The cap at a date-zero opponent deadline.**  No quit is early enough to
be solo, so the singleton value is simply absent from the menu. -/
theorem fable_canonicalPureTime_cap_of_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) (hzero : earliest = 0) :
    quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer =
      max (reward ⟨insert observer coalition,
            Finset.insert_nonempty observer coalition⟩ observer)
        (reward ⟨coalition, hne⟩ observer) := by
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  refine IsGreatest.csSup_eq (fable_isGreatest_of_two ?_ ?_ ?_)
  · exact ⟨some earliest, fable_canonicalPureTime_value_of_eq reward tau
      observer hearliest hcoalition⟩
  · exact ⟨none, fable_canonicalPureTime_value_never reward tau observer
      hearliest hcoalition hne⟩
  · intro choice
    match choice with
    | none =>
        exact Or.inr (fable_canonicalPureTime_value_never reward tau observer
          hearliest hcoalition hne)
    | some date =>
        rcases lt_trichotomy date earliest with hlt | heq | hgt
        · omega
        · subst heq
          exact Or.inl (fable_canonicalPureTime_value_of_eq reward tau observer
            hearliest hcoalition)
        · exact Or.inr (fable_canonicalPureTime_value_of_gt reward tau observer
            hearliest hcoalition hne hgt)

/-! ## C3: margin collapse of the cap -/

/-- **Margin collapse.**  Once the solo terminal reward sits strictly below
the cap, the early-quit row is unavailable and the cap is the maximum of the
two deadline rows. -/
theorem fable_canonicalPureTime_cap_of_margin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) (hpos : 0 < earliest)
    (hmargin : reward (quittingSingletonTerminal observer) observer <
      quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer) :
    quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer =
      max (reward ⟨insert observer coalition,
            Finset.insert_nonempty observer coalition⟩ observer)
        (reward ⟨coalition, hne⟩ observer) := by
  have hcap := fable_canonicalPureTime_cap reward tau observer hearliest
    hcoalition hne hpos
  rw [hcap] at hmargin ⊢
  exact max_eq_right (le_of_lt (lt_of_not_ge fun hcontra =>
    absurd (max_eq_left hcontra) (by
      intro hcase
      rw [hcase] at hmargin
      exact lt_irrefl _ hmargin)))

/-- **Margin collapse is attained.**  One of the two literal deadline plans -
quit exactly at the earliest opponent deadline, or never quit - realizes the
cap. -/
theorem fable_exists_canonicalPureTime_deadlineResponse_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hearliest : ∀ other, other ≠ observer →
      ∀ date, tau other = some date → earliest ≤ date)
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) (hpos : 0 < earliest)
    (hmargin : reward (quittingSingletonTerminal observer) observer <
      quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer) :
    ∃ choice ∈ ({some earliest, none} : Set (Option ℕ)),
      quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
          observer choice =
        quittingContinuationBestResponseValue reward
          (fableCanonicalProfile reward tau) observer := by
  have hcap := fable_canonicalPureTime_cap_of_margin reward tau observer
    hearliest hcoalition hne hpos hmargin
  rcases le_total
      (reward ⟨insert observer coalition,
        Finset.insert_nonempty observer coalition⟩ observer)
      (reward ⟨coalition, hne⟩ observer) with hcase | hcase
  · refine ⟨none, Or.inr rfl, ?_⟩
    rw [hcap, max_eq_right hcase]
    exact fable_canonicalPureTime_value_never reward tau observer hearliest
      hcoalition hne
  · refine ⟨some earliest, Or.inl rfl, ?_⟩
    rw [hcap, max_eq_left hcase]
    exact fable_canonicalPureTime_value_of_eq reward tau observer hearliest
      hcoalition

/-! ## C4: all-Never opponents -/

/-- Against all-Never opponents the canonical profile with a `Never`
observer is the all-Continue profile. -/
theorem fable_canonicalProfile_update_never_eq_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι)
    (hnever : ∀ other, other ≠ observer → tau other = none) :
    fableCanonicalProfile reward (Function.update tau observer none) =
      quittingAlwaysContinueProfile reward := by
  have hall : Function.update tau observer none = fun _ => none := by
    funext other
    by_cases hother : other = observer
    · subst other
      simp
    · rw [Function.update_of_ne hother, hnever other hother]
  rw [hall]
  rfl

/-- **All-Never opponents, finite quit.**  Every finite quit date is solo. -/
theorem fable_canonicalPureTime_never_value_of_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι)
    (hnever : ∀ other, other ≠ observer → tau other = none) (date : ℕ) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
        observer (some date) =
      reward (quittingSingletonTerminal observer) observer :=
  fable_canonicalPureTime_value_of_lt reward tau observer
    (earliest := date + 1)
    (fun other hother point hpoint => by
      rw [hnever other hother] at hpoint
      simp at hpoint)
    (by omega)

/-- **All-Never opponents, never.**  Never quitting never absorbs. -/
theorem fable_canonicalPureTime_never_value_of_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι)
    (hnever : ∀ other, other ≠ observer → tau other = none) :
    quittingPureTimeDeviationPayoff reward (fableCanonicalProfile reward tau)
        observer none = 0 := by
  rw [← fable_canonicalPureTimeDeviationPayoff_update_self reward tau observer
    none none]
  unfold quittingPureTimeDeviationPayoff
  rw [← fableCanonicalProfile_update,
    fable_canonicalProfile_update_never_eq_allContinue reward
      (Function.update tau observer none) observer
      (fun other hother => by rw [Function.update_of_ne hother, hnever other hother]),
    quittingTerminalPayoff_quittingAlwaysContinue]

/-- **The all-Never cap.**  The observer chooses between one solo quit and
never absorbing at all. -/
theorem fable_canonicalPureTime_never_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tau : ι → Option ℕ) (observer : ι)
    (hnever : ∀ other, other ≠ observer → tau other = none) :
    quittingContinuationBestResponseValue reward
        (fableCanonicalProfile reward tau) observer =
      max (reward (quittingSingletonTerminal observer) observer) 0 := by
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  refine IsGreatest.csSup_eq (fable_isGreatest_of_two ?_ ?_ ?_)
  · exact ⟨some 0, fable_canonicalPureTime_never_value_of_some reward tau
      observer hnever 0⟩
  · exact ⟨none, fable_canonicalPureTime_never_value_of_none reward tau
      observer hnever⟩
  · intro choice
    match choice with
    | none =>
        exact Or.inr (fable_canonicalPureTime_never_value_of_none reward tau
          observer hnever)
    | some date =>
        exact Or.inl (fable_canonicalPureTime_never_value_of_some reward tau
          observer hnever date)

/-! ## C5: the responses introduce no new finite date -/

/-- The finite canonical dates a date vector actually uses. -/
def fableFiniteDateSet (tau : ι → Option ℕ) : Set ℕ :=
  {date | ∃ who, tau who = some date}

omit [Fintype ι] [DecidableEq ι] in
theorem fableFiniteDateSet_mem
    {tau : ι → Option ℕ} {date : ℕ} :
    date ∈ fableFiniteDateSet tau ↔ ∃ who, tau who = some date :=
  Iff.rfl

omit [Fintype ι] in
/-- **Quitting at the deadline adds no date, pointwise.**  The deadline is
already used by a member of the earliest opponent coalition. -/
theorem fable_update_deadline_date_mem
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) (who : ι) (date : ℕ)
    (hwho : Function.update tau observer (some earliest) who = some date) :
    ∃ other, tau other = some date := by
  by_cases hcase : who = observer
  · subst who
    rw [Function.update_self] at hwho
    obtain rfl : earliest = date := Option.some.inj hwho
    obtain ⟨member, hmember⟩ := hne
    exact ⟨member, ((hcoalition member).mp hmember).2⟩
  · rw [Function.update_of_ne hcase] at hwho
    exact ⟨who, hwho⟩

omit [Fintype ι] in
/-- **Quitting at the deadline adds no date.** -/
theorem fable_fableFiniteDateSet_update_deadline_subset
    (tau : ι → Option ℕ) (observer : ι) {earliest : ℕ} {coalition : Finset ι}
    (hcoalition : ∀ other, other ∈ coalition ↔
      (other ≠ observer ∧ tau other = some earliest))
    (hne : coalition.Nonempty) :
    fableFiniteDateSet (Function.update tau observer (some earliest)) ⊆
      fableFiniteDateSet tau := by
  rintro date ⟨who, hwho⟩
  exact fable_update_deadline_date_mem tau observer hcoalition hne who date hwho

omit [Fintype ι] in
/-- **Never adds no date, pointwise.** -/
theorem fable_update_never_date_mem
    (tau : ι → Option ℕ) (observer : ι) (who : ι) (date : ℕ)
    (hwho : Function.update tau observer none who = some date) :
    tau who = some date ∧ who ≠ observer := by
  by_cases hcase : who = observer
  · subst who
    rw [Function.update_self] at hwho
    simp at hwho
  · rw [Function.update_of_ne hcase] at hwho
    exact ⟨hwho, hcase⟩

omit [Fintype ι] in
/-- **Never adds no date.** -/
theorem fable_fableFiniteDateSet_update_never_subset
    (tau : ι → Option ℕ) (observer : ι) :
    fableFiniteDateSet (Function.update tau observer none) ⊆
      fableFiniteDateSet tau := by
  rintro date ⟨who, hwho⟩
  exact ⟨who, (fable_update_never_date_mem tau observer who date hwho).1⟩

end GameTheory
