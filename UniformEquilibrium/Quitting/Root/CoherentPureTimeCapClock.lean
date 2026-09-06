import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection
import UniformEquilibrium.Quitting.Root.PureTimeCapChild
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineCapSelection

/-! # Coherent pure-time cap clocks along a nested behavioral source -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Once a pure-time-or-Never cap is attained at the first profile of a
nested root source, all later caps can be selected coherently: every next
choice is either immediate Quit or the old choice shifted by one date. -/
theorem exists_coherentPureTimeCapClock_of_nested
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (who : ι) (initialChoice : Option ℕ)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hinitial : quittingTerminalPayoff reward
        (Function.update (profiles 0) who
          (quittingPureTimeBehaviorStrategy reward who initialChoice)) who =
      quittingContinuationBestResponseValue reward (profiles 0) who) :
    ∃ choices : ℕ → Option ℕ,
      choices 0 = initialChoice ∧
        (∀ depth, quittingTerminalPayoff reward
            (Function.update (profiles depth) who
              (quittingPureTimeBehaviorStrategy reward who (choices depth))) who =
          quittingContinuationBestResponseValue reward (profiles depth) who) ∧
        ∀ depth, choices (depth + 1) = some 0 ∨
          choices (depth + 1) = (choices depth).map Nat.succ := by
  let CapChoice := fun depth => {choice : Option ℕ //
    quittingTerminalPayoff reward
        (Function.update (profiles depth) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who =
      quittingContinuationBestResponseValue reward (profiles depth) who}
  let initial : CapChoice 0 := ⟨initialChoice, hinitial⟩
  let next : ∀ depth, CapChoice depth → CapChoice (depth + 1) :=
    fun depth current => by
      have hexists := exists_pureTimeCap_zero_or_map_succ_of_suffixAttainer
        reward (roots depth) (profiles depth) who current.1 current.2
      let choice := Classical.choose hexists
      have hspec := Classical.choose_spec hexists
      refine ⟨choice, ?_⟩
      rw [hnested depth]
      exact hspec.2
  let selected : ∀ depth, CapChoice depth := fun depth =>
    Nat.rec initial (fun depth current => next depth current) depth
  refine ⟨fun depth => (selected depth).1, rfl, fun depth => (selected depth).2,
    fun depth => ?_⟩
  change (next depth (selected depth)).1 = some 0 ∨
    (next depth (selected depth)).1 = ((selected depth).1).map Nat.succ
  dsimp only [next]
  exact (Classical.choose_spec
    (exists_pureTimeCap_zero_or_map_succ_of_suffixAttainer
      reward (roots depth) (profiles depth) who (selected depth).1
        (selected depth).2)).1

/-- A sure opponent at date zero supplies the initial cap choice, after which
the coherent reset-or-shift selection runs through the whole nested source. -/
theorem exists_coherentPureTimeCapClock_of_sureOpponentAtZero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) {who opponent : ι} (hne : opponent ≠ who)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hsure : quittingProfileLiveRoot reward (profiles 0) 0 opponent =
      PMF.pure true) :
    ∃ choices : ℕ → Option ℕ,
      (choices 0 = none ∨ choices 0 = some 0) ∧
        (∀ depth, quittingTerminalPayoff reward
            (Function.update (profiles depth) who
              (quittingPureTimeBehaviorStrategy reward who (choices depth))) who =
          quittingContinuationBestResponseValue reward (profiles depth) who) ∧
        ∀ depth, choices (depth + 1) = some 0 ∨
          choices (depth + 1) = (choices depth).map Nat.succ := by
  obtain ⟨initialChoice, hchoice, hinitial⟩ :=
    exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap
      reward (profiles 0) 0 hne hsure
  obtain ⟨choices, hzero, hcaps, hsteps⟩ :=
    exists_coherentPureTimeCapClock_of_nested
      reward profiles roots who initialChoice hnested hinitial
  refine ⟨choices, ?_, hcaps, hsteps⟩
  rw [hzero]
  rcases hchoice with hnone | ⟨time, htime, htimeEq⟩
  · exact Or.inl hnone
  · right
    have : time = 0 := by omega
    simpa [this] using htimeEq

/-- For the literal `Quit depth` children of any actual nested source, every
fixed outsider admits one coherent complete-cap clock.  The owner is the
sure date-zero opponent in the initial child; no bounded-counterfactual-tail
hypothesis is imposed on the source profiles. -/
theorem exists_coherentOutsiderCapClock_on_pureTimeCapChildren
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) {owner who : ι} (hne : who ≠ owner)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth)) :
    ∃ choices : ℕ → Option ℕ,
      (choices 0 = none ∨ choices 0 = some 0) ∧
        (∀ depth, quittingTerminalPayoff reward
            (Function.update
              (quittingPureTimeCapChild reward (profiles depth) owner depth) who
              (quittingPureTimeBehaviorStrategy reward who (choices depth))) who =
          quittingContinuationBestResponseValue reward
            (quittingPureTimeCapChild reward (profiles depth) owner depth) who) ∧
        ∀ depth, choices (depth + 1) = some 0 ∨
          choices (depth + 1) = (choices depth).map Nat.succ := by
  let children := fun depth =>
    quittingPureTimeCapChild reward (profiles depth) owner depth
  let forcedRoots := fun depth =>
    Function.update (roots depth) owner (PMF.pure false)
  have hchildNested : ∀ depth, children (depth + 1) =
      quittingRootThenContinuationProfile reward (forcedRoots depth)
        (children depth) := by
    intro depth
    dsimp [children, forcedRoots]
    rw [hnested depth]
    exact update_quittingRootThenContinuationProfile_pureTime_succ_eq
      reward (roots depth) (profiles depth) owner depth
  have hsure : quittingProfileLiveRoot reward (children 0) 0 owner =
      PMF.pure true := by
    exact quittingPureTimeCapChild_sure_owner_at_deadline
      reward (profiles 0) owner 0
  simpa [children, forcedRoots] using
    exists_coherentPureTimeCapClock_of_sureOpponentAtZero
      reward children forcedRoots hne.symm hchildNested hsure

/-- Every reset-or-shift clock either eventually shifts forever or resets at
arbitrarily large depths.  This includes the permanent-`Never` clock in the
eventual-shift branch. -/
theorem quittingCapClock_eventually_shift_or_cofinally_reset
    (choices : ℕ → Option ℕ)
    (hstep : ∀ depth, choices (depth + 1) = some 0 ∨
      choices (depth + 1) = (choices depth).map Nat.succ) :
    (∃ cutoff, ∀ depth, cutoff ≤ depth →
        choices (depth + 1) = (choices depth).map Nat.succ) ∨
      ∀ cutoff, ∃ depth, cutoff ≤ depth ∧ choices (depth + 1) = some 0 := by
  by_cases heventual : ∃ cutoff, ∀ depth, cutoff ≤ depth →
      choices (depth + 1) = (choices depth).map Nat.succ
  · exact Or.inl heventual
  · right
    push Not at heventual
    intro cutoff
    obtain ⟨depth, hdepth, hnotShift⟩ := heventual cutoff
    refine ⟨depth, hdepth, ?_⟩
    rcases hstep depth with hreset | hshift
    · exact hreset
    · exact (hnotShift hshift).elim

/-- An eventual shift tail cannot contain cofinally many resets, including
when the selected cap on that tail is Never. No coherence premise is needed. -/
theorem quittingCapClock_not_eventually_shift_and_cofinally_reset
    (choices : ℕ → Option ℕ) :
    ¬ ((∃ cutoff, ∀ depth, cutoff ≤ depth →
        choices (depth + 1) = (choices depth).map Nat.succ) ∧
      ∀ cutoff, ∃ depth, cutoff ≤ depth ∧ choices (depth + 1) = some 0) := by
  rintro ⟨⟨cutoff, hshift⟩, hreset⟩
  obtain ⟨depth, hdepth, hzero⟩ := hreset cutoff
  have h := hshift depth hdepth
  rw [hzero] at h
  cases hchoice : choices depth <;> simp [hchoice] at h

/-- For a coherent clock, eventual pure shifting is exactly failure of
cofinal resetting. Together with the existing disjunction this is exclusive. -/
theorem quittingCapClock_eventually_shift_iff_not_cofinally_reset
    (choices : ℕ → Option ℕ)
    (hstep : ∀ depth, choices (depth + 1) = some 0 ∨
      choices (depth + 1) = (choices depth).map Nat.succ) :
    (∃ cutoff, ∀ depth, cutoff ≤ depth →
        choices (depth + 1) = (choices depth).map Nat.succ) ↔
      ¬ (∀ cutoff, ∃ depth, cutoff ≤ depth ∧ choices (depth + 1) = some 0) := by
  constructor
  · intro hshift hreset
    exact quittingCapClock_not_eventually_shift_and_cofinally_reset choices
      ⟨hshift, hreset⟩
  · intro hnot
    exact (quittingCapClock_eventually_shift_or_cofinally_reset choices hstep).resolve_right
      hnot

end GameTheory
