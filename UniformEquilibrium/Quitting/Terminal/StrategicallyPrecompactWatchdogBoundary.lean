/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.StrategicallyPrecompactWatchdogException

/-!
# Exact watchdog boundary

A fixed-gap profile-dependent selector needs two distinct strategically
nonprecompact player ranges.  Each such range has a fixed amount of genuinely
late finite stopping mass beyond every finite horizon.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability
open StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Failure of strategic total boundedness forces a fixed amount of genuinely
late finite mass in the stopping laws. -/
theorem exists_lateFiniteMass_escape_of_not_strategicallyTotallyBounded
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (family : Set ((quittingGame reward).BehaviorStrategy who))
    (hnot : ¬ IsQuittingStrategicallyTotallyBounded reward who family) :
    ∃ kappa : Real, 0 < kappa ∧ ∀ horizon : Nat,
      ∃ strategy ∈ family,
        kappa <= stoppingLawLateFiniteMass
          (quittingBehaviorStoppingLaw reward strategy) horizon := by
  have hlawsNotBounded : ¬ IsPMFGeneralTVTotallyBounded
      (quittingBehaviorStoppingLaw reward '' family) := by
    intro hlawsBounded
    exact hnot (isQuittingStrategicallyTotallyBounded_of_stoppingLaws
      reward who family hlawsBounded)
  obtain ⟨kappa, hkappa, hlate⟩ :=
    exists_pos_forall_exists_lateFiniteMass_ge_of_not_totallyBounded
      hlawsNotBounded
  refine ⟨kappa, hkappa, fun horizon => ?_⟩
  obtain ⟨law, ⟨strategy, hstrategy, rfl⟩, hmass⟩ := hlate horizon
  exact ⟨strategy, hstrategy, hmass⟩

/-- **Two-range obstruction.** A fixed positive-gain dependent selector has
two distinct nonempty player ranges which fail strategic total boundedness. -/
theorem exists_two_selectorRanges_not_strategicallyTotallyBounded
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (selector : (quittingGame reward).BehaviorProfile ->
      Sigma fun who => (quittingGame reward).BehaviorStrategy who)
    {gap : Real} (hgap : 0 < gap)
    (hgain : ∀ profile,
      gap <= quittingTerminalPayoff reward
          (Function.update profile (selector profile).1 (selector profile).2)
          (selector profile).1 -
        quittingTerminalPayoff reward profile (selector profile).1) :
    ∃ first second, first ≠ second ∧
      (quittingBehaviorSelectorRange reward selector first).Nonempty ∧
      ¬ IsQuittingStrategicallyTotallyBounded reward first
        (quittingBehaviorSelectorRange reward selector first) ∧
      (quittingBehaviorSelectorRange reward selector second).Nonempty ∧
      ¬ IsQuittingStrategicallyTotallyBounded reward second
        (quittingBehaviorSelectorRange reward selector second) := by
  classical
  obtain ⟨first, hfirstNonempty, hfirstNotBounded⟩ :=
    exists_nonempty_selectorRange_not_strategicallyTotallyBounded
      reward selector hgap hgain
  by_cases hsecond : ∃ second, second ≠ first ∧
      (quittingBehaviorSelectorRange reward selector second).Nonempty ∧
      ¬ IsQuittingStrategicallyTotallyBounded reward second
        (quittingBehaviorSelectorRange reward selector second)
  · obtain ⟨second, hsecondNe, hsecondNonempty, hsecondNotBounded⟩ := hsecond
    exact ⟨first, second, Ne.symm hsecondNe, hfirstNonempty,
      hfirstNotBounded, hsecondNonempty, hsecondNotBounded⟩
  · let fallback : (who : iota) ->
        (quittingGame reward).BehaviorStrategy who :=
      fun who => quittingPureTimeBehaviorStrategy reward who none
    let padded : (who : iota) ->
        Set ((quittingGame reward).BehaviorStrategy who) := fun who =>
      if (quittingBehaviorSelectorRange reward selector who).Nonempty then
        quittingBehaviorSelectorRange reward selector who
      else {fallback who}
    have hpaddedNonempty : ∀ who, (padded who).Nonempty := by
      intro who
      by_cases hrange :
          (quittingBehaviorSelectorRange reward selector who).Nonempty
      · change (if (quittingBehaviorSelectorRange reward selector who).Nonempty
            then quittingBehaviorSelectorRange reward selector who
            else {fallback who}).Nonempty
        rw [if_pos hrange]
        exact hrange
      · simp [padded, hrange]
    have hpaddedBoundedAway : ∀ who, who ≠ first ->
        IsQuittingStrategicallyTotallyBounded reward who (padded who) := by
      intro who hwho
      by_cases hrange :
          (quittingBehaviorSelectorRange reward selector who).Nonempty
      · have hbounded : IsQuittingStrategicallyTotallyBounded reward who
            (quittingBehaviorSelectorRange reward selector who) := by
          by_contra hnotBounded
          exact hsecond ⟨who, hwho, hrange, hnotBounded⟩
        simpa [padded, hrange] using hbounded
      · simpa [padded, hrange] using
          Set.Finite.isQuittingStrategicallyTotallyBounded reward who
            (Set.finite_singleton (fallback who))
    obtain ⟨profile, hsafe⟩ :=
      exists_quittingBehaviorProfile_forall_mem_oneException_payoff_le_add
        reward padded hpaddedNonempty first hpaddedBoundedAway
        (show 0 < gap / 2 by linarith)
    have hselectedRange :
        (selector profile).2 ∈
          quittingBehaviorSelectorRange reward selector (selector profile).1 :=
      ⟨profile, rfl⟩
    have hselectedPadded : (selector profile).2 ∈
        padded (selector profile).1 := by
      simp [padded, hselectedRange, Set.nonempty_of_mem hselectedRange]
    have hsafeSelected :=
      hsafe (selector profile).1 (selector profile).2 hselectedPadded
    linarith [hgain profile]

/-- Two distinct selector identities carry separate fixed late-finite escape
constants.  The witnessing laws may come from different profiles. -/
theorem exists_two_player_selectorRanges_lateFiniteMass_escape
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (selector : (quittingGame reward).BehaviorProfile ->
      Sigma fun who => (quittingGame reward).BehaviorStrategy who)
    {gap : Real} (hgap : 0 < gap)
    (hgain : ∀ profile,
      gap <= quittingTerminalPayoff reward
          (Function.update profile (selector profile).1 (selector profile).2)
          (selector profile).1 -
        quittingTerminalPayoff reward profile (selector profile).1) :
    ∃ first second, first ≠ second ∧
      ∃ kappaFirst kappaSecond : Real,
        0 < kappaFirst ∧ 0 < kappaSecond ∧
        (∀ horizon : Nat, ∃ strategy ∈
            quittingBehaviorSelectorRange reward selector first,
          kappaFirst <= stoppingLawLateFiniteMass
            (quittingBehaviorStoppingLaw reward strategy) horizon) ∧
        (∀ horizon : Nat, ∃ strategy ∈
            quittingBehaviorSelectorRange reward selector second,
          kappaSecond <= stoppingLawLateFiniteMass
            (quittingBehaviorStoppingLaw reward strategy) horizon) := by
  obtain ⟨first, second, hne, _hfirstNonempty, hfirstNotBounded,
      _hsecondNonempty, hsecondNotBounded⟩ :=
    exists_two_selectorRanges_not_strategicallyTotallyBounded
      reward selector hgap hgain
  obtain ⟨kappaFirst, hkappaFirst, hfirstLate⟩ :=
    exists_lateFiniteMass_escape_of_not_strategicallyTotallyBounded
      reward first (quittingBehaviorSelectorRange reward selector first)
      hfirstNotBounded
  obtain ⟨kappaSecond, hkappaSecond, hsecondLate⟩ :=
    exists_lateFiniteMass_escape_of_not_strategicallyTotallyBounded
      reward second (quittingBehaviorSelectorRange reward selector second)
      hsecondNotBounded
  exact ⟨first, second, hne, kappaFirst, kappaSecond,
    hkappaFirst, hkappaSecond, hfirstLate, hsecondLate⟩

end GameTheory
