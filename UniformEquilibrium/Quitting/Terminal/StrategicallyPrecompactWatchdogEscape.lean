/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.StoppingLawExposure
import UniformEquilibrium.Quitting.Paths.StoppingLawFiniteTail
import UniformEquilibrium.Quitting.Terminal.StrategicallyPrecompactWatchdog

/-!
# Tail escape for profile-dependent quitting watchdogs

A profile-dependent selector which gains one fixed positive amount at every
behavioral profile has a fixed player range which is not strategically totally
bounded.  Total-variation tightness of stopping laws would imply strategic
total boundedness, so that range carries a fixed amount of mass beyond every
finite horizon, excluding the `Never` atom.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability
open StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- The player-indexed range of a dependent behavioral selector. -/
def quittingBehaviorSelectorRange
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (selector : (quittingGame reward).BehaviorProfile ->
      Sigma fun who => (quittingGame reward).BehaviorStrategy who)
    (who : iota) : Set ((quittingGame reward).BehaviorStrategy who) :=
  {strategy | Sigma.mk who strategy ∈ Set.range selector}

/-- A finite strategic family is strategically totally bounded, with itself
as a net at every positive error. -/
theorem Set.Finite.isQuittingStrategicallyTotallyBounded
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    {family : Set ((quittingGame reward).BehaviorStrategy who)}
    (hfinite : family.Finite) :
    IsQuittingStrategicallyTotallyBounded reward who family := by
  intro error herror
  refine ⟨family, hfinite, Set.Subset.rfl, fun strategy hstrategy =>
    ⟨strategy, hstrategy, ?_⟩⟩
  intro profile
  simp [herror]

/-- Total-variation total boundedness of the induced stopping laws implies
total boundedness in the unrestricted strategic payoff pseudometric. -/
theorem isQuittingStrategicallyTotallyBounded_of_stoppingLaws
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (family : Set ((quittingGame reward).BehaviorStrategy who))
    (hbounded : IsPMFGeneralTVTotallyBounded
      (quittingBehaviorStoppingLaw reward '' family)) :
    IsQuittingStrategicallyTotallyBounded reward who family := by
  intro error herror
  let bound : Real := max 1 (quittingRewardBound reward)
  have hbound : 0 < bound := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hreward : ∀ terminal player, |reward terminal player| <= bound := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans
      (le_max_right _ _)
  have hscale : 0 < 2 * bound := by positivity
  obtain ⟨lawNet, hlawNetFinite, hlawNetSubset, hlawNetCover⟩ :=
    hbounded (error / (2 * bound)) ((div_pos herror hscale))
  let lawNetType := {law // law ∈ lawNet}
  letI : Fintype lawNetType := hlawNetFinite.fintype
  have hpreimage : ∀ law : lawNetType,
      ∃ strategy ∈ family,
        quittingBehaviorStoppingLaw reward strategy = law := by
    intro law
    obtain ⟨strategy, hstrategy, hlaw⟩ := hlawNetSubset law.property
    exact ⟨strategy, hstrategy, hlaw⟩
  choose strategy hstrategy hlaw using hpreimage
  let strategyNet : Set ((quittingGame reward).BehaviorStrategy who) :=
    Set.range strategy
  refine ⟨strategyNet, Set.finite_range _, ?_, fun source hsource => ?_⟩
  · rintro candidate ⟨law, rfl⟩
    exact hstrategy law
  · have hsourceLaw :
        quittingBehaviorStoppingLaw reward source ∈
          quittingBehaviorStoppingLaw reward '' family :=
      ⟨source, hsource, rfl⟩
    obtain ⟨centerLaw, hcenterLawNet, hclose⟩ :=
      hlawNetCover (quittingBehaviorStoppingLaw reward source) hsourceLaw
    let center : lawNetType := ⟨centerLaw, hcenterLawNet⟩
    refine ⟨strategy center, ⟨center, rfl⟩, ?_⟩
    intro profile
    have hforward :=
      quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV
        reward profile who (strategy center) source hreward
    have hreverse :=
      quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV
        reward profile who source (strategy center) hreward
    have hlawCenter :
        quittingBehaviorStoppingLaw reward (strategy center) = centerLaw :=
      hlaw center
    rw [hlawCenter] at hforward hreverse
    rw [pmfGeneralTV_symm] at hforward
    have hscaled : 2 * bound *
        pmfGeneralTV (quittingBehaviorStoppingLaw reward source) centerLaw <
          error := by
      exact (lt_div_iff₀' hscale).mp hclose
    rw [abs_lt]
    constructor <;> linarith

/-- **Selector-range obstruction.** A fixed positive-gain dependent selector
has one fixed nonempty player range which is not strategically totally
bounded. Empty ranges are padded only inside the proof. -/
theorem exists_nonempty_selectorRange_not_strategicallyTotallyBounded
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
    ∃ who,
      (quittingBehaviorSelectorRange reward selector who).Nonempty ∧
        ¬ IsQuittingStrategicallyTotallyBounded reward who
          (quittingBehaviorSelectorRange reward selector who) := by
  classical
  by_contra hcontra
  push Not at hcontra
  let fallback : (who : iota) ->
      (quittingGame reward).BehaviorStrategy who :=
    fun who => quittingPureTimeBehaviorStrategy reward who none
  let padded : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who) := fun who =>
    if (quittingBehaviorSelectorRange reward selector who).Nonempty then
      quittingBehaviorSelectorRange reward selector who
    else {fallback who}
  have hpaddedNonempty : ∀ who, (padded who).Nonempty := by
    intro who
    by_cases hnonempty :
        (quittingBehaviorSelectorRange reward selector who).Nonempty
    · simp [padded, hnonempty]
    · simp [padded, hnonempty]
  have hpaddedBounded : ∀ who,
      IsQuittingStrategicallyTotallyBounded reward who (padded who) := by
    intro who
    by_cases hnonempty :
        (quittingBehaviorSelectorRange reward selector who).Nonempty
    · simpa [padded, hnonempty] using hcontra who hnonempty
    · simpa [padded, hnonempty] using
        Set.Finite.isQuittingStrategicallyTotallyBounded reward who
          (Set.finite_singleton (fallback who))
  obtain ⟨profile, hsafe⟩ :=
    exists_quittingBehaviorProfile_forall_mem_totallyBounded_payoff_le_add
      reward padded hpaddedNonempty hpaddedBounded (show 0 < gap / 2 by linarith)
  have hselectedRange :
      (selector profile).2 ∈
        quittingBehaviorSelectorRange reward selector (selector profile).1 := by
    exact ⟨profile, rfl⟩
  have hselectedPadded : (selector profile).2 ∈ padded (selector profile).1 := by
    simp [padded, hselectedRange, Set.nonempty_of_mem hselectedRange]
  have hsafeSelected :=
    hsafe (selector profile).1 (selector profile).2 hselectedPadded
  linarith [hgain profile]

/-- Failure of total-variation total boundedness supplies one fixed positive
amount of late finite mass beyond every horizon. -/
theorem exists_pos_forall_exists_lateFiniteMass_ge_of_not_totallyBounded
    {family : Set (PMF (Option Nat))}
    (hnot : ¬ IsPMFGeneralTVTotallyBounded family) :
    ∃ kappa : Real, 0 < kappa ∧ ∀ horizon : Nat,
      ∃ law ∈ family, kappa <= stoppingLawLateFiniteMass law horizon := by
  obtain ⟨kappa, hkappa, hescape⟩ :=
    exists_pos_forall_exists_finiteComplementMass_ge_of_not_totallyBounded hnot
  exact ⟨kappa, hkappa, fun horizon => hescape (stoppingLawFinitePrefix horizon)⟩

/-- **Profile-dependent selectors escape to late finite time.** One fixed
player and one fixed positive mass work simultaneously for every horizon;
only the selected deviation may depend on the horizon. -/
theorem exists_player_selectorRange_lateFiniteMass_escape
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
    ∃ who, ∃ kappa : Real, 0 < kappa ∧ ∀ horizon : Nat,
      ∃ strategy ∈ quittingBehaviorSelectorRange reward selector who,
        kappa <= stoppingLawLateFiniteMass
          (quittingBehaviorStoppingLaw reward strategy) horizon := by
  obtain ⟨who, hrangeNonempty, hrangeNotBounded⟩ :=
    exists_nonempty_selectorRange_not_strategicallyTotallyBounded
      reward selector hgap hgain
  have hlawsNotBounded : ¬ IsPMFGeneralTVTotallyBounded
      (quittingBehaviorStoppingLaw reward ''
        quittingBehaviorSelectorRange reward selector who) := by
    intro hlawsBounded
    exact hrangeNotBounded
      (isQuittingStrategicallyTotallyBounded_of_stoppingLaws
        reward who (quittingBehaviorSelectorRange reward selector who)
        hlawsBounded)
  obtain ⟨kappa, hkappa, hlate⟩ :=
    exists_pos_forall_exists_lateFiniteMass_ge_of_not_totallyBounded
      hlawsNotBounded
  refine ⟨who, kappa, hkappa, fun horizon => ?_⟩
  obtain ⟨law, ⟨strategy, hstrategy, rfl⟩, hmass⟩ := hlate horizon
  exact ⟨strategy, hstrategy, hmass⟩

end GameTheory
