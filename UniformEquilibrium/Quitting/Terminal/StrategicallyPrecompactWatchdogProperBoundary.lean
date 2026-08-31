/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.ProperStoppingApproximation
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction
import UniformEquilibrium.Quitting.Terminal.StrategicallyPrecompactWatchdogBoundary

/-!
# Proper watchdog boundary

Proper strategic approximation means approximation by a finite nonempty menu
of behaviors which stop at a finite time almost surely.  The centers need not
belong to the family.  This module proves the metric and stopping-law parts of
the exact watchdog boundary:

* proper total-variation approximation implies proper strategic
  approximation;
* failure of proper strategic approximation forces a fixed amount of
  late-or-Never mass beyond every finite horizon; and
* a strategically totally bounded family which fails proper approximation
  contains one member uniformly separated from every proper behavior.

The compact-game Nash producer which rules out a fixed-gap selector from one
properly approximable range is a separate game-semantic statement.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open Math.Probability Math.Probability.DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A behavior is proper when its induced live-spine stopping law has no
Never atom. -/
def IsProperQuittingBehaviorStrategy
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (strategy : (quittingGame reward).BehaviorStrategy who) : Prop :=
  Math.Probability.IsProperStoppingLaw
    (quittingBehaviorStoppingLaw reward strategy)

/-- Finite strategic approximation by proper behaviors.  The centers need
not belong to the approximated family. -/
def IsQuittingProperStrategicallyApproximable
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (family : Set ((quittingGame reward).BehaviorStrategy who)) : Prop :=
  ∀ error : Real, 0 < error ->
    ∃ net : Set ((quittingGame reward).BehaviorStrategy who),
      net.Finite ∧ net.Nonempty ∧
        (∀ center ∈ net,
          IsProperQuittingBehaviorStrategy reward who center) ∧
        ∀ strategy ∈ family, ∃ center ∈ net,
          QuittingStrategicallyWithin reward who error strategy center

theorem QuittingStrategicallyWithin.mono
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota) {first second : (quittingGame reward).BehaviorStrategy who}
    {small large : Real}
    (hclose : QuittingStrategicallyWithin reward who small first second)
    (herror : small <= large) :
    QuittingStrategicallyWithin reward who large first second := by
  intro profile
  exact (hclose profile).trans_le herror

theorem QuittingStrategicallyWithin.symm
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota) {first second : (quittingGame reward).BehaviorStrategy who}
    {error : Real}
    (hclose : QuittingStrategicallyWithin reward who error first second) :
    QuittingStrategicallyWithin reward who error second first := by
  intro profile
  simpa only [abs_sub_comm] using hclose profile

theorem QuittingStrategicallyWithin.add
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    {first second third : (quittingGame reward).BehaviorStrategy who}
    {firstError secondError : Real}
    (hfirst : QuittingStrategicallyWithin reward who firstError first second)
    (hsecond : QuittingStrategicallyWithin reward who secondError second third) :
    QuittingStrategicallyWithin reward who (firstError + secondError)
      first third := by
  intro profile
  calc
    |quittingTerminalPayoff reward (Function.update profile who first) who -
        quittingTerminalPayoff reward (Function.update profile who third) who| <=
        |quittingTerminalPayoff reward (Function.update profile who first) who -
          quittingTerminalPayoff reward (Function.update profile who second) who| +
        |quittingTerminalPayoff reward (Function.update profile who second) who -
          quittingTerminalPayoff reward (Function.update profile who third) who| :=
      abs_sub_le _ _ _
    _ < firstError + secondError :=
      add_lt_add (hfirst profile) (hsecond profile)

/-- Proper TV nets of induced stopping laws give proper strategic nets of the
original behaviors. -/
theorem isQuittingProperStrategicallyApproximable_of_properTVApproximable
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (family : Set ((quittingGame reward).BehaviorStrategy who))
    (htv : Math.Probability.IsPMFProperTVApproximable
      (quittingBehaviorStoppingLaw reward '' family)) :
    IsQuittingProperStrategicallyApproximable reward who family := by
  intro error herror
  let scale : Real := 2 * max 1 (quittingRewardBound reward)
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  obtain ⟨lawNet, hlawFinite, hlawNonempty, hlawProper, hlawCover⟩ :=
    htv (error / scale) (div_pos herror hscale)
  let realize : PMF (Option Nat) ->
      (quittingGame reward).BehaviorStrategy who :=
    quittingStoppingLawBehaviorStrategy reward who
  let net : Set ((quittingGame reward).BehaviorStrategy who) :=
    realize '' lawNet
  have hnetFinite : net.Finite := hlawFinite.image realize
  have hnetNonempty : net.Nonempty := hlawNonempty.image realize
  refine ⟨net, hnetFinite, hnetNonempty, ?_, fun strategy hstrategy => ?_⟩
  · rintro center ⟨law, hlaw, rfl⟩
    simpa [IsProperQuittingBehaviorStrategy, realize] using
      hlawProper law hlaw
  · have hlawMem : quittingBehaviorStoppingLaw reward strategy ∈
        quittingBehaviorStoppingLaw reward '' family :=
      ⟨strategy, hstrategy, rfl⟩
    obtain ⟨centerLaw, hcenterLaw, hclose⟩ := hlawCover _ hlawMem
    refine ⟨realize centerLaw, ⟨centerLaw, hcenterLaw, rfl⟩, ?_⟩
    intro profile
    have hforward :=
      quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV
        reward profile who strategy (realize centerLaw)
        (abs_reward_le_quittingRewardBound reward)
    have hbackward :=
      quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV
        reward profile who (realize centerLaw) strategy
        (abs_reward_le_quittingRewardBound reward)
    have hlawRealize : quittingBehaviorStoppingLaw reward (realize centerLaw) =
        centerLaw := by
      simp [realize]
    rw [hlawRealize] at hforward
    rw [hlawRealize, Math.Probability.pmfGeneralTV_symm] at hbackward
    have hbound : 2 * quittingRewardBound reward *
        Math.Probability.pmfGeneralTV
          (quittingBehaviorStoppingLaw reward strategy) centerLaw < error := by
      calc
        2 * quittingRewardBound reward *
            Math.Probability.pmfGeneralTV
              (quittingBehaviorStoppingLaw reward strategy) centerLaw <=
            scale * Math.Probability.pmfGeneralTV
              (quittingBehaviorStoppingLaw reward strategy) centerLaw := by
          have htvNonneg := Math.Probability.pmfGeneralTV_nonneg
            (quittingBehaviorStoppingLaw reward strategy) centerLaw
          have hrewardLe := le_max_right 1 (quittingRewardBound reward)
          dsimp only [scale]
          nlinarith
        _ < scale * (error / scale) :=
          mul_lt_mul_of_pos_left hclose hscale
        _ = error := by field_simp
    rw [abs_lt]
    constructor <;> linarith

/-- Proper strategic approximation of the empty family, using immediate Quit
as a harmless proper center. -/
theorem isQuittingProperStrategicallyApproximable_empty
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota) :
    IsQuittingProperStrategicallyApproximable reward who ∅ := by
  intro error _herror
  let center := quittingStoppingLawBehaviorStrategy reward who
    (PMF.pure (some 0))
  refine ⟨{center}, Set.finite_singleton center, Set.singleton_nonempty center,
    ?_, by simp⟩
  intro strategy hstrategy
  rw [Set.mem_singleton_iff.mp hstrategy]
  simp [IsProperQuittingBehaviorStrategy, center,
    Math.Probability.IsProperStoppingLaw]

/-- Failure of proper strategic approximation forces failure of proper TV
approximation for the induced stopping laws. -/
theorem not_properTVApproximable_of_not_quittingProperStrategicallyApproximable
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (family : Set ((quittingGame reward).BehaviorStrategy who))
    (hnot : ¬ IsQuittingProperStrategicallyApproximable reward who family) :
    ¬ Math.Probability.IsPMFProperTVApproximable
      (quittingBehaviorStoppingLaw reward '' family) := by
  intro htv
  exact hnot
    (isQuittingProperStrategicallyApproximable_of_properTVApproximable
      reward who family htv)

/-- Every failure of proper strategic approximation carries one fixed amount
of late-or-Never mass beyond every finite horizon. -/
theorem exists_lateOrNeverMass_escape_of_not_properStrategicallyApproximable
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (family : Set ((quittingGame reward).BehaviorStrategy who))
    (hnot : ¬ IsQuittingProperStrategicallyApproximable reward who family) :
    ∃ kappa : Real, 0 < kappa ∧ ∀ horizon : Nat,
      ∃ strategy ∈ family,
        kappa <= Math.Probability.stoppingLawLateOrNeverMass
          (quittingBehaviorStoppingLaw reward strategy) horizon := by
  have hlawsNot :=
    not_properTVApproximable_of_not_quittingProperStrategicallyApproximable
      reward who family hnot
  obtain ⟨kappa, hkappa, hescape⟩ :=
    Math.Probability.exists_pos_forall_exists_lateOrNeverMass_ge_of_not_properTVApproximable
      hlawsNot
  refine ⟨kappa, hkappa, fun horizon => ?_⟩
  obtain ⟨law, ⟨strategy, hstrategy, rfl⟩, hmass⟩ := hescape horizon
  exact ⟨strategy, hstrategy, hmass⟩

/-- In a strategically totally bounded family, failure of proper
approximation is witnessed by one family member separated from every proper
behavior by a fixed positive strategic radius. -/
theorem exists_essentialNeverWitness_of_totallyBounded_not_properApproximable
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (family : Set ((quittingGame reward).BehaviorStrategy who))
    (htotallyBounded :
      IsQuittingStrategicallyTotallyBounded reward who family)
    (hnot : ¬ IsQuittingProperStrategicallyApproximable reward who family) :
    ∃ strategy ∈ family, ∃ separation : Real, 0 < separation ∧
      ∀ proper : (quittingGame reward).BehaviorStrategy who,
        IsProperQuittingBehaviorStrategy reward who proper ->
          ¬ QuittingStrategicallyWithin reward who separation strategy proper := by
  have hfamilyNonempty : family.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hnot
    exact hnot (isQuittingProperStrategicallyApproximable_empty reward who)
  unfold IsQuittingProperStrategicallyApproximable at hnot
  push Not at hnot
  obtain ⟨error, herror, hfailure⟩ := hnot
  let radius := error / 3
  have hradius : 0 < radius := by dsimp only [radius]; linarith
  obtain ⟨net, hnetFinite, hnetSubset, hnetCover⟩ :=
    htotallyBounded radius hradius
  have hnetNonempty : net.Nonempty := by
    obtain ⟨strategy, hstrategy⟩ := hfamilyNonempty
    obtain ⟨center, hcenter, _⟩ := hnetCover strategy hstrategy
    exact ⟨center, hcenter⟩
  by_contra hnone
  push Not at hnone
  have hproperChoice : ∀ center ∈ net,
      ∃ proper : (quittingGame reward).BehaviorStrategy who,
        IsProperQuittingBehaviorStrategy reward who proper ∧
          QuittingStrategicallyWithin reward who radius center proper := by
    intro center hcenter
    have hcenterFamily := hnetSubset hcenter
    obtain ⟨proper, hproper, hproperClose⟩ :=
      hnone center hcenterFamily radius hradius
    exact ⟨proper, hproper, hproperClose⟩
  classical
  let proper : (quittingGame reward).BehaviorStrategy who ->
      (quittingGame reward).BehaviorStrategy who := fun center =>
    if hcenter : center ∈ net then
      (hproperChoice center hcenter).choose
    else center
  have hproper : ∀ center ∈ net,
      IsProperQuittingBehaviorStrategy reward who (proper center) := by
    intro center hcenter
    simpa only [proper, dif_pos hcenter] using
      (hproperChoice center hcenter).choose_spec.1
  have hproperClose : ∀ center ∈ net,
      QuittingStrategicallyWithin reward who radius center
        (proper center) := by
    intro center hcenter
    simpa only [proper, dif_pos hcenter] using
      (hproperChoice center hcenter).choose_spec.2
  let properNet : Set ((quittingGame reward).BehaviorStrategy who) :=
    proper '' net
  have hproperNetFinite : properNet.Finite := hnetFinite.image proper
  have hproperNetNonempty : properNet.Nonempty := hnetNonempty.image proper
  have hproperNetProper : ∀ center ∈ properNet,
      IsProperQuittingBehaviorStrategy reward who center := by
    rintro center ⟨source, hsource, rfl⟩
    exact hproper source hsource
  have hproperNetCover : ∀ strategy ∈ family,
      ∃ center ∈ properNet,
        QuittingStrategicallyWithin reward who error strategy center := by
    intro strategy hstrategy
    obtain ⟨center, hcenter, hclose⟩ := hnetCover strategy hstrategy
    refine ⟨proper center, ⟨center, hcenter, rfl⟩, ?_⟩
    exact (hclose.add reward who (hproperClose center hcenter)).mono
      reward who (by dsimp only [radius]; linarith)
  obtain ⟨strategy, hstrategy, hbad⟩ :=
    hfailure properNet hproperNetFinite hproperNetNonempty hproperNetProper
  obtain ⟨center, hcenter, hclose⟩ :=
    hproperNetCover strategy hstrategy
  exact hbad center hcenter hclose

/-- The essential witness is itself nonproper, hence its induced stopping law
has a nonzero Never atom. -/
theorem exists_nonproper_essentialNeverWitness_of_totallyBounded
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (family : Set ((quittingGame reward).BehaviorStrategy who))
    (htotallyBounded :
      IsQuittingStrategicallyTotallyBounded reward who family)
    (hnot : ¬ IsQuittingProperStrategicallyApproximable reward who family) :
    ∃ strategy ∈ family,
      ¬ IsProperQuittingBehaviorStrategy reward who strategy ∧
      ∃ separation : Real, 0 < separation ∧
        ∀ proper : (quittingGame reward).BehaviorStrategy who,
          IsProperQuittingBehaviorStrategy reward who proper ->
            ¬ QuittingStrategicallyWithin reward who separation strategy proper := by
  obtain ⟨strategy, hstrategy, separation, hseparation, hfar⟩ :=
    exists_essentialNeverWitness_of_totallyBounded_not_properApproximable
      reward who family htotallyBounded hnot
  have hstrategyNotProper :
      ¬ IsProperQuittingBehaviorStrategy reward who strategy := by
    intro hproper
    apply hfar strategy hproper
    intro profile
    simpa using hseparation
  exact ⟨strategy, hstrategy, hstrategyNotProper, separation,
    hseparation, hfar⟩

end GameTheory
