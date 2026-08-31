/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.FiniteIndependentMixture
import UniformEquilibrium.Quitting.Paths.FiniteStoppingLawMixture
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Terminal.CompactStoppingLawProfile

/-!
# Canonical reconstruction from complete stopping laws

Reconstructing conditional hazards from the players' complete live-spine
stopping laws preserves prescribed terminal payoffs, unrestricted deviation
caps, and hence the full terminal semantic pair.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

omit [Nontrivial ι] in
/-- Arbitrary complete stopping-law reconstruction is affine for every payoff
observer, not only for the player whose law is reconstructed. -/
theorem quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mixer observer : ι) (law : PMF (Option Nat)) :
    quittingTerminalPayoff reward
        (Function.update profile mixer
          (quittingStoppingLawBehaviorStrategy reward mixer law)) observer =
      expect law (fun choice =>
        quittingTerminalPayoff reward
          (Function.update profile mixer
            (quittingPureTimeBehaviorStrategy reward mixer choice)) observer) := by
  let observerReward := quittingObserverReward reward observer
  have h := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    observerReward profile mixer
      (quittingStoppingLawBehaviorStrategy reward mixer law)
  rw [quittingTerminalPayoff_observerReward reward _ observer mixer] at h
  calc
    quittingTerminalPayoff reward
        (Function.update profile mixer
          (quittingStoppingLawBehaviorStrategy reward mixer law)) observer =
      expect
        (quittingBehaviorStoppingLaw observerReward
          (quittingStoppingLawBehaviorStrategy reward mixer law))
        (fun choice =>
          quittingTerminalPayoff observerReward
            (Function.update profile mixer
              (quittingPureTimeBehaviorStrategy observerReward mixer choice))
            mixer) := h
    _ = expect law (fun choice =>
        quittingTerminalPayoff reward
          (Function.update profile mixer
            (quittingPureTimeBehaviorStrategy reward mixer choice)) observer) := by
      rw [show quittingBehaviorStoppingLaw observerReward
          (quittingStoppingLawBehaviorStrategy reward mixer law) = law by
        change quittingBehaviorStoppingLaw observerReward
          (quittingStoppingLawBehaviorStrategy observerReward mixer law) = law
        exact quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy
          observerReward mixer law]
      apply congrArg (expect law)
      funext choice
      rw [quittingTerminalPayoff_observerReward reward _ observer mixer]
      rfl

omit [Nontrivial ι] in
/-- The payoff to any observer is the stopping-law mixture of one displayed
player's deterministic live-spine stopping times. -/
theorem quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mixer observer : ι) :
    quittingTerminalPayoff reward profile observer =
      expect (quittingBehaviorStoppingLaw reward (profile mixer))
        (fun choice => quittingTerminalPayoff reward
          (Function.update profile mixer
            (quittingPureTimeBehaviorStrategy reward mixer choice)) observer) := by
  let observerReward := quittingObserverReward reward observer
  have h := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    observerReward profile mixer (profile mixer)
  rw [Function.update_eq_self] at h
  rw [quittingTerminalPayoff_observerReward reward _ observer mixer] at h
  calc
    quittingTerminalPayoff reward profile observer =
        expect (quittingBehaviorStoppingLaw observerReward (profile mixer))
          (fun choice => quittingTerminalPayoff observerReward
            (Function.update profile mixer
              (quittingPureTimeBehaviorStrategy observerReward mixer choice))
            mixer) := h
    _ = expect (quittingBehaviorStoppingLaw reward (profile mixer))
          (fun choice => quittingTerminalPayoff reward
            (Function.update profile mixer
              (quittingPureTimeBehaviorStrategy reward mixer choice)) observer) := by
      apply congrArg
      funext choice
      rw [quittingTerminalPayoff_observerReward reward _ observer mixer]
      rfl

omit [Nontrivial ι] in
/-- Reconstructing one player's conditional hazard from that player's actual
stopping law preserves every observer's terminal payoff. -/
theorem quittingTerminalPayoff_update_stoppingLawReconstruction_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mixer observer : ι) :
    quittingTerminalPayoff reward
        (Function.update profile mixer
          (quittingStoppingLawBehaviorStrategy reward mixer
            (quittingBehaviorStoppingLaw reward (profile mixer)))) observer =
      quittingTerminalPayoff reward profile observer := by
  rw [quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect]
  exact (quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime
    reward profile mixer observer).symm

/-- Canonicalize the displayed players by reconstructing their actual
live-spine stopping laws. -/
def quittingStoppingLawCanonicalizeOn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (players : Finset ι) : (quittingGame reward).BehaviorProfile :=
  fun who => if who ∈ players then
    quittingStoppingLawBehaviorStrategy reward who
      (quittingBehaviorStoppingLaw reward (profile who))
  else profile who

omit [Nontrivial ι] in
/-- Canonicalizing any finite set of players preserves every observer's
terminal payoff. -/
theorem quittingTerminalPayoff_stoppingLawCanonicalizeOn_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (players : Finset ι) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawCanonicalizeOn reward profile players) observer =
      quittingTerminalPayoff reward profile observer := by
  classical
  induction players using Finset.induction_on with
  | empty => rfl
  | @insert mixer players hmixer ih =>
      have hmixerStrategy :
          quittingStoppingLawCanonicalizeOn reward profile players mixer =
            profile mixer := by
        simp [quittingStoppingLawCanonicalizeOn, hmixer]
      have hprofile :
          quittingStoppingLawCanonicalizeOn reward profile (insert mixer players) =
            Function.update
              (quittingStoppingLawCanonicalizeOn reward profile players) mixer
              (quittingStoppingLawBehaviorStrategy reward mixer
                (quittingBehaviorStoppingLaw reward (profile mixer))) := by
        funext who
        by_cases hwho : who = mixer
        · subst who
          simp [quittingStoppingLawCanonicalizeOn]
        · simp [quittingStoppingLawCanonicalizeOn, hwho]
      rw [hprofile]
      have hone := quittingTerminalPayoff_update_stoppingLawReconstruction_eq
        reward (quittingStoppingLawCanonicalizeOn reward profile players)
          mixer observer
      rw [hmixerStrategy] at hone
      exact hone.trans ih

/-- Compact stopping laws extracted from the actual live-spine hazards of a
behavior profile. -/
def quittingCompactStoppingLawsOfProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ι → CompactStoppingLaw :=
  fun who => CompactStoppingLaw.ofPMF
    (quittingBehaviorStoppingLaw reward (profile who))

omit [Nontrivial ι] in
/-- Canonicalizing every player is exactly reconstruction from the compact
stopping laws extracted from the source profile. -/
theorem quittingStoppingLawCanonicalizeOn_univ_eq_compactStoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingStoppingLawCanonicalizeOn reward profile Finset.univ =
      quittingCompactStoppingLawProfile reward
        (quittingCompactStoppingLawsOfProfile reward profile) := by
  funext who
  simp [quittingStoppingLawCanonicalizeOn,
    quittingCompactStoppingLawProfile, quittingCompactStoppingLawsOfProfile]

omit [Nontrivial ι] in
/-- Prescribed terminal payoffs depend only on the players' complete
live-spine stopping laws. -/
theorem quittingTerminalPayoff_eq_compactStoppingLawsOfProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    quittingTerminalPayoff reward profile observer =
      quittingTerminalPayoff reward
        (quittingCompactStoppingLawProfile reward
          (quittingCompactStoppingLawsOfProfile reward profile)) observer := by
  rw [← quittingStoppingLawCanonicalizeOn_univ_eq_compactStoppingLawProfile]
  exact (quittingTerminalPayoff_stoppingLawCanonicalizeOn_eq
    reward profile Finset.univ observer).symm

omit [Nontrivial ι] in
/-- Every deterministic deviation payoff depends only on the opponents'
complete stopping laws. -/
theorem quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : CompactStoppingTime) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) who =
      quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward
            (quittingCompactStoppingLawsOfProfile reward profile)) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who := by
  classical
  let deviation := quittingPureTimeBehaviorStrategy reward who choice
  let updated := Function.update profile who deviation
  have hcanonical :
      quittingStoppingLawCanonicalizeOn reward updated (Finset.univ.erase who) =
        Function.update
          (quittingCompactStoppingLawProfile reward
            (quittingCompactStoppingLawsOfProfile reward profile)) who deviation := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingStoppingLawCanonicalizeOn, updated]
    · simp [quittingStoppingLawCanonicalizeOn, updated,
        quittingCompactStoppingLawProfile, quittingCompactStoppingLawsOfProfile,
        hplayer]
  have hinvariant := quittingTerminalPayoff_stoppingLawCanonicalizeOn_eq
    reward updated (Finset.univ.erase who) who
  rw [hcanonical] at hinvariant
  exact hinvariant.symm

omit [Nontrivial ι] in
/-- The unrestricted behavioral deviation cap is also preserved by complete
stopping-law reconstruction.  Pure-time extremality is used only to identify
the exact supremum. -/
theorem quittingContinuationBestResponseValue_eq_compactStoppingLawsOfProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingContinuationBestResponseValue reward profile who =
      quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward
          (quittingCompactStoppingLawsOfProfile reward profile)) who := by
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime,
    sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  congr 2
  funext choice
  exact quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile
    reward profile who choice

omit [Nontrivial ι] in
/-- Exact source adapter: the full prescribed/unrestricted-cap semantic pair
is unchanged by canonical complete stopping-law reconstruction. -/
theorem quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward profile =
      quittingTerminalSemanticPair reward
        (quittingCompactStoppingLawProfile reward
          (quittingCompactStoppingLawsOfProfile reward profile)) := by
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_eq_compactStoppingLawsOfProfile
      reward profile who
  · funext who
    exact quittingContinuationBestResponseValue_eq_compactStoppingLawsOfProfile
      reward profile who

end GameTheory
