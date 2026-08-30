/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingRecursion
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingNash
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-!
# Retained-tail finite timing realization

This module realizes independent mixed finite timing laws as one literal
finite word of quitting roots followed by an arbitrary behavioral tail.  It
owns the exact normal-form payoff recursion and the conditional-tail Nash
transfer used to compile a positive-`Never` mixed Nash law into a credible
literal root stack.

The finite timing Nash hypothesis controls only the displayed timing menu.
It is compiled below to `IsQuittingRetainedTailFiniteTimingNash`; no equality
with the unrestricted behavioral best-response cap is asserted.

This module supplies the exact normal-form recursion omitted by the zero-tail
finite timing game.  Every pure timing declaration is executed for the finite
word and resumes one fixed actual behavioral tail on joint `Never`.  The mixed
evaluator is definitionally the expected payoff of that literal graft.

The final compiler starts from an actual mixed Nash law with positive `Never`
mass in every marginal.  It does not assume a supplied credible root stack.
No approximate-Nash, behavioral-Nash, Fin4 chronology, or punishment adapter
is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Retained-tail timing games and root words -/

/-- Pure root word represented by one finite timing-action profile.  A player
Quits at exactly its selected finite date and Continues at every displayed
date when it selects `Never`. -/
def quittingRetainedTailPureTimingRootStack
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) :
    List (ι → PMF Bool) :=
  List.ofFn fun date who => PMF.pure (decide (choices who = some date))

/-- The finite normal-form timing game whose `Never` action resumes one fixed
actual behavioral tail.  This differs from the hard zero-tail timing game. -/
abbrev quittingRetainedTailFiniteTimingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) : KernelGame ι :=
  KernelGame.ofPureEU (fun _ => QuittingFiniteDeadlineTimingAction deadline)
    (fun choices who => quittingTerminalPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward
        (quittingRetainedTailPureTimingRootStack deadline choices) tail) who)

/-- The retained-tail timing game has the finite timing-profile outcome
carrier. -/
instance quittingRetainedTailFiniteTimingGame_finiteOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) :
    Finite (quittingRetainedTailFiniteTimingGame reward deadline tail).Outcome := by
  unfold quittingRetainedTailFiniteTimingGame KernelGame.ofPureEU
  infer_instance

/-- The finite hazard word carried by independent mixed timing laws. -/
def quittingRetainedTailMixedTimingRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    List (ι → PMF Bool) :=
  List.ofFn fun date : Fin deadline => quittingProfileLiveRoot reward
    (quittingFiniteDeadlineTimingProfile reward deadline mixed) date.val

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingRetainedTailPureTimingRootStack_length
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) :
    (quittingRetainedTailPureTimingRootStack deadline choices).length =
      deadline := by
  simp [quittingRetainedTailPureTimingRootStack]

omit [DecidableEq ι] in
@[simp] theorem quittingRetainedTailMixedTimingRootStack_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingRetainedTailMixedTimingRootStack reward deadline mixed).length =
      deadline := by
  simp [quittingRetainedTailMixedTimingRootStack]

/-- A finite root word followed by the all-Continue tail is its hard
zero-tail realization. -/
def quittingRetainedTailFiniteTimingHardGraft
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) :
    (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailFiniteTimingGraft reward roots
    (quittingAlwaysContinueProfile reward)

/-- The actual behavioral profile which executes the mixed-law finite root
word and resumes the prescribed tail on joint `Never`. -/
def quittingRetainedTailMixedTimingProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailFiniteTimingGraft reward
    (quittingRetainedTailMixedTimingRootStack reward deadline mixed) tail

omit [DecidableEq ι] in
private theorem quittingLiteralRootStackProfile_apply_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) (history : (quittingGame reward).Hist time)
    (htime : time < roots.length) :
    quittingLiteralRootStackProfile reward roots tail who time history =
      roots.get ⟨time, htime⟩ who := by
  induction roots generalizing time with
  | nil => simp at htime
  | cons root roots ih =>
      cases time with
      | zero => rfl
      | succ time =>
          change quittingLiteralRootStackProfile reward roots tail who time
              (Fin.tail history.1, history.2) =
            roots.get ⟨time, by simpa using htime⟩ who
          exact ih time (Fin.tail history.1, history.2) (by simpa using htime)

omit [DecidableEq ι] in
private theorem quittingLiteralRootStackProfile_allContinue_of_length_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (who : ι) (time : ℕ) (history : (quittingGame reward).Hist time)
    (htime : roots.length ≤ time) :
    quittingLiteralRootStackProfile reward roots
        (quittingAlwaysContinueProfile reward) who time history =
      PMF.pure false := by
  induction roots generalizing time with
  | nil =>
      rfl
  | cons root roots ih =>
      cases time with
      | zero => simp at htime
      | succ time =>
          change quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward) who time
                (Fin.tail history.1, history.2) = PMF.pure false
          exact ih time (Fin.tail history.1, history.2) (by simpa using htime)

omit [DecidableEq ι] in
private theorem quittingLiteralRootStackProfile_player_eq_of_map_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι)
    (hmap : first.map (fun root ↦ root who) =
      second.map (fun root ↦ root who)) :
    quittingLiteralRootStackProfile reward first tail who =
      quittingLiteralRootStackProfile reward second tail who := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons root roots => simp at hmap
  | cons root roots ih =>
      cases second with
      | nil => simp at hmap
      | cons otherRoot otherRoots =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          funext time history
          cases time with
          | zero => exact hmap.1
          | succ time =>
              change quittingLiteralRootStackProfile reward roots tail who time
                  (Fin.tail history.1, history.2) =
                quittingLiteralRootStackProfile reward otherRoots tail who time
                  (Fin.tail history.1, history.2)
              rw [ih otherRoots hmap.2]

omit [DecidableEq ι] in
/-- The hard graft of the mixed-law hazard word is literally the canonical
behavioral realization of those independent finite timing laws.  This holds
also when a current survival probability is zero. -/
theorem quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingRetainedTailFiniteTimingHardGraft reward
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) =
      quittingFiniteDeadlineTimingProfile reward deadline mixed := by
  funext who time history
  by_cases htime : time < deadline
  · rw [quittingRetainedTailFiniteTimingHardGraft,
      quittingRetainedTailFiniteTimingGraft,
      quittingLiteralRootStackProfile_apply_lt]
    · simp only [quittingRetainedTailMixedTimingRootStack, List.get_ofFn]
      unfold quittingProfileLiveRoot quittingFiniteDeadlineTimingProfile
        quittingCompactStoppingLawProfile quittingStoppingLawBehaviorStrategy
      rfl
    · simpa using htime
  · rw [quittingRetainedTailFiniteTimingHardGraft,
      quittingRetainedTailFiniteTimingGraft,
      quittingLiteralRootStackProfile_allContinue_of_length_le]
    · have hroot := congrFun
          (quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
            reward deadline mixed (Nat.le_of_not_gt htime)) who
      unfold quittingProfileLiveRoot quittingFiniteDeadlineTimingProfile
        quittingCompactStoppingLawProfile quittingStoppingLawBehaviorStrategy
        quittingAllContinueRoot at hroot
      exact hroot.symm
    · simpa using Nat.le_of_not_gt htime

omit [DecidableEq ι] in
/-- Playerwise survival through the mixed timing root word is the declared
`Never` mass of that player's finite timing law. -/
theorem quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingLiteralRootStackOwnSurvival
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) who =
      (mixed who none).toReal := by
  let law : PMF (Option ℕ) :=
    (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
  unfold quittingLiteralRootStackOwnSurvival
    quittingRetainedTailMixedTimingRootStack quittingProfileLiveRoot
    quittingFiniteDeadlineTimingProfile quittingCompactStoppingLawProfile
    quittingStoppingLawBehaviorStrategy
  rw [List.map_ofFn]
  change (List.ofFn fun date : Fin deadline =>
      (((Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard law).toBoolean
        date.val false).toReal)).prod = (mixed who none).toReal
  rw [List.prod_ofFn]
  simp only [Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
    Math.Probability.DiscreteHazard.booleanCoin_false_toReal]
  let continuationMass : ℕ → ℝ := fun time =>
    1 - (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard law).stop time
  change (∏ date : Fin deadline, continuationMass date.val) =
    (mixed who none).toReal
  rw [Fin.prod_univ_eq_prod_range]
  have hproduct : Math.survivalProduct continuationMass 0 deadline =
      ∏ time ∈ Finset.range deadline, continuationMass time := by
    simp [Math.survivalProduct]
  rw [← hproduct]
  change (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard law).survival
      0 deadline = (mixed who none).toReal
  rw [Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard_survival]
  have htail : ∀ time, deadline ≤ time →
      Math.Probability.DiscreteHazard.StoppingLaw.finiteMass law time = 0 := by
    intro time htime
    have hzero := quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le
      (mixed who) htime
    dsimp only [law,
      Math.Probability.DiscreteHazard.StoppingLaw.finiteMass]
    exact congrArg ENNReal.toReal hzero
  have hsum : (∑' time,
      Math.Probability.DiscreteHazard.StoppingLaw.finiteMass law time) =
      ∑ time ∈ Finset.range deadline,
        Math.Probability.DiscreteHazard.StoppingLaw.finiteMass law time := by
    rw [tsum_eq_sum (s := Finset.range deadline)]
    intro time htime
    exact htail time (Nat.le_of_not_gt (by simpa using htime))
  have htotal :=
    Math.Probability.DiscreteHazard.StoppingLaw.none_add_tsum_finiteMass law
  rw [hsum] at htotal
  have hnone : (law none).toReal = (mixed who none).toReal := by
    have hmass : (mixed who).map quittingFiniteDeadlineTimingActionTime
        (⊤ : Math.Probability.CompactStoppingTime) = mixed who none := by
      rw [PMF.map_apply]
      rw [tsum_eq_single none]
      · simp [quittingFiniteDeadlineTimingActionTime]
      · intro action haction
        cases action with
        | none => exact (haction rfl).elim
        | some time => simp [quittingFiniteDeadlineTimingActionTime]
    dsimp only [law, quittingFiniteDeadlineTimingLaw]
    rw [Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    exact congrArg ENNReal.toReal hmass
  unfold Math.Probability.DiscreteHazard.StoppingLaw.survival
  linarith

omit [DecidableEq ι] in
/-- Joint finite-word survival is the product of the playerwise survival
coefficients. -/
theorem quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival
    (roots : List (ι → PMF Bool)) :
    quittingLiteralRootStackJointSurvival roots =
      ∏ player, quittingLiteralRootStackOwnSurvival roots player := by
  induction roots with
  | nil =>
      simp [quittingLiteralRootStackJointSurvival,
        quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      change quittingStationaryContinueMass root *
          quittingLiteralRootStackJointSurvival roots =
        ∏ player, (root player false).toReal *
          quittingLiteralRootStackOwnSurvival roots player
      rw [quittingStationaryContinueMass_eq_prod_continueProbability, ih,
        Finset.prod_mul_distrib]

private theorem quittingRootOpponentContinueMass_eq_prod_erase
    (root : ι → PMF Bool) (player : ι) :
    quittingRootOpponentContinueMass root player =
      ∏ other ∈ Finset.univ.erase player, (root other false).toReal := by
  classical
  rw [quittingRootOpponentContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  have hfunction :
      (fun other =>
        ((Function.update root player (PMF.pure false)) other false).toReal) =
        Function.update (fun other => (root other false).toReal) player 1 := by
    funext other
    by_cases hother : other = player
    · subst other
      simp
    · simp [Function.update_of_ne hother]
  rw [hfunction, Finset.prod_update_of_mem (Finset.mem_univ player)]
  simp only [one_mul, Finset.sdiff_singleton_eq_erase]

/-- Player-deleted finite-word survival is the product of every other
player's own survival coefficient. -/
theorem quittingLiteralRootStackOpponentSurvival_eq_prod_ownSurvival_erase
    (roots : List (ι → PMF Bool)) (player : ι) :
    quittingLiteralRootStackOpponentSurvival roots player =
      ∏ other ∈ Finset.univ.erase player,
        quittingLiteralRootStackOwnSurvival roots other := by
  induction roots with
  | nil =>
      simp [quittingLiteralRootStackOpponentSurvival,
        quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      change quittingRootOpponentContinueMass root player *
          quittingLiteralRootStackOpponentSurvival roots player =
        ∏ other ∈ Finset.univ.erase player,
          (root other false).toReal *
            quittingLiteralRootStackOwnSurvival roots other
      rw [quittingRootOpponentContinueMass_eq_prod_erase, ih,
        Finset.prod_mul_distrib]

omit [Fintype ι] [DecidableEq ι] in
/-- A deterministic player's finite timing word survives exactly when that
player selected `Never`. -/
theorem quittingRetainedTailPureTimingRootStack_ownSurvival_eq_indicator
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
    (who : ι) :
    quittingLiteralRootStackOwnSurvival
        (quittingRetainedTailPureTimingRootStack deadline choices) who =
      if choices who = none then 1 else 0 := by
  unfold quittingLiteralRootStackOwnSurvival
    quittingRetainedTailPureTimingRootStack
  rw [List.map_ofFn, List.prod_ofFn]
  cases hchoice : choices who with
  | none => simp [hchoice]
  | some chosen =>
      rw [if_neg (by simp)]
      apply Finset.prod_eq_zero (Finset.mem_univ chosen)
      simp [hchoice]

omit [DecidableEq ι] in
/-- A deterministic finite timing word jointly survives exactly on the
all-`Never` pure timing profile. -/
theorem quittingRetainedTailPureTimingRootStack_jointSurvival_eq_indicator
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) :
    quittingLiteralRootStackJointSurvival
        (quittingRetainedTailPureTimingRootStack deadline choices) =
      if choices = fun _ ↦ none then 1 else 0 := by
  rw [quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival]
  simp_rw [quittingRetainedTailPureTimingRootStack_ownSurvival_eq_indicator]
  by_cases hall : choices = fun _ ↦ none
  · subst choices
    simp
  · rw [if_neg hall]
    have hexists : ∃ who, choices who ≠ none := by
      by_contra hnone
      push Not at hnone
      exact hall (funext hnone)
    obtain ⟨who, hwho⟩ := hexists
    apply Finset.prod_eq_zero (Finset.mem_univ who)
    simp [hwho]

omit [DecidableEq ι] in
/-- Joint survival of the mixed-law root word is the product of all declared
`Never` masses. -/
theorem quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingLiteralRootStackJointSurvival
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) =
      ∏ player, (mixed player none).toReal := by
  rw [quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival]
  exact Finset.prod_congr rfl fun player _ =>
    quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
      reward deadline mixed player

/-- Player-deleted survival of the mixed-law root word is the product of the
opponents' declared `Never` masses. -/
theorem quittingRetainedTailMixedTimingRootStack_opponentSurvival_eq_prod_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingLiteralRootStackOpponentSurvival
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) who =
      ∏ other ∈ Finset.univ.erase who, (mixed other none).toReal := by
  rw [quittingLiteralRootStackOpponentSurvival_eq_prod_ownSurvival_erase]
  exact Finset.prod_congr rfl fun other _ =>
    quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
      reward deadline mixed other

/-- Replacing one timing marginal by pure `Never` literally forces that
player to Continue at every root of the finite word. -/
theorem quittingRetainedTailMixedTimingRootStack_update_pure_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingRetainedTailMixedTimingRootStack reward deadline
        (Function.update mixed who (PMF.pure none)) =
      quittingLiteralRootStackForceContinue
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) who := by
  unfold quittingRetainedTailMixedTimingRootStack
    quittingLiteralRootStackForceContinue
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext date
  funext player
  simp only [Function.comp_apply]
  unfold quittingProfileLiveRoot quittingFiniteDeadlineTimingProfile
    quittingCompactStoppingLawProfile quittingStoppingLawBehaviorStrategy
    quittingFiniteDeadlineTimingLaw
  by_cases hplayer : player = who
  · subst player
    simp only [Function.update_self,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    rw [PMF.pure_map]
    change
      (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
        (PMF.pure none)).toBoolean date.val = PMF.pure false
    apply pmfBool_eq_of_true_toReal_eq
    simp [Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
      Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard,
      Math.Probability.DiscreteHazard.StoppingLaw.finiteMass]
  · simp [Function.update_of_ne hplayer]

/-- Updating one mixed timing marginal changes only that player's complete
behavioral strategy in the realized retained-tail profile. -/
theorem quittingRetainedTailMixedTimingProfile_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile)
    (who : ι)
    (law : PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingRetainedTailMixedTimingProfile reward deadline
        (Function.update mixed who law) tail =
      Function.update
        (quittingRetainedTailMixedTimingProfile reward deadline mixed tail) who
        (quittingRetainedTailMixedTimingProfile reward deadline
          (Function.update mixed who law) tail who) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    rw [Function.update_self]
  · rw [Function.update_of_ne hplayer]
    unfold quittingRetainedTailMixedTimingProfile
      quittingRetainedTailFiniteTimingGraft
    apply quittingLiteralRootStackProfile_player_eq_of_map_eq
    unfold quittingRetainedTailMixedTimingRootStack
    rw [List.map_ofFn, List.map_ofFn]
    apply congrArg List.ofFn
    funext date
    unfold quittingProfileLiveRoot quittingFiniteDeadlineTimingProfile
      quittingCompactStoppingLawProfile quittingStoppingLawBehaviorStrategy
      quittingFiniteDeadlineTimingLaw
    simp [Function.update_of_ne hplayer]

/-- Literal pure payoff of one retained-tail finite timing declaration. -/
def quittingRetainedTailTimingPurePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
    (who : ι) : ℝ :=
  quittingTerminalPayoff reward
    (quittingRetainedTailFiniteTimingGraft reward
      (quittingRetainedTailPureTimingRootStack deadline choices) tail) who

/-- Expected retained-tail payoff under independent mixed timing laws. -/
def quittingRetainedTailTimingMixedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) : ℝ :=
  Math.Probability.expect (pmfPi mixed) fun choices =>
    quittingRetainedTailTimingPurePayoff reward tail deadline choices who

omit [DecidableEq ι] in
/-- The retained-tail normal-form mixed EU is exactly the expectation of the
literal behavioral graft, with no semantic replacement of the terminal tail. -/
theorem quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        mixed who =
      quittingRetainedTailTimingMixedPayoff reward tail deadline mixed who := by
  letI : Finite
      (quittingRetainedTailFiniteTimingGame reward deadline tail).Outcome :=
    quittingRetainedTailFiniteTimingGame_finiteOutcome reward deadline tail
  rw [(quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension_eu]
  unfold quittingRetainedTailTimingMixedPayoff
    quittingRetainedTailTimingPurePayoff quittingRetainedTailFiniteTimingGame
  simp only [KernelGame.eu_ofPureEU]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The current root and shifted choices split the literal pure root word. -/
theorem quittingRetainedTailPureTimingRootStack_succ
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (deadline + 1)) :
    quittingRetainedTailPureTimingRootStack (deadline + 1) choices =
      timingChoicesRoot choices ::
        quittingRetainedTailPureTimingRootStack deadline
          (timingChoicesTail choices) := by
  unfold quittingRetainedTailPureTimingRootStack
  rw [List.ofFn_succ]
  congr 1
  · funext who
    unfold timingChoicesRoot
    cases hchoice : choices who with
    | none => rfl
    | some time =>
        cases time using Fin.cases with
        | zero => rfl
        | succ later => rfl
  · apply congrArg List.ofFn
    funext date
    funext who
    apply congrArg PMF.pure
    cases hchoice : choices who with
    | none => simp [hchoice, timingChoicesTail, timingActionTail]
    | some time =>
        cases time using Fin.cases with
        | zero =>
            have htail : timingChoicesTail choices who = none := by
              unfold timingChoicesTail
              rw [hchoice]
              rfl
            rw [htail]
            have hleft : (0 : Fin (deadline + 1)) ≠ date.succ := by
              intro heq
              have := congrArg Fin.val heq
              simp at this
            have hright : (none : Option (Fin deadline)) ≠ some date := by
              intro heq
              cases heq
            simp [hleft, hright]
        | succ later => simp [hchoice, timingChoicesTail, timingActionTail]

omit [DecidableEq ι] in
/-- At deadline zero the retained timing payoff is the prescribed payoff of
the actual retained tail. -/
theorem quittingRetainedTailTimingMixedPayoff_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction 0))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail 0 mixed who =
      quittingTerminalPayoff reward tail who := by
  have hmixed : mixed = fun _ => PMF.pure none := by
    funext player
    exact Math.ProbabilityMassFunction.eq_pure_of_subsingleton _ none
  rw [hmixed]
  unfold quittingRetainedTailTimingMixedPayoff
  rw [pmfPi_pure]
  simp [quittingRetainedTailTimingPurePayoff,
    quittingRetainedTailPureTimingRootStack,
    quittingRetainedTailFiniteTimingGraft]

omit [DecidableEq ι] in
/-- Bellman peeling for a deterministic retained-tail timing declaration. -/
theorem quittingRetainedTailTimingPurePayoff_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (deadline + 1))
    (who : ι) :
    quittingRetainedTailTimingPurePayoff reward tail (deadline + 1) choices who =
      quittingRootPayoff reward
        (fun player => quittingRetainedTailTimingPurePayoff reward tail deadline
          (timingChoicesTail choices) player)
        (fun player => timingActionCurrent (choices player)) who := by
  unfold quittingRetainedTailTimingPurePayoff
    quittingRetainedTailFiniteTimingGraft
  rw [quittingRetainedTailPureTimingRootStack_succ,
    quittingLiteralRootStackProfile_cons,
    quittingTerminalPayoff_rootThenContinuation_eq]
  unfold quittingRootExpectedPayoff timingChoicesRoot
  rw [pmfPi_pure]
  simp only [Math.Probability.expect_pure]

omit [DecidableEq ι] in
/-- Replacing the retained tail by all-Continue recovers the ordinary hard
finite-timing pure payoff. -/
theorem quittingRetainedTailTimingPurePayoff_alwaysContinue_eq_timingPurePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ (deadline : ℕ)
      (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
      (who : ι),
      quittingRetainedTailTimingPurePayoff reward
          (quittingAlwaysContinueProfile reward) deadline choices who =
        timingPurePayoff reward deadline choices who := by
  intro deadline
  induction deadline with
  | zero =>
      intro choices who
      unfold quittingRetainedTailTimingPurePayoff
        quittingRetainedTailPureTimingRootStack
        quittingRetainedTailFiniteTimingGraft
      rw [timingPurePayoff_zero]
      simp
  | succ deadline ih =>
      intro choices who
      rw [quittingRetainedTailTimingPurePayoff_succ,
        timingPurePayoff_succ]
      congr 1
      funext player
      exact ih (timingChoicesTail choices) player

omit [DecidableEq ι] in
/-- A retained-tail pure timing payoff is the hard timing payoff plus the
tail payoff on the unique all-`Never` declaration. -/
theorem quittingRetainedTailTimingPurePayoff_eq_timingPurePayoff_add_indicator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
    (who : ι) :
    quittingRetainedTailTimingPurePayoff reward tail deadline choices who =
      timingPurePayoff reward deadline choices who +
        quittingTerminalPayoff reward tail who *
          (if choices = fun _ ↦ none then 1 else 0) := by
  have hsub :=
    quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul
      reward (quittingRetainedTailPureTimingRootStack deadline choices)
      tail (quittingAlwaysContinueProfile reward) who
  rw [quittingTerminalPayoff_quittingAlwaysContinue, sub_zero,
    quittingRetainedTailPureTimingRootStack_jointSurvival_eq_indicator] at hsub
  have hhard :=
    quittingRetainedTailTimingPurePayoff_alwaysContinue_eq_timingPurePayoff
      reward deadline choices who
  unfold quittingRetainedTailTimingPurePayoff at hhard ⊢
  rw [hhard] at hsub
  linarith

/-- The literal retained-tail graft of independent mixed timing laws has
exactly the mixed expected utility of the retained-tail normal-form game. -/
theorem quittingTerminalPayoff_retainedTailMixedTimingGraft_eq_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward
          (quittingRetainedTailMixedTimingRootStack reward deadline mixed)
          tail) who =
      (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        mixed who := by
  have hindicator :
      Math.Probability.expect (pmfPi mixed)
          (fun choices ↦ if choices = (fun _ ↦ none) then 1 else 0) =
        ∏ player, (mixed player none).toReal := by
    rw [← Math.Probability.apply_toReal_eq_expect_indicator]
    simp only [pmfPi_apply, ENNReal.toReal_prod]
  have hmixed :
      quittingRetainedTailTimingMixedPayoff reward tail deadline mixed who =
        timingMixedPayoff reward deadline mixed who +
          quittingTerminalPayoff reward tail who *
            ∏ player, (mixed player none).toReal := by
    unfold quittingRetainedTailTimingMixedPayoff timingMixedPayoff
    calc
      Math.Probability.expect (pmfPi mixed)
          (fun choices ↦
            quittingRetainedTailTimingPurePayoff reward tail deadline
              choices who) =
        Math.Probability.expect (pmfPi mixed)
          (fun choices ↦ timingPurePayoff reward deadline choices who +
            quittingTerminalPayoff reward tail who *
              (if choices = (fun _ ↦ none) then 1 else 0)) := by
            congr 1
            funext choices
            exact quittingRetainedTailTimingPurePayoff_eq_timingPurePayoff_add_indicator
              reward tail deadline choices who
      _ = Math.Probability.expect (pmfPi mixed)
              (fun choices ↦ timingPurePayoff reward deadline choices who) +
            Math.Probability.expect (pmfPi mixed)
              (fun choices ↦ quittingTerminalPayoff reward tail who *
                (if choices = (fun _ ↦ none) then 1 else 0)) := by
            rw [Math.Probability.expect_add]
      _ = timingMixedPayoff reward deadline mixed who +
            quittingTerminalPayoff reward tail who *
              Math.Probability.expect (pmfPi mixed)
                (fun choices ↦ if choices = (fun _ ↦ none) then 1 else 0) := by
            rw [Math.Probability.expect_const_mul]
            rfl
      _ = _ := by
        rw [hindicator]
        unfold timingMixedPayoff
        rfl
  have hgraft :=
    quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul
      reward (quittingRetainedTailMixedTimingRootStack reward deadline mixed)
      tail (quittingAlwaysContinueProfile reward) who
  rw [quittingTerminalPayoff_quittingAlwaysContinue, sub_zero,
    quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none] at hgraft
  have hhard := congrArg (fun profile ↦ quittingTerminalPayoff reward profile who)
    (quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile
      reward deadline mixed)
  rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU,
    finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff] at hhard
  rw [quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff, hmixed]
  unfold quittingRetainedTailFiniteTimingHardGraft at hhard
  linarith

/-- Profile-named form of the retained-graft mixed expected-utility identity. -/
theorem quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingTerminalPayoff reward
        (quittingRetainedTailMixedTimingProfile reward deadline mixed tail) who =
      (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        mixed who := by
  exact quittingTerminalPayoff_retainedTailMixedTimingGraft_eq_mixedEU
    reward tail deadline mixed who

/-- Once one player chooses a finite date purely, the retained tail is
unreachable, so retained and hard finite timing expected utilities agree. -/
theorem quittingRetainedTailFiniteTimingGame_update_pureDate_eq_hardMixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (date : Fin deadline) :
    (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        (Function.update mixed who (PMF.pure (some date))) who =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        (Function.update mixed who (PMF.pure (some date))) who := by
  let updated := Function.update mixed who (PMF.pure (some date))
  let roots := quittingRetainedTailMixedTimingRootStack reward deadline updated
  have hzero : ∏ player, (updated player none).toReal = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ who)
    simp [updated]
  have hgraft :=
    quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul
      reward roots tail (quittingAlwaysContinueProfile reward) who
  rw [quittingTerminalPayoff_quittingAlwaysContinue, sub_zero,
    quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none,
    hzero, zero_mul] at hgraft
  have hretained :=
    quittingTerminalPayoff_retainedTailMixedTimingGraft_eq_mixedEU
      reward tail deadline updated who
  have hhard := congrArg (fun profile ↦ quittingTerminalPayoff reward profile who)
    (quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile
      reward deadline updated)
  unfold roots at hgraft hhard
  unfold quittingRetainedTailFiniteTimingHardGraft at hhard
  rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU] at hhard
  unfold updated at hgraft hretained hhard
  calc
    (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        (Function.update mixed who (PMF.pure (some date))) who =
      quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward
          (quittingRetainedTailMixedTimingRootStack reward deadline
            (Function.update mixed who (PMF.pure (some date)))) tail) who :=
      hretained.symm
    _ = quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward
          (quittingRetainedTailMixedTimingRootStack reward deadline
            (Function.update mixed who (PMF.pure (some date))))
          (quittingAlwaysContinueProfile reward)) who := sub_eq_zero.mp hgraft
    _ = _ := hhard

/-- A pure finite-date timing deviation has exactly the payoff of the
corresponding pure-time behavioral deviation from the realized profile. -/
theorem quittingTerminalPayoff_retainedTailMixedTimingProfile_update_pureDate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (date : Fin deadline) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingRetainedTailMixedTimingProfile reward deadline mixed tail) who
          (quittingPureTimeBehaviorStrategy reward who (some date.val))) who =
      (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        (Function.update mixed who (PMF.pure (some date))) who := by
  change quittingPureTimeDeviationPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) tail)
      who (some date.val) = _
  rw [quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt
    reward (quittingRetainedTailMixedTimingRootStack reward deadline mixed)
    tail (quittingAlwaysContinueProfile reward) who date.val (by simp)]
  have hhard :=
    quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile
      reward deadline mixed
  unfold quittingRetainedTailFiniteTimingHardGraft at hhard
  rw [hhard]
  rw [quittingRetainedTailFiniteTimingGame_update_pureDate_eq_hardMixedEU]
  unfold quittingPureTimeDeviationPayoff
  change quittingTerminalPayoff reward
      (Function.update
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
        (quittingPureTimeBehaviorStrategy reward who
          (quittingFiniteDeadlineTimingActionTime (some date)))) who = _
  exact quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
    reward deadline mixed who (some date)

/-- Passing through the whole finite word to the actual tail has exactly the
payoff of the normal-form timing action `Never`. -/
theorem quittingTerminalPayoff_retainedTailFiniteTimingPassProfile_eq_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingPassProfile reward
          (quittingRetainedTailMixedTimingRootStack reward deadline mixed)
          tail who) who =
      (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        (Function.update mixed who (PMF.pure none)) who := by
  have hpayoff :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU
      reward tail deadline (Function.update mixed who (PMF.pure none)) who
  unfold quittingRetainedTailMixedTimingProfile at hpayoff
  rw [quittingRetainedTailMixedTimingRootStack_update_pure_none] at hpayoff
  simpa [quittingRetainedTailFiniteTimingPassProfile,
    quittingRetainedTailFiniteTimingGraft] using hpayoff

/-- An actual Nash equilibrium of the retained-tail finite timing game
unconditionally supplies all finite-date and pass comparisons for its
literal root word. -/
theorem isQuittingRetainedTailFiniteTimingNash_of_mixedNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.IsNash
      mixed) :
    IsQuittingRetainedTailFiniteTimingNash reward
      (quittingRetainedTailMixedTimingRootStack reward deadline mixed) tail where
  finiteStop_le who time htime := by
    let date : Fin deadline := ⟨time, by simpa using htime⟩
    have hdeviation := hnash who (PMF.pure (some date))
    rw [← quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU
        reward tail deadline mixed who,
      ← quittingTerminalPayoff_retainedTailMixedTimingProfile_update_pureDate
        reward tail deadline mixed who date] at hdeviation
    exact hdeviation
  pass_le who := by
    have hdeviation := hnash who (PMF.pure none)
    rw [← quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU
        reward tail deadline mixed who,
      ← quittingTerminalPayoff_retainedTailFiniteTimingPassProfile_eq_mixedEU
        reward tail deadline mixed who] at hdeviation
    exact hdeviation

omit [DecidableEq ι] in
/-- Conditional on a supported current action, the retained pure payoff
averages to the current root payoff with the independently conditioned
retained tails as continuation. -/
theorem expect_conditional_quittingRetainedTailTimingPurePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (now : ι → Bool)
    (hnow : pmfPi (fun who =>
      pushforward (mixed who) timingActionCurrent) now ≠ 0)
    (who : ι) :
    Math.Probability.expect
        (pmfPi fun player =>
          condOn (mixed player) timingActionCurrent (now player))
        (fun choices => quittingRetainedTailTimingPurePayoff reward tail
          (deadline + 1) choices who) =
      quittingRootPayoff reward
        (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun other => timingLawTail (mixed other)) player)
        now who := by
  let conditional : PMF
      (ι → QuittingFiniteDeadlineTimingAction (deadline + 1)) :=
    pmfPi fun player =>
      condOn (mixed player) timingActionCurrent (now player)
  have hcurrent : ∀ {choices : ι →
      QuittingFiniteDeadlineTimingAction (deadline + 1)},
      choices ∈ conditional.support →
        (fun player => timingActionCurrent (choices player)) = now := by
    intro choices hchoices
    funext player
    have hnowPlayer :
        pushforward (mixed player) timingActionCurrent (now player) ≠ 0 :=
      pmfPi_coord_ne_zero_of_ne_zero
        (fun other => pushforward (mixed other) timingActionCurrent)
        now hnow player
    have hchoicePlayer :
        condOn (mixed player) timingActionCurrent (now player)
            (choices player) ≠ 0 :=
      pmfPi_coord_ne_zero_of_ne_zero
        (fun other => condOn (mixed other) timingActionCurrent (now other))
        choices (by simpa only [PMF.mem_support_iff] using hchoices) player
    exact condOn_support_project (mixed player) timingActionCurrent
      (now player) hnowPlayer
      (by simpa only [PMF.mem_support_iff] using hchoicePlayer)
  by_cases hquit : (quittingQuitters now).Nonempty
  · calc
      Math.Probability.expect conditional
          (fun choices => quittingRetainedTailTimingPurePayoff reward tail
            (deadline + 1) choices who) =
        Math.Probability.expect conditional
          (fun _ => reward ⟨quittingQuitters now, hquit⟩ who) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro choices hchoices
            rw [quittingRetainedTailTimingPurePayoff_succ,
              hcurrent hchoices]
            simp [quittingRootPayoff, hquit]
      _ = reward ⟨quittingQuitters now, hquit⟩ who :=
        Math.Probability.expect_const conditional _
      _ = quittingRootPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          now who := by simp [quittingRootPayoff, hquit]
  · have hnowAll : now = quittingAllContinueAction :=
      eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty now hquit
    have hmap : pushforward conditional timingChoicesTail =
        pmfPi (fun player => timingLawTail (mixed player)) := by
      unfold conditional timingChoicesTail timingLawTail
      rw [hnowAll, pmfPi_push_coordwise]
      rfl
    calc
      Math.Probability.expect conditional
          (fun choices => quittingRetainedTailTimingPurePayoff reward tail
            (deadline + 1) choices who) =
        Math.Probability.expect conditional
          (fun choices => quittingRetainedTailTimingPurePayoff reward tail
            deadline (timingChoicesTail choices) who) := by
              apply Math.ProbabilityMassFunction.expect_congr_on_support
              intro choices hchoices
              rw [quittingRetainedTailTimingPurePayoff_succ,
                hcurrent hchoices, hnowAll]
              simp [quittingRootPayoff]
      _ = Math.Probability.expect
          (pushforward conditional timingChoicesTail)
          (fun choices => quittingRetainedTailTimingPurePayoff reward tail
            deadline choices who) := by
              unfold pushforward
              exact (Math.Probability.expect_map timingChoicesTail conditional
                (fun choices => quittingRetainedTailTimingPurePayoff reward tail
                  deadline choices who)).symm
      _ = quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun player => timingLawTail (mixed player)) who := by
            rw [hmap]
            rfl
      _ = quittingRootPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          now who := by
            rw [hnowAll]
            simp [quittingRootPayoff]

/-- Bellman peeling for arbitrary independent retained-tail timing laws. -/
theorem quittingRetainedTailTimingMixedPayoff_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1) mixed who =
      quittingRootExpectedPayoff reward
        (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun other => timingLawTail (mixed other)) player)
        (fun player => pushforward (mixed player) timingActionCurrent) who := by
  unfold quittingRetainedTailTimingMixedPayoff
  rw [pmfPi_disintegrate_timingCurrent,
    Math.Probability.expect_bind]
  unfold quittingRootExpectedPayoff
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro now hnow
  exact expect_conditional_quittingRetainedTailTimingPurePayoff
    reward tail deadline mixed now
      (by simpa only [PMF.mem_support_iff] using hnow) who

/-- Replacing one conditional timing tail changes retained payoff by the
shorter retained-game gain times the common current Continue reach. -/
theorem quittingRetainedTailTimingMixedPayoff_withTail_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι)
    (replacement : PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hcontinue : pushforward (mixed who) timingActionCurrent false ≠ 0) :
    quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          (timingMixedWithTail mixed who replacement) who -
        quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          mixed who =
      quittingStationaryContinueMass
          (fun player => pushforward (mixed player) timingActionCurrent) *
        (quittingRetainedTailTimingMixedPayoff reward tail deadline
            (Function.update (fun player => timingLawTail (mixed player))
              who replacement) who -
          quittingRetainedTailTimingMixedPayoff reward tail deadline
            (fun player => timingLawTail (mixed player)) who) := by
  rw [quittingRetainedTailTimingMixedPayoff_bellman,
    quittingRetainedTailTimingMixedPayoff_bellman,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    timingMixedWithTail_current,
    timingMixedWithTail_tail mixed who replacement hcontinue]
  ring

/-- Positive current reach transfers ordinary Nash equilibrium to the
coordinatewise conditioned retained-tail game. -/
theorem retainedTimingLawTail_isNash_of_isNash_of_positiveContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnash : (quittingRetainedTailFiniteTimingGame reward
      (deadline + 1) tail).mixedExtension.IsNash mixed)
    (hcontinue : ∀ who,
      pushforward (mixed who) timingActionCurrent false ≠ 0) :
    (quittingRetainedTailFiniteTimingGame reward
      deadline tail).mixedExtension.IsNash
        (fun who => timingLawTail (mixed who)) := by
  intro who replacement
  have hnashSplice := hnash who
    (timingLawWithTail (mixed who) replacement)
  have htransport := quittingRetainedTailTimingMixedPayoff_withTail_sub
    reward tail deadline mixed who replacement (hcontinue who)
  rw [← quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff
      reward tail (deadline + 1) mixed who,
    ← quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff
      reward tail (deadline + 1)
        (timingMixedWithTail mixed who replacement) who] at htransport
  change (quittingRetainedTailFiniteTimingGame reward
      (deadline + 1) tail).mixedExtension.eu mixed who ≥
    (quittingRetainedTailFiniteTimingGame reward
      (deadline + 1) tail).mixedExtension.eu
        (timingMixedWithTail mixed who replacement) who at hnashSplice
  have hreach := timingCurrentRoot_continueMass_pos deadline mixed hcontinue
  rw [quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff,
    quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff]
  by_contra htailGain
  have htailPos : 0 <
      quittingRetainedTailTimingMixedPayoff reward tail deadline
          (Function.update (fun player => timingLawTail (mixed player))
            who replacement) who -
        quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun player => timingLawTail (mixed player)) who :=
    sub_pos.mpr (lt_of_not_ge htailGain)
  have hmulPos := mul_pos hreach htailPos
  have hwholeNonpos :
      (quittingRetainedTailFiniteTimingGame reward
          (deadline + 1) tail).mixedExtension.eu
            (timingMixedWithTail mixed who replacement) who -
        (quittingRetainedTailFiniteTimingGame reward
          (deadline + 1) tail).mixedExtension.eu mixed who ≤ 0 :=
    sub_nonpos.mpr hnashSplice
  have hmulNonpos :
      quittingStationaryContinueMass
          (fun player => pushforward (mixed player) timingActionCurrent) *
        (quittingRetainedTailTimingMixedPayoff reward tail deadline
            (Function.update (fun player => timingLawTail (mixed player))
              who replacement) who -
          quittingRetainedTailTimingMixedPayoff reward tail deadline
            (fun player => timingLawTail (mixed player)) who) ≤ 0 := by
    rw [← htransport]
    exact hwholeNonpos
  exact (not_lt_of_ge hmulNonpos) hmulPos

/-- Pure current stopping is the current root's Quit endpoint in the retained
Bellman decomposition. -/
theorem quittingRetainedTailTimingMixedPayoff_update_current_eq_quitPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
        (Function.update mixed who
          (PMF.pure (some (0 : Fin (deadline + 1))))) who =
      quittingRootQuitPayoff reward
        (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun other => timingLawTail (mixed other)) player)
        (fun player => pushforward (mixed player) timingActionCurrent) who := by
  rw [quittingRetainedTailTimingMixedPayoff_bellman]
  let root : ι → PMF Bool := fun player =>
    pushforward (mixed player) timingActionCurrent
  let updated := Function.update mixed who
    (PMF.pure (some (0 : Fin (deadline + 1))))
  have hroot :
      (fun player => pushforward (updated player) timingActionCurrent) =
        Function.update root who (PMF.pure true) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Function.update_self]
      unfold updated pushforward
      rw [Function.update_self, PMF.pure_map]
      rfl
    · unfold updated root
      rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  rw [hroot]
  unfold quittingRootQuitPayoff
  exact quittingRootQuitPayoff_tail_irrel reward _ _ root who

/-- Forcing current Continue while retaining the conditioned timing tail is
the current root's Continue endpoint. -/
theorem quittingRetainedTailTimingMixedPayoff_update_liftedTail_eq_continuePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift)) who =
      quittingRootContinuePayoff reward
        (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun other => timingLawTail (mixed other)) player)
        (fun player => pushforward (mixed player) timingActionCurrent) who := by
  rw [quittingRetainedTailTimingMixedPayoff_bellman]
  let root : ι → PMF Bool := fun player =>
    pushforward (mixed player) timingActionCurrent
  let tails : ι → PMF (QuittingFiniteDeadlineTimingAction deadline) :=
    fun player => timingLawTail (mixed player)
  have hroot :
      (fun player => pushforward
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift) player)
        timingActionCurrent) =
      Function.update root who (PMF.pure false) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Function.update_self, Function.update_self]
      exact map_liftedTail_current _
    · unfold root
      rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  have htail :
      (fun player => timingLawTail
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift) player)) =
      tails := by
    rw [timingLawTail_update, timingLawTail_map_lifted]
    exact Function.update_eq_self who tails
  rw [hroot, htail]
  rfl

/-- The current Boolean marginal of a retained-tail mixed timing Nash law is
an exact endpoint Nash root against the actual conditioned retained payoff. -/
theorem retainedTimingCurrentRoot_isZeroEndpointNash_of_isNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnash : (quittingRetainedTailFiniteTimingGame reward
      (deadline + 1) tail).mixedExtension.IsNash mixed) :
    IsεQuittingRootEndpointNash reward
      (fun player => quittingRetainedTailTimingMixedPayoff reward tail deadline
        (fun other => timingLawTail (mixed other)) player)
      0 (fun player => pushforward (mixed player) timingActionCurrent) := by
  rw [isεQuittingRootEndpointNash_iff_purePayoff_le]
  intro who
  constructor
  · have hquit := hnash who
      (PMF.pure (some (0 : Fin (deadline + 1))))
    rw [quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff,
      quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff] at hquit
    calc
      quittingRootQuitPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          (fun player => pushforward (mixed player) timingActionCurrent) who =
        quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          (Function.update mixed who
            (PMF.pure (some (0 : Fin (deadline + 1))))) who :=
        (quittingRetainedTailTimingMixedPayoff_update_current_eq_quitPayoff
          reward tail deadline mixed who).symm
      _ ≤ quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          mixed who := hquit
      _ = quittingRootSuccessorPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          (fun player => pushforward (mixed player) timingActionCurrent) who :=
        quittingRetainedTailTimingMixedPayoff_bellman
          reward tail deadline mixed who
      _ ≤ _ := by simp
  · have hcontinue := hnash who
      ((timingLawTail (mixed who)).map timingActionLift)
    rw [quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff,
      quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff] at hcontinue
    calc
      quittingRootContinuePayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          (fun player => pushforward (mixed player) timingActionCurrent) who =
        quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          (Function.update mixed who
            ((timingLawTail (mixed who)).map timingActionLift)) who :=
        (quittingRetainedTailTimingMixedPayoff_update_liftedTail_eq_continuePayoff
          reward tail deadline mixed who).symm
      _ ≤ quittingRetainedTailTimingMixedPayoff reward tail (deadline + 1)
          mixed who := hcontinue
      _ = quittingRootSuccessorPayoff reward
          (fun player => quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other => timingLawTail (mixed other)) player)
          (fun player => pushforward (mixed player) timingActionCurrent) who :=
        quittingRetainedTailTimingMixedPayoff_bellman
          reward tail deadline mixed who
      _ ≤ _ := by simp

/-! ## Positive Never mass and exact reconstruction -/

/-- Positive mass on `Never` forces positive current Continue mass. -/
theorem timingActionCurrent_false_ne_zero_of_none_toReal_pos
    {deadline : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnever : 0 < (law none).toReal) :
    pushforward law timingActionCurrent false ≠ 0 := by
  intro hzero
  have hle : law none ≤
      pushforward law timingActionCurrent false := by
    simpa [timingActionCurrent] using
      (le_pushforward_apply law timingActionCurrent
        (none : QuittingFiniteDeadlineTimingAction (deadline + 1)))
  rw [hzero] at hle
  have hlaw : law none = 0 := le_antisymm hle bot_le
  rw [hlaw] at hnever
  simp at hnever

/-- Positive `Never` mass remains positive in the conditioned shifted tail. -/
theorem timingLawTail_none_toReal_pos_of_none_toReal_pos
    {deadline : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnever : 0 < (law none).toReal) :
    0 < (timingLawTail law none).toReal := by
  have hcontinue :=
    timingActionCurrent_false_ne_zero_of_none_toReal_pos law hnever
  have hlaw : law none ≠ 0 := by
    intro hzero
    rw [hzero] at hnever
    simp at hnever
  have hconditional : none ∈
      (condOn law timingActionCurrent false).support := by
    rw [PMF.mem_support_iff,
      condOn_apply law timingActionCurrent false none hcontinue]
    simp only [timingActionCurrent, ↓reduceIte]
    exact ENNReal.div_ne_zero.mpr ⟨hlaw,
      PMF.apply_ne_top (pushforward law timingActionCurrent) false⟩
  have hmapped : none ∈
      ((timingLawTail law).map timingActionLift).support := by
    rw [timingLawTail_map_lift law hcontinue]
    exact hconditional
  rcases (PMF.mem_support_map_iff timingActionLift
      (timingLawTail law) none).mp hmapped with
    ⟨action, haction, hlift⟩
  have hactionNone : action = none := by
    cases action with
    | none => rfl
    | some time => simp [timingActionLift] at hlift
  subst action
  exact ENNReal.toReal_pos
    ((PMF.mem_support_iff (timingLawTail law) none).mp haction)
    (PMF.apply_ne_top (timingLawTail law) none)

/-- The pure `Never` timing law has pure `Never` as its conditioned tail. -/
@[simp] theorem retainedTimingLawTail_pure_none {deadline : ℕ} :
    timingLawTail
        (PMF.pure none :
          PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) =
      (PMF.pure none :
        PMF (QuittingFiniteDeadlineTimingAction deadline)) := by
  let law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)) :=
    PMF.pure none
  have hcontinue : pushforward law timingActionCurrent false ≠ 0 := by
    unfold law pushforward
    rw [PMF.pure_map]
    simp [timingActionCurrent]
  have hcond : condOn law timingActionCurrent false = law := by
    apply PMF.ext
    intro action
    rw [condOn_apply law timingActionCurrent false action hcontinue]
    cases action with
    | none =>
        unfold pushforward law
        rw [PMF.pure_map]
        simp [timingActionCurrent]
    | some time => simp [law]
  have hlift := timingLawTail_map_lift law hcontinue
  rw [hcond] at hlift
  have hmapped := congrArg (fun source => source.map timingActionTail) hlift
  have hcomp :
      (timingActionTail (dates := deadline)) ∘
          (timingActionLift (dates := deadline)) =
        (id : QuittingFiniteDeadlineTimingAction deadline →
          QuittingFiniteDeadlineTimingAction deadline) := by
    funext action
    exact timingActionTail_lift action
  rw [PMF.map_comp, hcomp, PMF.map_id] at hmapped
  dsimp only [law] at hmapped
  simpa only [PMF.pure_map, timingActionTail] using hmapped

/-- Every retained timing deadline evaluates pure `Never` laws as the
prescribed actual tail payoff. -/
theorem quittingRetainedTailTimingMixedPayoff_pureNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile) :
    ∀ (deadline : ℕ) (who : ι),
      quittingRetainedTailTimingMixedPayoff reward tail deadline
          (fun _ => PMF.pure none) who =
        quittingTerminalPayoff reward tail who := by
  intro deadline
  induction deadline with
  | zero =>
      intro who
      exact quittingRetainedTailTimingMixedPayoff_zero
        reward tail (fun _ => PMF.pure none) who
  | succ deadline ih =>
      intro who
      rw [quittingRetainedTailTimingMixedPayoff_bellman]
      have hroot :
          (fun player : ι => pushforward
            (PMF.pure (none : QuittingFiniteDeadlineTimingAction
              (deadline + 1))) timingActionCurrent) =
            quittingAllContinueRoot := by
        funext player
        unfold pushforward quittingAllContinueRoot
        rw [PMF.pure_map]
        rfl
      have htail :
          (fun player : ι => timingLawTail
            (PMF.pure (none : QuittingFiniteDeadlineTimingAction
              (deadline + 1)))) =
            fun _ => (PMF.pure none :
              PMF (QuittingFiniteDeadlineTimingAction deadline)) := by
        funext player
        exact retainedTimingLawTail_pure_none
      rw [hroot, htail]
      have hpayoff :
          (fun player : ι =>
            quittingRetainedTailTimingMixedPayoff reward tail deadline
              (fun _ => PMF.pure none) player) =
            fun player => quittingTerminalPayoff reward tail player := by
        funext player
        exact ih player
      rw [hpayoff]
      unfold quittingRootExpectedPayoff quittingAllContinueRoot
      rw [pmfPi_pure]
      simp [quittingRootPayoff]

/-! ## The actual mixed-Nash compiler -/

omit [DecidableEq ι] in
/-- Under genuine playerwise current continuation, the mixed timing root
word splits into its current Boolean root and the conditional shifted word. -/
theorem quittingRetainedTailMixedTimingRootStack_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hcontinue : ∀ who,
      pushforward (mixed who) timingActionCurrent false ≠ 0) :
    quittingRetainedTailMixedTimingRootStack reward (deadline + 1) mixed =
      (fun who ↦ pushforward (mixed who) timingActionCurrent) ::
        quittingRetainedTailMixedTimingRootStack reward deadline
          (fun who ↦ timingLawTail (mixed who)) := by
  unfold quittingRetainedTailMixedTimingRootStack
  rw [List.ofFn_succ]
  congr 1
  · change quittingProfileRoot reward
        (quittingFiniteDeadlineTimingProfile reward (deadline + 1) mixed) = _
    exact finiteDeadlineTimingProfile_root_eq_current reward deadline mixed
  · apply congrArg List.ofFn
    funext date
    have hspine := finiteDeadlineTimingProfile_spine_one_eq_tail
      reward deadline mixed hcontinue
    exact congrArg
      (fun profile ↦ quittingProfileLiveRoot reward profile date.val) hspine

/-- Positive `Never` mass is needed only for credibility of every displayed
conditional suffix.  Under it, an actual retained-tail mixed Nash law
constructs a literal exact endpoint-Nash root stack. -/
theorem isQuittingLiteralExactRootStack_of_retainedTailMixedNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile) :
    ∀ (deadline : ℕ)
      (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)),
      (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.IsNash
          mixed →
      (∀ who, 0 < (mixed who none).toReal) →
      IsQuittingLiteralExactRootStack reward
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) tail := by
  intro deadline
  induction deadline with
  | zero =>
      intro mixed hnash hnever
      have hnil :
          quittingRetainedTailMixedTimingRootStack reward 0 mixed = [] :=
        List.eq_nil_of_length_eq_zero (by simp)
      rw [hnil]
      exact isQuittingLiteralExactRootStack_nil reward tail
  | succ deadline ih =>
      intro mixed hnash hnever
      have hcontinue : ∀ who,
          pushforward (mixed who) timingActionCurrent false ≠ 0 :=
        fun who ↦ timingActionCurrent_false_ne_zero_of_none_toReal_pos
          (mixed who) (hnever who)
      have htailNash :
          (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.IsNash
            (fun who ↦ timingLawTail (mixed who)) :=
        retainedTimingLawTail_isNash_of_isNash_of_positiveContinue
          reward tail deadline mixed hnash hcontinue
      have htailNever : ∀ who,
          0 < (timingLawTail (mixed who) none).toReal :=
        fun who ↦ timingLawTail_none_toReal_pos_of_none_toReal_pos
          (mixed who) (hnever who)
      have htailStack := ih (fun who ↦ timingLawTail (mixed who))
        htailNash htailNever
      have hcurrent := retainedTimingCurrentRoot_isZeroEndpointNash_of_isNash
        reward tail deadline mixed hnash
      have hcontinuation :
          (fun player ↦ quittingRetainedTailTimingMixedPayoff reward tail
            deadline (fun other ↦ timingLawTail (mixed other)) player) =
        fun player ↦ quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward deadline
            (fun other ↦ timingLawTail (mixed other)) tail) player := by
        funext player
        rw [quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU,
          quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff]
      rw [hcontinuation] at hcurrent
      rw [quittingRetainedTailMixedTimingRootStack_succ
        reward deadline mixed hcontinue,
        isQuittingLiteralExactRootStack_cons_iff]
      exact ⟨hcurrent, htailStack⟩

/-- If every exact endpoint-Nash current root against the prescribed tail is
all-Continue, then an actual retained-tail timing Nash law with positive
`Never` mass in every marginal is literally the pure-`Never` law. -/
theorem retainedTailFiniteTimingNash_eq_pureNever_of_root_rigidity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (hrootRigidity : ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward
          (fun who => quittingTerminalPayoff reward tail who) 0 root →
        root = quittingAllContinueRoot) :
    ∀ (deadline : ℕ)
      (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)),
      (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.IsNash
          mixed →
      (∀ who, 0 < (mixed who none).toReal) →
      ∀ who, mixed who = PMF.pure none := by
  intro deadline
  induction deadline with
  | zero =>
      intro mixed hnash hnever who
      exact Math.ProbabilityMassFunction.eq_pure_of_subsingleton
        (mixed who) none
  | succ deadline ih =>
      intro mixed hnash hnever
      have hcontinue : ∀ who,
          pushforward (mixed who) timingActionCurrent false ≠ 0 :=
        fun who =>
          timingActionCurrent_false_ne_zero_of_none_toReal_pos
            (mixed who) (hnever who)
      have htailNash :
          (quittingRetainedTailFiniteTimingGame reward
            deadline tail).mixedExtension.IsNash
              (fun who => timingLawTail (mixed who)) :=
        retainedTimingLawTail_isNash_of_isNash_of_positiveContinue
          reward tail deadline mixed hnash hcontinue
      have htailNever : ∀ who,
          0 < (timingLawTail (mixed who) none).toReal :=
        fun who =>
          timingLawTail_none_toReal_pos_of_none_toReal_pos
            (mixed who) (hnever who)
      have htailPure : ∀ who,
          timingLawTail (mixed who) = PMF.pure none :=
        ih (fun who => timingLawTail (mixed who)) htailNash htailNever
      have htails :
          (fun who => timingLawTail (mixed who)) =
            fun _ => (PMF.pure none :
              PMF (QuittingFiniteDeadlineTimingAction deadline)) := by
        funext who
        exact htailPure who
      have hendpoint :=
        retainedTimingCurrentRoot_isZeroEndpointNash_of_isNash
          reward tail deadline mixed hnash
      have hcontinuation :
          (fun player =>
            quittingRetainedTailTimingMixedPayoff reward tail deadline
              (fun other => timingLawTail (mixed other)) player) =
            fun player => quittingTerminalPayoff reward tail player := by
        rw [htails]
        funext player
        exact quittingRetainedTailTimingMixedPayoff_pureNever
          reward tail deadline player
      rw [hcontinuation] at hendpoint
      have hroot := hrootRigidity
        (fun player => pushforward (mixed player) timingActionCurrent)
        hendpoint
      intro who
      apply timingLaw_eq_of_current_tail_eq
          (mixed who)
          (PMF.pure none :
            PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
      · have hcoordinate := congrFun hroot who
        rw [hcoordinate]
        unfold quittingAllContinueRoot pushforward
        rw [PMF.pure_map]
        rfl
      · rw [htailPure who, retainedTimingLawTail_pure_none]
      · exact hcontinue who
      · unfold pushforward
        rw [PMF.pure_map]
        simp [timingActionCurrent]

end GameTheory
