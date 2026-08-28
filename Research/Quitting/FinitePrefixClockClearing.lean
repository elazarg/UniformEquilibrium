/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.PositiveStageAtomConcentratedPacket
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingNash
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap
import UniformEquilibrium.Quitting.Root.SelfTailClosure

/-!
# Finite literal-prefix clock clearing

This file owns the source-independent finite-word layer of clock clearing.
Clearing a set of player coordinates means forcing exactly those coordinates
to Continue at every root in one displayed word.  The definitions retain the
word, its terminal continuation, and every intermediate unilateral profile.

The packet constructor at the end repeats one actual marked profile.  It is a
generic concentrated-packet constructor; it does not assert minimum-fibre
membership, a return, recurrence of an incoming chronology, or a downstream
consumer.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Force every player in `cleared` to Continue throughout one finite root
word, leaving every other literal marginal untouched. -/
def quittingLiteralRootStackClear
    (roots : List (ι → PMF Bool)) (cleared : Finset ι) :
    List (ι → PMF Bool) :=
  roots.map fun root who =>
    if who ∈ cleared then PMF.pure false else root who

omit [Fintype ι] in
@[simp] theorem quittingLiteralRootStackClear_nil (cleared : Finset ι) :
    quittingLiteralRootStackClear ([] : List (ι → PMF Bool)) cleared = [] := rfl

omit [Fintype ι] in
@[simp] theorem quittingLiteralRootStackClear_cons
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (cleared : Finset ι) :
    quittingLiteralRootStackClear (root :: roots) cleared =
      (fun who => if who ∈ cleared then PMF.pure false else root who) ::
      quittingLiteralRootStackClear roots cleared := rfl

omit [Fintype ι] in
@[simp] theorem quittingLiteralRootStackClear_empty
    (roots : List (ι → PMF Bool)) :
    quittingLiteralRootStackClear roots ∅ = roots := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      simp [quittingLiteralRootStackClear]

omit [Fintype ι] in
/-- Clearing one additional player is exactly the existing Continue-through
operation on the already cleared word. -/
theorem quittingLiteralRootStackClear_insert
    (roots : List (ι → PMF Bool)) (cleared : Finset ι) (who : ι) :
    quittingLiteralRootStackClear roots (insert who cleared) =
      quittingLiteralRootStackForceContinue
        (quittingLiteralRootStackClear roots cleared) who := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      simp only [quittingLiteralRootStackClear_cons,
        quittingLiteralRootStackForceContinue, List.map_cons]
      rw [ih]
      congr 1
      funext player
      by_cases hplayer : player = who
      · subst player
        simp
      · by_cases hmem : player ∈ cleared <;> simp [hplayer, hmem]

omit [Fintype ι] in
/-- Re-clearing a player already in the cleared set changes no root. -/
theorem quittingLiteralRootStackClear_insert_eq_of_mem
    (roots : List (ι → PMF Bool)) (cleared : Finset ι) (who : ι)
    (hwho : who ∈ cleared) :
    quittingLiteralRootStackClear roots (insert who cleared) =
      quittingLiteralRootStackClear roots cleared := by
  rw [Finset.insert_eq_of_mem hwho]

/-- The cleared descendant of a fixed terminal continuation. -/
def quittingFinitePrefixClearedProfile
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (cleared : Finset ι) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (quittingLiteralRootStackClear roots cleared) terminal

/-- Clearing one new coordinate is one ordinary unilateral behavioral update
of the current descendant, with the original terminal strategy restored after
the word. -/
theorem quittingFinitePrefixClearedProfile_insert_eq_update
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (cleared : Finset ι) (who : ι) :
    quittingFinitePrefixClearedProfile (reward := reward) roots terminal
        (insert who cleared) =
      Function.update
        (quittingFinitePrefixClearedProfile (reward := reward) roots terminal
          cleared)
        who
        (quittingLiteralRootStackContinueDeviation reward
          (quittingLiteralRootStackClear roots cleared) (terminal who)) := by
  rw [quittingFinitePrefixClearedProfile,
    quittingFinitePrefixClearedProfile,
    quittingLiteralRootStackClear_insert]
  symm
  simpa only [Function.update_eq_self] using
    update_quittingLiteralRootStackProfile_continueDeviation
      reward (quittingLiteralRootStackClear roots cleared) terminal who
        (terminal who)

/-- A coordinate already cleared has a literally identical successor
profile. -/
theorem quittingFinitePrefixClearedProfile_insert_eq_of_mem
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (cleared : Finset ι) (who : ι) (hwho : who ∈ cleared) :
    quittingFinitePrefixClearedProfile (reward := reward) roots terminal
        (insert who cleared) =
      quittingFinitePrefixClearedProfile (reward := reward) roots terminal
        cleared := by
  rw [quittingFinitePrefixClearedProfile,
    quittingLiteralRootStackClear_insert_eq_of_mem roots cleared who hwho]
  rfl

/-- Clearing every player turns the displayed finite word into a literal
all-Continue word. -/
theorem quittingLiteralRootStackClear_univ
    (roots : List (ι → PMF Bool)) :
    quittingLiteralRootStackClear roots Finset.univ =
      roots.map fun _root _who => PMF.pure false := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      simp only [quittingLiteralRootStackClear_cons, Finset.mem_univ, if_true,
        List.map_cons, ih]

/-- Two unilateral hazards which agree through a sure-Quit date have the same
terminal value.  Their values after that date are immaterial. -/
theorem quittingRootSequenceHazardTerminalValue_eq_of_eq_le_of_pure_true
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (first second : ℕ → PMF Bool) (start fuel : ℕ)
    (hagree : ∀ offset, offset ≤ fuel →
      first (start + offset) = second (start + offset))
    (hquit : first (start + fuel) = PMF.pure true) :
    quittingRootSequenceHazardTerminalValue reward roots who first start =
      quittingRootSequenceHazardTerminalValue reward roots who second start := by
  induction fuel generalizing start with
  | zero =>
      have hzero := hagree 0 (by omega)
      simp only [Nat.add_zero] at hzero hquit
      calc
        quittingRootSequenceHazardTerminalValue reward roots who first start =
            (first start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (first start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingRootSequenceHazardTerminalValue reward roots who
                      first (start + 1)) :=
          quittingRootSequenceHazardTerminalValue_eq_hazardBellman
            reward roots who first start
        _ = quittingFixedOpponentsQuitValue reward roots who start := by
          rw [hquit]
          simp
        _ = quittingRootSequenceHazardTerminalValue reward roots who second
              start := by
          rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
            ← hzero, hquit]
          simp
  | succ fuel ih =>
      have hzero := hagree 0 (by omega)
      simp only [Nat.add_zero] at hzero
      have htail : ∀ offset, offset ≤ fuel →
          first (start + 1 + offset) = second (start + 1 + offset) := by
        intro offset hoffset
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hagree (offset + 1) (Nat.succ_le_succ hoffset)
      have htailQuit : first (start + 1 + fuel) = PMF.pure true := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hquit
      have hinduction := ih (start + 1) htail htailQuit
      calc
        quittingRootSequenceHazardTerminalValue reward roots who first start =
            (first start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (first start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingRootSequenceHazardTerminalValue reward roots who
                      first (start + 1)) :=
          quittingRootSequenceHazardTerminalValue_eq_hazardBellman
            reward roots who first start
        _ = (second start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start +
              (second start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingRootSequenceHazardTerminalValue reward roots who
                      second (start + 1)) := by rw [hzero, hinduction]
        _ = quittingRootSequenceHazardTerminalValue reward roots who second
              start :=
          (quittingRootSequenceHazardTerminalValue_eq_hazardBellman
            reward roots who second start).symm

/-- An early deterministic stop in a finite word has the payoff of the
literal one-date Quit profile built on the player's Continue-through sibling.
The latter resumes the supplied behavioral tail literally after the marked
date. -/
theorem quittingPureTimeDeviationPayoff_eq_literalOneDate_continuePrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) (htime : time < roots.length) :
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who
          (some time) =
      quittingTerminalPayoff reward
        (quittingLiteralOneDateProfile reward
          (quittingRetainedTailFiniteTimingPassProfile reward roots tail who)
          who time true) who := by
  let current := quittingRetainedTailFiniteTimingGraft reward roots tail
  let pass := quittingRetainedTailFiniteTimingPassProfile reward roots tail who
  have hpass : pass = Function.update current who
      (quittingLiteralRootStackContinueDeviation reward roots (tail who)) := by
    dsimp only [pass, current, quittingRetainedTailFiniteTimingGraft,
      quittingRetainedTailFiniteTimingPassProfile]
    symm
    simpa only [Function.update_eq_self] using
      update_quittingLiteralRootStackProfile_continueDeviation
        reward roots tail who (tail who)
  have hopponents : ∀ stage player, player ≠ who →
      quittingProfileLiveRoot reward current stage player =
        quittingProfileLiveRoot reward pass stage player := by
    intro stage player hplayer
    rw [hpass]
    unfold quittingProfileLiveRoot
    simp only [Function.update_of_ne hplayer]
  have hpassContinue : ∀ stage, stage < roots.length →
      quittingProfileLiveRoot reward pass stage who = PMF.pure false := by
    intro stage hstage
    dsimp only [pass, quittingRetainedTailFiniteTimingPassProfile]
    rw [congrFun
      (quittingProfileLiveRoot_literalRootStackProfile_eq_getElem reward
        (quittingLiteralRootStackForceContinue roots who) tail stage
          (by simpa [quittingLiteralRootStackForceContinue] using hstage)) who]
    simp [quittingLiteralRootStackForceContinue]
  unfold quittingPureTimeDeviationPayoff
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTerminalPayoff_literalOneDateProfile_eq_canonical,
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation]
  change quittingRootSequenceHazardTerminalValue reward
      (quittingProfileLiveRoot reward current) who
        (quittingPureTimeHazard (some time)) 0 = _
  rw [quittingRootSequenceHazardTerminalValue_congr_of_opponents
    reward who hopponents (quittingPureTimeHazard (some time)) 0]
  refine quittingRootSequenceHazardTerminalValue_eq_of_eq_le_of_pure_true
    reward (quittingProfileLiveRoot reward pass) who _ _ 0 time ?_ ?_
  · intro offset hoffset
    simp only [Nat.zero_add]
    by_cases heq : offset = time
    · subst offset
      simp
    · have hoffsetLt : offset < time := by omega
      rw [quittingPureTimeHazard_some_of_ne heq,
        quittingStageDeviationHazard_of_lt _ _ _ _ hoffsetLt,
        hpassContinue offset (hoffsetLt.trans htime)]
  · simp

/-- A literal one-date override preserves the entire behavioral spine after
that date, not only the live-root semantic projection. -/
theorem quittingAllContinueProfileSpine_literalOneDateProfile_succ_eq
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingAllContinueProfileSpine reward
        (quittingLiteralOneDateProfile reward profile who stage action)
        (stage + 1) =
      quittingAllContinueProfileSpine reward profile (stage + 1) := by
  apply quittingAllContinueProfileSpine_eq_of_eq_from reward
  intro player time history htime
  unfold quittingLiteralOneDateProfile
  by_cases hplayer : player = who
  · subst player
    simp only [Function.update_self]
    exact congrFun
      (quittingLiteralOneDateOverride_of_ne (profile who) stage time action
        (by omega)) history
  · simp [Function.update_of_ne hplayer]

/-- One genuinely paid Continue-through clearing of a finite word. -/
structure QuittingFinitePrefixPaidClear
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (gap : ℝ) where
  who : ι
  gain : gap / 2 ≤
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingPassProfile reward roots tail who) who -
      quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who

/-- A profitable literal premark atom before the end of a finite word.  Its
target resumes the Continue-through sibling literally off the marked date. -/
structure QuittingFinitePrefixPremarkAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (gap : ℝ) where
  who : ι
  time : ℕ
  time_lt : time < roots.length
  gain : gap / 4 <
    quittingTerminalPayoff reward
        (quittingLiteralOneDateProfile reward
          (quittingRetainedTailFiniteTimingPassProfile reward roots tail who)
          who time true) who -
      quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingPassProfile reward roots tail who) who

namespace QuittingFinitePrefixPremarkAtom

variable {roots : List (ι → PMF Bool)}
  {tail : (quittingGame reward).BehaviorProfile} {gap R : ℝ}

/-- The Continue-through comparison is literally pure Continue at the
selected premark coordinate and date. -/
theorem passProfile_liveRoot_self_eq_pureContinue
    (atom : QuittingFinitePrefixPremarkAtom reward roots tail gap) :
    quittingProfileLiveRoot reward
        (quittingRetainedTailFiniteTimingPassProfile reward roots tail atom.who)
        atom.time atom.who = PMF.pure false := by
  unfold quittingRetainedTailFiniteTimingPassProfile
  rw [congrFun
    (quittingProfileLiveRoot_literalRootStackProfile_eq_getElem reward
      (quittingLiteralRootStackForceContinue roots atom.who) tail atom.time
        (by simpa [quittingLiteralRootStackForceContinue] using atom.time_lt))
    atom.who]
  simp [quittingLiteralRootStackForceContinue]

/-- The strict premark gain and a common reward bound force live mass strictly
above `gap / (8 R)` at the marked date. -/
theorem gap_div_eight_mul_lt_liveMass
    (atom : QuittingFinitePrefixPremarkAtom reward roots tail gap)
    (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    gap / (8 * R) <
      quittingLiveMass reward
        (quittingRetainedTailFiniteTimingPassProfile reward roots tail atom.who)
        atom.time := by
  let pass := quittingRetainedTailFiniteTimingPassProfile reward roots tail atom.who
  let semanticTail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward pass (atom.time + 1))
  let root := quittingProfileLiveRoot reward pass atom.time
  let targetRoot := Function.update root atom.who (PMF.pure true)
  have htail : ∀ player, |semanticTail.1 player| ≤ R := by
    intro player
    exact abs_quittingTerminalPayoff_le reward
      (quittingAllContinueProfileSpine reward pass (atom.time + 1)) player
        hreward
  have htarget :
      |quittingRootSuccessorPayoff reward semanticTail.1 targetRoot atom.who| ≤ R := by
    exact abs_quittingRootExpectedPayoff_le_bound reward semanticTail.1
      targetRoot atom.who hreward htail
  have hsource :
      |quittingRootSuccessorPayoff reward semanticTail.1 root atom.who| ≤ R := by
    exact abs_quittingRootExpectedPayoff_le_bound reward semanticTail.1
      root atom.who hreward htail
  have hdefect : quittingRootSuccessorPayoff reward semanticTail.1
        targetRoot atom.who -
      quittingRootSuccessorPayoff reward semanticTail.1 root atom.who ≤ 2 * R := by
    linarith [le_of_abs_le htarget, neg_le_of_abs_le hsource]
  have hgain := atom.gain
  rw [quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect]
    at hgain
  change gap / 4 < quittingLiveMass reward pass atom.time *
    (quittingRootSuccessorPayoff reward semanticTail.1 targetRoot atom.who -
      quittingRootSuccessorPayoff reward semanticTail.1 root atom.who) at hgain
  have hlive := quittingLiveMass_nonneg reward pass atom.time
  have hupper := mul_le_mul_of_nonneg_left hdefect hlive
  by_contra hnot
  have hliveSmall : quittingLiveMass reward pass atom.time ≤ gap / (8 * R) :=
    le_of_not_gt hnot
  have hscaled : quittingLiveMass reward pass atom.time * (2 * R) ≤ gap / 4 := by
    apply (le_div_iff₀ (show 0 < (4 : ℝ) by norm_num)).2
    have hdenom : 0 < 8 * R := mul_pos (by norm_num) hR
    have := (le_div_iff₀ hdenom).1 hliveSmall
    nlinarith
  linarith

end QuittingFinitePrefixPremarkAtom

/-- A deterministic stopping time which is Never or lies beyond the finite
word differs from the Continue-through sibling by at most player-deleted
return times the reward diameter. -/
theorem quittingPureTimeDeviationPayoff_sub_pass_le_of_not_early
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) (R : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hlate : ∀ time, choice = some time → roots.length ≤ time) :
    quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who choice -
        quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingPassProfile reward roots tail who) who ≤
      2 * R * quittingLiteralRootStackOpponentSurvival roots who := by
  cases choice with
  | none =>
      have hexact := quittingPureTimeDeviationPayoff_absolute_sub_pass_eq
        reward roots tail who none
      have hpure := abs_quittingTerminalPayoff_le reward
        (Function.update tail who
          (quittingPureTimeBehaviorStrategy reward who none)) who hreward
      have htail := abs_quittingTerminalPayoff_le reward tail who hreward
      have hdiff : quittingPureTimeDeviationPayoff reward tail who none -
          quittingTerminalPayoff reward tail who ≤ 2 * R := by
        unfold quittingPureTimeDeviationPayoff
        linarith [le_of_abs_le hpure, neg_le_of_abs_le htail]
      have hscaled := mul_le_mul_of_nonneg_left hdiff
        (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
      simp only [quittingAbsolutePureTime] at hexact
      calc
        quittingPureTimeDeviationPayoff reward
              (quittingRetainedTailFiniteTimingGraft reward roots tail) who none -
            quittingTerminalPayoff reward
              (quittingRetainedTailFiniteTimingPassProfile reward roots tail who)
              who = _ := hexact
        _ ≤ quittingLiteralRootStackOpponentSurvival roots who * (2 * R) :=
          hscaled
        _ = 2 * R * quittingLiteralRootStackOpponentSurvival roots who := by ring
  | some time =>
      have htime : roots.length ≤ time := hlate time rfl
      let delay := time - roots.length
      have habsolute : quittingAbsolutePureTime roots.length (some delay) =
          some time := by
        simp only [quittingAbsolutePureTime]
        congr 1
        omega
      have hexact := quittingPureTimeDeviationPayoff_absolute_sub_pass_eq
        reward roots tail who (some delay)
      rw [habsolute] at hexact
      have hpure := abs_quittingTerminalPayoff_le reward
        (Function.update tail who
          (quittingPureTimeBehaviorStrategy reward who (some delay))) who hreward
      have htail := abs_quittingTerminalPayoff_le reward tail who hreward
      have hdiff : quittingPureTimeDeviationPayoff reward tail who (some delay) -
          quittingTerminalPayoff reward tail who ≤ 2 * R := by
        unfold quittingPureTimeDeviationPayoff
        linarith [le_of_abs_le hpure, neg_le_of_abs_le htail]
      have hscaled := mul_le_mul_of_nonneg_left hdiff
        (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
      calc
        quittingPureTimeDeviationPayoff reward
              (quittingRetainedTailFiniteTimingGraft reward roots tail) who
                (some time) -
            quittingTerminalPayoff reward
              (quittingRetainedTailFiniteTimingPassProfile reward roots tail who)
              who = _ := hexact
        _ ≤ quittingLiteralRootStackOpponentSurvival roots who * (2 * R) :=
          hscaled
        _ = 2 * R * quittingLiteralRootStackOpponentSurvival roots who := by ring

/-- Low player-deleted survival forces either a paid Continue-through clear or
a profitable literal atom strictly before the end of the finite word. -/
theorem quittingFinitePrefix_paidClear_or_premarkAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (gap R : ℝ) (hgap : 0 < gap) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hlow : ∀ who,
      quittingLiteralRootStackOpponentSurvival roots who < gap / (16 * R)) :
    Nonempty (QuittingFinitePrefixPaidClear reward roots tail gap) ∨
      Nonempty (QuittingFinitePrefixPremarkAtom reward roots tail gap) := by
  let current := quittingRetainedTailFiniteTimingGraft reward roots tail
  obtain ⟨who, deviation, hdeviation⟩ := hexploit current
  obtain ⟨choice, hpure⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward current who deviation (show 0 < gap / 4 by positivity)
  let purePayoff := quittingPureTimeDeviationPayoff reward current who choice
  let pass := quittingRetainedTailFiniteTimingPassProfile reward roots tail who
  have hpureGain : 3 * gap / 4 ≤
      purePayoff - quittingTerminalPayoff reward current who := by
    dsimp only [purePayoff, quittingPureTimeDeviationPayoff]
    linarith
  by_cases hclear : gap / 2 ≤
      quittingTerminalPayoff reward pass who -
        quittingTerminalPayoff reward current who
  · left
    exact ⟨{
      who := who
      gain := by simpa [pass, current] using hclear
    }⟩
  · right
    have hpurePass : gap / 4 <
        purePayoff - quittingTerminalPayoff reward pass who := by
      linarith
    have hlateImpossible : ¬(∀ time, choice = some time → roots.length ≤ time) := by
      intro hlate
      have hupper := quittingPureTimeDeviationPayoff_sub_pass_le_of_not_early
        reward roots tail who choice R hreward hlate
      have hsurvival := hlow who
      have hdenom : 0 < 16 * R := mul_pos (by norm_num) hR
      have hscaled : 16 * R *
          quittingLiteralRootStackOpponentSurvival roots who < gap := by
        simpa [mul_comm] using (lt_div_iff₀ hdenom).mp hsurvival
      have hsmall : 2 * R *
          quittingLiteralRootStackOpponentSurvival roots who < gap / 8 := by
        nlinarith
      dsimp only [purePayoff, current, pass] at hpurePass
      linarith
    cases choice with
    | none => exact (hlateImpossible (by intro time h; cases h)).elim
    | some time =>
        have htime : time < roots.length := by
          by_contra hnot
          exact hlateImpossible (by
            intro selected hselected
            simp only [Option.some.injEq] at hselected
            subst selected
            omega)
        refine ⟨{
          who := who
          time := time
          time_lt := htime
          gain := ?_
        }⟩
        rw [← quittingPureTimeDeviationPayoff_eq_literalOneDate_continuePrefix
          reward roots tail who time htime]
        simpa [purePayoff, current, pass] using hpurePass

/-- A common absolute reward bound controls every terminal exploitability
margin by the reward diameter. -/
theorem terminalExploitabilityGap_le_two_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap R : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    gap ≤ 2 * R := by
  obtain ⟨who, deviation, hgain⟩ :=
    hexploit (quittingAlwaysContinueProfile reward)
  have hsource := abs_quittingTerminalPayoff_le reward
    (quittingAlwaysContinueProfile reward) who hreward
  have htarget := abs_quittingTerminalPayoff_le reward
    (Function.update (quittingAlwaysContinueProfile reward) who deviation)
      who hreward
  linarith [neg_le_of_abs_le hsource, le_of_abs_le htarget]

/-- Generic data for repeating one actual marked profile as a concentrated
packet without changing its marked root. -/
structure QuittingConstantConcentratedPacketSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  profile : (quittingGame reward).BehaviorProfile
  owner : ι
  terminal : {S : Finset ι // S.Nonempty}
  stage : ℕ
  resolution : ℝ
  resolution_pos : 0 < resolution
  resolution_le_stageMass : resolution ≤
    quittingStageCoalitionMass reward profile stage terminal
  ownerDefect_eq_zero :
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))).1
      (quittingProfileLiveRoot reward profile stage) owner = 0

namespace QuittingConstantConcentratedPacketSource

variable (source : QuittingConstantConcentratedPacketSource reward)

def profiles : ℕ → (quittingGame reward).BehaviorProfile := fun _ => source.profile

def cutoff : ℕ → ℕ := fun _ => source.stage + 1

def scale (_source : QuittingConstantConcentratedPacketSource reward) : ℕ → ℝ :=
  fun rank => 1 / ((rank : ℝ) + 1)

theorem scale_pos (rank : ℕ) : 0 < source.scale rank := by
  simp only [scale]
  positivity

theorem scale_tendsto_zero : Tendsto source.scale atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Constant repetition supplies the literal generic recurrent packet.  Its
recurrence is only in the constructed packet index. -/
def packet : QuittingReprojectionConcentratedPacket reward source.profiles
    source.owner source.terminal source.cutoff source.scale where
  resolution := source.resolution
  resolution_pos := source.resolution_pos
  subseq := id
  subseq_strictMono := strictMono_id
  mark := fun _ => source.stage
  mark_lt := by simp [cutoff]
  stageMass := by
    intro rank
    simpa [profiles] using source.resolution_le_stageMass
  semanticPrefix := by
    intro rank
    simpa [profiles] using
      positive_stageCoalitionMass_has_semanticPrefixIncidence
        reward source.profile source.stage source.terminal
          (source.resolution_pos.trans_le source.resolution_le_stageMass)
  defect_tendsto := by
    simp only [id_eq]
    have hzero : (fun rank =>
        (quittingLiveMass reward (source.profiles rank) source.stage *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward
                (source.profiles rank) (source.stage + 1))).1
            (quittingProfileLiveRoot reward (source.profiles rank) source.stage)
            source.owner) /
          source.scale rank) = fun _ => 0 := by
      funext rank
      simp [profiles, source.ownerDefect_eq_zero]
    rw [hzero]
    exact tendsto_const_nhds

end QuittingConstantConcentratedPacketSource

end GameTheory
