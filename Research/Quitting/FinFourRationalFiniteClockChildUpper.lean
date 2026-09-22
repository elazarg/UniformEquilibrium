/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourRationalFiniteClockProfile
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Terminal.StoppingLawExploitability

/-!
# Exact rational child-only upper certificates for Fin4

This module checks the exploitability of the three surviving players after one
Fin4 player is deleted. The proof-free payload and fair raw enumeration are the
existing Fin4 finite-clock code. The deleted owner is required to have exactly
the deterministic-Never marginal, and its gap is masked out of the checked
maximum.

The semantic adapter reconstructs an actual profile of the deleted-player
quitting game from the decoded survivor stopping laws. Its canonical Never
lift has exactly the same complete stopping laws as the decoded Fin4 profile,
so the checked rational maximum is literally the child's unrestricted terminal
exploitability. No Fin3 encoding or normalization hypothesis is introduced.
-/

namespace GameTheory

open Math.ProbabilityMassFunction

namespace RationalFinFourFiniteClockProfileCode

/-- Exact positive-part gap of one Fin4 coordinate. -/
def playerGap (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (player : Fin 4) : ℚ :=
  max 0 (code.cap reward player - code.payoff reward player)

/-- Maximum exact gap of the three surviving coordinates. The owner coordinate
is present in the existing Fin4 enumeration but contributes zero. -/
def childExploitability (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (code : RationalFinFourFiniteClockProfileCode) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun player =>
    if player = owner then 0 else code.playerGap reward player

theorem playerGap_le_childExploitability
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (code : RationalFinFourFiniteClockProfileCode) (player : Fin 4)
    (hplayer : player ≠ owner) :
    code.playerGap reward player ≤ code.childExploitability reward owner := by
  unfold childExploitability
  simpa only [ite_eq_right hplayer] using
    (Finset.le_sup'
      (fun who : Fin 4 =>
        (if who = owner then 0 else code.playerGap reward who : ℚ))
      (Finset.mem_univ player))

/-- The owner's encoded marginal is supported exactly on Never. Validity then
forces its Never mass to be one. -/
def PureNeverAt (code : RationalFinFourFiniteClockProfileCode)
    (owner : Fin 4) : Prop :=
  ∀ atom, atom ≠ none → code.mass owner atom = 0

instance (code : RationalFinFourFiniteClockProfileCode) (owner : Fin 4) :
    Decidable (code.PureNeverAt owner) := by
  unfold PureNeverAt
  infer_instance

/-- Executable pure-Never marginal test. -/
def pureNeverAt (code : RationalFinFourFiniteClockProfileCode)
    (owner : Fin 4) : Bool :=
  decide (code.PureNeverAt owner)

theorem pureNeverAt_eq_true_iff
    (code : RationalFinFourFiniteClockProfileCode) (owner : Fin 4) :
    code.pureNeverAt owner = true ↔ code.PureNeverAt owner := by
  simp [pureNeverAt]

/-- Exact child-only upper checker on the existing Fin4 rational payload. -/
def verifiesChildUpper (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (target : ℚ) (code : RationalFinFourFiniteClockProfileCode) : Bool :=
  code.valid && code.pureNeverAt owner &&
    decide (code.childExploitability reward owner < target)

theorem verifiesChildUpper_eq_true_iff
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (code : RationalFinFourFiniteClockProfileCode) :
    code.verifiesChildUpper reward owner target = true ↔
      code.Valid ∧ code.PureNeverAt owner ∧
        code.childExploitability reward owner < target := by
  simp [verifiesChildUpper, valid_eq_true_iff, pureNeverAt_eq_true_iff,
    and_assoc]

/-- The existing raw candidate at stage `stage`, retained exactly when it
passes the child-only upper checker. -/
def checkedChildCandidateAt (reward : RationalFinFourRewardCode)
    (owner : Fin 4) (target : ℚ) (stage : ℕ) :
    Option RationalFinFourFiniteClockProfileCode :=
  match candidateAt stage with
  | none => none
  | some code =>
      if code.verifiesChildUpper reward owner target then some code else none

theorem checkedChildCandidateAt_eq_some_iff
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (stage : ℕ) (code : RationalFinFourFiniteClockProfileCode) :
    checkedChildCandidateAt reward owner target stage = some code ↔
      candidateAt stage = some code ∧
        code.verifiesChildUpper reward owner target = true := by
  cases hcandidate : candidateAt stage with
  | none => simp [checkedChildCandidateAt, hcandidate]
  | some candidate =>
      by_cases hverified :
          candidate.verifiesChildUpper reward owner target = true
      · constructor
        · intro hout
          have heq : candidate = code := by
            simpa [checkedChildCandidateAt, hcandidate, hverified] using hout
          subst code
          exact ⟨rfl, hverified⟩
        · rintro ⟨hcode, -⟩
          have heq : candidate = code := Option.some.inj hcode
          subst code
          simp [checkedChildCandidateAt, hcandidate, hverified]
      · have hfalse :
          candidate.verifiesChildUpper reward owner target = false :=
          Bool.eq_false_of_not_eq_true hverified
        constructor
        · intro hout
          simp [checkedChildCandidateAt, hcandidate, hfalse] at hout
        · rintro ⟨hcode, hcodeVerified⟩
          have heq : candidate = code := Option.some.inj hcode
          subst code
          exact (hverified hcodeVerified).elim

/-- Every passing child-only code occurs at a finite stage of the existing raw
enumeration. -/
theorem exists_checkedChildCandidateAt_of_verifiesChildUpper
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (code : RationalFinFourFiniteClockProfileCode)
    (hcode : code.verifiesChildUpper reward owner target = true) :
    ∃ stage, checkedChildCandidateAt reward owner target stage = some code := by
  obtain ⟨stage, hstage⟩ := candidateAt_surjective code
  exact ⟨stage, checkedChildCandidateAt_eq_some_iff
    reward owner target stage code |>.2 ⟨hstage, hcode⟩⟩

noncomputable section

private instance deletedFinFourNonempty (owner : Fin 4) :
    Nonempty {who : Fin 4 // who ≠ owner} := by
  fin_cases owner
  · exact ⟨⟨1, by decide⟩⟩
  all_goals exact ⟨⟨0, by decide⟩⟩

/-- Survivor stopping laws decoded from a valid Fin4 rational payload. -/
def decodedChildLaws (code : RationalFinFourFiniteClockProfileCode)
    (hvalid : code.Valid) (owner : Fin 4) :
    {who : Fin 4 // who ≠ owner} → PMF (Option ℕ) :=
  fun who => finiteClockDecodedLaws code.clockBound code.realMass
    (code.realMass_mem_stdSimplex hvalid) who.1

/-- Actual deleted-game profile reconstructed from the decoded survivor laws. -/
def toDeletedChildProfile (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (owner : Fin 4) :
    (quittingGame (quittingDeleteReward reward.realReward
      (fun who => who = owner))).BehaviorProfile :=
  quittingStoppingLawProfile
    (quittingDeleteReward reward.realReward (fun who => who = owner))
    (code.decodedChildLaws hvalid owner)

/-- The Never lift of the reconstructed child has exactly the decoded parent
stopping laws. -/
theorem behaviorStoppingLaws_lift_toDeletedChildProfile_eq
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (owner : Fin 4) (hpure : code.PureNeverAt owner) :
    quittingBehaviorStoppingLaws reward.realReward
        (quittingLiftDeletedProfile reward.realReward (fun who => who = owner)
          (code.toDeletedChildProfile reward hvalid owner)) =
      quittingBehaviorStoppingLaws reward.realReward
        (code.toBehaviorProfile reward hvalid) := by
  unfold quittingBehaviorStoppingLaws
  funext player
  by_cases hplayer : player = owner
  · subst player
    rw [quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
      reward.realReward (fun who => who = owner)
      (code.toDeletedChildProfile reward hvalid owner) rfl]
    exact (code.behaviorStoppingLaw_toBehaviorProfile_eq_pureNever
      reward hvalid owner hpure).symm
  · let who : {who : Fin 4 // who ≠ owner} := ⟨player, hplayer⟩
    rw [quittingBehaviorStoppingLaw_liftDeletedProfile reward.realReward
      (fun who => who = owner)
      (code.toDeletedChildProfile reward hvalid owner) who]
    change quittingBehaviorStoppingLaw
        (quittingDeleteReward reward.realReward (fun who => who = owner))
          (code.toDeletedChildProfile reward hvalid owner who) =
      quittingBehaviorStoppingLaw reward.realReward
        (code.toBehaviorProfile reward hvalid player)
    unfold toDeletedChildProfile
    rw [quittingBehaviorStoppingLaw_stoppingLawProfile]
    unfold toBehaviorProfile finiteClockDecodedProfile decodedChildLaws
    rw [quittingBehaviorStoppingLaw_stoppingLawProfile]

/-- Each exact rational survivor gap is the corresponding actual deleted-game
terminal gap. -/
theorem cast_playerGap_eq_deletedChildPlayerGap
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (owner : Fin 4) (hpure : code.PureNeverAt owner)
    (who : {who : Fin 4 // who ≠ owner}) :
    (code.playerGap reward who.1 : ℝ) =
      max 0
        (quittingContinuationBestResponseValue
            (quittingDeleteReward reward.realReward (fun player => player = owner))
            (code.toDeletedChildProfile reward hvalid owner) who -
          quittingTerminalPayoff
            (quittingDeleteReward reward.realReward (fun player => player = owner))
            (code.toDeletedChildProfile reward hvalid owner) who) := by
  let child := code.toDeletedChildProfile reward hvalid owner
  let lifted := quittingLiftDeletedProfile reward.realReward
    (fun player => player = owner) child
  let parent := code.toBehaviorProfile reward hvalid
  have hsame : quittingBehaviorStoppingLaws reward.realReward lifted =
      quittingBehaviorStoppingLaws reward.realReward parent := by
    exact code.behaviorStoppingLaws_lift_toDeletedChildProfile_eq
      reward hvalid owner hpure
  have hdebt :
      quittingContinuationBestResponseValue
            (quittingDeleteReward reward.realReward (fun player => player = owner))
            child who -
          quittingTerminalPayoff
            (quittingDeleteReward reward.realReward (fun player => player = owner))
            child who =
        quittingContinuationBestResponseValue reward.realReward parent who.1 -
          quittingTerminalPayoff reward.realReward parent who.1 := by
    calc
      _ = quittingBehaviorDeviationPayoffCap reward.realReward lifted who.1 -
          quittingTerminalPayoff reward.realReward lifted who.1 := by
        exact (quittingBehaviorDeviationDebt_liftDeletedProfile
          reward.realReward (fun player => player = owner) child who).symm
      _ = quittingBehaviorDeviationPayoffCap reward.realReward parent who.1 -
          quittingTerminalPayoff reward.realReward parent who.1 := by
        rw [quittingBehaviorDeviationPayoffCap_eq_of_behaviorStoppingLaws_eq
            reward.realReward lifted parent hsame who.1,
          quittingTerminalPayoff_eq_of_behaviorStoppingLaws_eq
            reward.realReward lifted parent hsame who.1]
      _ = _ := rfl
  unfold playerGap
  rw [code.cast_playerGap_eq_terminalPlayerGap reward hvalid who.1]
  simp only [child, parent, hdebt]

/-- The masked exact rational maximum is literally the terminal
exploitability of the reconstructed deleted-child profile. -/
theorem cast_childExploitability_eq_deletedChildTerminalExploitability
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (owner : Fin 4) (hpure : code.PureNeverAt owner) :
    (code.childExploitability reward owner : ℝ) =
      quittingTerminalExploitability
        (quittingDeleteReward reward.realReward (fun player => player = owner))
        (code.toDeletedChildProfile reward hvalid owner) := by
  unfold childExploitability quittingTerminalExploitability
    QuittingBoundaryHolonomy.finitePlayerMax
  apply le_antisymm
  · obtain ⟨player, -, hplayer⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty fun player : Fin 4 =>
        if player = owner then 0 else code.playerGap reward player
    rw [hplayer]
    by_cases howner : player = owner
    · subst player
      have hif :
          (if owner = owner then (0 : ℚ) else code.playerGap reward owner) = 0 :=
        ite_eq_left rfl
      rw [hif]
      simp only [Rat.cast_zero]
      change (0 : ℝ) ≤ quittingTerminalExploitability
        (quittingDeleteReward reward.realReward (fun who => who = owner))
        (code.toDeletedChildProfile reward hvalid owner)
      exact quittingTerminalExploitability_nonneg
        (quittingDeleteReward reward.realReward (fun who => who = owner))
        (code.toDeletedChildProfile reward hvalid owner)
    · let who : {who : Fin 4 // who ≠ owner} := ⟨player, howner⟩
      rw [ite_eq_right howner]
      calc
        (code.playerGap reward player : ℝ) =
            max 0
              (quittingContinuationBestResponseValue
                  (quittingDeleteReward reward.realReward
                    (fun candidate => candidate = owner))
                  (code.toDeletedChildProfile reward hvalid owner) who -
                quittingTerminalPayoff
                  (quittingDeleteReward reward.realReward
                    (fun candidate => candidate = owner))
                  (code.toDeletedChildProfile reward hvalid owner) who) := by
          exact code.cast_playerGap_eq_deletedChildPlayerGap
            reward hvalid owner hpure who
        _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun candidate =>
            max 0
              (quittingContinuationBestResponseValue
                  (quittingDeleteReward reward.realReward
                    (fun player => player = owner))
                  (code.toDeletedChildProfile reward hvalid owner) candidate -
                quittingTerminalPayoff
                  (quittingDeleteReward reward.realReward
                    (fun player => player = owner))
                  (code.toDeletedChildProfile reward hvalid owner) candidate)) :=
          Finset.le_sup'
            (fun candidate : {who : Fin 4 // who ≠ owner} =>
              max 0
                (quittingContinuationBestResponseValue
                    (quittingDeleteReward reward.realReward
                      (fun player => player = owner))
                    (code.toDeletedChildProfile reward hvalid owner) candidate -
                  quittingTerminalPayoff
                    (quittingDeleteReward reward.realReward
                      (fun player => player = owner))
                    (code.toDeletedChildProfile reward hvalid owner) candidate))
            (Finset.mem_univ who)
  · apply Finset.sup'_le Finset.univ_nonempty
    intro who _
    rw [← code.cast_playerGap_eq_deletedChildPlayerGap
      reward hvalid owner hpure who]
    exact_mod_cast code.playerGap_le_childExploitability
      reward owner who.1 who.2

/-- A passing child-only checker row decodes to an actual deleted-game profile
whose unrestricted terminal exploitability is strictly below the threshold. -/
theorem verifiesChildUpper_sound
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (code : RationalFinFourFiniteClockProfileCode)
    (hchecked : code.verifiesChildUpper reward owner target = true) :
    ∃ hvalid : code.Valid,
      code.PureNeverAt owner ∧
        quittingTerminalExploitability
            (quittingDeleteReward reward.realReward (fun player => player = owner))
            (code.toDeletedChildProfile reward hvalid owner) < (target : ℝ) := by
  obtain ⟨hvalid, hpure, htarget⟩ :=
    (code.verifiesChildUpper_eq_true_iff reward owner target).mp hchecked
  refine ⟨hvalid, hpure, ?_⟩
  rw [← code.cast_childExploitability_eq_deletedChildTerminalExploitability
    reward hvalid owner hpure]
  exact_mod_cast htarget

/-- Every emitted child-only search row carries the corresponding actual
deleted-game exploitability bound. -/
theorem checkedChildCandidateAt_sound
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (stage : ℕ) (code : RationalFinFourFiniteClockProfileCode)
    (hrow : checkedChildCandidateAt reward owner target stage = some code) :
    ∃ hvalid : code.Valid,
      code.PureNeverAt owner ∧
        quittingTerminalExploitability
            (quittingDeleteReward reward.realReward (fun player => player = owner))
            (code.toDeletedChildProfile reward hvalid owner) < (target : ℝ) := by
  exact code.verifiesChildUpper_sound reward owner target
    ((checkedChildCandidateAt_eq_some_iff
      reward owner target stage code).mp hrow).2

end

end RationalFinFourFiniteClockProfileCode

end GameTheory
