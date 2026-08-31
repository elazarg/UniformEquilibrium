/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.PureCoalitionOneDateNeverAdapters
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawMinimumFiberAffine

/-!
# Normalized Fin4 oriented minimum-pair response chord

This is a local compiler for supplied normalized date-zero pair data. It does
not construct that data from a source chronology and does not attach a
renewable trace.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct QuittingSureSetOwnerRepair
open scoped BigOperators

/-- Supplied normalized data for a strict incoming dropout from a triple to a
global-minimum pair. -/
structure FinFourOrientedMinimumPairData
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) where
  pair : Finset (Fin 4)
  pair_card : pair.card = 2
  incoming : Fin 4
  remaining : Fin 4
  incoming_not_mem : incoming ∉ pair
  remaining_not_mem : remaining ∉ pair
  incoming_ne_remaining : incoming ≠ remaining
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingPureCoalitionOneDateNeverProfile reward pair)) ≤
      quittingTerminalSemanticDebtSum candidate
  debt_pos : 0 < quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingPureCoalitionOneDateNeverProfile reward pair))
  incoming_dropout_gain_pos :
    0 < quittingSetReward reward pair incoming -
      quittingSetReward reward (insert incoming pair) incoming

namespace FinFourOrientedMinimumPairData

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

def profile (data : FinFourOrientedMinimumPairData reward) :
    (quittingGame reward).BehaviorProfile :=
  quittingPureCoalitionOneDateNeverProfile reward data.pair

def joinedProfile (data : FinFourOrientedMinimumPairData reward) :
    (quittingGame reward).BehaviorProfile :=
  quittingPureCoalitionOneDateNeverProfile reward
    (insert data.remaining data.pair)

theorem pair_nonempty (data : FinFourOrientedMinimumPairData reward) :
    data.pair.Nonempty := by
  apply Finset.card_pos.mp
  rw [data.pair_card]
  norm_num

theorem mem_pair_or_eq_incoming_or_eq_remaining
    (data : FinFourOrientedMinimumPairData reward) (who : Fin 4) :
    who ∈ data.pair ∨ who = data.incoming ∨ who = data.remaining := by
  have hincoming : data.incoming ∉ insert data.remaining data.pair := by
    simp [data.incoming_not_mem, data.incoming_ne_remaining]
  have hcard : (insert data.incoming (insert data.remaining data.pair)).card = 4 := by
    rw [Finset.card_insert_of_notMem hincoming,
      Finset.card_insert_of_notMem data.remaining_not_mem, data.pair_card]
  have huniv : insert data.incoming (insert data.remaining data.pair) =
      (Finset.univ : Finset (Fin 4)) := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  have hmem : who ∈ insert data.incoming (insert data.remaining data.pair) := by
    rw [huniv]
    simp
  simpa [eq_comm, or_assoc, or_left_comm, or_comm] using hmem

theorem incoming_debt_eq_zero
    (data : FinFourOrientedMinimumPairData reward) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward data.profile) data.incoming = 0 := by
  rw [profile, quittingTerminalSemanticDebt_pureCoalitionOneDateNever_eq
    reward data.pair (by rw [data.pair_card]) data.incoming]
  rw [Finset.erase_eq_of_notMem data.incoming_not_mem, max_eq_right]
  · ring
  · linarith [data.incoming_dropout_gain_pos]

theorem member_debt_eq_zero_of_no_positiveSingletonResponse
    (data : FinFourOrientedMinimumPairData reward)
    (hno : ¬∃ who ∈ data.pair,
      0 < quittingSetReward reward (data.pair.erase who) who -
        quittingSetReward reward data.pair who)
    (who : Fin 4) (hwho : who ∈ data.pair) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward data.profile) who = 0 := by
  have hle : quittingSetReward reward (data.pair.erase who) who ≤
      quittingSetReward reward data.pair who := by
    exact le_of_not_gt fun hgain ↦ hno ⟨who, hwho, by linarith⟩
  rw [profile, quittingTerminalSemanticDebt_pureCoalitionOneDateNever_eq
    reward data.pair (by rw [data.pair_card]) who,
    Finset.insert_eq_self.mpr hwho, max_eq_left hle]
  ring

theorem remaining_debt_eq_total_of_no_positiveSingletonResponse
    (data : FinFourOrientedMinimumPairData reward)
    (hno : ¬∃ who ∈ data.pair,
      0 < quittingSetReward reward (data.pair.erase who) who -
        quittingSetReward reward data.pair who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward data.profile) data.remaining =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile) := by
  let debt : Fin 4 → ℝ := fun who ↦ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward data.profile) who
  have hzero : ∀ who ≠ data.remaining, debt who = 0 := by
    intro who hwho
    rcases data.mem_pair_or_eq_incoming_or_eq_remaining who with
        hpair | hincoming | hremaining
    · exact data.member_debt_eq_zero_of_no_positiveSingletonResponse
        hno who hpair
    · subst who
      exact data.incoming_debt_eq_zero
    · exact (hwho hremaining).elim
  unfold quittingTerminalSemanticDebtSum
  change debt data.remaining = ∑ who ∈ Finset.univ, debt who
  rw [Finset.sum_eq_single data.remaining]
  · exact fun who _ hwho ↦ hzero who hwho
  · simp

/-- A literal profitable whole-profile member replacement to the deleted
singleton. -/
structure PositivePairMemberSingletonResponse
    (data : FinFourOrientedMinimumPairData reward) where
  mover : Fin 4
  mover_mem : mover ∈ data.pair
  gain_pos :
    0 < quittingSetReward reward (data.pair.erase mover) mover -
      quittingSetReward reward data.pair mover
  update_eq_singleton :
    Function.update data.profile mover
        (quittingPureTimeBehaviorStrategy reward mover none) =
      quittingPureCoalitionOneDateNeverProfile reward (data.pair.erase mover)
  terminalPayoff_gain_eq :
    quittingTerminalPayoff reward
          (Function.update data.profile mover
            (quittingPureTimeBehaviorStrategy reward mover none)) mover -
        quittingTerminalPayoff reward data.profile mover =
      quittingSetReward reward (data.pair.erase mover) mover -
        quittingSetReward reward data.pair mover

/-- The exact positive whole-profile response of the unique remaining
outsider. -/
structure UniqueRemainingOutsiderJoin
    (data : FinFourOrientedMinimumPairData reward) where
  source_debt_eq_total :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward data.profile) data.remaining =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile)
  source_other_debt_eq_zero : ∀ who ≠ data.remaining,
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward data.profile) who = 0
  gain_eq_total :
    quittingSetReward reward (insert data.remaining data.pair) data.remaining -
        quittingSetReward reward data.pair data.remaining =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile)
  update_eq_joined :
    Function.update data.profile data.remaining
        (quittingPureTimeBehaviorStrategy reward data.remaining (some 0)) =
      data.joinedProfile
  terminalPayoff_gain_eq :
    quittingTerminalPayoff reward
          (Function.update data.profile data.remaining
            (quittingPureTimeBehaviorStrategy reward data.remaining (some 0)))
          data.remaining -
        quittingTerminalPayoff reward data.profile data.remaining =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile)

theorem positivePairMemberSingletonResponse_or_uniqueRemainingOutsiderJoin
    (data : FinFourOrientedMinimumPairData reward) :
    Nonempty (PositivePairMemberSingletonResponse data) ∨
      Nonempty (UniqueRemainingOutsiderJoin data) := by
  classical
  by_cases hmember : ∃ who ∈ data.pair,
      0 < quittingSetReward reward (data.pair.erase who) who -
        quittingSetReward reward data.pair who
  · rcases hmember with ⟨mover, hmover, hgain⟩
    left
    refine ⟨{
      mover := mover
      mover_mem := hmover
      gain_pos := hgain
      update_eq_singleton := update_pureCoalitionOneDateNever_with_never
        reward data.pair mover
      terminalPayoff_gain_eq := ?_ }⟩
    rw [profile, update_pureCoalitionOneDateNever_with_never,
      quittingTerminalPayoff_pureCoalitionOneDateNever reward
        (data.pair.erase mover) (by
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem hmover, data.pair_card]
          norm_num) mover,
      quittingTerminalPayoff_pureCoalitionOneDateNever reward data.pair
        data.pair_nonempty mover]
  · right
    have hsource :=
      data.remaining_debt_eq_total_of_no_positiveSingletonResponse hmember
    have hformula := quittingTerminalSemanticDebt_pureCoalitionOneDateNever_eq
      reward data.pair (by rw [data.pair_card]) data.remaining
    rw [← profile, Finset.erase_eq_of_notMem data.remaining_not_mem] at hformula
    have hgainPos : 0 <
        quittingSetReward reward (insert data.remaining data.pair) data.remaining -
          quittingSetReward reward data.pair data.remaining := by
      by_contra hnot
      have hle : quittingSetReward reward
          (insert data.remaining data.pair) data.remaining ≤
        quittingSetReward reward data.pair data.remaining := by linarith
      rw [max_eq_right hle, sub_self] at hformula
      have hpos : 0 < quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.profile) := by
        simpa only [profile] using data.debt_pos
      linarith [hsource, hpos]
    have hgain :
        quittingSetReward reward (insert data.remaining data.pair) data.remaining -
            quittingSetReward reward data.pair data.remaining =
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward data.profile) := by
      rw [← hsource, hformula]
      rw [max_eq_left (by linarith)]
    refine ⟨{
      source_debt_eq_total := hsource
      source_other_debt_eq_zero := ?_
      gain_eq_total := hgain
      update_eq_joined := update_pureCoalitionOneDateNever_with_quitNow
        reward data.pair data.remaining
      terminalPayoff_gain_eq := ?_ }⟩
    · intro who hwho
      rcases data.mem_pair_or_eq_incoming_or_eq_remaining who with
          hpair | hincoming | hremaining
      · exact data.member_debt_eq_zero_of_no_positiveSingletonResponse
          hmember who hpair
      · subst who
        exact data.incoming_debt_eq_zero
      · exact (hwho hremaining).elim
    · rw [profile, update_pureCoalitionOneDateNever_with_quitNow,
        quittingTerminalPayoff_pureCoalitionOneDateNever reward
          (insert data.remaining data.pair)
          (Finset.insert_nonempty data.remaining data.pair) data.remaining,
        quittingTerminalPayoff_pureCoalitionOneDateNever reward data.pair
          data.pair_nonempty data.remaining]
      exact hgain

/-- Literal stopping-law chord from the normalized pair to its joined triple. -/
def pairToJoinedTripleChordProfile
    (data : FinFourOrientedMinimumPairData reward)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update data.profile data.remaining
    (quittingStoppingLawMixtureBehaviorStrategy reward data.remaining
      (data.profile data.remaining)
      (quittingPureTimeBehaviorStrategy reward data.remaining (some 0))
      lambda hlambda0 hlambda1)

theorem pairToJoinedTripleChord_debt_eq
    (data : FinFourOrientedMinimumPairData reward)
    (join : UniqueRemainingOutsiderJoin data)
    (hsame : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.joinedProfile) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.profile))
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (observer : Fin 4) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (pairToJoinedTripleChordProfile data lambda hlambda0 hlambda1))
        observer =
      (1 - lambda) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward data.profile) observer +
        lambda * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward data.joinedProfile) observer := by
  have haffine :=
    quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum
      reward data.profile data.remaining observer (data.profile data.remaining)
        (quittingPureTimeBehaviorStrategy reward data.remaining (some 0))
        lambda hlambda0 hlambda1
        (by simpa only [Function.update_eq_self, profile] using data.minimum)
        (by simpa only [Function.update_eq_self, join.update_eq_joined] using hsame)
  simpa only [pairToJoinedTripleChordProfile, Function.update_eq_self,
    join.update_eq_joined] using haffine

theorem pairToJoinedTripleChord_debtSum_eq
    (data : FinFourOrientedMinimumPairData reward)
    (join : UniqueRemainingOutsiderJoin data)
    (hsame : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.joinedProfile) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.profile))
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (pairToJoinedTripleChordProfile data lambda hlambda0 hlambda1)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile) := by
  unfold quittingTerminalSemanticDebtSum
  calc
    _ = ∑ observer,
          ((1 - lambda) * quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward data.profile) observer +
            lambda * quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward data.joinedProfile)
              observer) := by
      apply Finset.sum_congr rfl
      intro observer _
      exact pairToJoinedTripleChord_debt_eq data join hsame lambda
        hlambda0 hlambda1 observer
    _ = (1 - lambda) *
          (∑ observer, quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward data.profile) observer) +
        lambda *
          (∑ observer, quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward data.joinedProfile)
              observer) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
      have hsame' :
          (∑ observer, quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward data.joinedProfile)
                observer) =
            ∑ observer, quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward data.profile) observer := by
        simpa only [quittingTerminalSemanticDebtSum] using hsame
      rw [hsame']
      ring

theorem update_pairToJoinedTripleChord_with_quitNow
    (data : FinFourOrientedMinimumPairData reward)
    (join : UniqueRemainingOutsiderJoin data)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    Function.update (pairToJoinedTripleChordProfile data lambda hlambda0 hlambda1)
        data.remaining
        (quittingPureTimeBehaviorStrategy reward data.remaining (some 0)) =
      data.joinedProfile := by
  unfold pairToJoinedTripleChordProfile
  rw [Function.update_idem]
  exact join.update_eq_joined

theorem joinedTripleResponse_from_chord_gain_eq
    (data : FinFourOrientedMinimumPairData reward)
    (join : UniqueRemainingOutsiderJoin data)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalPayoff reward data.joinedProfile data.remaining -
        quittingTerminalPayoff reward
          (pairToJoinedTripleChordProfile data lambda hlambda0 hlambda1)
          data.remaining =
      (1 - lambda) * quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile) := by
  have hmixture := quittingTerminalPayoff_stoppingLawMixture_sub_eq
    reward data.profile data.remaining
      (quittingPureTimeBehaviorStrategy reward data.remaining (some 0))
      lambda hlambda0 hlambda1
  rw [join.update_eq_joined] at hmixture
  have hendpoint : quittingTerminalPayoff reward data.joinedProfile data.remaining -
        quittingTerminalPayoff reward data.profile data.remaining =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile) := by
    rw [← join.update_eq_joined]
    exact join.terminalPayoff_gain_eq
  unfold pairToJoinedTripleChordProfile
  calc
    _ =
        (quittingTerminalPayoff reward data.joinedProfile data.remaining -
          quittingTerminalPayoff reward data.profile data.remaining) -
        (quittingTerminalPayoff reward
            (Function.update data.profile data.remaining
              (quittingStoppingLawMixtureBehaviorStrategy reward data.remaining
                (data.profile data.remaining)
                (quittingPureTimeBehaviorStrategy reward data.remaining (some 0))
                lambda hlambda0 hlambda1)) data.remaining -
          quittingTerminalPayoff reward data.profile data.remaining) := by ring
    _ = quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.profile) -
        lambda * quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.profile) := by
      rw [hendpoint, hmixture, hendpoint]
    _ = _ := by ring

/-- The literal immediate-Quit update of the chord profile gains exactly the
remaining weight times the minimum pair's total debt. -/
theorem quitNowResponse_from_pairToJoinedTripleChord_gain_eq
    (data : FinFourOrientedMinimumPairData reward)
    (join : UniqueRemainingOutsiderJoin data)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalPayoff reward
          (Function.update
            (pairToJoinedTripleChordProfile data lambda hlambda0 hlambda1)
            data.remaining
            (quittingPureTimeBehaviorStrategy reward data.remaining (some 0)))
          data.remaining -
        quittingTerminalPayoff reward
          (pairToJoinedTripleChordProfile data lambda hlambda0 hlambda1)
          data.remaining =
      (1 - lambda) * quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile) := by
  rw [update_pairToJoinedTripleChord_with_quitNow data join]
  exact joinedTripleResponse_from_chord_gain_eq data join lambda
    hlambda0 hlambda1

inductive TerminalDispatch (data : FinFourOrientedMinimumPairData reward) : Type
  | positivePairToSingleton (response : PositivePairMemberSingletonResponse data)
  | offMinimumUniqueOutsiderJoin
      (join : UniqueRemainingOutsiderJoin data)
      (debt_lt : quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward data.profile) <
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward data.joinedProfile))
  | minimumUniqueOutsiderJoin
      (join : UniqueRemainingOutsiderJoin data)
      (debt_eq : quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward data.joinedProfile) =
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward data.profile))

theorem terminalDispatch_nonempty
    (data : FinFourOrientedMinimumPairData reward) :
    Nonempty (TerminalDispatch data) := by
  classical
  rcases positivePairMemberSingletonResponse_or_uniqueRemainingOutsiderJoin data with
      hresponse | hjoin
  · rcases hresponse with ⟨response⟩
    exact ⟨TerminalDispatch.positivePairToSingleton response⟩
  · rcases hjoin with ⟨join⟩
    have hle : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile) ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.joinedProfile) :=
      data.minimum _
        (quittingTerminalSemanticPair_mem_carrier reward data.joinedProfile)
    by_cases heq : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.joinedProfile) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.profile)
    · exact ⟨TerminalDispatch.minimumUniqueOutsiderJoin join heq⟩
    · exact ⟨TerminalDispatch.offMinimumUniqueOutsiderJoin join
        (lt_of_le_of_ne hle (Ne.symm heq))⟩

theorem joinedTripleResponse_from_midpoint_gain_eq_half
    (data : FinFourOrientedMinimumPairData reward)
    (join : UniqueRemainingOutsiderJoin data) :
    quittingTerminalPayoff reward data.joinedProfile data.remaining -
        quittingTerminalPayoff reward
          (pairToJoinedTripleChordProfile data (1 / 2 : ℝ)
            (by norm_num) (by norm_num)) data.remaining =
      (1 / 2 : ℝ) * quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.profile) := by
  rw [joinedTripleResponse_from_chord_gain_eq data join (1 / 2 : ℝ)
    (by norm_num) (by norm_num)]
  ring

end FinFourOrientedMinimumPairData

end GameTheory
