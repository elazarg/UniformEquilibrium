/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidRowExactPortAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicSupportBoundary

/-!
# A paid row carried by the cap-lifted summable port

Starting from an arbitrary attained paid profile, prefix exact roots selected
against the profile's all-behavior cap.  The cap annotations automatically lie
above the behavioral punishment floor, while the same roots prefix the literal
profile and preserve its prescribed payoff chronology.

At a positive global minimum of total terminal-semantic debt, exact cap-Nash
scaling makes the root absorption masses summable.  It also gives a uniform
lower bound on the probability of reaching the unchanged paid suffix.  Thus no
floor hypothesis on the paid profile's prescribed payoff is needed.

The limiting object is a terminal-semantic carrier point and an exact
all-Continue Bellman port.  It is not a behavior profile which reaches the
original suffix after infinitely many prefix stages.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open QuittingPunishmentFloorInfiniteOrbit

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}

/-- An attained paid row together with a positive global minimum of total
terminal-semantic debt. -/
structure QuittingPaidCapLiftedSource
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota) where
  minimum : QuittingTerminalSemanticPair iota
  minimum_le : ∀ candidate,
    candidate ∈ quittingTerminalSemanticCarrier reward →
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
  profile : (quittingGame reward).BehaviorProfile
  observer : iota
  gain : Real
  gain_pos : 0 < gain
  row : QuittingPaidFirstDisagreementRow reward profile observer gain

/-- Select one exact root against the literal profile's behavioral cap. -/
noncomputable def quittingCapLiftedPrefixRoot
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) : iota -> PMF Bool :=
  Classical.choose (exists_isZeroQuittingRootNash
    (reward := reward) (quittingTerminalSemanticPair reward profile).2)

theorem quittingCapLiftedPrefixRoot_exactNash
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) :
    IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2 0
      (quittingCapLiftedPrefixRoot reward profile) :=
  Classical.choose_spec (exists_isZeroQuittingRootNash
    (reward := reward) (quittingTerminalSemanticPair reward profile).2)

/-- Prefix cap-Nash roots outward while retaining the original profile as the
literal suffix at every finite depth. -/
noncomputable def quittingCapLiftedPrefixProfile
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) :
    Nat -> (quittingGame reward).BehaviorProfile
  | 0 => terminal
  | time + 1 => quittingRootThenContinuationProfile reward
      (quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward terminal time))
      (quittingCapLiftedPrefixProfile reward terminal time)

@[simp] theorem quittingCapLiftedPrefixProfile_zero
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingCapLiftedPrefixProfile reward terminal 0 = terminal := rfl

@[simp] theorem quittingCapLiftedPrefixProfile_succ
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) (time : Nat) :
    quittingCapLiftedPrefixProfile reward terminal (time + 1) =
      quittingRootThenContinuationProfile reward
        (quittingCapLiftedPrefixRoot reward
          (quittingCapLiftedPrefixProfile reward terminal time))
        (quittingCapLiftedPrefixProfile reward terminal time) := rfl

/-- The cap coordinates of the literal prefix profiles form an exact
punishment-floor infinite Nash--Bellman orbit. -/
noncomputable def quittingCapLiftedPunishmentFloorOrbit
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) :
    QuittingPunishmentFloorInfiniteOrbit reward where
  roots := fun time => quittingCapLiftedPrefixRoot reward
    (quittingCapLiftedPrefixProfile reward terminal time)
  value := fun time =>
    (quittingTerminalSemanticPair reward
      (quittingCapLiftedPrefixProfile reward terminal time)).2
  value_mem := by
    intro time
    constructor <;> intro who
    · exact neg_le_of_abs_le
        (abs_quittingContinuationBestResponseValue_le reward
          (quittingCapLiftedPrefixProfile reward terminal time) who
          (abs_reward_le_quittingRewardBound reward))
    · exact le_of_abs_le
        (abs_quittingContinuationBestResponseValue_le reward
          (quittingCapLiftedPrefixProfile reward terminal time) who
          (abs_reward_le_quittingRewardBound reward))
  anchor_floor := by
    intro who
    exact quittingPunishmentValue_le_terminalSemanticEnvelope
      (quittingTerminalSemanticPair reward terminal)
      (quittingTerminalSemanticPair_mem_carrier reward terminal) who
  policy := by
    intro time
    rw [quittingCapLiftedPrefixProfile_succ,
      quittingTerminalSemanticPair_rootThenContinuation reward
        (quittingCapLiftedPrefixRoot reward
          (quittingCapLiftedPrefixProfile reward terminal time))
        (quittingCapLiftedPrefixProfile reward terminal time)]
    exact
      quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
        (reward := reward)
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward terminal time))
        (quittingCapLiftedPrefixRoot reward
          (quittingCapLiftedPrefixProfile reward terminal time))
        (quittingCapLiftedPrefixRoot_exactNash reward
          (quittingCapLiftedPrefixProfile reward terminal time))
  exactNash := by
    intro time
    exact quittingCapLiftedPrefixRoot_exactNash reward
      (quittingCapLiftedPrefixProfile reward terminal time)

/-- Literal prefixing identifies the successor semantic pair. -/
theorem quittingCapLiftedPrefixProfile_semanticPair_succ
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) (time : Nat) :
    quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward terminal (time + 1)) =
      quittingTerminalSemanticPrefix reward
        (quittingCapLiftedPrefixRoot reward
          (quittingCapLiftedPrefixProfile reward terminal time))
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward terminal time)) := by
  rw [quittingCapLiftedPrefixProfile_succ]
  exact quittingTerminalSemanticPair_rootThenContinuation
    reward
    (quittingCapLiftedPrefixRoot reward
      (quittingCapLiftedPrefixProfile reward terminal time))
    (quittingCapLiftedPrefixProfile reward terminal time)

/-- Total terminal-semantic debt scales by the exact joint Continue mass at
each cap-Nash prefix. -/
theorem quittingCapLiftedPrefixProfile_debt_succ
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) (time : Nat) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward terminal (time + 1))) =
      quittingStationaryContinueMass
          (quittingCapLiftedPrefixRoot reward
            (quittingCapLiftedPrefixProfile reward terminal time)) *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward terminal time)) := by
  rw [quittingCapLiftedPrefixProfile_semanticPair_succ]
  unfold quittingTerminalSemanticDebtSum
  simp_rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
    (reward := reward)
    (quittingTerminalSemanticPair reward
      (quittingCapLiftedPrefixProfile reward terminal time))
    (quittingCapLiftedPrefixRoot reward
      (quittingCapLiftedPrefixProfile reward terminal time)) _
    (quittingCapLiftedPrefixRoot_exactNash reward
      (quittingCapLiftedPrefixProfile reward terminal time))]
  rw [Finset.mul_sum]

/-- Probability that every cap root prefixed before a finite horizon plays
all Continue. -/
def quittingCapLiftedSuffixReach
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) (horizon : Nat) : Real :=
  ∏ time ∈ Finset.range horizon,
    quittingStationaryContinueMass
      (quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward terminal time))

@[simp] theorem quittingCapLiftedSuffixReach_zero
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingCapLiftedSuffixReach reward terminal 0 = 1 := by
  simp [quittingCapLiftedSuffixReach]

theorem quittingCapLiftedSuffixReach_succ
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) (time : Nat) :
    quittingCapLiftedSuffixReach reward terminal (time + 1) =
      quittingCapLiftedSuffixReach reward terminal time *
        quittingStationaryContinueMass
          (quittingCapLiftedPrefixRoot reward
            (quittingCapLiftedPrefixProfile reward terminal time)) := by
  simp [quittingCapLiftedSuffixReach, Finset.prod_range_succ]

/-- Finite cap-prefix survival scales total debt exactly. -/
theorem quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) (time : Nat) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward terminal time)) =
      quittingCapLiftedSuffixReach reward terminal time *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [quittingCapLiftedPrefixProfile_debt_succ, ih,
        quittingCapLiftedSuffixReach_succ]
      ring

/-! ## Pure-time transport through literal prefixes -/

/-- Shift a finite deterministic quit time by a prefix length; `Never`
remains `Never`. -/
def quittingCapLiftPureTimeShift (depth : Nat) : Option Nat -> Option Nat :=
  quittingAbsolutePureTime depth

@[simp] theorem quittingCapLiftPureTimeShift_none (depth : Nat) :
    quittingCapLiftPureTimeShift depth none = none := rfl

@[simp] theorem quittingCapLiftPureTimeShift_some (depth time : Nat) :
    quittingCapLiftPureTimeShift depth (some time) = some (depth + time) := rfl

private theorem quittingPureTimeValue_splice_shift_tail
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (root : iota -> PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : iota) (choice : Option Nat) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward
          (quittingRootThenContinuationProfile reward root continuation)) who
        (quittingCapLiftPureTimeShift 1 choice) 1 =
      quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward continuation) who choice 0 := by
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
    quittingRootSequenceTerminalValue
  congr 1
  funext player time history
  unfold quittingRootSequenceProfile quittingRootSequenceUpdate
  rw [show 1 + time = time + 1 by omega,
    quittingProfileLiveRoot_rootThenContinuation_succ]
  cases choice with
  | none =>
      simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime,
        quittingPureTimeHazard]
  | some value =>
      have htime : time + 1 = 1 + value ↔ time = value := by omega
      simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime,
        quittingPureTimeHazard, htime]

/-- Prefixing one root scales the difference between two delayed pure-time
payoffs by the observer's opponents-only Continue mass. -/
theorem quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (root : iota -> PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : iota) (first second : Option Nat) :
    quittingPureTimeDeviationPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who
          (quittingCapLiftPureTimeShift 1 first) -
        quittingPureTimeDeviationPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who
          (quittingCapLiftPureTimeShift 1 second) =
      quittingStationaryFixedOpponentsContinueMass root who *
        (quittingPureTimeDeviationPayoff reward continuation who first -
          quittingPureTimeDeviationPayoff reward continuation who second) := by
  unfold quittingPureTimeDeviationPayoff
  simp only [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  have hvalue : ∀ choice : Option Nat,
      quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward
            (quittingRootThenContinuationProfile reward root continuation)) who
          (quittingCapLiftPureTimeShift 1 choice) 0 =
        quittingFixedOpponentsContinueReward reward (fun _ => root) who 0 +
          quittingStationaryFixedOpponentsContinueMass root who *
            quittingRootSequencePureTimeTerminalValue reward
              (quittingProfileLiveRoot reward continuation) who choice 0 := by
    intro choice
    unfold quittingRootSequencePureTimeTerminalValue
    rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
    cases choice with
    | none =>
        have htail := quittingPureTimeValue_splice_shift_tail
          reward root continuation who none
        unfold quittingRootSequencePureTimeTerminalValue at htail
        simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime] at htail
        simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime,
          quittingPureTimeHazard]
        rw [htail]
        rfl
    | some time =>
        have htail := quittingPureTimeValue_splice_shift_tail
          reward root continuation who (some time)
        unfold quittingRootSequencePureTimeTerminalValue at htail
        simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime] at htail
        have hzero : (0 : Nat) ≠ 1 + time := by omega
        simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime,
          quittingPureTimeHazard, hzero]
        rw [htail]
        rfl
  rw [hvalue first, hvalue second]
  ring

namespace QuittingPaidCapLiftedSource

variable (source : QuittingPaidCapLiftedSource reward)

/-- Total debt of the attained paid profile. -/
def initialDebt : Real :=
  quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward source.profile)

/-- The positive minimum lies below the source's actual total debt. -/
theorem minimum_le_initialDebt :
    quittingTerminalSemanticDebtSum source.minimum ≤ source.initialDebt :=
  source.minimum_le _
    (quittingTerminalSemanticPair_mem_carrier reward source.profile)

theorem initialDebt_pos : 0 < source.initialDebt :=
  source.minimum_pos.trans_le source.minimum_le_initialDebt

/-- Uniform fraction of the original paid suffix retained by every finite
cap prefix. -/
def reachFloor : Real :=
  quittingTerminalSemanticDebtSum source.minimum / source.initialDebt

theorem reachFloor_pos : 0 < source.reachFloor :=
  div_pos source.minimum_pos source.initialDebt_pos

theorem reachFloor_le_one : source.reachFloor ≤ 1 := by
  apply (div_le_one source.initialDebt_pos).2
  exact source.minimum_le_initialDebt

/-- Every finite cap prefix reaches the original paid suffix with the same
strictly positive debt-ratio lower bound. -/
theorem reachFloor_le_suffixReach (horizon : Nat) :
    source.reachFloor ≤
      quittingCapLiftedSuffixReach reward source.profile horizon := by
  have hfinalLower := source.minimum_le
    (quittingTerminalSemanticPair reward
      (quittingCapLiftedPrefixProfile reward source.profile horizon))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  rw [quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul] at hfinalLower
  apply (div_le_iff₀ source.initialDebt_pos).2
  simpa [reachFloor, initialDebt] using hfinalLower

/-- Probability that the paid observer's opponents Continue through all cap
roots before a finite prefix. -/
def observerReach (horizon : Nat) : Real :=
  ∏ time ∈ Finset.range horizon,
    quittingStationaryFixedOpponentsContinueMass
      (quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward source.profile time))
      source.observer

@[simp] theorem observerReach_zero : source.observerReach 0 = 1 := by
  simp [observerReach]

theorem observerReach_succ (time : Nat) :
    source.observerReach (time + 1) = source.observerReach time *
      quittingStationaryFixedOpponentsContinueMass
        (quittingCapLiftedPrefixRoot reward
          (quittingCapLiftedPrefixProfile reward source.profile time))
        source.observer := by
  simp [observerReach, Finset.prod_range_succ]

theorem observerReach_nonneg (horizon : Nat) :
    0 ≤ source.observerReach horizon := by
  apply Finset.prod_nonneg
  intro time _
  exact quittingStationaryFixedOpponentsContinueMass_nonneg _ _

/-- Opponents-only paid reach dominates the joint reach of the literal paid
suffix. -/
theorem suffixReach_le_observerReach (horizon : Nat) :
    quittingCapLiftedSuffixReach reward source.profile horizon ≤
      source.observerReach horizon := by
  apply Finset.prod_le_prod
  · intro time _
    exact quittingStationaryContinueMass_nonneg _
  · intro time _
    exact quittingStationaryContinueMass_le_fixedOpponentsContinueMass _ _

/-- Pure-time payoff differences through the finite cap prefix are scaled
exactly by the paid observer's opponents-only reach. -/
theorem pureTimePayoff_sub_shift (horizon : Nat)
    (first second : Option Nat) :
    quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)
          source.observer (quittingCapLiftPureTimeShift horizon first) -
        quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)
          source.observer (quittingCapLiftPureTimeShift horizon second) =
      source.observerReach horizon *
        (quittingPureTimeDeviationPayoff reward source.profile source.observer
            first -
          quittingPureTimeDeviationPayoff reward source.profile source.observer
            second) := by
  induction horizon with
  | zero =>
      rw [quittingCapLiftedPrefixProfile_zero, observerReach_zero, one_mul]
      cases first <;> cases second <;>
        simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime]
  | succ horizon ih =>
      rw [quittingCapLiftedPrefixProfile_succ]
      have hshift : ∀ choice : Option Nat,
          quittingCapLiftPureTimeShift (horizon + 1) choice =
            quittingCapLiftPureTimeShift 1
              (quittingCapLiftPureTimeShift horizon choice) := by
        intro choice
        cases choice with
        | none => rfl
        | some value =>
            simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime]
            omega
      rw [hshift first, hshift second,
        quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one,
        ih, observerReach_succ]
      ring

/-- The original paid difference survives every finite cap prefix with the
uniform positive gain supplied by the global debt ratio. -/
theorem shifted_gain_le (horizon : Nat) :
    source.reachFloor * source.gain ≤
      quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)
          source.observer
          (quittingCapLiftPureTimeShift horizon source.row.receivingWitness) -
        quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)
          source.observer
          (quittingCapLiftPureTimeShift horizon source.row.sourceWitness) := by
  rw [source.pureTimePayoff_sub_shift horizon]
  have hreach : source.reachFloor ≤ source.observerReach horizon :=
    (source.reachFloor_le_suffixReach horizon).trans
      (source.suffixReach_le_observerReach horizon)
  have hedge : source.gain ≤
      quittingPureTimeDeviationPayoff reward source.profile source.observer
          source.row.receivingWitness -
        quittingPureTimeDeviationPayoff reward source.profile source.observer
          source.row.sourceWitness :=
    source.row.gain_le_paid.trans_eq source.row.edge_identity.symm
  exact (mul_le_mul_of_nonneg_right hreach source.gain_pos.le).trans
    (mul_le_mul_of_nonneg_left hedge (source.observerReach_nonneg horizon))

/-- A decoded paid row on one finite cap prefix, with its two pure times
identified as the literal shifts of the original witnesses. -/
structure ShiftedPaidRow (horizon : Nat) where
  row : QuittingPaidFirstDisagreementRow reward
    (quittingCapLiftedPrefixProfile reward source.profile horizon)
    source.observer (source.reachFloor * source.gain)
  sourceWitness_eq : row.sourceWitness =
    quittingCapLiftPureTimeShift horizon source.row.sourceWitness
  receivingWitness_eq : row.receivingWitness =
    quittingCapLiftPureTimeShift horizon source.row.receivingWitness

namespace ShiftedPaidRow

variable {source : QuittingPaidCapLiftedSource reward} {horizon : Nat}

/-- Shifting both witnesses preserves which one is earlier. -/
theorem receivingEarlier_eq (shifted : source.ShiftedPaidRow horizon) :
    shifted.row.receivingEarlier = source.row.receivingEarlier := by
  have hold := source.row.chronology
  have hnew := shifted.row.chronology
  rw [shifted.sourceWitness_eq, shifted.receivingWitness_eq] at hnew
  cases holdEarlier : source.row.receivingEarlier with
  | false =>
      rw [holdEarlier] at hold
      rw [hold.1, hold.2] at hnew
      cases newEarlier : shifted.row.receivingEarlier with
      | false => rfl
      | true =>
          rw [newEarlier] at hnew
          cases later : source.row.later with
          | none =>
              simp [later, quittingAbsolutePureTime,
                quittingCapLiftPureTimeShift] at hold hnew
          | some delay =>
              have hdelay : 0 < delay := by
                simpa [IsQuittingStrictlyLaterDelay, later] using
                  source.row.later_strict
              cases newLater : shifted.row.later with
              | none =>
                  simp [later, newLater, quittingAbsolutePureTime,
                    quittingCapLiftPureTimeShift] at hold hnew
              | some newDelay =>
                  have hnewDelay : 0 < newDelay := by
                    simpa [IsQuittingStrictlyLaterDelay, newLater] using
                      shifted.row.later_strict
                  simp [later, newLater, quittingAbsolutePureTime,
                    quittingCapLiftPureTimeShift] at hold hnew
                  omega
  | true =>
      rw [holdEarlier] at hold
      rw [hold.1, hold.2] at hnew
      cases newEarlier : shifted.row.receivingEarlier with
      | true => rfl
      | false =>
          rw [newEarlier] at hnew
          cases later : source.row.later with
          | none =>
              simp [later, quittingAbsolutePureTime,
                quittingCapLiftPureTimeShift] at hold hnew
          | some delay =>
              have hdelay : 0 < delay := by
                simpa [IsQuittingStrictlyLaterDelay, later] using
                  source.row.later_strict
              cases newLater : shifted.row.later with
              | none =>
                  simp [later, newLater, quittingAbsolutePureTime,
                    quittingCapLiftPureTimeShift] at hold hnew
              | some newDelay =>
                  have hnewDelay : 0 < newDelay := by
                    simpa [IsQuittingStrictlyLaterDelay, newLater] using
                      shifted.row.later_strict
                  simp [later, newLater, quittingAbsolutePureTime,
                    quittingCapLiftPureTimeShift] at hold hnew
                  omega

/-- The first disagreement is shifted by exactly the prefix depth. -/
theorem start_eq (shifted : source.ShiftedPaidRow horizon) :
    shifted.row.start = horizon + source.row.start := by
  have hold := source.row.chronology
  have hnew := shifted.row.chronology
  rw [shifted.receivingEarlier_eq] at hnew
  rw [shifted.sourceWitness_eq, shifted.receivingWitness_eq] at hnew
  cases earlier : source.row.receivingEarlier with
  | false =>
      rw [earlier] at hold hnew
      simp [hold.1, quittingCapLiftPureTimeShift,
        quittingAbsolutePureTime] at hnew
      exact hnew.1.symm
  | true =>
      rw [earlier] at hold hnew
      simp [hold.1, quittingCapLiftPureTimeShift,
        quittingAbsolutePureTime] at hnew
      exact hnew.1.symm

/-- The relative delay after the first disagreement is unchanged. -/
theorem later_eq (shifted : source.ShiftedPaidRow horizon) :
    shifted.row.later = source.row.later := by
  have hold := source.row.chronology
  have hnew := shifted.row.chronology
  rw [shifted.receivingEarlier_eq] at hnew
  rw [shifted.sourceWitness_eq, shifted.receivingWitness_eq] at hnew
  have hcompare :
      quittingCapLiftPureTimeShift horizon
          (quittingAbsolutePureTime source.row.start source.row.later) =
        quittingAbsolutePureTime (horizon + source.row.start)
          shifted.row.later := by
    cases earlier : source.row.receivingEarlier with
    | false =>
        rw [earlier] at hold hnew
        calc
          _ = quittingCapLiftPureTimeShift horizon
                source.row.receivingWitness := by rw [hold.2]
          _ = quittingAbsolutePureTime shifted.row.start shifted.row.later :=
            hnew.2
          _ = _ := by rw [shifted.start_eq]
    | true =>
        rw [earlier] at hold hnew
        calc
          _ = quittingCapLiftPureTimeShift horizon
                source.row.sourceWitness := by rw [hold.2]
          _ = quittingAbsolutePureTime shifted.row.start shifted.row.later :=
            hnew.2
          _ = _ := by rw [shifted.start_eq]
  cases oldLater : source.row.later with
  | none =>
      cases newLater : shifted.row.later with
      | none => rfl
      | some delay =>
          simp [oldLater, newLater, quittingCapLiftPureTimeShift,
            quittingAbsolutePureTime] at hcompare
  | some oldDelay =>
      cases newLater : shifted.row.later with
      | none =>
          simp [oldLater, newLater, quittingCapLiftPureTimeShift,
            quittingAbsolutePureTime] at hcompare
      | some newDelay =>
          have hdelay : oldDelay = newDelay := by
            simp [oldLater, newLater, quittingCapLiftPureTimeShift,
              quittingAbsolutePureTime] at hcompare
            omega
          simpa [oldLater, newLater] using congrArg some hdelay.symm

end ShiftedPaidRow

private theorem opponentSurvival_prefixProfile_succ
    (time start : Nat) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingCapLiftedPrefixProfile reward source.profile (time + 1)))
        source.observer 0 (time + 1 + start) =
      quittingStationaryFixedOpponentsContinueMass
          (quittingCapLiftedPrefixRoot reward
            (quittingCapLiftedPrefixProfile reward source.profile time))
          source.observer *
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward
            (quittingCapLiftedPrefixProfile reward source.profile time))
          source.observer 0 (time + start) := by
  rw [quittingCapLiftedPrefixProfile_succ]
  rw [show time + 1 + start = (time + start) + 1 by omega,
    quittingOpponentSurvivalWeight_succ_left]
  congr 1
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_congr rfl
  intro offset _
  unfold quittingFixedOpponentsContinueMass
  rw [show 0 + 1 + offset = offset + 1 by omega,
    quittingProfileLiveRoot_rootThenContinuation_succ]
  simp

/-- Exact deleted-player survival factorization through all cap prefixes. -/
theorem opponentSurvival_shift (horizon start : Nat) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon))
        source.observer 0 (horizon + start) =
      source.observerReach horizon *
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward source.profile)
          source.observer 0 start := by
  induction horizon with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ horizon ih =>
      rw [source.opponentSurvival_prefixProfile_succ horizon start, ih,
        source.observerReach_succ]
      ring

/-- The decoded row's first-disagreement live mass is exactly the original
live mass times the observer-deleted prefix reach. -/
theorem ShiftedPaidRow.liveMass_eq
    {source : QuittingPaidCapLiftedSource reward} {horizon : Nat}
    (shifted : source.ShiftedPaidRow horizon) :
    shifted.row.liveMass = source.observerReach horizon * source.row.liveMass := by
  rw [shifted.row.liveMass_eq, shifted.start_eq, source.opponentSurvival_shift,
    source.row.liveMass_eq]

/-- Every finite cap prefix carries a paid row of the same uniform positive
gain. -/
theorem nonempty_shiftedPaidRow (horizon : Nat) :
    Nonempty (source.ShiftedPaidRow horizon) := by
  have hgain : 0 < source.reachFloor * source.gain :=
    mul_pos source.reachFloor_pos source.gain_pos
  obtain ⟨row, hsource, hreceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward
      (quittingCapLiftedPrefixProfile reward source.profile horizon)
      source.observer
      (quittingCapLiftPureTimeShift horizon source.row.sourceWitness)
      (quittingCapLiftPureTimeShift horizon source.row.receivingWitness)
      (source.reachFloor * source.gain) hgain
      (source.shifted_gain_le horizon)
  exact ⟨⟨row, hsource, hreceiving⟩⟩

end QuittingPaidCapLiftedSource

namespace QuittingPaidCapLiftedSource

variable (source : QuittingPaidCapLiftedSource reward)

/-- Every literal semantic debt coordinate decreases along the cap-lifted
profile sequence. -/
theorem debt_antitone (who : iota) : Antitone (fun time =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward source.profile time)) who) := by
  apply antitone_nat_of_succ_le
  intro time
  rw [quittingCapLiftedPrefixProfile_semanticPair_succ]
  rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
    (reward := reward)
    (quittingTerminalSemanticPair reward
      (quittingCapLiftedPrefixProfile reward source.profile time))
    (quittingCapLiftedPrefixRoot reward
      (quittingCapLiftedPrefixProfile reward source.profile time)) who
    (quittingCapLiftedPrefixRoot_exactNash reward
      (quittingCapLiftedPrefixProfile reward source.profile time))]
  have hcontinue := quittingStationaryContinueMass_le_one
    (quittingCapLiftedPrefixRoot reward
      (quittingCapLiftedPrefixProfile reward source.profile time))
  have hdebt := quittingTerminalDeviationDebt_nonneg reward
    (quittingCapLiftedPrefixProfile reward source.profile time) who
  have hdebt' : 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward source.profile time)) who := by
    simpa [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDeviationDebt] using hdebt
  nlinarith [mul_nonneg (sub_nonneg.mpr hcontinue) hdebt']

/-- The global positive minimum charges every finite prefix absorption. -/
theorem minimum_mul_partialAbsorption_le_debtDrop (horizon : Nat) :
    quittingTerminalSemanticDebtSum source.minimum *
          ∑ time ∈ Finset.range horizon,
            quittingRootAbsorptionMass
              (quittingCapLiftedPrefixRoot reward
                (quittingCapLiftedPrefixProfile reward source.profile time)) ≤
      source.initialDebt -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward source.profile horizon)) := by
  induction horizon with
  | zero => simp [initialDebt]
  | succ horizon ih =>
      let profile :=
        quittingCapLiftedPrefixProfile reward source.profile horizon
      let root := quittingCapLiftedPrefixRoot reward profile
      let debt := quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile)
      have hminimumDebt :
          quittingTerminalSemanticDebtSum source.minimum ≤ debt :=
        source.minimum_le _
          (quittingTerminalSemanticPair_mem_carrier reward profile)
      have habsorption : 0 ≤ quittingRootAbsorptionMass root :=
        quittingRootAbsorptionMass_nonneg root
      have hlocal : quittingTerminalSemanticDebtSum source.minimum *
            quittingRootAbsorptionMass root ≤
          debt * quittingRootAbsorptionMass root :=
        mul_le_mul_of_nonneg_right hminimumDebt habsorption
      have hstep := quittingCapLiftedPrefixProfile_debt_succ
        reward source.profile horizon
      have hlocalDrop : quittingTerminalSemanticDebtSum source.minimum *
            quittingRootAbsorptionMass root ≤
          debt - quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingCapLiftedPrefixProfile reward source.profile
                (horizon + 1))) := by
        dsimp only [profile, root, debt] at hstep ⊢
        unfold quittingRootAbsorptionMass at hlocal ⊢
        nlinarith
      rw [Finset.sum_range_succ]
      dsimp only [profile, root, debt] at hlocalDrop
      nlinarith [hlocalDrop]

/-- The finite debt drop is bounded by the source's excess above the global
minimum. -/
theorem debtDrop_le_initial_sub_minimum (horizon : Nat) :
    source.initialDebt -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward source.profile horizon)) ≤
      source.initialDebt -
        quittingTerminalSemanticDebtSum source.minimum := by
  have hfinalLower := source.minimum_le
    (quittingTerminalSemanticPair reward
      (quittingCapLiftedPrefixProfile reward source.profile horizon))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  linarith

/-- Complete finite quantitative charge budget. -/
theorem partialAbsorption_budget (horizon : Nat) :
    quittingTerminalSemanticDebtSum source.minimum *
          ∑ time ∈ Finset.range horizon,
            quittingRootAbsorptionMass
              (quittingCapLiftedPrefixRoot reward
                (quittingCapLiftedPrefixProfile reward source.profile time)) ≤
        source.initialDebt -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingCapLiftedPrefixProfile reward source.profile horizon)) ∧
      source.initialDebt -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingCapLiftedPrefixProfile reward source.profile horizon)) ≤
        source.initialDebt -
          quittingTerminalSemanticDebtSum source.minimum :=
  ⟨source.minimum_mul_partialAbsorption_le_debtDrop horizon,
    source.debtDrop_le_initial_sub_minimum horizon⟩

/-- Cap-root absorption is summable, with no prescribed-payoff floor
hypothesis. -/
theorem absorption_summable : Summable (fun time =>
    quittingRootAbsorptionMass
      (quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward source.profile time))) := by
  refine summable_of_sum_range_le
    (c := source.initialDebt /
      quittingTerminalSemanticDebtSum source.minimum)
    (fun time => quittingRootAbsorptionMass_nonneg _) ?_
  intro horizon
  have hcharge := source.minimum_mul_partialAbsorption_le_debtDrop horizon
  have hfinalLower := source.minimum_le
    (quittingTerminalSemanticPair reward
      (quittingCapLiftedPrefixProfile reward source.profile horizon))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  have hfinalNonneg : 0 ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward source.profile horizon)) :=
    source.minimum_pos.le.trans hfinalLower
  have hscaled : quittingTerminalSemanticDebtSum source.minimum *
        ∑ time ∈ Finset.range horizon,
          quittingRootAbsorptionMass
            (quittingCapLiftedPrefixRoot reward
              (quittingCapLiftedPrefixProfile reward source.profile time)) ≤
      source.initialDebt :=
    hcharge.trans (sub_le_self source.initialDebt hfinalNonneg)
  apply (le_div_iff₀ source.minimum_pos).2
  simpa [mul_comm] using hscaled

/-- The cap orbit enters the standard summable all-Continue port. -/
theorem nonempty_capPort : Nonempty
    (QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
      (quittingCapLiftedPunishmentFloorOrbit reward source.profile)) := by
  apply nonempty_summableChargeAllContinuePort_of_summable_absorption
  exact source.absorption_summable

/-- The cap limit together with the limiting honest prescribed payoff of the
same literal profile sequence. -/
structure SummableSemanticPort
    (source : QuittingPaidCapLiftedSource reward) where
  capPort :
    QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
      (quittingCapLiftedPunishmentFloorOrbit reward source.profile)
  limit : QuittingTerminalSemanticPair iota
  envelope_eq : limit.2 = capPort.limit
  semantic_tendsto : Tendsto (fun time =>
    quittingTerminalSemanticPair reward
      (quittingCapLiftedPrefixProfile reward source.profile time))
    atTop (nhds limit)
  limit_mem : limit ∈ quittingTerminalSemanticCarrier reward
  selfLoop : quittingTerminalSemanticPrefix reward quittingAllContinueRoot limit =
    limit

/-- Summable cap charge gives a terminal-semantic all-Continue port for the
same finite-depth literal profiles. -/
theorem nonempty_summableSemanticPort :
    Nonempty (SummableSemanticPort source) := by
  obtain ⟨capPort⟩ := source.nonempty_capPort
  let debt : Nat -> iota -> Real := fun time who =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward source.profile time)) who
  let debtLimit : iota -> Real := fun who =>
    sInf (Set.range (fun time => debt time who))
  have hdebtNonneg : ∀ time who, 0 ≤ debt time who := by
    intro time who
    exact quittingTerminalDeviationDebt_nonneg reward
      (quittingCapLiftedPrefixProfile reward source.profile time) who
  have hdebtTendsto : ∀ who,
      Tendsto (fun time => debt time who) atTop (nhds (debtLimit who)) := by
    intro who
    apply tendsto_atTop_ciInf
    · exact source.debt_antitone who
    · exact ⟨0, by
        rintro value ⟨time, rfl⟩
        exact hdebtNonneg time who⟩
  have hdebtLimitNonneg : ∀ who, 0 ≤ debtLimit who := by
    intro who
    exact ge_of_tendsto' (hdebtTendsto who)
      (fun time => hdebtNonneg time who)
  let semanticLimit : QuittingTerminalSemanticPair iota :=
    (fun who => capPort.limit who - debtLimit who, capPort.limit)
  have hsemantic : Tendsto (fun time =>
      quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward source.profile time))
      atTop (nhds semanticLimit) := by
    apply (Prod.tendsto_iff _ _).2
    constructor
    · apply tendsto_pi_nhds.2
      intro who
      have hsub := (capPort.value_tendsto who).sub (hdebtTendsto who)
      apply hsub.congr'
      filter_upwards [] with time
      change
        quittingContinuationBestResponseValue reward
              (quittingCapLiftedPrefixProfile reward source.profile time) who -
            debt time who =
          quittingTerminalPayoff reward
            (quittingCapLiftedPrefixProfile reward source.profile time) who
      simp only [debt, quittingTerminalSemanticDebt,
        quittingTerminalSemanticPair]
      ring
    · apply tendsto_pi_nhds.2
      intro who
      exact capPort.value_tendsto who
  have hmem : semanticLimit ∈ quittingTerminalSemanticCarrier reward := by
    apply isClosed_closure.mem_of_tendsto hsemantic
    filter_upwards [] with time
    apply subset_closure
    exact ⟨quittingCapLiftedPrefixProfile reward source.profile time, rfl⟩
  have hfixed : quittingTerminalSemanticPrefix reward quittingAllContinueRoot
      semanticLimit = semanticLimit := by
    apply quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
    exact capPort.singleton_le
  exact ⟨{
    capPort := capPort
    limit := semanticLimit
    envelope_eq := rfl
    semantic_tendsto := hsemantic
    limit_mem := hmem
    selfLoop := hfixed }⟩

/-- Full cap-lifted output: one summable semantic port and a uniformly
positive paid row on every finite literal prefix. -/
structure SummablePort (source : QuittingPaidCapLiftedSource reward) where
  semanticPort : SummableSemanticPort source
  shiftedRows : ∀ horizon, source.ShiftedPaidRow horizon

/-- The cap lift removes the prescribed-payoff floor hypothesis and produces
the marked summable port unconditionally from a positive semantic minimum. -/
theorem nonempty_summablePort : Nonempty (SummablePort source) := by
  obtain ⟨semanticPort⟩ := source.nonempty_summableSemanticPort
  let shiftedRows : ∀ horizon, source.ShiftedPaidRow horizon := fun horizon =>
    Classical.choice (source.nonempty_shiftedPaidRow horizon)
  exact ⟨⟨semanticPort, shiftedRows⟩⟩

end QuittingPaidCapLiftedSource

namespace QuittingStoppingLawCurvaturePaidWitness

variable {profile : (quittingGame reward).BehaviorProfile}
variable {mover observer : iota}
variable {target : (quittingGame reward).BehaviorStrategy mover}
variable {sourceError endpointError gain : Real}

/-- The actual receiving profile of a curvature-paid witness, lifted to the
positive-minimum cap source without a prescribed-payoff floor assumption. -/
def capLiftedSource
    (carrier : QuittingStoppingLawCurvaturePaidWitness reward profile mover
      observer target sourceError endpointError gain)
    (minimum : QuittingTerminalSemanticPair iota)
    (hminimum : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hgain : 0 < gain) : QuittingPaidCapLiftedSource reward where
  minimum := minimum
  minimum_le := hminimum
  minimum_pos := hminimumPos
  profile := Function.update profile mover target
  observer := observer
  gain := gain
  gain_pos := hgain
  row := carrier.row

/-- Source-facing curvature adapter.  The carrier's source and receiving
near-optimality fields remain available on `carrier`; the shifted rows assert
no new near-optimality statement. -/
theorem nonempty_capLiftedSummablePort
    (carrier : QuittingStoppingLawCurvaturePaidWitness reward profile mover
      observer target sourceError endpointError gain)
    (minimum : QuittingTerminalSemanticPair iota)
    (hminimum : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hgain : 0 < gain) :
    Nonempty (QuittingPaidCapLiftedSource.SummablePort
      (carrier.capLiftedSource minimum hminimum hminimumPos hgain)) :=
  QuittingPaidCapLiftedSource.nonempty_summablePort _

/-- A positive-minimum tangent family supplies the minimum hypotheses of the
cap-lifted curvature adapter directly. -/
theorem nonempty_capLiftedSummablePort_of_tangentFamily
    (carrier : QuittingStoppingLawCurvaturePaidWitness reward profile mover
      observer target sourceError endpointError gain)
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hgain : 0 < gain) :
    Nonempty (QuittingPaidCapLiftedSource.SummablePort
      (carrier.capLiftedSource frontier.base frontier.base_minimum
        frontier.base_positive hgain)) :=
  carrier.nonempty_capLiftedSummablePort frontier.base frontier.base_minimum
    frontier.base_positive hgain

end QuittingStoppingLawCurvaturePaidWitness

end GameTheory
