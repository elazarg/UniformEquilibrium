import UniformEquilibrium.Quitting.Classification.MixedSignTripleCoreSureClassification
import UniformEquilibrium.Quitting.Classification.ParticipantRewardInvariance

/-! # Seven passive-entry changes on the mixed-sign equality stratum

The positive-pair passive singleton payments decrease. The four negative-pair
passive singleton payments and the third player's passive positive-pair payment
increase. Both zero two-opponent differences remain exactly unchanged.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

structure HasWeakMixedSignTripleJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second third : ι) : Prop where
  first_second_nonneg : 0 ≤ quittingPairJoiningGap reward first second
  second_first_nonneg : 0 ≤ quittingPairJoiningGap reward second first
  first_third_nonpos : quittingPairJoiningGap reward first third ≤ 0
  third_first_nonpos : quittingPairJoiningGap reward third first ≤ 0
  second_third_nonpos : quittingPairJoiningGap reward second third ≤ 0
  third_second_nonpos : quittingPairJoiningGap reward third second ≤ 0
  first_triple_zero : quittingTripleJoiningGap reward first second third = 0
  second_triple_zero : quittingTripleJoiningGap reward second first third = 0
  third_triple_nonpos : quittingTripleJoiningGap reward third first second ≤ 0

def mixedSignTriplePassivePerturbation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second third : ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) : ℝ :=
  if player ∈ terminal.val then reward terminal player
  else if terminal.val.card = 1 then
    if (player = first ∧ terminal.val = {second}) ∨
        (player = second ∧ terminal.val = {first}) then reward terminal player - delta
    else if ((player = first ∨ player = second) ∧ terminal.val = {third}) ∨
        (player = third ∧ (terminal.val = {first} ∨ terminal.val = {second})) then
      reward terminal player + delta
    else reward terminal player
  else if player = third ∧ terminal.val = {first, second} then reward terminal player + delta
  else reward terminal player

theorem mixedSignTriplePassivePerturbation_participant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second third : ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) (hmember : player ∈ terminal.val) :
    mixedSignTriplePassivePerturbation reward first second third delta terminal player =
      reward terminal player := by
  simp [mixedSignTriplePassivePerturbation, hmember]

theorem mixedSignTriplePassivePerturbation_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second third : ι) (delta : ℝ) (player : ι) :
    mixedSignTriplePassivePerturbation reward first second third delta
      (quittingSingletonTerminal player) player =
        reward (quittingSingletonTerminal player) player :=
  mixedSignTriplePassivePerturbation_participant reward first second third delta _ player
    (by simp [quittingSingletonTerminal])

theorem mixedSignTriplePassivePerturbation_trap_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second third : ι) (delta : ℝ) (active : Finset ι) :
    IsQuittingPremiumTrap (mixedSignTriplePassivePerturbation reward first second third delta)
        active ↔ IsQuittingPremiumTrap reward active :=
  quittingPremiumTrap_iff_of_participantReward_eq reward _
    (mixedSignTriplePassivePerturbation_participant reward first second third delta) active

theorem mixedSignTriplePassivePerturbation_core [Fintype ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second third : ι) (delta : ℝ) :
    quittingPremiumCore (mixedSignTriplePassivePerturbation reward first second third delta) =
      quittingPremiumCore reward :=
  quittingPremiumCore_eq_of_participantReward_eq reward _
    (mixedSignTriplePassivePerturbation_participant reward first second third delta)

theorem abs_mixedSignTriplePassivePerturbation_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second third : ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) :
    |mixedSignTriplePassivePerturbation reward first second third delta terminal player -
      reward terminal player| ≤ |delta| := by
  unfold mixedSignTriplePassivePerturbation
  split
  · simpa only [sub_self, abs_zero] using abs_nonneg delta
  · split
    · split
      · simp only [sub_sub_cancel_left, abs_neg, le_refl]
      · split
        · simp only [add_sub_cancel_left, le_refl]
        · simpa only [sub_self, abs_zero] using abs_nonneg delta
    · split
      · simp only [add_sub_cancel_left, le_refl]
      · simpa only [sub_self, abs_zero] using abs_nonneg delta

theorem mixedSignTriplePassivePerturbation_strict_of_weak
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second third : ι} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hweak : HasWeakMixedSignTripleJoining reward first second third)
    (delta : ℝ) (hdelta : 0 < delta) :
    HasMixedSignTripleJoining
      (mixedSignTriplePassivePerturbation reward first second third delta) first second third := by
  rcases hweak with ⟨h12, h21, h13, h31, h23, h32, h123, h213, h312⟩
  have hsecondFirst := Ne.symm hfirstSecond
  have hthirdFirst := Ne.symm hfirstThird
  have hthirdSecond := Ne.symm hsecondThird
  constructor <;>
    simp_all [quittingPairJoiningGap, quittingTripleJoiningGap, quittingSingletonTerminal,
      mixedSignTriplePassivePerturbation] <;> linarith

end GameTheory
