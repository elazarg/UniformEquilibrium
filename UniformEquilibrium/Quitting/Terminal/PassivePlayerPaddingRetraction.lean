/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.PassivePlayerPaddingCanonical

/-!
# Constructive retraction for canonical passive-player padding

Canonical passive padding has a literal old-player projection.  A terminal
approximate Nash profile of the padded game bounds fresh-only absorption and
therefore projects quantitatively to the old game against every behavioral
deviation.  This module also constructs the literal quiet lift used in the
forward direction.

The results concern only the canonical padded reward.  They do not project an
arbitrary larger-player table, assume cap attainment, or prove a new
cardinality case.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- Division-free loss multiplier for the canonical projection. -/
def quittingPassivePaddingRetractionMultiplier [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (penalty : ℝ) : ℝ :=
  1 + (Fintype.card J : ℝ) * quittingPassivePaddingWidth reward / penalty

/-- Sharp multiplicative factor retained by the canonical projection. -/
def quittingPassivePaddingRetractionFactor [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (penalty : ℝ) : ℝ :=
  penalty /
    (penalty +
      (Fintype.card J : ℝ) * quittingPassivePaddingWidth reward)

omit [DecidableEq I] [DecidableEq J] in
theorem quittingPassivePaddingRetractionFactor_pos
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty) :
    0 < quittingPassivePaddingRetractionFactor (J := J) reward penalty := by
  unfold quittingPassivePaddingRetractionFactor
  have hplayers : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have hwidth := quittingPassivePaddingWidth_nonneg reward
  positivity

omit [DecidableEq I] [DecidableEq J] in
theorem quittingPassivePaddingRetractionFactor_mul_multiplier
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty) :
    quittingPassivePaddingRetractionFactor (J := J) reward penalty *
        quittingPassivePaddingRetractionMultiplier (J := J) reward penalty =
      1 := by
  unfold quittingPassivePaddingRetractionFactor
    quittingPassivePaddingRetractionMultiplier
  have hplayers : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)
  have hwidth := quittingPassivePaddingWidth_nonneg reward
  have hdenom : 0 < penalty +
      (Fintype.card J : ℝ) * quittingPassivePaddingWidth reward := by
    positivity
  field_simp

omit [DecidableEq I] [DecidableEq J] in
theorem mul_retractionMultiplier_eq_div_retractionFactor
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty) (error : ℝ) :
    error * quittingPassivePaddingRetractionMultiplier (J := J) reward penalty =
      error / quittingPassivePaddingRetractionFactor (J := J) reward penalty := by
  have hfactor := quittingPassivePaddingRetractionFactor_pos
    (J := J) reward hpenalty
  apply (eq_div_iff hfactor.ne').2
  rw [mul_assoc, mul_comm
      (quittingPassivePaddingRetractionMultiplier (J := J) reward penalty),
    quittingPassivePaddingRetractionFactor_mul_multiplier
      (J := J) reward hpenalty]
  ring

/-- Terminal approximate Nash bounds the probability of fresh-only first
absorption by `card J * error / penalty`. -/
theorem quittingPassivePaddingFreshOnlyMass_le_of_isεAsymptoticNash
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty error : ℝ} (hpenalty : 0 < penalty)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty))
        error profile) :
    quittingPassivePaddingFreshOnlyMass
        (quittingProfileLiveRoot
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty)
          profile) 0 ≤
      (Fintype.card J : ℝ) * error / penalty := by
  let paddedReward := quittingPassivePaddingReward (J := J) reward
    (quittingPassivePaddingUpperEndpoint reward) penalty
  let mass := quittingPassivePaddingFreshOnlyMass
    (quittingProfileLiveRoot paddedReward profile) 0
  have hnever : ∀ fresh : J,
      -quittingTerminalPayoff paddedReward profile (.inr fresh) ≤ error := by
    intro fresh
    let never := quittingPureTimeBehaviorStrategy paddedReward
      (.inr fresh) none
    have hstep := hnash (.inr fresh) never
    have hzero :=
      quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero
        (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
        penalty profile fresh
    dsimp only [never, paddedReward] at hstep hzero
    rw [hzero] at hstep
    linarith
  have hsumUpper :
      (∑ fresh : J, -quittingTerminalPayoff paddedReward profile (.inr fresh)) ≤
        (Fintype.card J : ℝ) * error := by
    calc
      (∑ fresh : J,
          -quittingTerminalPayoff paddedReward profile (.inr fresh)) ≤
          ∑ _fresh : J, error := by
            exact Finset.sum_le_sum fun fresh _ => hnever fresh
      _ = (Fintype.card J : ℝ) * error := by simp
  have haggregate :=
    sum_quittingTerminalPayoff_passivePadding_fresh_le
      (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
      hpenalty.le profile
  have hmassScaled : penalty * mass ≤
      ∑ fresh : J, -quittingTerminalPayoff paddedReward profile (.inr fresh) := by
    dsimp only [paddedReward, mass] at haggregate ⊢
    rw [Finset.sum_neg_distrib]
    linarith
  apply (le_div_iff₀ hpenalty).2
  simpa [mul_comm] using hmassScaled.trans hsumUpper

/-- Division-free quantitative projection against every unilateral old-player
behavioral deviation. -/
theorem isεAsymptoticNash_project_passivePadding_mul
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty error : ℝ} (hpenalty : 0 < penalty) (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty))
        error profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (error * quittingPassivePaddingRetractionMultiplier
        (J := J) reward penalty)
      (quittingPassivePaddingProjectProfile reward profile) := by
  intro who deviation
  let paddedReward := quittingPassivePaddingReward (J := J) reward
    (quittingPassivePaddingUpperEndpoint reward) penalty
  let projected := quittingPassivePaddingProjectProfile reward profile
  let mass := quittingPassivePaddingFreshOnlyMass
    (quittingProfileLiveRoot paddedReward profile) 0
  have herrorNonneg : 0 ≤ error := herror
  have hmass := quittingPassivePaddingFreshOnlyMass_le_of_isεAsymptoticNash
    (J := J) reward hpenalty profile hnash
  have hbase := quittingTerminalPayoff_passivePadding_old
    (J := J) reward (quittingPassivePaddingUpperEndpoint reward) penalty
    profile who (quittingPassivePaddingLowerEndpoint_nonpos reward who)
    (quittingPassivePaddingUpperEndpoint_nonneg reward who)
    (fun terminal =>
      quittingPassivePaddingReward_mem_canonicalInterval reward terminal who)
  have hwidth := quittingPassivePaddingCoordinateWidth_le_width reward who
  have hwidthNonneg := quittingPassivePaddingWidth_nonneg reward
  have hdev := quittingTerminalPayoff_update_passivePadding_old_ge
    (J := J) reward (quittingPassivePaddingUpperEndpoint reward) penalty
    profile who deviation
    (quittingPassivePaddingLowerEndpoint_nonpos reward who)
    (quittingPassivePaddingUpperEndpoint_nonneg reward who)
    (fun terminal =>
      quittingPassivePaddingReward_mem_canonicalInterval reward terminal who)
  have hpaddedNash := hnash (.inl who)
    (quittingPassivePaddingLiftOldDeviation (J := J) reward
      (quittingPassivePaddingUpperEndpoint reward) penalty deviation)
  have hmassWidth : quittingPassivePaddingWidth reward * mass ≤
      quittingPassivePaddingWidth reward *
        ((Fintype.card J : ℝ) * error / penalty) :=
    mul_le_mul_of_nonneg_left hmass hwidthNonneg
  dsimp only [paddedReward, projected, mass] at hbase hdev hpaddedNash
  unfold quittingPassivePaddingRetractionMultiplier
  calc
    quittingTerminalPayoff reward
        (Function.update
          (quittingPassivePaddingProjectProfile reward profile) who deviation)
        who ≤
      quittingTerminalPayoff paddedReward
        (Function.update profile (.inl who)
          (quittingPassivePaddingLiftOldDeviation
            (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
              penalty deviation)) (.inl who) := hdev
    _ ≤ quittingTerminalPayoff paddedReward profile (.inl who) + error :=
      hpaddedNash
    _ ≤ quittingTerminalPayoff reward
          (quittingPassivePaddingProjectProfile reward profile) who +
        error + quittingPassivePaddingWidth reward * mass := by
      have hcoordinate :
          quittingPassivePaddingUpperEndpoint reward who -
              quittingPassivePaddingLowerEndpoint reward who =
            quittingPassivePaddingCoordinateWidth reward who := rfl
      rw [hcoordinate] at hbase
      nlinarith [mul_le_mul_of_nonneg_right hwidth
        (quittingPassivePaddingFreshOnlyMass_nonneg
          (quittingProfileLiveRoot paddedReward profile) 0)]
    _ ≤ quittingTerminalPayoff reward
          (quittingPassivePaddingProjectProfile reward profile) who +
        error * (1 +
          (Fintype.card J : ℝ) * quittingPassivePaddingWidth reward /
            penalty) := by
      calc
        _ ≤ quittingTerminalPayoff reward
              (quittingPassivePaddingProjectProfile reward profile) who +
            error + quittingPassivePaddingWidth reward *
              ((Fintype.card J : ℝ) * error / penalty) := by
          nlinarith [herrorNonneg]
        _ = _ := by ring

/-- Ratio form of quantitative projection against every unilateral
behavioral deviation. -/
theorem isεAsymptoticNash_project_passivePadding
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty error : ℝ} (hpenalty : 0 < penalty) (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty))
        error profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (error /
        quittingPassivePaddingRetractionFactor (J := J) reward penalty)
      (quittingPassivePaddingProjectProfile reward profile) := by
  rw [← mul_retractionMultiplier_eq_div_retractionFactor
    (J := J) reward hpenalty]
  exact isεAsymptoticNash_project_passivePadding_mul
    (J := J) reward hpenalty herror profile hnash

/-- Division-free target-error projection on every old coordinate. -/
theorem terminalTargetError_project_passivePadding_mul
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty error : ℝ} (hpenalty : 0 < penalty)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty))
        error profile)
    (target : Payoff (I ⊕ J))
    (hclose : ∀ who : I,
      |quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty)
          profile (.inl who) - target (.inl who)| ≤ error) :
    ∀ who : I,
      |quittingTerminalPayoff reward
          (quittingPassivePaddingProjectProfile reward profile) who -
        target (.inl who)| ≤
      error * quittingPassivePaddingRetractionMultiplier
        (J := J) reward penalty := by
  intro who
  let paddedReward := quittingPassivePaddingReward (J := J) reward
    (quittingPassivePaddingUpperEndpoint reward) penalty
  let padded := quittingTerminalPayoff paddedReward profile (.inl who)
  let old := quittingTerminalPayoff reward
    (quittingPassivePaddingProjectProfile reward profile) who
  let mass := quittingPassivePaddingFreshOnlyMass
    (quittingProfileLiveRoot paddedReward profile) 0
  have hmass := quittingPassivePaddingFreshOnlyMass_le_of_isεAsymptoticNash
    (J := J) reward hpenalty profile hnash
  have hbase := quittingTerminalPayoff_passivePadding_old
    (J := J) reward (quittingPassivePaddingUpperEndpoint reward) penalty
    profile who (quittingPassivePaddingLowerEndpoint_nonpos reward who)
    (quittingPassivePaddingUpperEndpoint_nonneg reward who)
    (fun terminal ↦
      quittingPassivePaddingReward_mem_canonicalInterval reward terminal who)
  have hcoordinate :
      quittingPassivePaddingUpperEndpoint reward who -
          quittingPassivePaddingLowerEndpoint reward who =
        quittingPassivePaddingCoordinateWidth reward who := rfl
  rw [hcoordinate] at hbase
  have hmassNonneg : 0 ≤ mass :=
    quittingPassivePaddingFreshOnlyMass_nonneg
      (quittingProfileLiveRoot paddedReward profile) 0
  have hcoordinateWidth :
      quittingPassivePaddingCoordinateWidth reward who * mass ≤
        quittingPassivePaddingWidth reward * mass :=
    mul_le_mul_of_nonneg_right
      (quittingPassivePaddingCoordinateWidth_le_width reward who) hmassNonneg
  have hmassWidth : quittingPassivePaddingWidth reward * mass ≤
      quittingPassivePaddingWidth reward *
        ((Fintype.card J : ℝ) * error / penalty) :=
    mul_le_mul_of_nonneg_left hmass
      (quittingPassivePaddingWidth_nonneg reward)
  have htriangle : |old - target (.inl who)| ≤
      |padded - target (.inl who)| + |padded - old| := by
    calc
      |old - target (.inl who)| =
          |(padded - target (.inl who)) - (padded - old)| := by
        congr 1
        ring
      _ ≤ |padded - target (.inl who)| + |padded - old| := abs_sub _ _
  have habsBase : |padded - old| = padded - old := abs_of_nonneg hbase.1
  dsimp only [paddedReward, padded, old, mass] at hbase hmassWidth htriangle ⊢
  unfold quittingPassivePaddingRetractionMultiplier
  rw [habsBase] at htriangle
  calc
    _ ≤ |quittingTerminalPayoff
            (quittingPassivePaddingReward (J := J) reward
              (quittingPassivePaddingUpperEndpoint reward) penalty)
            profile (.inl who) - target (.inl who)| +
          (quittingTerminalPayoff
            (quittingPassivePaddingReward (J := J) reward
              (quittingPassivePaddingUpperEndpoint reward) penalty)
            profile (.inl who) -
          quittingTerminalPayoff reward
            (quittingPassivePaddingProjectProfile reward profile) who) :=
      htriangle
    _ ≤ error + quittingPassivePaddingWidth reward *
          quittingPassivePaddingFreshOnlyMass
            (quittingProfileLiveRoot
              (quittingPassivePaddingReward (J := J) reward
                (quittingPassivePaddingUpperEndpoint reward) penalty)
              profile) 0 := by
      exact add_le_add (hclose who)
        (hbase.2.trans hcoordinateWidth)
    _ ≤ error + quittingPassivePaddingWidth reward *
          ((Fintype.card J : ℝ) * error / penalty) := by
      linarith
    _ = error * (1 +
          (Fintype.card J : ℝ) * quittingPassivePaddingWidth reward /
            penalty) := by
      field_simp

/-- Ratio form of old-coordinate target-error projection. -/
theorem terminalTargetError_project_passivePadding
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty error : ℝ} (hpenalty : 0 < penalty)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty))
        error profile)
    (target : Payoff (I ⊕ J))
    (hclose : ∀ who : I,
      |quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty)
          profile (.inl who) - target (.inl who)| ≤ error) :
    ∀ who : I,
      |quittingTerminalPayoff reward
          (quittingPassivePaddingProjectProfile reward profile) who -
        target (.inl who)| ≤
      error / quittingPassivePaddingRetractionFactor
        (J := J) reward penalty := by
  rw [← mul_retractionMultiplier_eq_div_retractionFactor
    (J := J) reward hpenalty]
  exact terminalTargetError_project_passivePadding_mul
    (J := J) reward hpenalty profile hnash target hclose

/-! ## Literal quiet lift -/

/-- Lift an old profile by retaining its live old roots and making every
fresh player Continue surely at every live date. -/
def quittingPassivePaddingQuietProfile [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) :
    (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)).BehaviorProfile :=
  quittingRootSequenceProfile
    (quittingPassivePaddingReward (J := J) reward
      (quittingPassivePaddingUpperEndpoint reward) penalty)
    (fun time ↦ Sum.elim (quittingProfileLiveRoot reward profile time)
      (fun _ ↦ PMF.pure false)) 0

@[simp] theorem quittingProfileLiveRoot_passivePaddingQuietProfile
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingProfileLiveRoot
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (quittingPassivePaddingQuietProfile (J := J) reward penalty profile) =
      fun time ↦ Sum.elim (quittingProfileLiveRoot reward profile time)
        (fun _ ↦ PMF.pure false) := by
  apply quittingProfileLiveRoot_quittingRootSequenceProfile_zero

@[simp] theorem quittingPassivePaddingProjectProfile_quietProfile_liveRoot
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingProfileLiveRoot reward
        (quittingPassivePaddingProjectProfile reward
          (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)) =
      quittingProfileLiveRoot reward profile := by
  rw [quittingProfileLiveRoot_passivePaddingProjectProfile,
    quittingProfileLiveRoot_passivePaddingQuietProfile]
  rfl

theorem quittingTerminalPayoff_passivePadding_fresh_nonpos
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) {penalty : ℝ} (hpenalty : 0 ≤ penalty)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile)
    (fresh : J) :
    quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        profile (.inr fresh) ≤ 0 := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  apply tsum_nonpos
  intro offset
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact quittingJointSurvivalWeight_nonneg _ 0 offset
  · let roots := quittingProfileLiveRoot
        (quittingPassivePaddingReward (J := J) reward upper penalty) profile
    have hroot : roots offset = Sum.elim
        (quittingPassivePaddingOldRoots roots offset)
        (quittingPassivePaddingFreshRoots roots offset) := by
      funext player
      cases player <;> rfl
    simp only [Nat.zero_add]
    change quittingRootAbsorbingContribution
      (quittingPassivePaddingReward (J := J) reward upper penalty)
      (roots offset) (.inr fresh) ≤ 0
    rw [hroot,
      quittingRootAbsorbingContribution_passivePadding_fresh]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpenalty)
        (quittingStationaryContinueMass_nonneg _)) ENNReal.toReal_nonneg

theorem quittingPassivePaddingFreshOnlyMass_quietProfile_eq_zero
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingPassivePaddingFreshOnlyMass
        (quittingProfileLiveRoot
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty)
          (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)) 0 =
      0 := by
  unfold quittingPassivePaddingFreshOnlyMass
  calc
    ∑' offset, quittingPassivePaddingFreshOnlyStageMass
        (quittingProfileLiveRoot
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty)
          (quittingPassivePaddingQuietProfile (J := J) reward penalty profile))
        0 offset = ∑' _offset : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro offset
      rw [quittingProfileLiveRoot_passivePaddingQuietProfile]
      unfold quittingPassivePaddingFreshOnlyStageMass
        quittingPassivePaddingFreshRoots quittingRootAbsorptionMass
      apply mul_eq_zero_of_right
      change 1 - quittingStationaryContinueMass
        (quittingAllContinueRoot : J → PMF Bool) = 0
      rw [quittingStationaryContinueMass_allContinueRoot]
      ring
    _ = 0 := tsum_zero

/-- Updating an old coordinate of the quiet lift still leaves zero probability
of fresh-only absorption. -/
theorem quittingPassivePaddingFreshOnlyMass_update_quietProfile_old_eq_zero
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : I)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingPassivePaddingFreshOnlyMass
        (quittingProfileLiveRoot
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty)
          (Function.update
            (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
            (.inl who)
            (quittingPassivePaddingLiftOldDeviation
              (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
                penalty deviation))) 0 = 0 := by
  unfold quittingPassivePaddingFreshOnlyMass
  calc
    ∑' offset, quittingPassivePaddingFreshOnlyStageMass
        (quittingProfileLiveRoot
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty)
          (Function.update
            (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
            (.inl who)
            (quittingPassivePaddingLiftOldDeviation
              (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
                penalty deviation))) 0 offset =
      ∑' _offset : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro offset
      unfold quittingPassivePaddingFreshOnlyStageMass
      apply mul_eq_zero_of_right
      unfold quittingRootAbsorptionMass quittingPassivePaddingFreshRoots
      rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
        quittingProfileLiveRoot_passivePaddingQuietProfile]
      change 1 - quittingStationaryContinueMass
        (quittingAllContinueRoot : J → PMF Bool) = 0
      rw [quittingStationaryContinueMass_allContinueRoot]
      ring
    _ = 0 := tsum_zero

/-- The quiet lift preserves every old player's terminal payoff exactly. -/
theorem quittingTerminalPayoff_passivePaddingQuietProfile_old_eq
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : I) :
    quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
        (.inl who) =
      quittingTerminalPayoff reward profile who := by
  have hcoupling := quittingTerminalPayoff_passivePadding_old
    (J := J) reward (quittingPassivePaddingUpperEndpoint reward) penalty
    (quittingPassivePaddingQuietProfile (J := J) reward penalty profile) who
    (quittingPassivePaddingLowerEndpoint_nonpos reward who)
    (quittingPassivePaddingUpperEndpoint_nonneg reward who)
    (fun terminal ↦
      quittingPassivePaddingReward_mem_canonicalInterval reward terminal who)
  rw [quittingPassivePaddingFreshOnlyMass_quietProfile_eq_zero] at hcoupling
  have hproject : quittingTerminalPayoff reward
      (quittingPassivePaddingProjectProfile reward
        (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)) who =
      quittingTerminalPayoff reward profile who := by
    simp only [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
      quittingPassivePaddingProjectProfile_quietProfile_liveRoot]
  dsimp only at hcoupling
  rw [hproject] at hcoupling
  nlinarith

/-- Every fresh coordinate of the quiet lift has terminal payoff zero. -/
theorem quittingTerminalPayoff_passivePaddingQuietProfile_fresh_eq_zero
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (fresh : J) :
    quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
        (.inr fresh) = 0 := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_passivePaddingQuietProfile,
    quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  calc
    ∑' offset, quittingJointSurvivalWeight
          (fun time ↦ Sum.elim (quittingProfileLiveRoot reward profile time)
            (fun _ ↦ PMF.pure false)) 0 offset *
        quittingRootAbsorbingContribution
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty)
          (Sum.elim (quittingProfileLiveRoot reward profile (0 + offset))
            (fun _ ↦ PMF.pure false)) (.inr fresh) =
        ∑' _offset : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro offset
      apply mul_eq_zero_of_right
      rw [quittingRootAbsorbingContribution_passivePadding_fresh]
      simp
    _ = 0 := tsum_zero

/-- Project an arbitrary padded old-player deviation by replaying its live-path
hazard in the old game. -/
def quittingPassivePaddingProjectOldDeviation
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) {who : I}
    (deviation : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty))
        |>.BehaviorStrategy (.inl who)) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time _history ↦ quittingBehaviorLiveHazard
    (quittingPassivePaddingReward (J := J) reward upper penalty) deviation time

@[simp] theorem quittingBehaviorLiveHazard_passivePaddingProjectOldDeviation
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ) {who : I}
    (deviation : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty))
        |>.BehaviorStrategy (.inl who)) :
    quittingBehaviorLiveHazard reward
        (quittingPassivePaddingProjectOldDeviation
          (J := J) reward upper penalty deviation) =
      quittingBehaviorLiveHazard
        (quittingPassivePaddingReward (J := J) reward upper penalty)
        deviation := by
  rfl

/-- Against the quiet lift, lifting an arbitrary old behavioral deviation
preserves that deviator's terminal payoff exactly. -/
theorem quittingTerminalPayoff_update_passivePaddingQuietProfile_liftOld_eq
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : I)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (Function.update
          (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
          (.inl who)
          (quittingPassivePaddingLiftOldDeviation
            (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
              penalty deviation)) (.inl who) =
      quittingTerminalPayoff reward (Function.update profile who deviation) who := by
  let paddedReward := quittingPassivePaddingReward (J := J) reward
    (quittingPassivePaddingUpperEndpoint reward) penalty
  let paddedProfile := Function.update
    (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
    (.inl who)
    (quittingPassivePaddingLiftOldDeviation
      (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
        penalty deviation)
  have hcoupling := quittingTerminalPayoff_passivePadding_old
    (J := J) reward (quittingPassivePaddingUpperEndpoint reward) penalty
    paddedProfile who (quittingPassivePaddingLowerEndpoint_nonpos reward who)
    (quittingPassivePaddingUpperEndpoint_nonneg reward who)
    (fun terminal ↦
      quittingPassivePaddingReward_mem_canonicalInterval reward terminal who)
  have hmass : quittingPassivePaddingFreshOnlyMass
      (quittingProfileLiveRoot paddedReward paddedProfile) 0 = 0 := by
    exact quittingPassivePaddingFreshOnlyMass_update_quietProfile_old_eq_zero
      (J := J) reward penalty profile who deviation
  have hproject : quittingTerminalPayoff reward
      (quittingPassivePaddingProjectProfile reward paddedProfile) who =
      quittingTerminalPayoff reward (Function.update profile who deviation) who := by
    simp only [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
      quittingProfileLiveRoot_passivePaddingProjectProfile]
    congr 1
    funext time old
    rw [show paddedProfile = Function.update
      (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
      (.inl who)
      (quittingPassivePaddingLiftOldDeviation
        (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
          penalty deviation) by rfl,
      quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
      quittingProfileLiveRoot_passivePaddingQuietProfile,
      quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
    unfold quittingPassivePaddingOldRoots quittingRootSequenceUpdate
    by_cases hold : old = who
    · subst old
      simp
    · simp [Function.update_of_ne hold]
  dsimp only [paddedReward, paddedProfile] at hcoupling hmass hproject ⊢
  rw [hmass, hproject] at hcoupling
  nlinarith

/-- Every arbitrary padded old-player behavioral deviation against the quiet
lift has exactly the payoff of its live-hazard projection in the old game. -/
theorem quittingTerminalPayoff_update_passivePaddingQuietProfile_old_eq
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : I)
    (deviation : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
        |>.BehaviorStrategy (.inl who)) :
    quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (Function.update
          (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
          (.inl who) deviation) (.inl who) =
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPassivePaddingProjectOldDeviation
            (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
              penalty deviation)) who := by
  let oldDeviation := quittingPassivePaddingProjectOldDeviation
    (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
      penalty deviation
  have hlive : quittingBehaviorLiveHazard
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)
      deviation =
      quittingBehaviorLiveHazard
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (quittingPassivePaddingLiftOldDeviation
          (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
            penalty oldDeviation) := by
    rw [quittingBehaviorLiveHazard_passivePaddingLiftOldDeviation]
    exact (quittingBehaviorLiveHazard_passivePaddingProjectOldDeviation
      (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
        penalty deviation).symm
  calc
    _ = quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (Function.update
          (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
          (.inl who)
          (quittingPassivePaddingLiftOldDeviation
            (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
              penalty oldDeviation)) (.inl who) := by
      rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
        quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
        hlive]
    _ = _ := quittingTerminalPayoff_update_passivePaddingQuietProfile_liftOld_eq
      (J := J) reward penalty profile who oldDeviation

/-- The quiet lift preserves terminal approximate Nash against every arbitrary
behavioral deviation of both old and fresh players. -/
theorem isεAsymptoticNash_passivePaddingQuietProfile
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty error : ℝ} (hpenalty : 0 ≤ penalty) (herror : 0 ≤ error)
    (profile : (quittingGame reward).BehaviorProfile)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error profile) :
    (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty))
        error
        (quittingPassivePaddingQuietProfile (J := J) reward penalty profile) := by
  intro player deviation
  cases player with
  | inl who =>
      rw [quittingTerminalPayoff_passivePaddingQuietProfile_old_eq,
        quittingTerminalPayoff_update_passivePaddingQuietProfile_old_eq]
      exact hnash who
        (quittingPassivePaddingProjectOldDeviation
          (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
            penalty deviation)
  | inr fresh =>
      rw [quittingTerminalPayoff_passivePaddingQuietProfile_fresh_eq_zero]
      have hdeviation := quittingTerminalPayoff_passivePadding_fresh_nonpos
        (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
        hpenalty
        (Function.update
          (quittingPassivePaddingQuietProfile (J := J) reward penalty profile)
          (.inr fresh) deviation) fresh
      linarith

/-- The entire quiet-lift terminal payoff is the old payoff extended by zero
on the fresh coordinates. -/
theorem quittingTerminalPayoff_passivePaddingQuietProfile_eq_sumElim
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (quittingPassivePaddingQuietProfile (J := J) reward penalty profile) =
      Sum.elim (quittingTerminalPayoff reward profile) (fun _ ↦ 0) := by
  funext player
  cases player with
  | inl who =>
      exact quittingTerminalPayoff_passivePaddingQuietProfile_old_eq
        (J := J) reward penalty profile who
  | inr fresh =>
      exact quittingTerminalPayoff_passivePaddingQuietProfile_fresh_eq_zero
        (J := J) reward penalty profile fresh

end GameTheory
