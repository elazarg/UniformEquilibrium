/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.GeneralTotalVariation
import UniformEquilibrium.Quitting.Paths.StoppingLawMixture

/-!
# Payoff gain and finite stopping mass

A bounded unilateral payoff separates two complete stopping laws by at most
twice the reward bound times their total variation.  Since a stopping law has
only one non-finite atom, that variation is at most the sum of the two
probabilities of ever quitting.  Consequently every profitable radial
stopping-law mixture carries a quantitative amount of finite stopping mass.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open Math.Probability.DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Probability that a Boolean hazard eventually quits at a finite date. -/
def quittingHazardEverQuitMass (hazard : Nat -> PMF Bool) : Real :=
  1 - quittingHazardNeverMass hazard

/-- Probability that a behavioral quitting strategy eventually quits on the
live spine. -/
def quittingBehaviorEverQuitMass
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    {who : iota} (strategy : (quittingGame reward).BehaviorStrategy who) : Real :=
  quittingHazardEverQuitMass (quittingBehaviorLiveHazard reward strategy)

theorem quittingHazardEverQuitMass_nonneg (hazard : Nat -> PMF Bool) :
    0 <= quittingHazardEverQuitMass hazard := by
  unfold quittingHazardEverQuitMass
  exact sub_nonneg.mpr <| by
    simpa using quittingHazardNeverMass_le_survival hazard 0

omit [DecidableEq iota] in
theorem quittingBehaviorEverQuitMass_nonneg
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    {who : iota} (strategy : (quittingGame reward).BehaviorStrategy who) :
    0 <= quittingBehaviorEverQuitMass reward strategy :=
  quittingHazardEverQuitMass_nonneg _

/-- Payoff gain from replacing one player's complete stopping law is bounded
by total variation of the two induced stopping laws. -/
theorem quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    {M : Real} (hreward : forall terminal player, |reward terminal player| <= M) :
    quittingTerminalPayoff reward (Function.update profile who target) who -
        quittingTerminalPayoff reward (Function.update profile who source) who <=
      2 * M * pmfGeneralTV
        (quittingBehaviorStoppingLaw reward source)
        (quittingBehaviorStoppingLaw reward target) := by
  let value : Option Nat -> Real := fun choice =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hvalue : forall choice, |value choice| <= M := by
    intro choice
    exact abs_quittingTerminalPayoff_le reward _ who hreward
  rw [quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime,
    quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime]
  have hbound := abs_expect_sub_le_two_mul_bound_mul_pmfGeneralTV
    (quittingBehaviorStoppingLaw reward target)
    (quittingBehaviorStoppingLaw reward source) value hvalue
  rw [pmfGeneralTV_symm] at hbound
  exact (le_abs_self _).trans hbound

omit [DecidableEq iota] in
/-- Total variation of two stopping laws is at most the sum of their finite
stopping masses. -/
theorem stoppingLawTV_le_everQuitMass_add
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    {who : iota}
    (source target : (quittingGame reward).BehaviorStrategy who) :
    pmfGeneralTV
        (quittingBehaviorStoppingLaw reward source)
        (quittingBehaviorStoppingLaw reward target) <=
      quittingBehaviorEverQuitMass reward source +
        quittingBehaviorEverQuitMass reward target := by
  simpa [quittingBehaviorEverQuitMass, quittingHazardEverQuitMass] using
    (pmfGeneralTV_le_one_sub_apply_add_one_sub_apply
      (quittingBehaviorStoppingLaw reward source)
      (quittingBehaviorStoppingLaw reward target) none)

omit [DecidableEq iota] in
/-- Ever-quit mass is affine under complete stopping-law mixing. -/
theorem quittingBehaviorEverQuitMass_stoppingLawMixture
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : Real) (hlambda0 : 0 <= lambda) (hlambda1 : lambda <= 1) :
    quittingBehaviorEverQuitMass reward
        (quittingStoppingLawMixtureBehaviorStrategy reward who source target
          lambda hlambda0 hlambda1) =
      (1 - lambda) * quittingBehaviorEverQuitMass reward source +
        lambda * quittingBehaviorEverQuitMass reward target := by
  have hlaw := congrArg
    (fun law : PMF (Option Nat) => (law none).toReal)
    (quittingBehaviorStoppingLaw_stoppingLawMixture
      reward who source target lambda hlambda0 hlambda1)
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum,
    Fintype.sum_bool] at hlaw
  simp only [mixtureCoin_false_toReal, mixtureCoin_true_toReal,
    Bool.false_eq_true, ↓reduceIte,
    quittingBehaviorStoppingLaw_none_toReal] at hlaw
  unfold quittingBehaviorEverQuitMass quittingHazardEverQuitMass
  linarith

/-- A profitable radial mixture of effective weight at most one half carries
finite stopping mass proportional to that weight and gain. -/
theorem radialEverQuitMass_ge_weight_mul_gain_div
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (weight gain M : Real)
    (hweight0 : 0 <= weight) (hweightHalf : weight <= 1 / 2)
    (hM : 0 < M)
    (hreward : forall terminal player, |reward terminal player| <= M)
    (hgain : gain <=
      quittingTerminalPayoff reward (Function.update profile who target) who -
        quittingTerminalPayoff reward (Function.update profile who source) who) :
    weight * gain / (2 * M) <=
      quittingBehaviorEverQuitMass reward
        (quittingStoppingLawMixtureBehaviorStrategy reward who source target
          weight hweight0 (hweightHalf.trans (by norm_num))) := by
  let sourceMass := quittingBehaviorEverQuitMass reward source
  let targetMass := quittingBehaviorEverQuitMass reward target
  have hvariation :=
    quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV
      reward profile who source target hreward
  have htv := stoppingLawTV_le_everQuitMass_add reward source target
  have hgainMass : gain <= 2 * M * (sourceMass + targetMass) := by
    calc
      gain <= quittingTerminalPayoff reward
            (Function.update profile who target) who -
          quittingTerminalPayoff reward
            (Function.update profile who source) who := hgain
      _ <= 2 * M * pmfGeneralTV
            (quittingBehaviorStoppingLaw reward source)
            (quittingBehaviorStoppingLaw reward target) := hvariation
      _ <= 2 * M * (sourceMass + targetMass) := by
        exact mul_le_mul_of_nonneg_left htv (by positivity)
  have hsourceMass : 0 <= sourceMass :=
    quittingBehaviorEverQuitMass_nonneg reward source
  have htargetMass : 0 <= targetMass :=
    quittingBehaviorEverQuitMass_nonneg reward target
  rw [quittingBehaviorEverQuitMass_stoppingLawMixture]
  have hweightComplement : weight <= 1 - weight := by linarith
  have hmixedLower :
      weight * (sourceMass + targetMass) <=
        (1 - weight) * sourceMass + weight * targetMass := by
    nlinarith [mul_le_mul_of_nonneg_right hweightComplement hsourceMass]
  have hscaled : weight * gain <=
      weight * (2 * M * (sourceMass + targetMass)) :=
    mul_le_mul_of_nonneg_left hgainMass hweight0
  apply (div_le_iff₀ (by positivity : 0 < 2 * M)).2
  calc
    weight * gain <= weight * (2 * M * (sourceMass + targetMass)) := hscaled
    _ = (weight * (sourceMass + targetMass)) * (2 * M) := by ring
    _ <= ((1 - weight) * sourceMass + weight * targetMass) * (2 * M) :=
      mul_le_mul_of_nonneg_right hmixedLower (by positivity)

/-- The nested radial reset has effective endpoint weight
`outerWeight * innerWeight`.  Its finite stopping mass obeys the same gain
bound at that effective weight. -/
theorem nestedRadialEverQuitMass_ge_weight_mul_gain_div
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (outerWeight innerWeight gain M : Real)
    (houter0 : 0 <= outerWeight) (houter1 : outerWeight <= 1)
    (hinner0 : 0 <= innerWeight) (hinner1 : innerWeight <= 1)
    (heffectiveHalf : outerWeight * innerWeight <= 1 / 2)
    (hM : 0 < M)
    (hreward : forall terminal player, |reward terminal player| <= M)
    (hgain : gain <=
      quittingTerminalPayoff reward (Function.update profile who target) who -
        quittingTerminalPayoff reward (Function.update profile who source) who) :
    outerWeight * innerWeight * gain / (2 * M) <=
      quittingBehaviorEverQuitMass reward
        (quittingStoppingLawMixtureBehaviorStrategy reward who source
          (quittingStoppingLawMixtureBehaviorStrategy reward who source target
            innerWeight hinner0 hinner1)
          outerWeight houter0 houter1) := by
  let sourceMass := quittingBehaviorEverQuitMass reward source
  let targetMass := quittingBehaviorEverQuitMass reward target
  have hvariation :=
    quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV
      reward profile who source target hreward
  have htv := stoppingLawTV_le_everQuitMass_add reward source target
  have hgainMass : gain <= 2 * M * (sourceMass + targetMass) := by
    calc
      gain <= quittingTerminalPayoff reward
            (Function.update profile who target) who -
          quittingTerminalPayoff reward
            (Function.update profile who source) who := hgain
      _ <= 2 * M * pmfGeneralTV
            (quittingBehaviorStoppingLaw reward source)
            (quittingBehaviorStoppingLaw reward target) := hvariation
      _ <= 2 * M * (sourceMass + targetMass) := by
        exact mul_le_mul_of_nonneg_left htv (by positivity)
  have hsourceMass : 0 <= sourceMass :=
    quittingBehaviorEverQuitMass_nonneg reward source
  have heffective0 : 0 <= outerWeight * innerWeight :=
    mul_nonneg houter0 hinner0
  rw [quittingBehaviorEverQuitMass_stoppingLawMixture,
    quittingBehaviorEverQuitMass_stoppingLawMixture]
  have heffectiveComplement :
      outerWeight * innerWeight <= 1 - outerWeight * innerWeight := by
    linarith
  have hmixedIdentity :
      (1 - outerWeight) * sourceMass +
          outerWeight * ((1 - innerWeight) * sourceMass +
            innerWeight * targetMass) =
        (1 - outerWeight * innerWeight) * sourceMass +
          (outerWeight * innerWeight) * targetMass := by ring
  rw [hmixedIdentity]
  have hmixedLower :
      (outerWeight * innerWeight) * (sourceMass + targetMass) <=
        (1 - outerWeight * innerWeight) * sourceMass +
          (outerWeight * innerWeight) * targetMass := by
    nlinarith [mul_le_mul_of_nonneg_right heffectiveComplement hsourceMass]
  have hscaled : outerWeight * innerWeight * gain <=
      (outerWeight * innerWeight) *
        (2 * M * (sourceMass + targetMass)) :=
    mul_le_mul_of_nonneg_left hgainMass heffective0
  apply (div_le_iff₀ (by positivity : 0 < 2 * M)).2
  calc
    outerWeight * innerWeight * gain <=
        (outerWeight * innerWeight) *
          (2 * M * (sourceMass + targetMass)) := hscaled
    _ = ((outerWeight * innerWeight) *
          (sourceMass + targetMass)) * (2 * M) := by ring
    _ <= ((1 - outerWeight * innerWeight) * sourceMass +
          (outerWeight * innerWeight) * targetMass) * (2 * M) :=
      mul_le_mul_of_nonneg_right hmixedLower (by positivity)

end GameTheory
