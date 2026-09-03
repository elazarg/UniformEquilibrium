/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.LiteralRootStackSurvival

/-!
# Transporting a behavioral deviation through a literal root prefix

A deviation may copy its prescribed marginal through a finite root word and
then change only the reached suffix.  The resulting actual-profile gain is
exactly the suffix gain multiplied by the joint survival of the word.  These
are profile and payoff identities; no Nash, compactness, or player-count
hypothesis is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The behavior strategy which copies one player's displayed marginal
through a literal root word and then uses a supplied suffix deviation. -/
def quittingCopyLiteralRootStackThenDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).BehaviorStrategy who :=
  match roots with
  | [] => deviation
  | root :: remaining =>
      quittingRootAndContinuationDeviation reward (root who)
        (quittingCopyLiteralRootStackThenDeviation reward remaining who
          deviation)

omit [DecidableEq ι] in
@[simp] theorem quittingCopyLiteralRootStackThenDeviation_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingCopyLiteralRootStackThenDeviation reward [] who deviation =
      deviation := rfl

omit [DecidableEq ι] in
@[simp] theorem quittingCopyLiteralRootStackThenDeviation_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingCopyLiteralRootStackThenDeviation reward (root :: roots) who
        deviation =
      quittingRootAndContinuationDeviation reward (root who)
        (quittingCopyLiteralRootStackThenDeviation reward roots who
          deviation) := rfl

/-- Updating the prefixed profile by the copy-then-deviate strategy changes
exactly the suffix strategy. -/
theorem update_quittingLiteralRootStackProfile_copyThenDeviation_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    Function.update
        (quittingLiteralRootStackProfile reward roots terminal) who
        (quittingCopyLiteralRootStackThenDeviation reward roots who
          deviation) =
      quittingLiteralRootStackProfile reward roots
        (Function.update terminal who deviation) := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      rw [quittingLiteralRootStackProfile_cons,
        quittingCopyLiteralRootStackThenDeviation_cons,
        update_quittingRootThenContinuationProfile_eq,
        Function.update_eq_self, ih,
        quittingLiteralRootStackProfile_cons]

omit [DecidableEq ι] in
/-- Changing only the suffix behind a literal root word changes every
prescribed payoff coordinate by joint survival times the suffix change. -/
theorem quittingTerminalPayoff_literalRootStackProfile_sub_eq_jointSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots first) who -
        quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots second) who =
      quittingLiteralRootStackJointSurvival roots *
        (quittingTerminalPayoff reward first who -
          quittingTerminalPayoff reward second who) := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      rw [quittingLiteralRootStackProfile_cons,
        quittingLiteralRootStackProfile_cons,
        quittingTerminalPayoff_rootThenContinuation_eq,
        quittingTerminalPayoff_rootThenContinuation_eq,
        quittingRootExpectedPayoff_eq_absorbingContribution_add,
        quittingRootExpectedPayoff_eq_absorbingContribution_add]
      calc
        quittingRootAbsorbingContribution reward root who +
              quittingStationaryContinueMass root *
                quittingTerminalPayoff reward
                  (quittingLiteralRootStackProfile reward roots first) who -
            (quittingRootAbsorbingContribution reward root who +
              quittingStationaryContinueMass root *
                quittingTerminalPayoff reward
                  (quittingLiteralRootStackProfile reward roots second) who) =
            quittingStationaryContinueMass root *
              (quittingTerminalPayoff reward
                  (quittingLiteralRootStackProfile reward roots first) who -
                quittingTerminalPayoff reward
                  (quittingLiteralRootStackProfile reward roots second) who) := by
          ring
        _ = quittingStationaryContinueMass root *
            (quittingLiteralRootStackJointSurvival roots *
              (quittingTerminalPayoff reward first who -
                quittingTerminalPayoff reward second who)) := by rw [ih]
        _ = quittingLiteralRootStackJointSurvival (root :: roots) *
            (quittingTerminalPayoff reward first who -
              quittingTerminalPayoff reward second who) := by
          simp only [quittingLiteralRootStackJointSurvival, List.map_cons,
            List.prod_cons]
          ring

/-- The actual gain of a copied-prefix behavioral deviation is exactly the
suffix gain multiplied by full joint survival through the prefix. -/
theorem quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward roots terminal) who
            (quittingCopyLiteralRootStackThenDeviation reward roots who
              deviation)) who -
        quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) who =
      quittingLiteralRootStackJointSurvival roots *
        (quittingTerminalPayoff reward
            (Function.update terminal who deviation) who -
          quittingTerminalPayoff reward terminal who) := by
  rw [update_quittingLiteralRootStackProfile_copyThenDeviation_eq]
  exact quittingTerminalPayoff_literalRootStackProfile_sub_eq_jointSurvival_mul
    reward roots (Function.update terminal who deviation) terminal who

/-- A positive suffix gain and a lower bound on prefix survival give a
literal profitable deviation at the prefixed profile. -/
theorem quittingLiteralRootStackProfile_debt_ge_survivalFloor_mul_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {survivalFloor gain : ℝ} (hsurvival : survivalFloor ≤
      quittingLiteralRootStackJointSurvival roots)
    (hgain : 0 ≤ gain)
    (hsuffix : quittingTerminalPayoff reward terminal who + gain ≤
      quittingTerminalPayoff reward
        (Function.update terminal who deviation) who) :
    survivalFloor * gain ≤
      quittingTerminalDeviationDebt reward
        (quittingLiteralRootStackProfile reward roots terminal) who := by
  have hjoint := quittingLiteralRootStackJointSurvival_nonneg roots
  have htransport :=
    quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq
      reward roots terminal who deviation
  have hscaled : survivalFloor * gain ≤
      quittingLiteralRootStackJointSurvival roots *
        (quittingTerminalPayoff reward
            (Function.update terminal who deviation) who -
          quittingTerminalPayoff reward terminal who) := by
    calc
      survivalFloor * gain ≤
          quittingLiteralRootStackJointSurvival roots * gain :=
        mul_le_mul_of_nonneg_right hsurvival hgain
      _ ≤ quittingLiteralRootStackJointSurvival roots *
          (quittingTerminalPayoff reward
              (Function.update terminal who deviation) who -
            quittingTerminalPayoff reward terminal who) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hjoint
  unfold quittingTerminalDeviationDebt
  have hcap :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingLiteralRootStackProfile reward roots terminal) who
        (quittingCopyLiteralRootStackThenDeviation reward roots who deviation)
  linarith

end GameTheory
