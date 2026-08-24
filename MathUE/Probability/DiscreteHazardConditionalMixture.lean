/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.DiscreteHazardMixture

/-!
# Conditioning a mixture of discrete stopping laws

After survival to a finite cutoff, a convex mixture of two stopping laws is
again the convex mixture of the two shifted hazards.  Its new coefficient is
the posterior component weight.  The identity is exact, including after a
later row at which the residual survival becomes zero.
-/

noncomputable section

namespace Math.Probability.DiscreteHazard

namespace ScalarHazard

/-- The residual hazard seen after surviving to `cutoff`. -/
def shift (hazard : ScalarHazard) (cutoff : Nat) : ScalarHazard where
  stop time := hazard.stop (cutoff + time)
  stop_nonneg time := hazard.stop_nonneg (cutoff + time)
  stop_le_one time := hazard.stop_le_one (cutoff + time)

@[simp] theorem shift_stop (hazard : ScalarHazard) (cutoff time : Nat) :
    (hazard.shift cutoff).stop time = hazard.stop (cutoff + time) := by
  rfl

theorem shift_survival (hazard : ScalarHazard) (cutoff start fuel : Nat) :
    (hazard.shift cutoff).survival start fuel =
      hazard.survival (cutoff + start) fuel := by
  unfold ScalarHazard.survival Math.survivalProduct
  apply Finset.prod_congr rfl
  intro offset hoffset
  change 1 - hazard.stop (cutoff + (start + offset)) =
    1 - hazard.stop (cutoff + start + offset)
  congr 2
  omega

@[simp] theorem shift_survival_zero
    (hazard : ScalarHazard) (cutoff fuel : Nat) :
    (hazard.shift cutoff).survival 0 fuel =
      hazard.survival cutoff fuel := by
  simpa using hazard.shift_survival cutoff 0 fuel

/-- The shifted mixture survival is the original mixture survival divided by
the mass which reached the conditioning cutoff. -/
theorem mixedSurvival_shift_posteriorTargetWeight
    (source target : ScalarHazard) (lambda : Real)
    (hlambda0 : 0 <= lambda) (hlambda1 : lambda <= 1)
    (cutoff fuel : Nat)
    (hpositive : 0 < mixedSurvival source target lambda cutoff) :
    mixedSurvival (source.shift cutoff) (target.shift cutoff)
        (posteriorTargetWeight source target lambda cutoff) fuel =
      mixedSurvival source target lambda (cutoff + fuel) /
        mixedSurvival source target lambda cutoff := by
  have hconditional := convexMix_conditionalSurvival_eq_posteriorMix
    source target lambda hlambda0 hlambda1 cutoff fuel hpositive
  rw [convexMix_survival, convexMix_survival] at hconditional
  simpa [mixedSurvival, shift_survival_zero] using hconditional.symm

/-- The shifted mixture stopping mass has the same normalization factor as
its shifted survival. -/
theorem mixedStopMass_shift_posteriorTargetWeight
    (source target : ScalarHazard) (lambda : Real)
    (hlambda0 : 0 <= lambda) (hlambda1 : lambda <= 1)
    (cutoff time : Nat)
    (hpositive : 0 < mixedSurvival source target lambda cutoff) :
    mixedStopMass (source.shift cutoff) (target.shift cutoff)
        (posteriorTargetWeight source target lambda cutoff) time =
      mixedStopMass source target lambda (cutoff + time) /
        mixedSurvival source target lambda cutoff := by
  rw [mixedStopMass_eq_survival_sub_succ,
    mixedSurvival_shift_posteriorTargetWeight source target lambda
      hlambda0 hlambda1 cutoff time hpositive,
    mixedSurvival_shift_posteriorTargetWeight source target lambda
      hlambda0 hlambda1 cutoff (time + 1) hpositive,
    mixedStopMass_eq_survival_sub_succ]
  have hindex : cutoff + (time + 1) = cutoff + time + 1 := by omega
  rw [hindex]
  ring

/-- Exact posterior conditioning of a convex stopping-law hazard. -/
theorem shift_convexMix
    (source target : ScalarHazard) (lambda : Real)
    (hlambda0 : 0 <= lambda) (hlambda1 : lambda <= 1)
    (cutoff : Nat)
    (hpositive : 0 < mixedSurvival source target lambda cutoff) :
    (convexMix source target lambda hlambda0 hlambda1).shift cutoff =
      convexMix (source.shift cutoff) (target.shift cutoff)
        (posteriorTargetWeight source target lambda cutoff)
        (posteriorTargetWeight_nonneg source target lambda
          hlambda0 hlambda1 cutoff)
        (posteriorTargetWeight_le_one source target lambda
          hlambda1 cutoff hpositive) := by
  apply eq_of_stop_eq
  funext time
  have hdenom := mixedSurvival_shift_posteriorTargetWeight
    source target lambda hlambda0 hlambda1 cutoff time hpositive
  have hmass := mixedStopMass_shift_posteriorTargetWeight
    source target lambda hlambda0 hlambda1 cutoff time hpositive
  by_cases hlocal : mixedSurvival (source.shift cutoff) (target.shift cutoff)
      (posteriorTargetWeight source target lambda cutoff) time = 0
  · have hglobal : mixedSurvival source target lambda (cutoff + time) = 0 := by
      rw [hlocal] at hdenom
      have hcutoff : mixedSurvival source target lambda cutoff ≠ 0 :=
        ne_of_gt hpositive
      field_simp [hcutoff] at hdenom
      simpa using hdenom.symm
    change (if mixedSurvival source target lambda (cutoff + time) = 0 then 0
      else _) =
      (if mixedSurvival (source.shift cutoff) (target.shift cutoff)
        (posteriorTargetWeight source target lambda cutoff) time = 0 then 0
      else _)
    simp [hlocal, hglobal]
  · have hglobal : mixedSurvival source target lambda (cutoff + time) ≠ 0 := by
      intro hzero
      rw [hzero, zero_div] at hdenom
      exact hlocal hdenom
    change (if mixedSurvival source target lambda (cutoff + time) = 0 then 0
      else mixedStopMass source target lambda (cutoff + time) /
        mixedSurvival source target lambda (cutoff + time)) =
      (if mixedSurvival (source.shift cutoff) (target.shift cutoff)
        (posteriorTargetWeight source target lambda cutoff) time = 0 then 0
      else mixedStopMass (source.shift cutoff) (target.shift cutoff)
          (posteriorTargetWeight source target lambda cutoff) time /
        mixedSurvival (source.shift cutoff) (target.shift cutoff)
          (posteriorTargetWeight source target lambda cutoff) time)
    rw [if_neg hglobal, if_neg hlocal]
    rw [hmass, hdenom]
    field_simp [ne_of_gt hpositive, hglobal]

/-- Both mixture components remain positively available after conditioning
when each has positive residual survival and both prior weights are strict. -/
theorem posteriorTargetWeight_mem_Ioo
    (source target : ScalarHazard) (lambda : Real)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (cutoff : Nat)
    (hsource : 0 < source.survival 0 cutoff)
    (htarget : 0 < target.survival 0 cutoff) :
    posteriorTargetWeight source target lambda cutoff ∈ Set.Ioo 0 1 := by
  have hsourceFlux : 0 < (1 - lambda) * source.survival 0 cutoff :=
    mul_pos (sub_pos.mpr hlambda1) hsource
  have htargetFlux : 0 < lambda * target.survival 0 cutoff :=
    mul_pos hlambda0 htarget
  have hmixed : 0 < mixedSurvival source target lambda cutoff := by
    unfold mixedSurvival
    positivity
  constructor
  · unfold posteriorTargetWeight
    positivity
  · have hcomplement : 0 <
        1 - posteriorTargetWeight source target lambda cutoff := by
      rw [one_sub_posteriorTargetWeight source target lambda cutoff hmixed]
      positivity
    linarith

end ScalarHazard

/-- Shift a Boolean hazard past a finite survived prefix. -/
def BooleanHazard.shift (hazard : BooleanHazard) (cutoff : Nat) : BooleanHazard :=
  fun time => hazard (cutoff + time)

@[simp] theorem BooleanHazard.toScalar_shift
    (hazard : BooleanHazard) (cutoff : Nat) :
    (hazard.shift cutoff).toScalar = hazard.toScalar.shift cutoff := by
  rfl

/-- Boolean hazards are determined by their scalar stop probabilities. -/
theorem BooleanHazard.eq_of_toScalar_eq
    (first second : BooleanHazard) (hscalar : first.toScalar = second.toScalar) :
    first = second := by
  funext time
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro stop
  cases stop with
  | false =>
      have hfirst := continue_add_stop first time
      have hsecond := continue_add_stop second time
      have hstop : stopProbability first time = stopProbability second time := by
        exact congrFun (congrArg ScalarHazard.stop hscalar) time
      dsimp [continueProbability] at hfirst hsecond ⊢
      dsimp [stopProbability] at hfirst hsecond hstop
      linarith
  | true =>
      have hstop : stopProbability first time = stopProbability second time := by
        exact congrFun (congrArg ScalarHazard.stop hscalar) time
      exact hstop

/-- Exact posterior conditioning in the Boolean-hazard presentation. -/
theorem BooleanHazard.shift_convexMix
    (source target : BooleanHazard) (lambda : Real)
    (hlambda0 : 0 <= lambda) (hlambda1 : lambda <= 1)
    (cutoff : Nat)
    (hpositive : 0 < ScalarHazard.mixedSurvival
      source.toScalar target.toScalar lambda cutoff) :
    (BooleanHazard.convexMix source target lambda hlambda0 hlambda1).shift cutoff =
      BooleanHazard.convexMix (source.shift cutoff) (target.shift cutoff)
        (ScalarHazard.posteriorTargetWeight
          source.toScalar target.toScalar lambda cutoff)
        (ScalarHazard.posteriorTargetWeight_nonneg
          source.toScalar target.toScalar lambda hlambda0 hlambda1 cutoff)
        (ScalarHazard.posteriorTargetWeight_le_one
          source.toScalar target.toScalar lambda hlambda1 cutoff hpositive) := by
  apply BooleanHazard.eq_of_toScalar_eq
  simp only [BooleanHazard.toScalar_shift, BooleanHazard.toScalar_convexMix]
  exact ScalarHazard.shift_convexMix source.toScalar target.toScalar lambda
    hlambda0 hlambda1 cutoff hpositive

end Math.Probability.DiscreteHazard
