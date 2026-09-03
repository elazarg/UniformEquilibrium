/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.GeneralTotalVariation
import MathUE.Probability.DiscreteHazardConditionalMixture
import MathUE.Probability.DiscreteHazardMixture
import MathUE.Probability.FiniteIndependentMixture
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw
import UniformEquilibrium.Quitting.Paths.PureTimeDeadlineProfile
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization

/-!
# Operational distance and behavioral semantics of complete stopping laws

The operational distance is the full discrete `L¹` distance, including the
`Never` atom.  Independent product pushforward contracts the sum of marginal
distances.  The resulting estimates apply uniformly to every unilateral
replacement and therefore to the complete stopping-law replacement cap.  The
final semantic bridge identifies that cap with the unrestricted behavioral
best-response value.

The prefix and positive-reach suffix constructions below are operations on
complete stopping laws.  They do not produce a source family, a chronological
path, or a uniform equilibrium.
-/

noncomputable section

namespace Math
namespace Probability

/-- Full discrete `L¹` distance between two arbitrary PMFs. -/
def pmfOperationalDistance {Omega : Type*} (first second : PMF Omega) : Real :=
  2 * pmfGeneralTV first second

private theorem summable_min_toReal {Omega : Type*} (first second : PMF Omega) :
    Summable (fun omega => min ((first omega).toReal) ((second omega).toReal)) := by
  exact Summable.of_nonneg_of_le
    (fun _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun _ => min_le_left _ _) (pmf_toReal_summable first)

private theorem summable_abs_toReal_sub {Omega : Type*} (first second : PMF Omega) :
    Summable (fun omega => |(first omega).toReal - (second omega).toReal|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun omega => abs_sub_le_iff.mpr ?_)
    ((pmf_toReal_summable first).add (pmf_toReal_summable second))
  have hfirst : 0 <= (first omega).toReal := ENNReal.toReal_nonneg
  have hsecond : 0 <= (second omega).toReal := ENNReal.toReal_nonneg
  constructor <;> nlinarith

/-- The doubled-overlap definition is literally the full discrete `L¹` sum. -/
theorem pmfOperationalDistance_eq_tsum_abs {Omega : Type*}
    (first second : PMF Omega) :
    pmfOperationalDistance first second =
      ∑' omega, |(first omega).toReal - (second omega).toReal| := by
  have hfirst := pmf_toReal_summable first
  have hsecond := pmf_toReal_summable second
  have hmin := summable_min_toReal first second
  have hpoint : forall omega,
      |(first omega).toReal - (second omega).toReal| =
        (first omega).toReal + (second omega).toReal -
          2 * min ((first omega).toReal) ((second omega).toReal) := by
    intro omega
    rcases le_total (first omega).toReal (second omega).toReal with hle | hle
    · rw [min_eq_left hle, abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    · rw [min_eq_right hle, abs_of_nonneg (sub_nonneg.mpr hle)]
      ring
  rw [pmfOperationalDistance, pmfGeneralTV]
  rw [show (∑' omega, |(first omega).toReal - (second omega).toReal|) =
      ∑' omega, ((first omega).toReal + (second omega).toReal -
        2 * min ((first omega).toReal) ((second omega).toReal)) by
    apply tsum_congr hpoint]
  rw [(hfirst.add hsecond).tsum_sub (hmin.mul_left 2),
    hfirst.tsum_add hsecond, hmin.tsum_mul_left,
    pmf_toReal_tsum_one, pmf_toReal_tsum_one]
  ring

theorem pmfOperationalDistance_nonneg {Omega : Type*}
    (first second : PMF Omega) :
    0 <= pmfOperationalDistance first second := by
  exact mul_nonneg (by norm_num) (pmfGeneralTV_nonneg first second)

theorem pmfOperationalDistance_symm {Omega : Type*}
    (first second : PMF Omega) :
    pmfOperationalDistance first second = pmfOperationalDistance second first := by
  simp only [pmfOperationalDistance, pmfGeneralTV_symm]

theorem pmfOperationalDistance_triangle {Omega : Type*}
    (first middle last : PMF Omega) :
    pmfOperationalDistance first last <=
      pmfOperationalDistance first middle +
        pmfOperationalDistance middle last := by
  rw [pmfOperationalDistance_eq_tsum_abs,
    pmfOperationalDistance_eq_tsum_abs,
    pmfOperationalDistance_eq_tsum_abs]
  have hsummable : Summable (fun omega =>
      |(first omega).toReal - (middle omega).toReal| +
        |(middle omega).toReal - (last omega).toReal|) :=
    (summable_abs_toReal_sub first middle).add
      (summable_abs_toReal_sub middle last)
  calc
    (∑' omega, |(first omega).toReal - (last omega).toReal|) <=
        ∑' omega,
          (|(first omega).toReal - (middle omega).toReal| +
            |(middle omega).toReal - (last omega).toReal|) :=
      Summable.tsum_le_tsum
        (fun omega => abs_sub_le _ _ _)
        (summable_abs_toReal_sub first last) hsummable
    _ = (∑' omega, |(first omega).toReal - (middle omega).toReal|) +
          ∑' omega, |(middle omega).toReal - (last omega).toReal| :=
      (summable_abs_toReal_sub first middle).tsum_add
        (summable_abs_toReal_sub middle last)

@[simp] theorem pmfOperationalDistance_self {Omega : Type*} (law : PMF Omega) :
    pmfOperationalDistance law law = 0 := by
  rw [pmfOperationalDistance_eq_tsum_abs]
  simp

/-- Delay every finite stopping time by one while preserving `Never`. -/
def delayStoppingTime : Option Nat -> Option Nat
  | none => none
  | some time => some (time + 1)

@[simp] theorem map_delayStoppingTime_none (law : PMF (Option Nat)) :
    law.map delayStoppingTime none = law none := by
  rw [PMF.map_apply, tsum_eq_single none]
  · simp [delayStoppingTime]
  · intro choice hchoice
    cases choice with
    | none => exact (hchoice rfl).elim
    | some time => simp [delayStoppingTime]

@[simp] theorem map_delayStoppingTime_zero (law : PMF (Option Nat)) :
    law.map delayStoppingTime (some 0) = 0 := by
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro choice
  cases choice <;> simp [delayStoppingTime]

@[simp] theorem map_delayStoppingTime_succ
    (law : PMF (Option Nat)) (time : Nat) :
    law.map delayStoppingTime (some (time + 1)) = law (some time) := by
  rw [PMF.map_apply, tsum_eq_single (some time)]
  · simp [delayStoppingTime]
  · intro choice hchoice
    cases choice with
    | none => simp [delayStoppingTime]
    | some other =>
        rw [if_neg]
        intro heq
        apply hchoice
        simp only [delayStoppingTime, Option.some.injEq] at heq
        congr 1
        omega

private theorem tsum_option_eq_none_add_some {f : Option Nat -> Real}
    (hf : Summable f) :
    (∑' choice, f choice) = f none + ∑' time, f (some time) := by
  have hcode : Summable fun code : Nat =>
      f (DiscreteHazard.optionNatEquivNat.symm code) :=
    (DiscreteHazard.optionNatEquivNat.symm.summable_iff).2 hf
  have heq := DiscreteHazard.optionNatEquivNat.symm.tsum_eq f
  rw [hcode.tsum_eq_zero_add] at heq
  simpa [DiscreteHazard.optionNatEquivNat] using heq.symm

/-- Prefix a complete stopping law by one independent quit/continue coin. -/
def prefixStoppingLaw (law : PMF (Option Nat))
    (quitNow : Real) (hquitNow0 : 0 <= quitNow) (hquitNow1 : quitNow <= 1) :
    PMF (Option Nat) :=
  (DiscreteHazard.mixtureCoin quitNow hquitNow0 hquitNow1).bind fun quit =>
    if quit then PMF.pure (some 0) else law.map delayStoppingTime

@[simp] theorem prefixStoppingLaw_none_toReal
    (law : PMF (Option Nat))
    (quitNow : Real) (hquitNow0 : 0 <= quitNow) (hquitNow1 : quitNow <= 1) :
    (prefixStoppingLaw law quitNow hquitNow0 hquitNow1 none).toReal =
      (1 - quitNow) * (law none).toReal := by
  rw [prefixStoppingLaw,
    Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [map_delayStoppingTime_none]
  simp [DiscreteHazard.mixtureCoin_false_toReal,
    DiscreteHazard.mixtureCoin_true_toReal]

@[simp] theorem prefixStoppingLaw_zero_toReal
    (law : PMF (Option Nat))
    (quitNow : Real) (hquitNow0 : 0 <= quitNow) (hquitNow1 : quitNow <= 1) :
    (prefixStoppingLaw law quitNow hquitNow0 hquitNow1 (some 0)).toReal =
      quitNow := by
  rw [prefixStoppingLaw,
    Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [map_delayStoppingTime_zero]
  simp [DiscreteHazard.mixtureCoin_false_toReal,
    DiscreteHazard.mixtureCoin_true_toReal]

@[simp] theorem prefixStoppingLaw_succ_toReal
    (law : PMF (Option Nat))
    (quitNow : Real) (hquitNow0 : 0 <= quitNow) (hquitNow1 : quitNow <= 1)
    (time : Nat) :
    (prefixStoppingLaw law quitNow hquitNow0 hquitNow1 (some (time + 1))).toReal =
      (1 - quitNow) * (law (some time)).toReal := by
  rw [prefixStoppingLaw,
    Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [map_delayStoppingTime_succ]
  simp [DiscreteHazard.mixtureCoin_false_toReal,
    DiscreteHazard.mixtureCoin_true_toReal]

/-- With the prefix coin fixed, the delayed tail's operational distance is
scaled by the probability of continuing. -/
theorem pmfOperationalDistance_prefixStoppingLaw_same_rate
    (first second : PMF (Option Nat))
    (quitNow : Real) (hquitNow0 : 0 <= quitNow) (hquitNow1 : quitNow <= 1) :
    pmfOperationalDistance
        (prefixStoppingLaw first quitNow hquitNow0 hquitNow1)
        (prefixStoppingLaw second quitNow hquitNow0 hquitNow1) =
      (1 - quitNow) * pmfOperationalDistance first second := by
  rw [pmfOperationalDistance_eq_tsum_abs]
  rw [tsum_option_eq_none_add_some
    (summable_abs_toReal_sub
      (prefixStoppingLaw first quitNow hquitNow0 hquitNow1)
      (prefixStoppingLaw second quitNow hquitNow0 hquitNow1))]
  have hfinite : Summable (fun time =>
      |(prefixStoppingLaw first quitNow hquitNow0 hquitNow1 (some time)).toReal -
        (prefixStoppingLaw second quitNow hquitNow0 hquitNow1
          (some time)).toReal|) :=
    (summable_abs_toReal_sub
      (prefixStoppingLaw first quitNow hquitNow0 hquitNow1)
      (prefixStoppingLaw second quitNow hquitNow0 hquitNow1)).comp_injective
        (Option.some_injective Nat)
  rw [hfinite.tsum_eq_zero_add]
  simp only [prefixStoppingLaw_none_toReal, prefixStoppingLaw_zero_toReal,
    prefixStoppingLaw_succ_toReal, sub_self, abs_zero, zero_add]
  have hcontinue : 0 <= 1 - quitNow := sub_nonneg.mpr hquitNow1
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg hcontinue]
  rw [tsum_mul_left]
  rw [pmfOperationalDistance_eq_tsum_abs]
  rw [tsum_option_eq_none_add_some (summable_abs_toReal_sub first second)]
  ring

/-- Changing only the prefix coin costs exactly twice the absolute change in
its Quit probability. -/
theorem pmfOperationalDistance_prefixStoppingLaw_same_tail
    (law : PMF (Option Nat))
    (firstRate secondRate : Real)
    (hfirst0 : 0 <= firstRate) (hfirst1 : firstRate <= 1)
    (hsecond0 : 0 <= secondRate) (hsecond1 : secondRate <= 1) :
    pmfOperationalDistance
        (prefixStoppingLaw law firstRate hfirst0 hfirst1)
        (prefixStoppingLaw law secondRate hsecond0 hsecond1) =
      2 * |firstRate - secondRate| := by
  rw [pmfOperationalDistance_eq_tsum_abs]
  rw [tsum_option_eq_none_add_some
    (summable_abs_toReal_sub
      (prefixStoppingLaw law firstRate hfirst0 hfirst1)
      (prefixStoppingLaw law secondRate hsecond0 hsecond1))]
  have hfinite : Summable (fun time =>
      |(prefixStoppingLaw law firstRate hfirst0 hfirst1 (some time)).toReal -
        (prefixStoppingLaw law secondRate hsecond0 hsecond1
          (some time)).toReal|) :=
    (summable_abs_toReal_sub
      (prefixStoppingLaw law firstRate hfirst0 hfirst1)
      (prefixStoppingLaw law secondRate hsecond0 hsecond1)).comp_injective
        (Option.some_injective Nat)
  rw [hfinite.tsum_eq_zero_add]
  simp only [prefixStoppingLaw_none_toReal, prefixStoppingLaw_zero_toReal,
    prefixStoppingLaw_succ_toReal]
  have hpoint : forall mass : Real,
      |(1 - firstRate) * mass - (1 - secondRate) * mass| =
        |firstRate - secondRate| * |mass| := by
    intro mass
    rw [← sub_mul, abs_mul]
    congr 1
    rw [show (1 - firstRate) - (1 - secondRate) =
        -(firstRate - secondRate) by ring, abs_neg]
  rw [hpoint]
  simp_rw [hpoint, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [tsum_mul_left]
  have htotal := DiscreteHazard.StoppingLaw.none_add_tsum_finiteMass law
  change (law none).toReal + ∑' time, (law (some time)).toReal = 1 at htotal
  calc
    |firstRate - secondRate| * (law none).toReal +
        (|firstRate - secondRate| +
          |firstRate - secondRate| * ∑' time, (law (some time)).toReal) =
      |firstRate - secondRate| *
        (1 + ((law none).toReal + ∑' time, (law (some time)).toReal)) := by
          ring
    _ = 2 * |firstRate - secondRate| := by rw [htotal]; ring

/-- Product-root prefixing obeys the literal operational-distance estimate
`2 * |x-y| + distance tail tail'`, including the `Never` atom. -/
theorem pmfOperationalDistance_prefixStoppingLaw_le
    (first second : PMF (Option Nat))
    (firstRate secondRate : Real)
    (hfirst0 : 0 <= firstRate) (hfirst1 : firstRate <= 1)
    (hsecond0 : 0 <= secondRate) (hsecond1 : secondRate <= 1) :
    pmfOperationalDistance
        (prefixStoppingLaw first firstRate hfirst0 hfirst1)
        (prefixStoppingLaw second secondRate hsecond0 hsecond1) <=
      2 * |firstRate - secondRate| +
        pmfOperationalDistance first second := by
  calc
    pmfOperationalDistance
        (prefixStoppingLaw first firstRate hfirst0 hfirst1)
        (prefixStoppingLaw second secondRate hsecond0 hsecond1) <=
      pmfOperationalDistance
          (prefixStoppingLaw first firstRate hfirst0 hfirst1)
          (prefixStoppingLaw first secondRate hsecond0 hsecond1) +
        pmfOperationalDistance
          (prefixStoppingLaw first secondRate hsecond0 hsecond1)
          (prefixStoppingLaw second secondRate hsecond0 hsecond1) :=
      pmfOperationalDistance_triangle _ _ _
    _ = 2 * |firstRate - secondRate| +
        (1 - secondRate) * pmfOperationalDistance first second := by
      rw [pmfOperationalDistance_prefixStoppingLaw_same_tail,
        pmfOperationalDistance_prefixStoppingLaw_same_rate]
    _ <= 2 * |firstRate - secondRate| +
        pmfOperationalDistance first second := by
      gcongr
      exact mul_le_of_le_one_left
        (pmfOperationalDistance_nonneg first second)
        (sub_le_self 1 hsecond0)

/-! ## Finite concatenation -/

/-- One admissible Quit probability for a finite stopping-law prefix. -/
structure StoppingRate where
  value : Real
  nonneg : 0 <= value
  le_one : value <= 1

/-- Concatenate a finite list of one-stage stopping coins in front of one
complete tail law.  The list head is the earliest stage. -/
def finitePrefixStoppingLaw (rates : List StoppingRate)
    (tail : PMF (Option Nat)) : PMF (Option Nat) :=
  rates.foldr
    (fun rate law => prefixStoppingLaw law rate.value rate.nonneg rate.le_one)
    tail

/-- Probability of reaching the supplied tail after all finite prefix coins. -/
def finitePrefixContinuationWeight (rates : List StoppingRate) : Real :=
  (rates.map fun rate => 1 - rate.value).prod

/-- Coordinatewise `L¹` distance between two equally long finite lists of
stopping rates. -/
def finiteStoppingRateDifference
    (first second : List StoppingRate) : Real :=
  ((first.zip second).map fun rates => |rates.1.value - rates.2.value|).sum

@[simp] theorem finitePrefixStoppingLaw_nil (tail : PMF (Option Nat)) :
    finitePrefixStoppingLaw [] tail = tail := rfl

@[simp] theorem finitePrefixStoppingLaw_cons
    (rate : StoppingRate) (rates : List StoppingRate)
    (tail : PMF (Option Nat)) :
    finitePrefixStoppingLaw (rate :: rates) tail =
      prefixStoppingLaw (finitePrefixStoppingLaw rates tail)
        rate.value rate.nonneg rate.le_one := rfl

@[simp] theorem finitePrefixContinuationWeight_nil :
    finitePrefixContinuationWeight [] = 1 := rfl

@[simp] theorem finitePrefixContinuationWeight_cons
    (rate : StoppingRate) (rates : List StoppingRate) :
    finitePrefixContinuationWeight (rate :: rates) =
      (1 - rate.value) * finitePrefixContinuationWeight rates := by
  simp [finitePrefixContinuationWeight]

/-- A common finite prefix scales the complete tail-law distance by exactly
the probability of reaching that tail. -/
theorem pmfOperationalDistance_finitePrefixStoppingLaw_same_rates
    (rates : List StoppingRate) (first second : PMF (Option Nat)) :
    pmfOperationalDistance (finitePrefixStoppingLaw rates first)
        (finitePrefixStoppingLaw rates second) =
      finitePrefixContinuationWeight rates *
        pmfOperationalDistance first second := by
  induction rates with
  | nil => simp
  | cons rate rates ih =>
      rw [finitePrefixStoppingLaw_cons, finitePrefixStoppingLaw_cons,
        pmfOperationalDistance_prefixStoppingLaw_same_rate, ih,
        finitePrefixContinuationWeight_cons]
      ring

/-- Finite concatenation is jointly Lipschitz: the tail pays its full
operational distance and each displayed prefix coin pays twice its rate
difference. -/
theorem pmfOperationalDistance_finitePrefixStoppingLaw_le
    (firstRates secondRates : List StoppingRate)
    (firstTail secondTail : PMF (Option Nat))
    (hlength : firstRates.length = secondRates.length) :
    pmfOperationalDistance (finitePrefixStoppingLaw firstRates firstTail)
        (finitePrefixStoppingLaw secondRates secondTail) <=
      2 * finiteStoppingRateDifference firstRates secondRates +
        pmfOperationalDistance firstTail secondTail := by
  induction firstRates generalizing secondRates with
  | nil =>
      cases secondRates with
      | nil => simp [finiteStoppingRateDifference]
      | cons secondRate secondRates => simp at hlength
  | cons firstRate firstRates ih =>
      cases secondRates with
      | nil => simp at hlength
      | cons secondRate secondRates =>
          have htailLength : firstRates.length = secondRates.length := by
            simpa using hlength
          calc
            pmfOperationalDistance
                (finitePrefixStoppingLaw (firstRate :: firstRates) firstTail)
                (finitePrefixStoppingLaw (secondRate :: secondRates) secondTail) <=
              2 * |firstRate.value - secondRate.value| +
                pmfOperationalDistance
                  (finitePrefixStoppingLaw firstRates firstTail)
                  (finitePrefixStoppingLaw secondRates secondTail) := by
                exact pmfOperationalDistance_prefixStoppingLaw_le _ _ _ _
                  firstRate.nonneg firstRate.le_one
                  secondRate.nonneg secondRate.le_one
            _ <= 2 * |firstRate.value - secondRate.value| +
                (2 * finiteStoppingRateDifference firstRates secondRates +
                  pmfOperationalDistance firstTail secondTail) := by
              gcongr
              exact ih secondRates htailLength
            _ = 2 * finiteStoppingRateDifference
                  (firstRate :: firstRates) (secondRate :: secondRates) +
                pmfOperationalDistance firstTail secondTail := by
              simp [finiteStoppingRateDifference]
              ring

/-! ## Positive-reach suffixes -/

/-- The complete stopping law seen after survival to a finite cutoff.
On a zero-reach cutoff the post-cut hazards are still well-defined, but the
quantitative conditional-law interface below deliberately requires positive
reach. -/
def suffixStoppingLaw (law : PMF (Option Nat)) (cutoff : Nat) : PMF (Option Nat) :=
  ((DiscreteHazard.StoppingLaw.toScalarHazard law).shift cutoff).stoppingLaw

/-- Reinterpret a suffix-relative stopping time as an absolute stopping time. -/
def suffixSourceChoice (cutoff : Nat) : Option Nat -> Option Nat
  | none => none
  | some time => some (cutoff + time)

theorem suffixSourceChoice_injective (cutoff : Nat) :
    Function.Injective (suffixSourceChoice cutoff) := by
  intro first second
  cases first <;> cases second <;> simp [suffixSourceChoice]

@[simp] theorem suffixStoppingLaw_some_toReal_of_survival_pos
    (law : PMF (Option Nat)) (cutoff time : Nat)
    (hreach : 0 < DiscreteHazard.StoppingLaw.survival law cutoff) :
    (suffixStoppingLaw law cutoff (some time)).toReal =
      (law (some (cutoff + time))).toReal /
        DiscreteHazard.StoppingLaw.survival law cutoff := by
  let hazard := DiscreteHazard.StoppingLaw.toScalarHazard law
  have hmass := DiscreteHazard.StoppingLaw.toScalarHazard_stopMass law (cutoff + time)
  have hsplit : hazard.survival 0 (cutoff + time) =
      hazard.survival 0 cutoff * hazard.survival cutoff time := by
    unfold DiscreteHazard.ScalarHazard.survival
    simpa using Math.survivalProduct_add
      (fun index => 1 - hazard.stop index) 0 cutoff time
  rw [suffixStoppingLaw,
    DiscreteHazard.ScalarHazard.stoppingLaw_some_toReal,
    DiscreteHazard.ScalarHazard.stopMass,
    DiscreteHazard.ScalarHazard.shift_survival_zero,
    DiscreteHazard.ScalarHazard.shift_stop]
  change hazard.survival cutoff time * hazard.stop (cutoff + time) = _
  rw [← DiscreteHazard.StoppingLaw.toScalarHazard_survival law cutoff] at hreach
  change hazard.stopMass (cutoff + time) =
    DiscreteHazard.StoppingLaw.finiteMass law (cutoff + time) at hmass
  rw [DiscreteHazard.ScalarHazard.stopMass, hsplit] at hmass
  change hazard.survival cutoff time * hazard.stop (cutoff + time) =
    DiscreteHazard.StoppingLaw.finiteMass law (cutoff + time) /
      DiscreteHazard.StoppingLaw.survival law cutoff
  rw [← DiscreteHazard.StoppingLaw.toScalarHazard_survival law cutoff]
  rw [← hmass]
  field_simp
  simp [hazard]

@[simp] theorem suffixStoppingLaw_none_toReal_of_survival_pos
    (law : PMF (Option Nat)) (cutoff : Nat)
    (hreach : 0 < DiscreteHazard.StoppingLaw.survival law cutoff) :
    (suffixStoppingLaw law cutoff none).toReal =
      (law none).toReal / DiscreteHazard.StoppingLaw.survival law cutoff := by
  let hazard := DiscreteHazard.StoppingLaw.toScalarHazard law
  have hshifted := (hazard.shift cutoff).tendsto_survival_neverMass
  have hscaled : Filter.Tendsto
      (fun fuel => hazard.survival 0 cutoff *
        (hazard.shift cutoff).survival 0 fuel) Filter.atTop
      (nhds (hazard.survival 0 cutoff * (hazard.shift cutoff).neverMass)) :=
    tendsto_const_nhds.mul hshifted
  have hsource : Filter.Tendsto
      (fun fuel => hazard.survival 0 (cutoff + fuel)) Filter.atTop
      (nhds hazard.neverMass) := by
    simpa [Function.comp_def, Nat.add_comm] using
      hazard.tendsto_survival_neverMass.comp
        (Filter.tendsto_add_atTop_nat cutoff)
  have hfactor (fuel : Nat) :
      hazard.survival 0 (cutoff + fuel) =
        hazard.survival 0 cutoff * (hazard.shift cutoff).survival 0 fuel := by
    rw [DiscreteHazard.ScalarHazard.shift_survival_zero]
    unfold DiscreteHazard.ScalarHazard.survival
    simpa using Math.survivalProduct_add
      (fun index => 1 - hazard.stop index) 0 cutoff fuel
  have hnever : hazard.neverMass =
      hazard.survival 0 cutoff * (hazard.shift cutoff).neverMass :=
    tendsto_nhds_unique hsource
      (hscaled.congr' (Filter.Eventually.of_forall fun fuel => (hfactor fuel).symm))
  rw [suffixStoppingLaw,
    DiscreteHazard.ScalarHazard.stoppingLaw_none_toReal]
  change (hazard.shift cutoff).neverMass =
    (law none).toReal / DiscreteHazard.StoppingLaw.survival law cutoff
  have hneverLaw : (law none).toReal = hazard.neverMass := by
    simpa only [hazard] using
      (DiscreteHazard.StoppingLaw.toScalarHazard_neverMass law).symm
  have hsurvivalLaw : DiscreteHazard.StoppingLaw.survival law cutoff =
      hazard.survival 0 cutoff := by
    simpa only [hazard] using
      (DiscreteHazard.StoppingLaw.toScalarHazard_survival law cutoff).symm
  have hreach' : 0 < hazard.survival 0 cutoff := hsurvivalLaw ▸ hreach
  rw [hneverLaw, hsurvivalLaw, hnever]
  field_simp [ne_of_gt hreach']

/-- Changing a complete stopping law changes its survival to any fixed cutoff
by at most the full operational distance. -/
theorem abs_stoppingLawSurvival_sub_le_operationalDistance
    (first second : PMF (Option Nat)) (cutoff : Nat) :
    |DiscreteHazard.StoppingLaw.survival first cutoff -
        DiscreteHazard.StoppingLaw.survival second cutoff| <=
      pmfOperationalDistance first second := by
  let difference : Nat -> Real := fun time =>
    (first (some time)).toReal - (second (some time)).toReal
  have hsummable : Summable (fun time => |difference time|) := by
    exact (summable_abs_toReal_sub first second).comp_injective
      (Option.some_injective Nat)
  have hprefix :
      (∑ time ∈ Finset.range cutoff, |difference time|) <=
        ∑' time, |difference time| :=
    hsummable.sum_le_tsum (Finset.range cutoff) fun _ _ => abs_nonneg _
  rw [pmfOperationalDistance_eq_tsum_abs,
    tsum_option_eq_none_add_some (summable_abs_toReal_sub first second)]
  unfold DiscreteHazard.StoppingLaw.survival
    DiscreteHazard.StoppingLaw.finiteMass
  have hrewrite :
      (1 - ∑ time ∈ Finset.range cutoff, (first (some time)).toReal) -
          (1 - ∑ time ∈ Finset.range cutoff, (second (some time)).toReal) =
        -(∑ time ∈ Finset.range cutoff, difference time) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hrewrite, abs_neg]
  calc
    |∑ time ∈ Finset.range cutoff, difference time| <=
        ∑ time ∈ Finset.range cutoff, |difference time| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑' time, |difference time| := hprefix
    _ <= |(first none).toReal - (second none).toReal| +
        ∑' time, |difference time| :=
      le_add_of_nonneg_left (abs_nonneg _)

private theorem summable_suffixSource_abs_toReal_sub
    (first second : PMF (Option Nat)) (cutoff : Nat) :
    Summable (fun choice =>
      |(first (suffixSourceChoice cutoff choice)).toReal -
        (second (suffixSourceChoice cutoff choice)).toReal|) :=
  (summable_abs_toReal_sub first second).comp_injective
    (suffixSourceChoice_injective cutoff)

private theorem tsum_suffixSource_abs_toReal_sub_le
    (first second : PMF (Option Nat)) (cutoff : Nat) :
    (∑' choice,
        |(first (suffixSourceChoice cutoff choice)).toReal -
          (second (suffixSourceChoice cutoff choice)).toReal|) <=
      pmfOperationalDistance first second := by
  rw [pmfOperationalDistance_eq_tsum_abs]
  exact Summable.tsum_le_tsum_of_inj (suffixSourceChoice cutoff)
    (suffixSourceChoice_injective cutoff)
    (fun _ _ => abs_nonneg _) (fun _ => le_rfl)
    (summable_suffixSource_abs_toReal_sub first second cutoff)
    (summable_abs_toReal_sub first second)

/-- Conditioning at a cutoff reached with mass at least `rho` is
`2 / rho`-Lipschitz in full operational distance.  Both `Never` atoms are
retained. -/
theorem pmfOperationalDistance_suffixStoppingLaw_le
    (first second : PMF (Option Nat)) (cutoff : Nat) (rho : Real)
    (hrho : 0 < rho)
    (hfirstReach : rho <= DiscreteHazard.StoppingLaw.survival first cutoff)
    (hsecondReach : rho <= DiscreteHazard.StoppingLaw.survival second cutoff) :
    pmfOperationalDistance (suffixStoppingLaw first cutoff)
        (suffixStoppingLaw second cutoff) <=
      (2 / rho) * pmfOperationalDistance first second := by
  let firstReach := DiscreteHazard.StoppingLaw.survival first cutoff
  let secondReach := DiscreteHazard.StoppingLaw.survival second cutoff
  let distance := pmfOperationalDistance first second
  let reachError := |firstReach - secondReach|
  let rawError : Option Nat -> Real := fun choice =>
    |(first (suffixSourceChoice cutoff choice)).toReal -
      (second (suffixSourceChoice cutoff choice)).toReal|
  have hfirstPos : 0 < firstReach := hrho.trans_le hfirstReach
  have hsecondPos : 0 < secondReach := hrho.trans_le hsecondReach
  have hdistance : 0 <= distance := pmfOperationalDistance_nonneg first second
  have hreachError : reachError <= distance := by
    exact abs_stoppingLawSurvival_sub_le_operationalDistance first second cutoff
  have hraw : Summable rawError :=
    summable_suffixSource_abs_toReal_sub first second cutoff
  have hrawLe : (∑' choice, rawError choice) <= distance :=
    tsum_suffixSource_abs_toReal_sub_le first second cutoff
  have hpoint (choice : Option Nat) :
      |(suffixStoppingLaw first cutoff choice).toReal -
          (suffixStoppingLaw second cutoff choice).toReal| <=
        rawError choice / firstReach +
          (suffixStoppingLaw second cutoff choice).toReal *
            (reachError / firstReach) := by
    have hfirstFormula : (suffixStoppingLaw first cutoff choice).toReal =
        (first (suffixSourceChoice cutoff choice)).toReal / firstReach := by
      cases choice with
      | none =>
          exact suffixStoppingLaw_none_toReal_of_survival_pos
            first cutoff hfirstPos
      | some time =>
          exact suffixStoppingLaw_some_toReal_of_survival_pos
            first cutoff time hfirstPos
    have hsecondFormula : (suffixStoppingLaw second cutoff choice).toReal =
        (second (suffixSourceChoice cutoff choice)).toReal / secondReach := by
      cases choice with
      | none =>
          exact suffixStoppingLaw_none_toReal_of_survival_pos
            second cutoff hsecondPos
      | some time =>
          exact suffixStoppingLaw_some_toReal_of_survival_pos
            second cutoff time hsecondPos
    rw [hfirstFormula, hsecondFormula]
    let firstMass := (first (suffixSourceChoice cutoff choice)).toReal
    let secondMass := (second (suffixSourceChoice cutoff choice)).toReal
    have hsecondMass : 0 <= secondMass := ENNReal.toReal_nonneg
    have hdecompose : firstMass / firstReach - secondMass / secondReach =
        (firstMass - secondMass) / firstReach +
          secondMass / secondReach *
            ((secondReach - firstReach) / firstReach) := by
      field_simp [ne_of_gt hfirstPos, ne_of_gt hsecondPos]
      ring
    rw [hdecompose]
    calc
      |(firstMass - secondMass) / firstReach +
          secondMass / secondReach *
            ((secondReach - firstReach) / firstReach)| <=
        |(firstMass - secondMass) / firstReach| +
          |secondMass / secondReach *
            ((secondReach - firstReach) / firstReach)| := abs_add_le _ _
      _ = |firstMass - secondMass| / firstReach +
          secondMass / secondReach *
            (|firstReach - secondReach| / firstReach) := by
        rw [abs_div, abs_of_pos hfirstPos, abs_mul, abs_div,
          abs_of_nonneg hsecondMass, abs_of_pos hsecondPos, abs_div,
          abs_of_pos hfirstPos]
        rw [abs_sub_comm secondReach firstReach]
      _ = rawError choice / firstReach +
          secondMass / secondReach * (reachError / firstReach) := rfl
  have hrawDiv : Summable (fun choice => rawError choice / firstReach) :=
    hraw.div_const firstReach
  have hsecondScaled : Summable (fun choice =>
      (suffixStoppingLaw second cutoff choice).toReal *
        (reachError / firstReach)) :=
    (pmf_toReal_summable (suffixStoppingLaw second cutoff)).mul_right
      (reachError / firstReach)
  have hrightSummable : Summable (fun choice =>
      rawError choice / firstReach +
        (suffixStoppingLaw second cutoff choice).toReal *
          (reachError / firstReach)) := hrawDiv.add hsecondScaled
  rw [pmfOperationalDistance_eq_tsum_abs]
  calc
    (∑' choice,
        |(suffixStoppingLaw first cutoff choice).toReal -
          (suffixStoppingLaw second cutoff choice).toReal|) <=
        ∑' choice, (rawError choice / firstReach +
          (suffixStoppingLaw second cutoff choice).toReal *
            (reachError / firstReach)) :=
      Summable.tsum_le_tsum hpoint
        (summable_abs_toReal_sub
          (suffixStoppingLaw first cutoff) (suffixStoppingLaw second cutoff))
        hrightSummable
    _ = (∑' choice, rawError choice) / firstReach +
        reachError / firstReach := by
      rw [hrawDiv.tsum_add hsecondScaled, tsum_div_const, tsum_mul_right,
        pmf_toReal_tsum_one, one_mul]
    _ <= distance / firstReach + distance / firstReach := by
      gcongr
    _ = (2 / firstReach) * distance := by ring
    _ <= (2 / rho) * distance := by
      gcongr

end Probability
end Math

namespace GameTheory

open _root_.Math _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem operational_pureTimeProfile_liveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingPureTimeProfileBehavior reward times) time =
      QuittingSureSetOwnerRepair.quittingPureSetRoot
        (quittingPureTimeCoalitionAt times time) := by
  funext who
  simp only [quittingProfileLiveRoot, quittingPureTimeProfileBehavior,
    quittingPureTimeBehaviorStrategy, quittingPureTimeCoalitionAt,
    QuittingSureSetOwnerRepair.quittingPureSetRoot,
    QuittingSureSetOwnerRepair.quittingSetAction, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases hchoice : times who with
  | none => simp [quittingPureTimeHazard]
  | some chosen =>
      by_cases hchosen : chosen = time
      · subst chosen
        simp
      · rw [quittingPureTimeHazard_some_of_ne (Ne.symm hchosen)]
        simp [hchosen]

omit [DecidableEq ι] in
private theorem operational_liveRoot_allContinueContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingProfileAllContinueContinuation reward profile) time =
      quittingProfileLiveRoot reward profile (time + 1) := by
  funext who
  unfold quittingProfileLiveRoot quittingProfileAllContinueContinuation
    StochasticGame.shiftProfile
  rw [consHist_allContinue_quittingLiveHist]

omit [DecidableEq ι] in
private theorem operational_allContinueSpine_continuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingAllContinueProfileSpine reward
        (quittingProfileAllContinueContinuation reward profile) time =
      quittingAllContinueProfileSpine reward profile (time + 1) := by
  induction time with
  | zero => rfl
  | succ time ih =>
      change quittingProfileAllContinueContinuation reward
          (quittingAllContinueProfileSpine reward
            (quittingProfileAllContinueContinuation reward profile) time) =
        quittingProfileAllContinueContinuation reward
          (quittingAllContinueProfileSpine reward profile (time + 1))
      exact congrArg (quittingProfileAllContinueContinuation reward) ih

private theorem operational_terminalPayoff_eq_spine_of_roots_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    ∀ {deadline : ℕ},
      (∀ time < deadline,
        quittingProfileLiveRoot reward profile time = quittingAllContinueRoot) →
      quittingTerminalPayoff reward profile observer =
        quittingTerminalPayoff reward
          (quittingAllContinueProfileSpine reward profile deadline) observer := by
  intro deadline
  induction deadline generalizing profile with
  | zero =>
      intro _
      rfl
  | succ deadline ih =>
      intro hbefore
      have hroot : quittingProfileRoot reward profile =
          quittingAllContinueRoot := by
        have hzero := hbefore 0 (Nat.zero_lt_succ deadline)
        rw [← quittingProfileSpineRoot_eq_profileLiveRoot] at hzero
        simpa [quittingProfileSpineRoot,
          quittingAllContinueProfileSpine] using hzero
      have hone : quittingTerminalPayoff reward profile observer =
          quittingTerminalPayoff reward
            (quittingProfileAllContinueContinuation reward profile) observer := by
        rw [← quittingTerminalPayoff_firstStageAdapter reward profile observer]
        unfold quittingFirstStageAdapter
        rw [hroot, quittingTerminalPayoff_rootThenContinuation_eq]
        change (quittingTerminalSemanticPrefix reward quittingAllContinueRoot
          (quittingTerminalSemanticPair reward
            (quittingProfileAllContinueContinuation reward profile))).1 observer = _
        rw [quittingTerminalSemanticPrefix_allContinue_eq]
        rfl
      have htailBefore : ∀ time < deadline,
          quittingProfileLiveRoot reward
              (quittingProfileAllContinueContinuation reward profile) time =
            quittingAllContinueRoot := by
        intro time htime
        rw [operational_liveRoot_allContinueContinuation]
        exact hbefore (time + 1) (by omega)
      rw [hone, ih _ htailBefore,
        operational_allContinueSpine_continuation]

private theorem operational_pureTimeProfile_terminalPayoff_eq_deadline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (deadline : ℕ)
    (hbefore : ∀ time < deadline,
      quittingPureTimeCoalitionAt times time = ∅)
    (hnonempty : (quittingPureTimeCoalitionAt times deadline).Nonempty) :
    quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward times) =
      reward ⟨quittingPureTimeCoalitionAt times deadline, hnonempty⟩ := by
  let profile := quittingPureTimeProfileBehavior reward times
  let coalition := quittingPureTimeCoalitionAt times deadline
  have hrootsBefore : ∀ time < deadline,
      quittingProfileLiveRoot reward profile time = quittingAllContinueRoot := by
    intro time htime
    rw [operational_pureTimeProfile_liveRoot]
    rw [hbefore time htime]
    exact quittingPureSetRoot_empty
  have hspine : quittingTerminalPayoff reward profile =
      quittingTerminalPayoff reward
        (quittingAllContinueProfileSpine reward profile deadline) := by
    funext observer
    exact operational_terminalPayoff_eq_spine_of_roots_before
      reward profile observer hrootsBefore
  rw [show quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward times) =
      quittingTerminalPayoff reward
        (quittingAllContinueProfileSpine reward profile deadline) by
    simpa [profile] using hspine]
  have hroot : quittingProfileRoot reward
      (quittingAllContinueProfileSpine reward profile deadline) =
    QuittingSureSetOwnerRepair.quittingPureSetRoot coalition := by
    have hlive := operational_pureTimeProfile_liveRoot reward times deadline
    rw [← quittingProfileSpineRoot_eq_profileLiveRoot] at hlive
    simpa [quittingProfileSpineRoot, profile, coalition] using hlive
  funext observer
  rw [← quittingTerminalPayoff_firstStageAdapter]
  unfold quittingFirstStageAdapter
  rw [hroot]
  rw [← QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty
    reward hnonempty]
  exact quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
    coalition hnonempty _ observer

/-- The terminal payoff of a deterministic stopping-time profile is exactly
the reward attached to its labelled first-stopping outcome, including the
all-Never outcome. -/
theorem quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward times) observer =
      quittingTerminalOutcomeReward reward
        (quittingFirstStoppingOutcome times) observer := by
  classical
  by_cases hfinite : ∃ who time, times who = some time
  · have hearliestNe : quittingEarliestStoppingValue times ≠ ⊤ := by
      intro hearliest
      obtain ⟨who, time, htime⟩ := hfinite
      have hle : quittingEarliestStoppingValue times ≤
          quittingStoppingTimeValue (times who) :=
        Finset.inf_le (Finset.mem_univ who)
      rw [hearliest, htime] at hle
      simp [quittingStoppingTimeValue] at hle
    obtain ⟨first, -, hfirst⟩ := Finset.exists_mem_eq_inf
      (Finset.univ : Finset ι) Finset.univ_nonempty
      (fun who => quittingStoppingTimeValue (times who))
    cases htime : times first with
    | none =>
        exfalso
        apply hearliestNe
        unfold quittingEarliestStoppingValue
        rw [hfirst, htime]
        rfl
    | some deadline =>
        have hearliest : quittingEarliestStoppingValue times = deadline := by
          unfold quittingEarliestStoppingValue
          rw [hfirst, htime]
          rfl
        have hbefore : ∀ time < deadline,
            quittingPureTimeCoalitionAt times time = ∅ := by
          intro time htimeLt
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨who, hwho⟩
          have hwhoTime : times who = some time := by
            simpa [quittingPureTimeCoalitionAt] using hwho
          have hle : quittingEarliestStoppingValue times ≤
              quittingStoppingTimeValue (times who) :=
            Finset.inf_le (Finset.mem_univ who)
          rw [hearliest, hwhoTime] at hle
          have : deadline ≤ time := by
            simpa [quittingStoppingTimeValue] using hle
          omega
        have hnonempty :
            (quittingPureTimeCoalitionAt times deadline).Nonempty := by
          exact ⟨first, by simp [quittingPureTimeCoalitionAt, htime]⟩
        have hcoalition : quittingEarliestStoppingCoalition times =
            quittingPureTimeCoalitionAt times deadline := by
          ext who
          simp only [quittingEarliestStoppingCoalition,
            quittingPureTimeCoalitionAt, Finset.mem_filter,
            Finset.mem_univ, true_and, hearliest]
          cases hwho : times who with
          | none => simp [quittingStoppingTimeValue]
          | some time => simp [quittingStoppingTimeValue]
        have houtcome : quittingFirstStoppingOutcome times =
            some ⟨quittingPureTimeCoalitionAt times deadline, hnonempty⟩ := by
          rw [quittingFirstStoppingOutcome, if_neg hearliestNe]
          congr 2
        rw [houtcome]
        exact congrFun
          (operational_pureTimeProfile_terminalPayoff_eq_deadline
            reward times deadline hbefore hnonempty) observer
  · have htimes : times = fun _ => none := by
      funext who
      cases htime : times who with
      | none => rfl
      | some time => exact False.elim (hfinite ⟨who, time, htime⟩)
    subst times
    change quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) observer =
      quittingTerminalOutcomeReward reward
        (quittingFirstStoppingOutcome (fun _ : ι => none)) observer
    rw [quittingTerminalPayoff_quittingAlwaysContinue,
      quittingFirstStoppingOutcome_all_never]
    rfl

/-- Operational distance between the labelled terminal laws generated by two
families of independent complete stopping laws. -/
def quittingTerminalOutcomeOperationalDistance [Nonempty ι]
    (first second : ι -> PMF (Option Nat)) : Real :=
  2 * pmfTV
    (quittingIndependentTerminalOutcomeLaw first)
    (quittingIndependentTerminalOutcomeLaw second)

/-- Replacing one complete marginal changes the finite terminal law by at
most that marginal's general total variation. -/
theorem pmfTV_quittingIndependentTerminalOutcomeLaw_update_le [Nonempty ι]
    (laws : ι -> PMF (Option Nat)) (who : ι)
    (first second : PMF (Option Nat)) :
    pmfTV
        (quittingIndependentTerminalOutcomeLaw
          (Function.update laws who first))
        (quittingIndependentTerminalOutcomeLaw
          (Function.update laws who second)) <=
      pmfGeneralTV first second := by
  have hwho : who ∉
      (QuittingStoppingIntervention.empty :
        QuittingStoppingIntervention ι).carrier := by
    simp [QuittingStoppingIntervention.empty]
  have h := pmfTV_quittingCounterfactualOutcomeLaw_update_le
    laws QuittingStoppingIntervention.empty first second (who := who) hwho
  have hempty (family : ι -> PMF (Option Nat)) :
      (QuittingStoppingIntervention.empty :
        QuittingStoppingIntervention ι).applyLaws family = family := by
    funext other
    simp [QuittingStoppingIntervention.empty,
      QuittingStoppingIntervention.applyLaws]
  simpa only [quittingCounterfactualOutcomeLaw, hempty] using h

/-- Changing any supplied finite set of independent marginals costs at most
the sum of their general total variations after terminal pushforward. -/
theorem pmfTV_quittingIndependentTerminalOutcomeLaw_replaceOn_le_sum
    [Nonempty ι] (first second : ι -> PMF (Option Nat))
    (coordinates : Finset ι) :
    pmfTV (quittingIndependentTerminalOutcomeLaw first)
        (quittingIndependentTerminalOutcomeLaw fun who =>
          if who ∈ coordinates then second who else first who) <=
      ∑ who ∈ coordinates, pmfGeneralTV (first who) (second who) := by
  classical
  induction coordinates using Finset.induction_on with
  | empty => simp [pmfTV_self]
  | @insert who coordinates hwho ih =>
      let intermediate : ι -> PMF (Option Nat) := fun other =>
        if other ∈ coordinates then second other else first other
      have hwhoIntermediate : intermediate who = first who := by
        simp [intermediate, hwho]
      have hfinal :
          (fun other =>
              if other ∈ insert who coordinates then second other else first other) =
            Function.update intermediate who (second who) := by
        funext other
        by_cases hother : other = who
        · subst other
          simp
        · simp [intermediate, hother]
      calc
        pmfTV (quittingIndependentTerminalOutcomeLaw first)
            (quittingIndependentTerminalOutcomeLaw fun other =>
              if other ∈ insert who coordinates then second other else first other) =
            pmfTV (quittingIndependentTerminalOutcomeLaw first)
              (quittingIndependentTerminalOutcomeLaw
                (Function.update intermediate who (second who))) := by rw [hfinal]
        _ <= pmfTV (quittingIndependentTerminalOutcomeLaw first)
              (quittingIndependentTerminalOutcomeLaw intermediate) +
            pmfTV (quittingIndependentTerminalOutcomeLaw intermediate)
              (quittingIndependentTerminalOutcomeLaw
                (Function.update intermediate who (second who))) :=
          pmfTV_triangle _ _ _
        _ <= (∑ other ∈ coordinates,
              pmfGeneralTV (first other) (second other)) +
            pmfGeneralTV (first who) (second who) := by
          gcongr
          have hstep :=
            pmfTV_quittingIndependentTerminalOutcomeLaw_update_le
              intermediate who (intermediate who) (second who)
          rw [Function.update_eq_self, hwhoIntermediate] at hstep
          exact hstep
        _ = ∑ other ∈ insert who coordinates,
            pmfGeneralTV (first other) (second other) := by
          rw [Finset.sum_insert hwho]
          ring

/-- Terminal outcome pushforward contracts the sum of marginal operational
distances. -/
theorem quittingTerminalOutcomeOperationalDistance_le_sum
    [Nonempty ι] (first second : ι -> PMF (Option Nat)) :
    quittingTerminalOutcomeOperationalDistance first second <=
      ∑ who, pmfOperationalDistance (first who) (second who) := by
  have h := pmfTV_quittingIndependentTerminalOutcomeLaw_replaceOn_le_sum
    first second Finset.univ
  simp only [Finset.mem_univ, ↓reduceIte] at h
  unfold quittingTerminalOutcomeOperationalDistance pmfOperationalDistance
  calc
    2 * pmfTV
          (quittingIndependentTerminalOutcomeLaw first)
          (quittingIndependentTerminalOutcomeLaw second) <=
        2 * ∑ who, pmfGeneralTV (first who) (second who) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ∑ who, 2 * pmfGeneralTV (first who) (second who) := by
      rw [Finset.mul_sum]

/-- A common unilateral replacement removes that player's marginal from the
terminal-law stability bill. -/
theorem quittingTerminalOutcomeOperationalDistance_update_same_le_sum_opponents
    [Nonempty ι] (first second : ι -> PMF (Option Nat)) (who : ι)
    (replacement : PMF (Option Nat)) :
    quittingTerminalOutcomeOperationalDistance
        (Function.update first who replacement)
        (Function.update second who replacement) <=
      ∑ other ∈ Finset.univ.erase who,
        pmfOperationalDistance (first other) (second other) := by
  have h := quittingTerminalOutcomeOperationalDistance_le_sum
    (Function.update first who replacement)
    (Function.update second who replacement)
  calc
    quittingTerminalOutcomeOperationalDistance
        (Function.update first who replacement)
        (Function.update second who replacement) <=
      ∑ other,
        pmfOperationalDistance
          ((Function.update first who replacement) other)
          ((Function.update second who replacement) other) := h
    _ = ∑ other ∈ Finset.univ.erase who,
        pmfOperationalDistance (first other) (second other) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
      simp only [Function.update_self, pmfOperationalDistance_self, add_zero]
      apply Finset.sum_congr rfl
      intro other hother
      have hne : other ≠ who := Finset.ne_of_mem_erase hother
      simp only [Function.update_of_ne hne]

/-- Expected terminal reward read directly from independent complete stopping
laws. -/
def quittingStoppingLawExpectedPayoff [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> PMF (Option Nat)) (who : ι) : Real :=
  expect (quittingIndependentTerminalOutcomeLaw laws)
    (fun outcome => quittingTerminalOutcomeReward reward outcome who)

/-- The expected payoff of independent complete stopping laws is exactly the
terminal payoff of their canonical conditional-hazard realization. -/
theorem quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> PMF (Option Nat)) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward laws) observer =
      quittingStoppingLawExpectedPayoff reward laws observer := by
  classical
  have hmixture := Math.Probability.expect_pmfPi_eq_of_separatelyAffine
    (fun who choice =>
      quittingPureTimeBehaviorStrategy reward who choice)
    (fun who law =>
      quittingStoppingLawBehaviorStrategy reward who law)
    (fun profile => quittingTerminalPayoff reward profile observer)
    laws
    (fun profile => abs_quittingTerminalPayoff_le_quittingRewardBound
      reward profile observer)
    (fun mixer profile =>
      quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect
        reward profile mixer observer (laws mixer))
  calc
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward laws) observer =
      expect (Math.PMFProduct.pmfPi laws) (fun times =>
        quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward times) observer) := by
      change quittingTerminalPayoff reward
          (fun i => quittingStoppingLawBehaviorStrategy reward i (laws i))
          observer =
        expect (Math.PMFProduct.pmfPi laws) (fun times =>
          quittingTerminalPayoff reward
            (fun i => quittingPureTimeBehaviorStrategy reward i (times i))
            observer)
      exact hmixture
    _ = expect (Math.PMFProduct.pmfPi laws) (fun times =>
        quittingTerminalOutcomeReward reward
          (quittingFirstStoppingOutcome times) observer) := by
      apply congrArg (expect (Math.PMFProduct.pmfPi laws))
      funext times
      exact quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome
        reward times observer
    _ = quittingStoppingLawExpectedPayoff reward laws observer := by
      rw [quittingStoppingLawExpectedPayoff,
        quittingIndependentTerminalOutcomeLaw, expect_map]

/-- The expected-payoff semantics of the complete stopping laws extracted
from any behavior profile is its actual terminal payoff. -/
theorem quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    quittingStoppingLawExpectedPayoff reward
        (quittingBehaviorStoppingLaws reward profile) observer =
      quittingTerminalPayoff reward profile observer := by
  classical
  let canonical := quittingStoppingLawProfile reward
    (quittingBehaviorStoppingLaws reward profile)
  have hcanonical : canonical =
      quittingStoppingLawCanonicalizeOn reward profile Finset.univ := by
    funext who
    simp [canonical, quittingStoppingLawProfile,
      quittingStoppingLawCanonicalizeOn, quittingBehaviorStoppingLaws]
  rw [← quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  change quittingTerminalPayoff reward canonical observer = _
  rw [hcanonical,
    quittingTerminalPayoff_stoppingLawCanonicalizeOn_eq]

omit [DecidableEq ι] in
/-- Terminal expected payoff is Lipschitz in the terminal outcome operational
distance. -/
theorem abs_quittingStoppingLawExpectedPayoff_sub_le_terminalOutcomeDistance
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (first second : ι -> PMF (Option Nat)) (who : ι) {bound : Real}
    (hreward : forall terminal player, |reward terminal player| <= bound) :
    |quittingStoppingLawExpectedPayoff reward first who -
        quittingStoppingLawExpectedPayoff reward second who| <=
      bound * quittingTerminalOutcomeOperationalDistance first second := by
  have hbound : 0 <= bound :=
    (abs_nonneg (reward ⟨{who}, Finset.singleton_nonempty who⟩ who)).trans
      (hreward ⟨{who}, Finset.singleton_nonempty who⟩ who)
  have houtcome : forall outcome : QuittingTerminalOutcome ι,
      |quittingTerminalOutcomeReward reward outcome who| <= bound := by
    intro outcome
    cases outcome with
    | none =>
        simpa [quittingTerminalOutcomeReward] using hbound
    | some terminal =>
        simpa [quittingTerminalOutcomeReward] using hreward terminal who
  have h := abs_expect_sub_le_two_mul_pmfTV
      (quittingIndependentTerminalOutcomeLaw first)
      (quittingIndependentTerminalOutcomeLaw second)
      (fun outcome => quittingTerminalOutcomeReward reward outcome who)
      houtcome
  unfold quittingStoppingLawExpectedPayoff
    quittingTerminalOutcomeOperationalDistance
  calc
    _ <= 2 * bound * pmfTV
        (quittingIndependentTerminalOutcomeLaw first)
        (quittingIndependentTerminalOutcomeLaw second) := h
    _ = bound * (2 * pmfTV
        (quittingIndependentTerminalOutcomeLaw first)
        (quittingIndependentTerminalOutcomeLaw second)) := by ring

/-- A common unilateral replacement changes expected payoff by at most the
reward bound times the sum of opponent marginal operational distances. -/
theorem abs_quittingStoppingLawExpectedPayoff_update_same_sub_le_opponents
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (first second : ι -> PMF (Option Nat)) (who : ι)
    (replacement : PMF (Option Nat)) {bound : Real}
    (hreward : forall terminal player, |reward terminal player| <= bound) :
    |quittingStoppingLawExpectedPayoff reward
          (Function.update first who replacement) who -
        quittingStoppingLawExpectedPayoff reward
          (Function.update second who replacement) who| <=
      bound * ∑ other ∈ Finset.univ.erase who,
        pmfOperationalDistance (first other) (second other) := by
  have hbound : 0 <= bound := by
    simpa using
      (abs_nonneg (reward ⟨{who}, Finset.singleton_nonempty who⟩ who)).trans
        (hreward ⟨{who}, Finset.singleton_nonempty who⟩ who)
  exact
    (abs_quittingStoppingLawExpectedPayoff_sub_le_terminalOutcomeDistance
      reward (Function.update first who replacement)
        (Function.update second who replacement) who hreward).trans
      (mul_le_mul_of_nonneg_left
        (quittingTerminalOutcomeOperationalDistance_update_same_le_sum_opponents
          first second who replacement) hbound)

/-- The unrestricted replacement-law payoff envelope at one player. -/
def quittingStoppingLawReplacementPayoffCap [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> PMF (Option Nat)) (who : ι) : Real :=
  sSup (Set.range fun replacement : PMF (Option Nat) =>
    quittingStoppingLawExpectedPayoff reward
      (Function.update laws who replacement) who)

omit [DecidableEq ι] in
private theorem abs_quittingStoppingLawExpectedPayoff_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> PMF (Option Nat)) (who : ι) {bound : Real}
    (hreward : forall terminal player, |reward terminal player| <= bound) :
    |quittingStoppingLawExpectedPayoff reward laws who| <= bound := by
  apply abs_expect_le_of_abs_le
  intro outcome
  cases outcome with
  | none =>
      have hbound : 0 <= bound :=
        (abs_nonneg (reward ⟨{who}, Finset.singleton_nonempty who⟩ who)).trans
          (hreward ⟨{who}, Finset.singleton_nonempty who⟩ who)
      simpa [quittingTerminalOutcomeReward] using hbound
  | some terminal =>
      simpa [quittingTerminalOutcomeReward] using hreward terminal who

/-- Taking the supremum over all complete unilateral replacement laws does
not increase the opponent-distance stability constant. -/
theorem abs_quittingStoppingLawReplacementPayoffCap_sub_le_opponents
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (first second : ι -> PMF (Option Nat)) (who : ι) {bound : Real}
    (hreward : forall terminal player, |reward terminal player| <= bound) :
    |quittingStoppingLawReplacementPayoffCap reward first who -
        quittingStoppingLawReplacementPayoffCap reward second who| <=
      bound * ∑ other ∈ Finset.univ.erase who,
        pmfOperationalDistance (first other) (second other) := by
  let firstValue := fun replacement : PMF (Option Nat) =>
    quittingStoppingLawExpectedPayoff reward
      (Function.update first who replacement) who
  let secondValue := fun replacement : PMF (Option Nat) =>
    quittingStoppingLawExpectedPayoff reward
      (Function.update second who replacement) who
  let error := bound * ∑ other ∈ Finset.univ.erase who,
    pmfOperationalDistance (first other) (second other)
  have hfirstBound : BddAbove (Set.range firstValue) := by
    refine ⟨bound, ?_⟩
    rintro value ⟨replacement, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingStoppingLawExpectedPayoff_le reward _ who hreward)
  have hsecondBound : BddAbove (Set.range secondValue) := by
    refine ⟨bound, ?_⟩
    rintro value ⟨replacement, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingStoppingLawExpectedPayoff_le reward _ who hreward)
  have hpoint : forall replacement,
      |firstValue replacement - secondValue replacement| <= error := by
    intro replacement
    exact abs_quittingStoppingLawExpectedPayoff_update_same_sub_le_opponents
      reward first second who replacement hreward
  have hfirstSecond :
      sSup (Set.range firstValue) <= sSup (Set.range secondValue) + error := by
    apply csSup_le (Set.range_nonempty firstValue)
    rintro _ ⟨replacement, rfl⟩
    have hsup := le_csSup hsecondBound ⟨replacement, rfl⟩
    linarith [le_abs_self (firstValue replacement - secondValue replacement),
      hpoint replacement]
  have hsecondFirst :
      sSup (Set.range secondValue) <= sSup (Set.range firstValue) + error := by
    apply csSup_le (Set.range_nonempty secondValue)
    rintro _ ⟨replacement, rfl⟩
    have hsup := le_csSup hfirstBound ⟨replacement, rfl⟩
    linarith [neg_le_abs (firstValue replacement - secondValue replacement),
      hpoint replacement]
  change |sSup (Set.range firstValue) - sSup (Set.range secondValue)| <= error
  rw [abs_le]
  constructor <;> linarith

/-- The replacement-law payoff envelope of the stopping laws extracted from
an arbitrary behavior profile is exactly its unrestricted behavioral
best-response value. -/
theorem quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingStoppingLawReplacementPayoffCap reward
        (quittingBehaviorStoppingLaws reward profile) who =
      quittingContinuationBestResponseValue reward profile who := by
  classical
  unfold quittingStoppingLawReplacementPayoffCap
    quittingContinuationBestResponseValue
  apply congrArg sSup
  ext value
  simp only [Set.mem_range]
  constructor
  · rintro ⟨replacement, rfl⟩
    let deviation :=
      quittingStoppingLawBehaviorStrategy reward who replacement
    refine ⟨deviation, ?_⟩
    rw [← quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff
      reward (Function.update profile who deviation) who]
    rw [quittingBehaviorStoppingLaws_update,
      quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy]
  · rintro ⟨deviation, rfl⟩
    refine ⟨quittingBehaviorStoppingLaw reward deviation, ?_⟩
    rw [← quittingBehaviorStoppingLaws_update]
    exact quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff
      reward (Function.update profile who deviation) who

omit [DecidableEq ι] in
/-- The canonical conditional-hazard realization returns every supplied
complete stopping law exactly, coordinate by coordinate. -/
theorem quittingBehaviorStoppingLaws_stoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> PMF (Option Nat)) :
    quittingBehaviorStoppingLaws reward
        (quittingStoppingLawProfile reward laws) = laws := by
  funext who
  exact quittingBehaviorStoppingLaw_stoppingLawProfile reward laws who

/-- For a supplied complete stopping-law profile, the law-replacement cap is
literally the unrestricted behavioral best-response value of its canonical
conditional-hazard realization. -/
theorem quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> PMF (Option Nat)) (who : ι) :
    quittingStoppingLawReplacementPayoffCap reward laws who =
      quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward laws) who := by
  calc
    quittingStoppingLawReplacementPayoffCap reward laws who =
        quittingStoppingLawReplacementPayoffCap reward
          (quittingBehaviorStoppingLaws reward
            (quittingStoppingLawProfile reward laws)) who := by
      rw [quittingBehaviorStoppingLaws_stoppingLawProfile]
    _ = quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward laws) who :=
      quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue
        reward (quittingStoppingLawProfile reward laws) who

/-- Complete behavioral best-response values are Lipschitz in the full
operational distance between the opponents' induced stopping laws. -/
theorem abs_quittingContinuationBestResponseValue_sub_le_opponentStoppingLaws
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (who : ι) {bound : Real}
    (hreward : forall terminal player, |reward terminal player| <= bound) :
    |quittingContinuationBestResponseValue reward first who -
        quittingContinuationBestResponseValue reward second who| <=
      bound * ∑ other ∈ Finset.univ.erase who,
        pmfOperationalDistance
          (quittingBehaviorStoppingLaws reward first other)
          (quittingBehaviorStoppingLaws reward second other) := by
  rw [← quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue
      reward first who,
    ← quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue
      reward second who]
  exact abs_quittingStoppingLawReplacementPayoffCap_sub_le_opponents
    reward (quittingBehaviorStoppingLaws reward first)
      (quittingBehaviorStoppingLaws reward second) who hreward

end GameTheory
