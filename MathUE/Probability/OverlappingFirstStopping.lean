/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.StoppingLawReconstruction

/-!
# Overlapping first-stopping square-root law

Three independent complete stopping laws cannot put arbitrary mass on the
events that the first clock ties the second strictly before the third and
that the first clock ties the third strictly before the second.  Independence
is represented definitionally by taking three marginal laws and multiplying
their finite-date masses.
-/

noncomputable section

open scoped BigOperators

namespace Math.Probability.DiscreteHazard

namespace ScalarHazard

/-- Conditional mass, inside a finite window, that the first two clocks stop
together strictly before the third clock. -/
def equalFirstSecondBeforeThirdWindowMass
    (first second third : ScalarHazard) (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    first.survival start offset * second.survival start offset *
      third.survival start offset * first.stop (start + offset) *
        second.stop (start + offset) * (1 - third.stop (start + offset))

/-- Conditional mass, inside a finite window, that the first and third clocks
stop together strictly before the second clock. -/
def equalFirstThirdBeforeSecondWindowMass
    (first second third : ScalarHazard) (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    first.survival start offset * second.survival start offset *
      third.survival start offset * first.stop (start + offset) *
        third.stop (start + offset) * (1 - second.stop (start + offset))

theorem equalFirstSecondBeforeThirdWindowMass_nonneg
    (first second third : ScalarHazard) (start fuel : ℕ) :
    0 ≤ equalFirstSecondBeforeThirdWindowMass first second third start fuel := by
  apply Finset.sum_nonneg
  intro offset _
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (first.survival_nonneg start offset)
            (second.survival_nonneg start offset))
          (third.survival_nonneg start offset))
        (first.stop_nonneg _))
      (second.stop_nonneg _))
    (sub_nonneg.mpr (third.stop_le_one _))

theorem equalFirstThirdBeforeSecondWindowMass_nonneg
    (first second third : ScalarHazard) (start fuel : ℕ) :
    0 ≤ equalFirstThirdBeforeSecondWindowMass first second third start fuel := by
  apply Finset.sum_nonneg
  intro offset _
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (first.survival_nonneg start offset)
            (second.survival_nonneg start offset))
          (third.survival_nonneg start offset))
        (first.stop_nonneg _))
      (third.stop_nonneg _))
    (sub_nonneg.mpr (second.stop_le_one _))

private theorem equalFirstSecondBeforeThirdWindowMass_succ
    (first second third : ScalarHazard) (start fuel : ℕ) :
    equalFirstSecondBeforeThirdWindowMass first second third start (fuel + 1) =
      first.stop start * second.stop start * (1 - third.stop start) +
        (1 - first.stop start) * (1 - second.stop start) *
          (1 - third.stop start) *
            equalFirstSecondBeforeThirdWindowMass
              first second third (start + 1) fuel := by
  rw [equalFirstSecondBeforeThirdWindowMass, Finset.sum_range_succ']
  simp only [survival_zero, one_mul, Nat.add_zero]
  rw [add_comm]
  rw [equalFirstSecondBeforeThirdWindowMass, Finset.mul_sum]
  apply congrArg (fun value =>
    first.stop start * second.stop start * (1 - third.stop start) + value)
  apply Finset.sum_congr rfl
  intro offset _
  rw [survival_succ_left, survival_succ_left, survival_succ_left]
  simp only [Nat.add_comm, Nat.add_left_comm]
  ring

private theorem equalFirstThirdBeforeSecondWindowMass_succ
    (first second third : ScalarHazard) (start fuel : ℕ) :
    equalFirstThirdBeforeSecondWindowMass first second third start (fuel + 1) =
      first.stop start * third.stop start * (1 - second.stop start) +
        (1 - first.stop start) * (1 - second.stop start) *
          (1 - third.stop start) *
            equalFirstThirdBeforeSecondWindowMass
              first second third (start + 1) fuel := by
  rw [equalFirstThirdBeforeSecondWindowMass, Finset.sum_range_succ']
  simp only [survival_zero, one_mul, Nat.add_zero]
  rw [add_comm]
  rw [equalFirstThirdBeforeSecondWindowMass, Finset.mul_sum]
  apply congrArg (fun value =>
    first.stop start * third.stop start * (1 - second.stop start) + value)
  apply Finset.sum_congr rfl
  intro offset _
  rw [survival_succ_left, survival_succ_left, survival_succ_left]
  simp only [Nat.add_comm, Nat.add_left_comm]
  ring

end ScalarHazard

/-! ## Scalar square-root propagation -/

/-- The square root of a nonnegative quadratic lies below its endpoint chord. -/
theorem sqrt_quadratic_chord
    {constant scale weight : ℝ}
    (hconstant : 0 ≤ constant) (hscale : 0 ≤ scale)
    (hweight : weight ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (constant + scale * weight ^ 2) ≤
      weight * Real.sqrt (constant + scale) +
        (1 - weight) * Real.sqrt constant := by
  have hconstantScale : 0 ≤ constant + scale := add_nonneg hconstant hscale
  have hsqrtOrder : Real.sqrt constant ≤ Real.sqrt (constant + scale) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right hscale)
  have hcross : constant ≤
      Real.sqrt (constant + scale) * Real.sqrt constant := by
    calc
      constant = Real.sqrt constant * Real.sqrt constant := by
        rw [Real.mul_self_sqrt hconstant]
      _ ≤ Real.sqrt (constant + scale) * Real.sqrt constant :=
        mul_le_mul_of_nonneg_right hsqrtOrder (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg
      (mul_nonneg hweight.1 (Real.sqrt_nonneg _))
      (mul_nonneg (sub_nonneg.mpr hweight.2) (Real.sqrt_nonneg _))
  · have hsquareConstant := Real.sq_sqrt hconstant
    have hsquareConstantScale := Real.sq_sqrt hconstantScale
    have hcoefficient : 0 ≤ 2 * weight * (1 - weight) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hweight.1)
        (sub_nonneg.mpr hweight.2)
    have hproduct : 0 ≤ 2 * weight * (1 - weight) *
        (Real.sqrt (constant + scale) * Real.sqrt constant - constant) :=
      mul_nonneg hcoefficient (sub_nonneg.mpr hcross)
    nlinarith

/-- The two-term Cauchy--Schwarz bound written with nonnegative square roots. -/
theorem sqrt_mul_add_sqrt_mul_le_sqrt_add_mul_add
    {firstWeight secondWeight firstValue secondValue : ℝ}
    (hfirstWeight : 0 ≤ firstWeight) (hsecondWeight : 0 ≤ secondWeight)
    (hfirstValue : 0 ≤ firstValue) (hsecondValue : 0 ≤ secondValue) :
    Real.sqrt (firstWeight * firstValue) +
        Real.sqrt (secondWeight * secondValue) ≤
      Real.sqrt ((firstWeight + secondWeight) *
        (firstValue + secondValue)) := by
  let f : Bool → ℝ := fun bit => if bit then secondWeight else firstWeight
  let g : Bool → ℝ := fun bit => if bit then secondValue else firstValue
  have hf : ∀ bit, 0 ≤ f bit := by
    intro bit
    cases bit <;> simp [f, hfirstWeight, hsecondWeight]
  have hg : ∀ bit, 0 ≤ g bit := by
    intro bit
    cases bit <;> simp [g, hfirstValue, hsecondValue]
  have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset Bool) hf hg
  simp only [Fintype.sum_bool, f, g, Bool.false_eq_true, ↓reduceIte] at hcs
  rw [Real.sqrt_mul hfirstWeight, Real.sqrt_mul hsecondWeight]
  have hcs' :
      Real.sqrt firstWeight * Real.sqrt firstValue +
          Real.sqrt secondWeight * Real.sqrt secondValue ≤
        Real.sqrt (firstWeight + secondWeight) *
          Real.sqrt (firstValue + secondValue) := by
    simpa [add_comm] using hcs
  rw [← Real.sqrt_mul (add_nonneg hfirstWeight hsecondWeight)] at hcs'
  exact hcs'

/-- The overlapping-pair bound at the future endpoint concentrated on the first pair. -/
theorem firstSecond_endpoint_le_one
    {first second third : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt
          (first * second * (1 - third) +
            (1 - first) * (1 - second) * (1 - third)) +
        Real.sqrt (first * third * (1 - second)) ≤ 1 := by
  let middle := first * second + (1 - first) * (1 - second)
  have hmiddle : 0 ≤ middle := by
    dsimp only [middle]
    exact add_nonneg (mul_nonneg hfirst.1 hsecond.1)
      (mul_nonneg (sub_nonneg.mpr hfirst.2) (sub_nonneg.mpr hsecond.2))
  have hfirstContinue : 0 ≤ first * (1 - second) :=
    mul_nonneg hfirst.1 (sub_nonneg.mpr hsecond.2)
  have hcs := sqrt_mul_add_sqrt_mul_le_sqrt_add_mul_add
    (sub_nonneg.mpr hthird.2) hthird.1 hmiddle hfirstContinue
  have hsumLe : middle + first * (1 - second) ≤ 1 := by
    have hgap : 0 ≤ (1 - first) * second :=
      mul_nonneg (sub_nonneg.mpr hfirst.2) hsecond.1
    calc
      middle + first * (1 - second) = 1 - (1 - first) * second := by
        dsimp only [middle]
        ring
      _ ≤ 1 := sub_le_self _ hgap
  have hsqrtLe : Real.sqrt (middle + first * (1 - second)) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith⟩
  calc
    _ = Real.sqrt ((1 - third) * middle) +
        Real.sqrt (third * (first * (1 - second))) := by
      apply congrArg₂ (· + ·)
      · apply congrArg Real.sqrt
        dsimp only [middle]
        ring
      · apply congrArg Real.sqrt
        ring
    _ ≤ Real.sqrt (((1 - third) + third) *
        (middle + first * (1 - second))) := hcs
    _ = Real.sqrt (middle + first * (1 - second)) := by ring_nf
    _ ≤ 1 := hsqrtLe

/-- The overlapping-pair bound at the future endpoint concentrated on the second pair. -/
theorem firstThird_endpoint_le_one
    {first second third : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (first * second * (1 - third)) +
        Real.sqrt
          (first * third * (1 - second) +
            (1 - first) * (1 - second) * (1 - third)) ≤ 1 := by
  rw [add_comm]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    firstSecond_endpoint_le_one hfirst hthird hsecond

/-- One-row propagation of the overlapping first-stopping square-root body. -/
theorem overlappingFirstStopping_squareRoot_step
    {first second third futureFirstSecond futureFirstThird : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hfutureFirstSecond : 0 ≤ futureFirstSecond)
    (hfutureFirstThird : 0 ≤ futureFirstThird)
    (hfuture : Real.sqrt futureFirstSecond +
      Real.sqrt futureFirstThird ≤ 1) :
    Real.sqrt
          (first * second * (1 - third) +
            (1 - first) * (1 - second) * (1 - third) *
              futureFirstSecond) +
        Real.sqrt
          (first * third * (1 - second) +
            (1 - first) * (1 - second) * (1 - third) *
              futureFirstThird) ≤ 1 := by
  let commonContinue :=
    (1 - first) * (1 - second) * (1 - third)
  let firstSecondNow := first * second * (1 - third)
  let firstThirdNow := first * third * (1 - second)
  let u := Real.sqrt futureFirstSecond
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_nonneg _
    · linarith [Real.sqrt_nonneg futureFirstThird]
  have hcommonContinue : 0 ≤ commonContinue := by
    dsimp only [commonContinue]
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hfirst.2) (sub_nonneg.mpr hsecond.2))
      (sub_nonneg.mpr hthird.2)
  have hfirstSecondNow : 0 ≤ firstSecondNow := by
    dsimp only [firstSecondNow]
    exact mul_nonneg (mul_nonneg hfirst.1 hsecond.1)
      (sub_nonneg.mpr hthird.2)
  have hfirstThirdNow : 0 ≤ firstThirdNow := by
    dsimp only [firstThirdNow]
    exact mul_nonneg (mul_nonneg hfirst.1 hthird.1)
      (sub_nonneg.mpr hsecond.2)
  have hfutureFirstSecondEq : futureFirstSecond = u ^ 2 := by
    dsimp only [u]
    rw [Real.sq_sqrt hfutureFirstSecond]
  have hfutureFirstThirdBound : futureFirstThird ≤ (1 - u) ^ 2 := by
    have hsqrtBound : Real.sqrt futureFirstThird ≤ 1 - u := by
      dsimp only [u]
      linarith
    have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg _) hsqrtBound
    nlinarith [Real.sq_sqrt hfutureFirstThird]
  have hsecondRadicand :
      firstThirdNow + commonContinue * futureFirstThird ≤
        firstThirdNow + commonContinue * (1 - u) ^ 2 := by
    simpa [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left hfutureFirstThirdBound hcommonContinue)
      firstThirdNow
  have hfirstChord := sqrt_quadratic_chord hfirstSecondNow hcommonContinue hu
  have hsecondChord := sqrt_quadratic_chord hfirstThirdNow hcommonContinue
    (show 1 - u ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith [hu.1, hu.2])
  have hfirstEndpoint := firstSecond_endpoint_le_one hfirst hsecond hthird
  have hsecondEndpoint := firstThird_endpoint_le_one hfirst hsecond hthird
  rw [hfutureFirstSecondEq]
  calc
    Real.sqrt (firstSecondNow + commonContinue * u ^ 2) +
        Real.sqrt (firstThirdNow + commonContinue * futureFirstThird) ≤
      Real.sqrt (firstSecondNow + commonContinue * u ^ 2) +
        Real.sqrt (firstThirdNow + commonContinue * (1 - u) ^ 2) := by
          simpa [add_comm] using add_le_add_left
            (Real.sqrt_le_sqrt hsecondRadicand)
            (Real.sqrt (firstSecondNow + commonContinue * u ^ 2))
    _ ≤ u * Real.sqrt (firstSecondNow + commonContinue) +
          (1 - u) * Real.sqrt firstSecondNow +
        ((1 - u) * Real.sqrt (firstThirdNow + commonContinue) +
          (1 - (1 - u)) * Real.sqrt firstThirdNow) := by
      gcongr
    _ = u *
          (Real.sqrt (firstSecondNow + commonContinue) +
            Real.sqrt firstThirdNow) +
        (1 - u) *
          (Real.sqrt firstSecondNow +
            Real.sqrt (firstThirdNow + commonContinue)) := by ring
    _ ≤ u * 1 + (1 - u) * 1 := by
      have hfirstEndpoint' :
          Real.sqrt (firstSecondNow + commonContinue) +
            Real.sqrt firstThirdNow ≤ 1 := by
        simpa [firstSecondNow, firstThirdNow, commonContinue,
          mul_assoc] using hfirstEndpoint
      have hsecondEndpoint' :
          Real.sqrt firstSecondNow +
            Real.sqrt (firstThirdNow + commonContinue) ≤ 1 := by
        simpa [firstSecondNow, firstThirdNow, commonContinue,
          mul_assoc] using hsecondEndpoint
      exact add_le_add
        (mul_le_mul_of_nonneg_left hfirstEndpoint' hu.1)
        (mul_le_mul_of_nonneg_left hsecondEndpoint'
          (sub_nonneg.mpr hu.2))
    _ = 1 := by ring

namespace ScalarHazard

/-- The square-root law on every common finite window of three scalar hazards. -/
theorem twoOverlappingFirstStoppingWindowMasses_sqrt_sum_le_one
    (first second third : ScalarHazard) (start fuel : ℕ) :
    Real.sqrt (equalFirstSecondBeforeThirdWindowMass first second third start fuel) +
      Real.sqrt (equalFirstThirdBeforeSecondWindowMass first second third start fuel) ≤ 1 := by
  induction fuel generalizing start with
  | zero => simp [equalFirstSecondBeforeThirdWindowMass,
      equalFirstThirdBeforeSecondWindowMass]
  | succ fuel ih =>
      rw [equalFirstSecondBeforeThirdWindowMass_succ,
        equalFirstThirdBeforeSecondWindowMass_succ]
      exact overlappingFirstStopping_squareRoot_step
        ⟨first.stop_nonneg start, first.stop_le_one start⟩
        ⟨second.stop_nonneg start, second.stop_le_one start⟩
        ⟨third.stop_nonneg start, third.stop_le_one start⟩
        (equalFirstSecondBeforeThirdWindowMass_nonneg
          first second third (start + 1) fuel)
        (equalFirstThirdBeforeSecondWindowMass_nonneg
          first second third (start + 1) fuel)
        (ih (start + 1))

end ScalarHazard

namespace StoppingLaw

/-- Probability that the first and second independent clocks stop together at
a finite date strictly before the third clock. -/
def equalFirstSecondBeforeThirdMass
    (first second third : PMF (Option ℕ)) : ℝ :=
  ∑' time, finiteMass first time * finiteMass second time *
    survival third (time + 1)

/-- Probability that the first and third independent clocks stop together at
a finite date strictly before the second clock. -/
def equalFirstThirdBeforeSecondMass
    (first second third : PMF (Option ℕ)) : ℝ :=
  ∑' time, finiteMass first time * finiteMass third time *
    survival second (time + 1)

/-- The finite-date atoms of a stopping law form a summable real sequence. -/
theorem summable_finiteMass (law : PMF (Option ℕ)) :
    Summable (finiteMass law) := by
  change Summable (fun time : ℕ => (law (some time)).toReal)
  exact (Math.Probability.pmf_toReal_summable law).comp_injective
    (Option.some_injective ℕ)

/-- A finite stopping-time atom has mass at most one. -/
theorem finiteMass_le_one (law : PMF (Option ℕ)) (time : ℕ) :
    finiteMass law time ≤ 1 := by
  exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one law (some time))

/-- Survival through any finite cutoff has probability at most one. -/
theorem survival_le_one (law : PMF (Option ℕ)) (cutoff : ℕ) :
    survival law cutoff ≤ 1 := by
  unfold survival
  exact sub_le_self _ (Finset.sum_nonneg fun time _ => finiteMass_nonneg law time)

theorem summable_equalFirstSecondBeforeThirdMass_terms
    (first second third : PMF (Option ℕ)) :
    Summable fun time => finiteMass first time * finiteMass second time *
      survival third (time + 1) := by
  apply Summable.of_nonneg_of_le
  · intro time
    exact mul_nonneg
      (mul_nonneg (finiteMass_nonneg first time) (finiteMass_nonneg second time))
      (survival_nonneg third (time + 1))
  · intro time
    have hfirst := finiteMass_nonneg first time
    have hsecond := finiteMass_nonneg second time
    have hsecondLe := finiteMass_le_one second time
    have hsurvival := survival_nonneg third (time + 1)
    have hsurvivalLe := survival_le_one third (time + 1)
    calc
      finiteMass first time * finiteMass second time * survival third (time + 1) ≤
          finiteMass first time * finiteMass second time :=
        mul_le_of_le_one_right (mul_nonneg hfirst hsecond) hsurvivalLe
      _ ≤ finiteMass first time :=
        mul_le_of_le_one_right hfirst hsecondLe
  · exact summable_finiteMass first

theorem summable_equalFirstThirdBeforeSecondMass_terms
    (first second third : PMF (Option ℕ)) :
    Summable fun time => finiteMass first time * finiteMass third time *
      survival second (time + 1) :=
  summable_equalFirstSecondBeforeThirdMass_terms first third second

theorem equalFirstSecondBeforeThirdMass_nonneg
    (first second third : PMF (Option ℕ)) :
    0 ≤ equalFirstSecondBeforeThirdMass first second third := by
  apply tsum_nonneg
  intro time
  exact mul_nonneg
    (mul_nonneg (finiteMass_nonneg first time) (finiteMass_nonneg second time))
    (survival_nonneg third (time + 1))

theorem equalFirstThirdBeforeSecondMass_nonneg
    (first second third : PMF (Option ℕ)) :
    0 ≤ equalFirstThirdBeforeSecondMass first second third := by
  apply tsum_nonneg
  intro time
  exact mul_nonneg
    (mul_nonneg (finiteMass_nonneg first time) (finiteMass_nonneg third time))
    (survival_nonneg second (time + 1))

private theorem equalFirstSecondBeforeThirdWindowMass_toScalarHazard
    (first second third : PMF (Option ℕ)) (cutoff : ℕ) :
    ScalarHazard.equalFirstSecondBeforeThirdWindowMass
        (toScalarHazard first) (toScalarHazard second) (toScalarHazard third)
        0 cutoff =
      ∑ time ∈ Finset.range cutoff,
        finiteMass first time * finiteMass second time *
          survival third (time + 1) := by
  unfold ScalarHazard.equalFirstSecondBeforeThirdWindowMass
  apply Finset.sum_congr rfl
  intro time _
  simp only [Nat.zero_add]
  let firstHazard := toScalarHazard first
  let secondHazard := toScalarHazard second
  let thirdHazard := toScalarHazard third
  change firstHazard.survival 0 time * secondHazard.survival 0 time *
      thirdHazard.survival 0 time * firstHazard.stop time *
        secondHazard.stop time * (1 - thirdHazard.stop time) = _
  calc
    _ = firstHazard.stopMass time * secondHazard.stopMass time *
        thirdHazard.survival 0 (time + 1) := by
      unfold ScalarHazard.stopMass
      rw [ScalarHazard.survival_succ]
      simp only [Nat.zero_add]
      ring
    _ = _ := by
      simp only [firstHazard, secondHazard, thirdHazard,
        toScalarHazard_stopMass, toScalarHazard_survival]

private theorem equalFirstThirdBeforeSecondWindowMass_toScalarHazard
    (first second third : PMF (Option ℕ)) (cutoff : ℕ) :
    ScalarHazard.equalFirstThirdBeforeSecondWindowMass
        (toScalarHazard first) (toScalarHazard second) (toScalarHazard third)
        0 cutoff =
      ∑ time ∈ Finset.range cutoff,
        finiteMass first time * finiteMass third time *
          survival second (time + 1) := by
  rw [show ScalarHazard.equalFirstThirdBeforeSecondWindowMass
      (toScalarHazard first) (toScalarHazard second) (toScalarHazard third)
      0 cutoff =
      ScalarHazard.equalFirstSecondBeforeThirdWindowMass
        (toScalarHazard first) (toScalarHazard third) (toScalarHazard second)
        0 cutoff by
    unfold ScalarHazard.equalFirstThirdBeforeSecondWindowMass
      ScalarHazard.equalFirstSecondBeforeThirdWindowMass
    apply Finset.sum_congr rfl
    intro time _
    ring]
  exact equalFirstSecondBeforeThirdWindowMass_toScalarHazard
    first third second cutoff

/-- Sharp square-root law for the two overlapping exact first-stopping events
of three arbitrary independent complete stopping laws. -/
theorem twoOverlappingFirstStoppingMasses_sqrt_sum_le_one
    (first second third : PMF (Option ℕ)) :
    Real.sqrt (equalFirstSecondBeforeThirdMass first second third) +
      Real.sqrt (equalFirstThirdBeforeSecondMass first second third) ≤ 1 := by
  have hfirstTendsto : Filter.Tendsto
      (fun cutoff => Real.sqrt
        (∑ time ∈ Finset.range cutoff,
          finiteMass first time * finiteMass second time *
            survival third (time + 1)))
      Filter.atTop
      (nhds (Real.sqrt (equalFirstSecondBeforeThirdMass first second third))) := by
    apply Real.continuous_sqrt.continuousAt.tendsto.comp
    unfold equalFirstSecondBeforeThirdMass
    exact (summable_equalFirstSecondBeforeThirdMass_terms
      first second third).hasSum.tendsto_sum_nat
  have hsecondTendsto : Filter.Tendsto
      (fun cutoff => Real.sqrt
        (∑ time ∈ Finset.range cutoff,
          finiteMass first time * finiteMass third time *
            survival second (time + 1)))
      Filter.atTop
      (nhds (Real.sqrt (equalFirstThirdBeforeSecondMass first second third))) := by
    apply Real.continuous_sqrt.continuousAt.tendsto.comp
    unfold equalFirstThirdBeforeSecondMass
    exact (summable_equalFirstThirdBeforeSecondMass_terms
      first second third).hasSum.tendsto_sum_nat
  apply le_of_tendsto' (hfirstTendsto.add hsecondTendsto)
  intro cutoff
  simpa only [equalFirstSecondBeforeThirdWindowMass_toScalarHazard,
    equalFirstThirdBeforeSecondWindowMass_toScalarHazard] using
    ScalarHazard.twoOverlappingFirstStoppingWindowMasses_sqrt_sum_le_one
      (toScalarHazard first) (toScalarHazard second) (toScalarHazard third)
      0 cutoff

/-! ## Exact first-coalition consequences -/

section Coalitions

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- Exact mass that a nonempty coalition is the set of clocks attaining the
first finite stopping date. -/
def exactFiniteFirstStoppingCoalitionMass
    (laws : Player → PMF (Option ℕ))
    (coalition : {C : Finset Player // C.Nonempty}) : ℝ :=
  ∑' time,
    (∏ who ∈ coalition.1, finiteMass (laws who) time) *
      ∏ who ∈ coalition.1ᶜ, survival (laws who) (time + 1)

private theorem finiteMass_mem_Icc
    (law : PMF (Option ℕ)) (time : ℕ) :
    finiteMass law time ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨finiteMass_nonneg law time, finiteMass_le_one law time⟩

private theorem survival_mem_Icc
    (law : PMF (Option ℕ)) (cutoff : ℕ) :
    survival law cutoff ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨survival_nonneg law cutoff, survival_le_one law cutoff⟩

private theorem exactFiniteFirstStoppingCoalitionMass_term_nonneg
    (laws : Player → PMF (Option ℕ))
    (coalition : {C : Finset Player // C.Nonempty}) (time : ℕ) :
    0 ≤ (∏ who ∈ coalition.1, finiteMass (laws who) time) *
      ∏ who ∈ coalition.1ᶜ, survival (laws who) (time + 1) := by
  exact mul_nonneg
    (Finset.prod_nonneg fun who _ => finiteMass_nonneg (laws who) time)
    (Finset.prod_nonneg fun who _ => survival_nonneg (laws who) (time + 1))

theorem summable_exactFiniteFirstStoppingCoalitionMass_terms
    (laws : Player → PMF (Option ℕ))
    (coalition : {C : Finset Player // C.Nonempty}) :
    Summable fun time =>
      (∏ who ∈ coalition.1, finiteMass (laws who) time) *
        ∏ who ∈ coalition.1ᶜ, survival (laws who) (time + 1) := by
  let anchor := coalition.2.choose
  have hanchor : anchor ∈ coalition.1 := coalition.2.choose_spec
  apply Summable.of_nonneg_of_le
  · exact exactFiniteFirstStoppingCoalitionMass_term_nonneg laws coalition
  · intro time
    have hquit :
        (∏ who ∈ coalition.1, finiteMass (laws who) time) ≤
          finiteMass (laws anchor) time := by
      have hsubset : ({anchor} : Finset Player) ⊆ coalition.1 := by
        simpa only [Finset.singleton_subset_iff] using hanchor
      have h := Finset.prod_le_prod_of_subset_of_le_one hsubset
        (fun who _ => (finiteMass_mem_Icc (laws who) time).1)
        (fun who _ _ => (finiteMass_mem_Icc (laws who) time).2)
      simpa using h
    have hquitNonneg :
        0 ≤ ∏ who ∈ coalition.1, finiteMass (laws who) time :=
      Finset.prod_nonneg fun who _ => finiteMass_nonneg (laws who) time
    have hcontinueLe :
        (∏ who ∈ coalition.1ᶜ, survival (laws who) (time + 1)) ≤ 1 :=
      Finset.prod_le_one
        (fun who _ => (survival_mem_Icc (laws who) (time + 1)).1)
        (fun who _ => (survival_mem_Icc (laws who) (time + 1)).2)
    calc
      (∏ who ∈ coalition.1, finiteMass (laws who) time) *
          ∏ who ∈ coalition.1ᶜ, survival (laws who) (time + 1) ≤
        ∏ who ∈ coalition.1, finiteMass (laws who) time :=
          mul_le_of_le_one_right hquitNonneg hcontinueLe
      _ ≤ finiteMass (laws anchor) time := hquit
  · exact summable_finiteMass (laws anchor)

theorem exactFiniteFirstStoppingCoalitionMass_nonneg
    (laws : Player → PMF (Option ℕ))
    (coalition : {C : Finset Player // C.Nonempty}) :
    0 ≤ exactFiniteFirstStoppingCoalitionMass laws coalition := by
  apply tsum_nonneg
  exact exactFiniteFirstStoppingCoalitionMass_term_nonneg laws coalition

theorem exactFiniteFirstStoppingCoalitionMass_le_equalFirstSecondBeforeThirdMass
    (laws : Player → PMF (Option ℕ))
    (coalition : {C : Finset Player // C.Nonempty})
    {first second third : Player}
    (hfirst : first ∈ coalition.1) (hsecond : second ∈ coalition.1)
    (hfirstSecond : first ≠ second) (hthird : third ∉ coalition.1) :
    exactFiniteFirstStoppingCoalitionMass laws coalition ≤
      equalFirstSecondBeforeThirdMass
        (laws first) (laws second) (laws third) := by
  unfold exactFiniteFirstStoppingCoalitionMass equalFirstSecondBeforeThirdMass
  apply (summable_exactFiniteFirstStoppingCoalitionMass_terms laws coalition).tsum_le_tsum
  · intro time
    have hpairSubset : ({first, second} : Finset Player) ⊆ coalition.1 := by
      intro who hwho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
      rcases hwho with rfl | rfl
      · exact hfirst
      · exact hsecond
    have hthirdComplement : third ∈ coalition.1ᶜ := by
      simpa using hthird
    have hquit :
        (∏ who ∈ coalition.1, finiteMass (laws who) time) ≤
          finiteMass (laws first) time * finiteMass (laws second) time := by
      have h := Finset.prod_le_prod_of_subset_of_le_one hpairSubset
        (fun who _ => (finiteMass_mem_Icc (laws who) time).1)
        (fun who _ _ => (finiteMass_mem_Icc (laws who) time).2)
      simpa [hfirstSecond, mul_comm] using h
    have hcontinue :
        (∏ who ∈ coalition.1ᶜ, survival (laws who) (time + 1)) ≤
          survival (laws third) (time + 1) := by
      have hsubset : ({third} : Finset Player) ⊆ coalition.1ᶜ := by
        simpa only [Finset.singleton_subset_iff] using hthirdComplement
      have h := Finset.prod_le_prod_of_subset_of_le_one hsubset
        (fun who _ => (survival_mem_Icc (laws who) (time + 1)).1)
        (fun who _ _ => (survival_mem_Icc (laws who) (time + 1)).2)
      simpa using h
    have hquitNonneg :
        0 ≤ ∏ who ∈ coalition.1, finiteMass (laws who) time :=
      Finset.prod_nonneg fun who _ => finiteMass_nonneg (laws who) time
    have hpairNonneg :
        0 ≤ finiteMass (laws first) time * finiteMass (laws second) time :=
      mul_nonneg (finiteMass_nonneg _ _) (finiteMass_nonneg _ _)
    exact mul_le_mul hquit hcontinue
      (Finset.prod_nonneg fun who _ => survival_nonneg (laws who) (time + 1))
      hpairNonneg
  · exact summable_equalFirstSecondBeforeThirdMass_terms
      (laws first) (laws second) (laws third)

/-- Exact first-stopping masses of two incomparable intersecting coalitions
satisfy the sharp overlapping square-root law. -/
theorem sqrt_exactFiniteFirstStoppingCoalitionMass_add_sqrt_le_one_of_incomparable
    (laws : Player → PMF (Option ℕ))
    (firstCoalition secondCoalition :
      {C : Finset Player // C.Nonempty})
    (hintersection : (firstCoalition.1 ∩ secondCoalition.1).Nonempty)
    (hfirstNotSubset : ¬ firstCoalition.1 ⊆ secondCoalition.1)
    (hsecondNotSubset : ¬ secondCoalition.1 ⊆ firstCoalition.1) :
    Real.sqrt
          (exactFiniteFirstStoppingCoalitionMass laws firstCoalition) +
        Real.sqrt
          (exactFiniteFirstStoppingCoalitionMass laws secondCoalition) ≤ 1 := by
  obtain ⟨common, hcommon⟩ := hintersection
  have ⟨hcommonFirst, hcommonSecond⟩ := Finset.mem_inter.mp hcommon
  obtain ⟨firstOnly, hfirstOnlyFirst, hfirstOnlySecond⟩ :=
    Finset.not_subset.mp hfirstNotSubset
  obtain ⟨secondOnly, hsecondOnlySecond, hsecondOnlyFirst⟩ :=
    Finset.not_subset.mp hsecondNotSubset
  have hcommonFirstOnly : common ≠ firstOnly := by
    intro heq
    subst firstOnly
    exact hfirstOnlySecond hcommonSecond
  have hcommonSecondOnly : common ≠ secondOnly := by
    intro heq
    subst secondOnly
    exact hsecondOnlyFirst hcommonFirst
  have hfirstBound :=
    exactFiniteFirstStoppingCoalitionMass_le_equalFirstSecondBeforeThirdMass
      laws firstCoalition hcommonFirst hfirstOnlyFirst hcommonFirstOnly
      hsecondOnlyFirst
  have hsecondBound :=
    exactFiniteFirstStoppingCoalitionMass_le_equalFirstSecondBeforeThirdMass
      laws secondCoalition hcommonSecond hsecondOnlySecond
      hcommonSecondOnly hfirstOnlySecond
  calc
    Real.sqrt (exactFiniteFirstStoppingCoalitionMass laws firstCoalition) +
        Real.sqrt (exactFiniteFirstStoppingCoalitionMass laws secondCoalition) ≤
      Real.sqrt
          (equalFirstSecondBeforeThirdMass
            (laws common) (laws firstOnly) (laws secondOnly)) +
        Real.sqrt
          (equalFirstThirdBeforeSecondMass
            (laws common) (laws firstOnly) (laws secondOnly)) := by
      exact add_le_add (Real.sqrt_le_sqrt hfirstBound)
        (Real.sqrt_le_sqrt (by
          simpa only [equalFirstThirdBeforeSecondMass,
            equalFirstSecondBeforeThirdMass] using hsecondBound))
    _ ≤ 1 :=
      twoOverlappingFirstStoppingMasses_sqrt_sum_le_one
        (laws common) (laws firstOnly) (laws secondOnly)

end Coalitions

end StoppingLaw

end Math.Probability.DiscreteHazard
