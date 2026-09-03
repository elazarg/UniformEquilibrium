/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.OverlappingFirstStopping
import MathUE.Probability.SquareRootCoalitionClock

/-!
# Pair projections of independent first-stopping coalition laws

This file adapts four complete stopping laws to the existing disjoint-pair
hazard clock and combines that result with the overlapping first-stopping law.
It does not duplicate the disjoint-pair square-root proof.
-/

noncomputable section

open scoped BigOperators

namespace Math.Probability.DiscreteHazard

open Math.Probability

namespace StoppingLaw

/-- Probability that the first two clocks stop together at a finite date
strictly before both the third and fourth clocks. -/
def equalFirstSecondBeforeThirdFourthMass
    (first second third fourth : PMF (Option ℕ)) : ℝ :=
  ∑' time, finiteMass first time * finiteMass second time *
    survival third (time + 1) * survival fourth (time + 1)

/-- Probability that the third and fourth clocks stop together at a finite
date strictly before both the first and second clocks. -/
def equalThirdFourthBeforeFirstSecondMass
    (first second third fourth : PMF (Option ℕ)) : ℝ :=
  ∑' time, finiteMass third time * finiteMass fourth time *
    survival first (time + 1) * survival second (time + 1)

private theorem finiteMass_le_one (law : PMF (Option ℕ)) (time : ℕ) :
    finiteMass law time ≤ 1 := by
  exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one law (some time))

private theorem survival_le_one (law : PMF (Option ℕ)) (cutoff : ℕ) :
    survival law cutoff ≤ 1 := by
  unfold survival
  exact sub_le_self _ (Finset.sum_nonneg fun time _ => finiteMass_nonneg law time)

private theorem summable_finiteMass (law : PMF (Option ℕ)) :
    Summable (finiteMass law) := by
  change Summable (fun time : ℕ => (law (some time)).toReal)
  exact (Math.Probability.pmf_toReal_summable law).comp_injective
    (Option.some_injective ℕ)

theorem summable_equalFirstSecondBeforeThirdFourthMass_terms
    (first second third fourth : PMF (Option ℕ)) :
    Summable fun time => finiteMass first time * finiteMass second time *
      survival third (time + 1) * survival fourth (time + 1) := by
  apply Summable.of_nonneg_of_le
  · intro time
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (finiteMass_nonneg first time) (finiteMass_nonneg second time))
        (survival_nonneg third (time + 1)))
      (survival_nonneg fourth (time + 1))
  · intro time
    have hfirst := finiteMass_nonneg first time
    have hsecond := finiteMass_nonneg second time
    have hthird : 0 ≤ survival third (time + 1) := survival_nonneg _ _
    calc
      finiteMass first time * finiteMass second time * survival third (time + 1) *
          survival fourth (time + 1) ≤
        finiteMass first time * finiteMass second time * survival third (time + 1) :=
          mul_le_of_le_one_right
            (mul_nonneg (mul_nonneg hfirst hsecond) hthird)
            (survival_le_one fourth (time + 1))
      _ ≤ finiteMass first time * finiteMass second time :=
          mul_le_of_le_one_right (mul_nonneg hfirst hsecond)
            (survival_le_one third (time + 1))
      _ ≤ finiteMass first time :=
          mul_le_of_le_one_right hfirst (finiteMass_le_one second time)
  · exact summable_finiteMass first

theorem summable_equalThirdFourthBeforeFirstSecondMass_terms
    (first second third fourth : PMF (Option ℕ)) :
    Summable fun time => finiteMass third time * finiteMass fourth time *
      survival first (time + 1) * survival second (time + 1) :=
  summable_equalFirstSecondBeforeThirdFourthMass_terms third fourth first second

private def fourLawTwoPairHazardClock
    (first second third fourth : PMF (Option ℕ)) : TwoPairHazardClock where
  first := (toScalarHazard first).stop
  second := (toScalarHazard second).stop
  third := (toScalarHazard third).stop
  fourth := (toScalarHazard fourth).stop
  background := fun _ => 1
  survivalRoot := fun time =>
    Real.sqrt ((toScalarHazard first).survival 0 time) *
      Real.sqrt ((toScalarHazard second).survival 0 time) *
      Real.sqrt ((toScalarHazard third).survival 0 time) *
      Real.sqrt ((toScalarHazard fourth).survival 0 time)
  first_mem := fun time =>
    ⟨(toScalarHazard first).stop_nonneg time,
      (toScalarHazard first).stop_le_one time⟩
  second_mem := fun time =>
    ⟨(toScalarHazard second).stop_nonneg time,
      (toScalarHazard second).stop_le_one time⟩
  third_mem := fun time =>
    ⟨(toScalarHazard third).stop_nonneg time,
      (toScalarHazard third).stop_le_one time⟩
  fourth_mem := fun time =>
    ⟨(toScalarHazard fourth).stop_nonneg time,
      (toScalarHazard fourth).stop_le_one time⟩
  background_mem := fun _ => by simp
  survivalRoot_nonneg := fun time => by positivity
  survivalRoot_zero := by simp [ScalarHazard.survival_zero]
  survivalRoot_step := fun time => by
    have hfirst := (toScalarHazard first).survival_nonneg 0 time
    have hsecond := (toScalarHazard second).survival_nonneg 0 time
    have hthird := (toScalarHazard third).survival_nonneg 0 time
    have hfourth := (toScalarHazard fourth).survival_nonneg 0 time
    have hfirstContinue : 0 ≤ 1 - (toScalarHazard first).stop time :=
      sub_nonneg.mpr ((toScalarHazard first).stop_le_one time)
    have hthirdContinue : 0 ≤ 1 - (toScalarHazard third).stop time :=
      sub_nonneg.mpr ((toScalarHazard third).stop_le_one time)
    simp only [ScalarHazard.survival_succ, Nat.zero_add,
      pairContinueAmplitude]
    rw [Real.sqrt_mul hfirst, Real.sqrt_mul hsecond,
      Real.sqrt_mul hthird, Real.sqrt_mul hfourth]
    rw [Real.sqrt_mul hfirstContinue, Real.sqrt_mul hthirdContinue]
    ring

private theorem fourLawTwoPairHazardClock_firstTargetAmplitude_sq
    (first second third fourth : PMF (Option ℕ)) (time : ℕ) :
    ((fourLawTwoPairHazardClock first second third fourth).firstTargetAmplitude
      time) ^ 2 =
      finiteMass first time * finiteMass second time *
        survival third (time + 1) * survival fourth (time + 1) := by
  let firstHazard := toScalarHazard first
  let secondHazard := toScalarHazard second
  let thirdHazard := toScalarHazard third
  let fourthHazard := toScalarHazard fourth
  have hfirst := firstHazard.survival_nonneg 0 time
  have hsecond := secondHazard.survival_nonneg 0 time
  have hthird := thirdHazard.survival_nonneg 0 time
  have hfourth := fourthHazard.survival_nonneg 0 time
  have hfirstStop := firstHazard.stop_nonneg time
  have hsecondStop := secondHazard.stop_nonneg time
  have hthirdContinue : 0 ≤ 1 - thirdHazard.stop time :=
    sub_nonneg.mpr (thirdHazard.stop_le_one time)
  have hfourthContinue : 0 ≤ 1 - fourthHazard.stop time :=
    sub_nonneg.mpr (fourthHazard.stop_le_one time)
  change (Real.sqrt (firstHazard.survival 0 time) *
      Real.sqrt (secondHazard.survival 0 time) *
      Real.sqrt (thirdHazard.survival 0 time) *
      Real.sqrt (fourthHazard.survival 0 time) * 1 *
      Real.sqrt (firstHazard.stop time * secondHazard.stop time) *
      Real.sqrt
        ((1 - thirdHazard.stop time) * (1 - fourthHazard.stop time))) ^ 2 = _
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]
  rw [Real.sq_sqrt hfirst, Real.sq_sqrt hsecond,
    Real.sq_sqrt hthird, Real.sq_sqrt hfourth]
  rw [Real.sq_sqrt (mul_nonneg hfirstStop hsecondStop)]
  rw [Real.sq_sqrt (mul_nonneg hthirdContinue hfourthContinue)]
  rw [← toScalarHazard_stopMass, ← toScalarHazard_stopMass,
    ← toScalarHazard_survival, ← toScalarHazard_survival]
  unfold ScalarHazard.stopMass
  rw [ScalarHazard.survival_succ, ScalarHazard.survival_succ]
  simp only [Nat.zero_add]
  ring

private theorem fourLawTwoPairHazardClock_secondTargetAmplitude_sq
    (first second third fourth : PMF (Option ℕ)) (time : ℕ) :
    ((fourLawTwoPairHazardClock first second third fourth).secondTargetAmplitude
      time) ^ 2 =
      finiteMass third time * finiteMass fourth time *
        survival first (time + 1) * survival second (time + 1) := by
  calc
    ((fourLawTwoPairHazardClock first second third fourth).secondTargetAmplitude
        time) ^ 2 =
      ((fourLawTwoPairHazardClock third fourth first second).firstTargetAmplitude
        time) ^ 2 := by
      congr 1
      unfold TwoPairHazardClock.secondTargetAmplitude
        TwoPairHazardClock.firstTargetAmplitude fourLawTwoPairHazardClock
      ring
    _ = _ :=
      fourLawTwoPairHazardClock_firstTargetAmplitude_sq
        third fourth first second time

/-- The existing disjoint two-pair hazard theorem, applied to four arbitrary
complete stopping laws. -/
theorem twoDisjointFirstStoppingPairMasses_sqrt_sum_le_one
    (first second third fourth : PMF (Option ℕ)) :
    Real.sqrt (equalFirstSecondBeforeThirdFourthMass first second third fourth) +
      Real.sqrt (equalThirdFourthBeforeFirstSecondMass first second third fourth) ≤ 1 := by
  let clock := fourLawTwoPairHazardClock first second third fourth
  have hfirstTendsto : Filter.Tendsto
      (fun cutoff => Real.sqrt
        (∑ time ∈ Finset.range cutoff,
          finiteMass first time * finiteMass second time *
            survival third (time + 1) * survival fourth (time + 1)))
      Filter.atTop
      (nhds (Real.sqrt
        (equalFirstSecondBeforeThirdFourthMass first second third fourth))) := by
    apply Real.continuous_sqrt.continuousAt.tendsto.comp
    unfold equalFirstSecondBeforeThirdFourthMass
    exact (summable_equalFirstSecondBeforeThirdFourthMass_terms
      first second third fourth).hasSum.tendsto_sum_nat
  have hsecondTendsto : Filter.Tendsto
      (fun cutoff => Real.sqrt
        (∑ time ∈ Finset.range cutoff,
          finiteMass third time * finiteMass fourth time *
            survival first (time + 1) * survival second (time + 1)))
      Filter.atTop
      (nhds (Real.sqrt
        (equalThirdFourthBeforeFirstSecondMass first second third fourth))) := by
    apply Real.continuous_sqrt.continuousAt.tendsto.comp
    unfold equalThirdFourthBeforeFirstSecondMass
    exact (summable_equalThirdFourthBeforeFirstSecondMass_terms
      first second third fourth).hasSum.tendsto_sum_nat
  apply le_of_tendsto' (hfirstTendsto.add hsecondTendsto)
  intro cutoff
  simpa only [clock, fourLawTwoPairHazardClock_firstTargetAmplitude_sq,
    fourLawTwoPairHazardClock_secondTargetAmplitude_sq] using
    clock.finite_targetMass_sqrt_sum_le_one cutoff

section Coalitions

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

private theorem finiteMass_mem_Icc
    (law : PMF (Option ℕ)) (time : ℕ) :
    finiteMass law time ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨finiteMass_nonneg law time, finiteMass_le_one law time⟩

private theorem survival_mem_Icc
    (law : PMF (Option ℕ)) (cutoff : ℕ) :
    survival law cutoff ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨survival_nonneg law cutoff, survival_le_one law cutoff⟩

private theorem exactFiniteFirstStoppingCoalitionMass_le_firstDisjointPairMass
    (laws : Player → PMF (Option ℕ))
    (coalition : {C : Finset Player // C.Nonempty})
    {first second third fourth : Player}
    (hfirst : first ∈ coalition.1) (hsecond : second ∈ coalition.1)
    (hfirstSecond : first ≠ second)
    (hthird : third ∉ coalition.1) (hfourth : fourth ∉ coalition.1)
    (hthirdFourth : third ≠ fourth) :
    exactFiniteFirstStoppingCoalitionMass laws coalition ≤
      equalFirstSecondBeforeThirdFourthMass
        (laws first) (laws second) (laws third) (laws fourth) := by
  unfold exactFiniteFirstStoppingCoalitionMass
    equalFirstSecondBeforeThirdFourthMass
  apply (summable_exactFiniteFirstStoppingCoalitionMass_terms laws coalition).tsum_le_tsum
  · intro time
    have hpairSubset : ({first, second} : Finset Player) ⊆ coalition.1 := by
      intro who hwho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
      rcases hwho with rfl | rfl
      · exact hfirst
      · exact hsecond
    have hthirdComplement : third ∈ coalition.1ᶜ := by simpa using hthird
    have hfourthComplement : fourth ∈ coalition.1ᶜ := by simpa using hfourth
    have hotherPairSubset : ({third, fourth} : Finset Player) ⊆ coalition.1ᶜ := by
      intro who hwho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
      rcases hwho with rfl | rfl
      · exact hthirdComplement
      · exact hfourthComplement
    have hquit :
        (∏ who ∈ coalition.1, finiteMass (laws who) time) ≤
          finiteMass (laws first) time * finiteMass (laws second) time := by
      have h := Finset.prod_le_prod_of_subset_of_le_one hpairSubset
        (fun who _ => (finiteMass_mem_Icc (laws who) time).1)
        (fun who _ _ => (finiteMass_mem_Icc (laws who) time).2)
      simpa [hfirstSecond, mul_comm] using h
    have hcontinue :
        (∏ who ∈ coalition.1ᶜ, survival (laws who) (time + 1)) ≤
          survival (laws third) (time + 1) *
            survival (laws fourth) (time + 1) := by
      have h := Finset.prod_le_prod_of_subset_of_le_one hotherPairSubset
        (fun who _ => (survival_mem_Icc (laws who) (time + 1)).1)
        (fun who _ _ => (survival_mem_Icc (laws who) (time + 1)).2)
      simpa [hthirdFourth, mul_comm] using h
    have hpairNonneg :
        0 ≤ finiteMass (laws first) time * finiteMass (laws second) time :=
      mul_nonneg (finiteMass_nonneg _ _) (finiteMass_nonneg _ _)
    calc
      (∏ who ∈ coalition.1, finiteMass (laws who) time) *
          ∏ who ∈ coalition.1ᶜ, survival (laws who) (time + 1) ≤
        (finiteMass (laws first) time * finiteMass (laws second) time) *
          (survival (laws third) (time + 1) *
            survival (laws fourth) (time + 1)) :=
        mul_le_mul hquit hcontinue
          (Finset.prod_nonneg fun who _ =>
            survival_nonneg (laws who) (time + 1))
          hpairNonneg
      _ = _ := by ring
  · exact summable_equalFirstSecondBeforeThirdFourthMass_terms
      (laws first) (laws second) (laws third) (laws fourth)

/-- Exact first-stopping masses of two disjoint coalitions, each containing at
least two clocks, satisfy the disjoint square-root law. -/
theorem sqrt_exactFiniteFirstStoppingCoalitionMass_add_sqrt_le_one_of_disjoint
    (laws : Player → PMF (Option ℕ))
    (firstCoalition secondCoalition :
      {C : Finset Player // C.Nonempty})
    (hdisjoint : Disjoint firstCoalition.1 secondCoalition.1)
    (hfirstCard : 2 ≤ firstCoalition.1.card)
    (hsecondCard : 2 ≤ secondCoalition.1.card) :
    Real.sqrt
          (exactFiniteFirstStoppingCoalitionMass laws firstCoalition) +
        Real.sqrt
          (exactFiniteFirstStoppingCoalitionMass laws secondCoalition) ≤ 1 := by
  obtain ⟨first, hfirst, second, hsecond, hfirstSecond⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le Nat.one_lt_two hfirstCard)
  obtain ⟨third, hthird, fourth, hfourth, hthirdFourth⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le Nat.one_lt_two hsecondCard)
  have hthirdNotFirst : third ∉ firstCoalition.1 :=
    fun hthirdFirst => Finset.disjoint_left.mp hdisjoint hthirdFirst hthird
  have hfourthNotFirst : fourth ∉ firstCoalition.1 :=
    fun hfourthFirst => Finset.disjoint_left.mp hdisjoint hfourthFirst hfourth
  have hfirstNotSecond : first ∉ secondCoalition.1 :=
    Finset.disjoint_left.mp hdisjoint hfirst
  have hsecondNotSecond : second ∉ secondCoalition.1 :=
    Finset.disjoint_left.mp hdisjoint hsecond
  have hfirstBound :=
    exactFiniteFirstStoppingCoalitionMass_le_firstDisjointPairMass
      laws firstCoalition hfirst hsecond hfirstSecond
      hthirdNotFirst hfourthNotFirst hthirdFourth
  have hsecondBound :=
    exactFiniteFirstStoppingCoalitionMass_le_firstDisjointPairMass
      laws secondCoalition hthird hfourth hthirdFourth
      hfirstNotSecond hsecondNotSecond hfirstSecond
  calc
    Real.sqrt (exactFiniteFirstStoppingCoalitionMass laws firstCoalition) +
        Real.sqrt (exactFiniteFirstStoppingCoalitionMass laws secondCoalition) ≤
      Real.sqrt
          (equalFirstSecondBeforeThirdFourthMass
            (laws first) (laws second) (laws third) (laws fourth)) +
        Real.sqrt
          (equalThirdFourthBeforeFirstSecondMass
            (laws first) (laws second) (laws third) (laws fourth)) := by
      exact add_le_add (Real.sqrt_le_sqrt hfirstBound)
        (Real.sqrt_le_sqrt (by
          simpa only [equalThirdFourthBeforeFirstSecondMass,
            equalFirstSecondBeforeThirdFourthMass] using hsecondBound))
    _ ≤ 1 :=
      twoDisjointFirstStoppingPairMasses_sqrt_sum_le_one
        (laws first) (laws second) (laws third) (laws fourth)

/-- Every pair of distinct two-clock exact first-stopping coalitions satisfies
the square-root law, whether the two pairs overlap or are disjoint. -/
theorem sqrt_exactFiniteFirstStoppingPairMass_add_sqrt_le_one
    (laws : Player → PMF (Option ℕ))
    (firstCoalition secondCoalition :
      {C : Finset Player // C.Nonempty})
    (hfirstCard : firstCoalition.1.card = 2)
    (hsecondCard : secondCoalition.1.card = 2)
    (hne : firstCoalition ≠ secondCoalition) :
    Real.sqrt
          (exactFiniteFirstStoppingCoalitionMass laws firstCoalition) +
        Real.sqrt
          (exactFiniteFirstStoppingCoalitionMass laws secondCoalition) ≤ 1 := by
  by_cases hintersection :
      (firstCoalition.1 ∩ secondCoalition.1).Nonempty
  · apply
      sqrt_exactFiniteFirstStoppingCoalitionMass_add_sqrt_le_one_of_incomparable
        laws firstCoalition secondCoalition hintersection
    · intro hsubset
      apply hne
      apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le hsubset (by
        rw [hfirstCard, hsecondCard])
    · intro hsubset
      apply hne
      apply Subtype.ext
      exact (Finset.eq_of_subset_of_card_le hsubset (by
        rw [hfirstCard, hsecondCard])).symm
  · have hdisjoint : Disjoint firstCoalition.1 secondCoalition.1 := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.not_nonempty_iff_eq_empty.mp hintersection
    exact sqrt_exactFiniteFirstStoppingCoalitionMass_add_sqrt_le_one_of_disjoint
      laws firstCoalition secondCoalition hdisjoint
      (by omega) (by omega)

end Coalitions

end StoppingLaw

end Math.Probability.DiscreteHazard
