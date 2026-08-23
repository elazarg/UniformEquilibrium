/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.PowersetBernoulliWeight
import UniformEquilibrium.Quitting.Classification.Existence.ConditionalFaceGap

/-!
# Literal reward ranges imply conditional face gaps

This file gives a finite source-data adapter for the division-free conditional
face-gap producer.  For each player, rewards after that player Quits are
bounded separately according to whether a designated blocker also Quits.
Rewards after that player Continues are bounded uniformly over nonempty
opponent coalitions.  Two scalar mixture comparisons then imply the required
opposite-face signs.

The lower mixture comparison is strict.  The upper comparison is only weak,
matching the strongest form of the underlying Poincare--Miranda theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Finset Math.Topology Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def conditionalRangeBackground (who blocker : ι) : Finset ι :=
  (Finset.univ.erase who).erase blocker

private lemma erase_eq_insert_conditionalRangeBackground
    {who blocker : ι} (hne : blocker ≠ who) :
    Finset.univ.erase who =
      insert blocker (conditionalRangeBackground who blocker) := by
  ext other
  simp [conditionalRangeBackground, hne]

private lemma blocker_not_mem_conditionalRangeBackground (who blocker : ι) :
    blocker ∉ conditionalRangeBackground who blocker := by
  simp [conditionalRangeBackground]

private lemma who_not_mem_conditionalRangeBackground (who blocker : ι) :
    who ∉ conditionalRangeBackground who blocker := by
  simp [conditionalRangeBackground]

omit [Fintype ι] in
private lemma bernoulliWeight_nonneg_of_mem_cube
    {hazard : ι → ℝ} (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier subset : Finset ι) :
    0 ≤ bernoulliWeight hazard carrier subset := by
  exact mul_nonneg
    (Finset.prod_nonneg fun who _ => hhazard.1 who)
    (Finset.prod_nonneg fun who _ => sub_nonneg.mpr (hhazard.2 who))

omit [Fintype ι] in
private lemma weightedAverage_le_of_le
    {hazard : ι → ℝ} (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) (value : Finset ι → ℝ) (upper : ℝ)
    (hvalue : ∀ subset ∈ carrier.powerset, value subset ≤ upper) :
    (∑ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset * value subset) ≤ upper := by
  calc
    (∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset * value subset) ≤
        ∑ subset ∈ carrier.powerset,
          bernoulliWeight hazard carrier subset * upper := by
      apply Finset.sum_le_sum
      intro subset hsubset
      exact mul_le_mul_of_nonneg_left (hvalue subset hsubset)
        (bernoulliWeight_nonneg_of_mem_cube hhazard carrier subset)
    _ = upper := by
      rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

omit [Fintype ι] in
private lemma weightedAverage_le_of_lower
    {hazard : ι → ℝ} (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) (value : Finset ι → ℝ) (lower : ℝ)
    (hvalue : ∀ subset ∈ carrier.powerset, lower ≤ value subset) :
    lower ≤ ∑ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset * value subset := by
  calc
    lower = ∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset * lower := by
      rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]
    _ ≤ ∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset * value subset := by
      apply Finset.sum_le_sum
      intro subset hsubset
      exact mul_le_mul_of_nonneg_left (hvalue subset hsubset)
        (bernoulliWeight_nonneg_of_mem_cube hhazard carrier subset)

private lemma sigmaValue_eq_blocker_mixture
    (weight : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who blocker : ι)
    (hne : blocker ≠ who) :
    sigmaValue weight hazard who =
      (1 - hazard blocker) *
          (∑ background ∈ (conditionalRangeBackground who blocker).powerset,
            bernoulliWeight hazard (conditionalRangeBackground who blocker) background *
              weight (insert who background) who) +
        hazard blocker *
          (∑ background ∈ (conditionalRangeBackground who blocker).powerset,
            bernoulliWeight hazard (conditionalRangeBackground who blocker) background *
              weight (insert blocker (insert who background)) who) := by
  unfold sigmaValue bernoulliWeight
  rw [erase_eq_insert_conditionalRangeBackground hne,
    Finset.sum_powerset_insert
      (blocker_not_mem_conditionalRangeBackground who blocker)]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro background hbackground
    have hsubset := Finset.mem_powerset.mp hbackground
    have hblocker : blocker ∉ background := fun hmem =>
      blocker_not_mem_conditionalRangeBackground who blocker (hsubset hmem)
    have hdiff :
        insert blocker (conditionalRangeBackground who blocker) \ background =
          insert blocker (conditionalRangeBackground who blocker \ background) := by
      ext other
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    rw [hdiff, Finset.prod_insert]
    · ring
    · intro hmem
      exact blocker_not_mem_conditionalRangeBackground who blocker
        (Finset.mem_sdiff.mp hmem).1
  · apply Finset.sum_congr rfl
    intro background hbackground
    have hsubset := Finset.mem_powerset.mp hbackground
    have hblocker : blocker ∉ background := fun hmem =>
      blocker_not_mem_conditionalRangeBackground who blocker (hsubset hmem)
    rw [Finset.prod_insert hblocker]
    have hdiff :
        insert blocker (conditionalRangeBackground who blocker) \
            insert blocker background =
          conditionalRangeBackground who blocker \ background := by
      ext other
      by_cases hother : other = blocker
      · subst other
        simp [blocker_not_mem_conditionalRangeBackground]
      · simp [hother]
    rw [hdiff, Finset.insert_comm blocker who]
    ring

private lemma excludedValue_le_one_sub_continueMass_mul
    (weight : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι)
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1)) (upper : ℝ)
    (hupper : ∀ coalition ∈ (Finset.univ.erase who).powerset.erase ∅,
      weight coalition who ≤ upper) :
    excludedValue weight hazard who ≤
      (1 - continueMassExcl hazard who) * upper := by
  unfold excludedValue continueMassExcl
  let carrier := Finset.univ.erase who
  have hempty :
      bernoulliWeight hazard carrier ∅ =
        ∏ other ∈ carrier, (1 - hazard other) := by
    simp [bernoulliWeight]
  have hmass := sum_bernoulliWeight hazard carrier
  have hsumErase :
      ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition =
        1 - ∏ other ∈ carrier, (1 - hazard other) := by
    have hsplit := Finset.sum_erase_add carrier.powerset
      (fun coalition => bernoulliWeight hazard carrier coalition)
      (Finset.empty_mem_powerset carrier)
    rw [hempty, hmass] at hsplit
    linarith
  calc
    ∑ coalition ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier coalition * weight coalition who ≤
        ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition * upper := by
      apply Finset.sum_le_sum
      intro coalition hcoalition
      exact mul_le_mul_of_nonneg_left (hupper coalition hcoalition)
        (bernoulliWeight_nonneg_of_mem_cube hhazard carrier coalition)
    _ = (1 - ∏ other ∈ carrier, (1 - hazard other)) * upper := by
      rw [← Finset.sum_mul, hsumErase]

private lemma one_sub_continueMass_mul_le_excludedValue
    (weight : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι)
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1)) (lower : ℝ)
    (hlower : ∀ coalition ∈ (Finset.univ.erase who).powerset.erase ∅,
      lower ≤ weight coalition who) :
    (1 - continueMassExcl hazard who) * lower ≤
      excludedValue weight hazard who := by
  unfold excludedValue continueMassExcl
  let carrier := Finset.univ.erase who
  have hempty :
      bernoulliWeight hazard carrier ∅ =
        ∏ other ∈ carrier, (1 - hazard other) := by
    simp [bernoulliWeight]
  have hmass := sum_bernoulliWeight hazard carrier
  have hsumErase :
      ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition =
        1 - ∏ other ∈ carrier, (1 - hazard other) := by
    have hsplit := Finset.sum_erase_add carrier.powerset
      (fun coalition => bernoulliWeight hazard carrier coalition)
      (Finset.empty_mem_powerset carrier)
    rw [hempty, hmass] at hsplit
    linarith
  calc
    (1 - ∏ other ∈ carrier, (1 - hazard other)) * lower =
        ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition * lower := by
      rw [← Finset.sum_mul, hsumErase]
    _ ≤ ∑ coalition ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier coalition * weight coalition who := by
      apply Finset.sum_le_sum
      intro coalition hcoalition
      exact mul_le_mul_of_nonneg_left (hlower coalition hcoalition)
        (bernoulliWeight_nonneg_of_mem_cube hhazard carrier coalition)

/-- Literal reward bounds sufficient for opposite conditional face gaps.
The six bound functions are supplied data; callers need not construct finite
minimum or maximum objects. -/
def IsQuittingConditionalFaceGapRange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper : ι → ℝ)
    (continueLower continueUpper : ι → ℝ) : Prop :=
  (∀ who, blocker who ≠ who) ∧
    (∀ who background,
      who ∉ background → blocker who ∉ background →
        quitWithoutLower who ≤
            reward ⟨insert who background, Finset.insert_nonempty _ _⟩ who ∧
          reward ⟨insert who background, Finset.insert_nonempty _ _⟩ who ≤
            quitWithoutUpper who ∧
          quitWithLower who ≤
            reward
              ⟨insert (blocker who) (insert who background),
                Finset.insert_nonempty _ _⟩ who ∧
          reward
              ⟨insert (blocker who) (insert who background),
                Finset.insert_nonempty _ _⟩ who ≤
            quitWithUpper who) ∧
    (∀ who (coalition : {S : Finset ι // S.Nonempty}),
      who ∉ coalition.1 →
        continueLower who ≤ reward coalition who ∧
          reward coalition who ≤ continueUpper who) ∧
    (∀ who,
      continueUpper who <
        (1 - lower (blocker who)) * quitWithoutLower who +
          lower (blocker who) * quitWithLower who) ∧
    ∀ who,
      (1 - upper (blocker who)) * quitWithoutUpper who +
          upper (blocker who) * quitWithUpper who ≤
        continueLower who

private lemma sigmaValue_lower_bound_of_conditionalRange
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {lower upper : ι → ℝ} {blocker : Equiv.Perm ι}
    {quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper : ι → ℝ}
    {continueLower continueUpper : ι → ℝ}
    (hrange : IsQuittingConditionalFaceGapRange reward lower upper blocker
      quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper
      continueLower continueUpper)
    (hazard : ι → ℝ) (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (who : ι) :
    (1 - hazard (blocker who)) * quitWithoutLower who +
        hazard (blocker who) * quitWithLower who ≤
      sigmaValue (weightOfReward reward) hazard who := by
  rw [sigmaValue_eq_blocker_mixture _ _ who (blocker who) (hrange.1 who)]
  have hwithout := weightedAverage_le_of_lower hhazard
    (conditionalRangeBackground who (blocker who))
    (fun background => weightOfReward reward (insert who background) who)
    (quitWithoutLower who) (fun background hbackground => by
      have hsubset := Finset.mem_powerset.mp hbackground
      have hwho := fun hmem =>
        who_not_mem_conditionalRangeBackground who (blocker who) (hsubset hmem)
      have hblocker := fun hmem =>
        blocker_not_mem_conditionalRangeBackground who (blocker who) (hsubset hmem)
      simpa [weightOfReward] using
        (hrange.2.1 who background hwho hblocker).1)
  have hwith := weightedAverage_le_of_lower hhazard
    (conditionalRangeBackground who (blocker who))
    (fun background =>
      weightOfReward reward (insert (blocker who) (insert who background)) who)
    (quitWithLower who) (fun background hbackground => by
      have hsubset := Finset.mem_powerset.mp hbackground
      have hwho := fun hmem =>
        who_not_mem_conditionalRangeBackground who (blocker who) (hsubset hmem)
      have hblocker := fun hmem =>
        blocker_not_mem_conditionalRangeBackground who (blocker who) (hsubset hmem)
      simpa [weightOfReward] using
        (hrange.2.1 who background hwho hblocker).2.2.1)
  have hqNonneg : 0 ≤ hazard (blocker who) := hhazard.1 (blocker who)
  have hqLeOne : hazard (blocker who) ≤ 1 := hhazard.2 (blocker who)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hwithout (sub_nonneg.mpr hqLeOne))
    (mul_le_mul_of_nonneg_left hwith hqNonneg)

private lemma sigmaValue_upper_bound_of_conditionalRange
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {lower upper : ι → ℝ} {blocker : Equiv.Perm ι}
    {quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper : ι → ℝ}
    {continueLower continueUpper : ι → ℝ}
    (hrange : IsQuittingConditionalFaceGapRange reward lower upper blocker
      quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper
      continueLower continueUpper)
    (hazard : ι → ℝ) (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (who : ι) :
    sigmaValue (weightOfReward reward) hazard who ≤
      (1 - hazard (blocker who)) * quitWithoutUpper who +
        hazard (blocker who) * quitWithUpper who := by
  rw [sigmaValue_eq_blocker_mixture _ _ who (blocker who) (hrange.1 who)]
  have hwithout := weightedAverage_le_of_le hhazard
    (conditionalRangeBackground who (blocker who))
    (fun background => weightOfReward reward (insert who background) who)
    (quitWithoutUpper who) (fun background hbackground => by
      have hsubset := Finset.mem_powerset.mp hbackground
      have hwho := fun hmem =>
        who_not_mem_conditionalRangeBackground who (blocker who) (hsubset hmem)
      have hblocker := fun hmem =>
        blocker_not_mem_conditionalRangeBackground who (blocker who) (hsubset hmem)
      simpa [weightOfReward] using
        (hrange.2.1 who background hwho hblocker).2.1)
  have hwith := weightedAverage_le_of_le hhazard
    (conditionalRangeBackground who (blocker who))
    (fun background =>
      weightOfReward reward (insert (blocker who) (insert who background)) who)
    (quitWithUpper who) (fun background hbackground => by
      have hsubset := Finset.mem_powerset.mp hbackground
      have hwho := fun hmem =>
        who_not_mem_conditionalRangeBackground who (blocker who) (hsubset hmem)
      have hblocker := fun hmem =>
        blocker_not_mem_conditionalRangeBackground who (blocker who) (hsubset hmem)
      simpa [weightOfReward] using
        (hrange.2.1 who background hwho hblocker).2.2.2)
  have hqNonneg : 0 ≤ hazard (blocker who) := hhazard.1 (blocker who)
  have hqLeOne : hazard (blocker who) ≤ 1 := hhazard.2 (blocker who)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hwithout (sub_nonneg.mpr hqLeOne))
    (mul_le_mul_of_nonneg_left hwith hqNonneg)

private lemma continueMassExcl_lt_one_of_blocker_positive
    (hazard : ι → ℝ) (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (who blocker : ι) (hne : blocker ≠ who) (hpositive : 0 < hazard blocker) :
    continueMassExcl hazard who < 1 := by
  unfold continueMassExcl
  have hmem : blocker ∈ Finset.univ.erase who := by simp [hne]
  have hrestLe :
      (∏ other ∈ (Finset.univ.erase who).erase blocker,
        (1 - hazard other)) ≤ 1 :=
    Finset.prod_le_one
      (fun other _ => sub_nonneg.mpr (hhazard.2 other))
      (fun other _ => by linarith [hhazard.1 other])
  have hfactorNonneg : 0 ≤ 1 - hazard blocker :=
    sub_nonneg.mpr (hhazard.2 blocker)
  calc
    ∏ other ∈ Finset.univ.erase who, (1 - hazard other) =
        (∏ other ∈ (Finset.univ.erase who).erase blocker,
          (1 - hazard other)) * (1 - hazard blocker) := by
      exact (Finset.prod_erase_mul (Finset.univ.erase who)
        (fun other => 1 - hazard other) hmem).symm
    _ ≤ 1 * (1 - hazard blocker) :=
      mul_le_mul_of_nonneg_right hrestLe hfactorNonneg
    _ < 1 := by linarith

/-- Supplied literal reward ranges imply the strict-lower and weak-upper
division-free face signs on the hazard box. -/
theorem conditionalFaceSigns_of_rewardRange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper : ι → ℝ)
    (continueLower continueUpper : ι → ℝ)
    (hblockerLower : ∀ who, 0 < lower (blocker who))
    (hupper : ∀ who, upper who ≤ 1)
    (hrange : IsQuittingConditionalFaceGapRange reward lower upper blocker
      quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper
      continueLower continueUpper) :
    (∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = lower (blocker who) →
        0 < quittingFaceNumerator (weightOfReward reward) hazard who) ∧
      ∀ hazard ∈ Icc lower upper, ∀ who,
        hazard (blocker who) = upper (blocker who) →
          quittingFaceNumerator (weightOfReward reward) hazard who ≤ 0 := by
  have hlower : ∀ who, 0 ≤ lower who := by
    intro who
    have h := (hblockerLower (blocker.symm who)).le
    simpa using h
  have hbox : Icc lower upper ⊆ Icc (fun _ => 0) (fun _ => 1) := by
    rintro hazard ⟨hazardLower, hazardUpper⟩
    exact ⟨fun who => (hlower who).trans (hazardLower who),
      fun who => (hazardUpper who).trans (hupper who)⟩
  constructor
  · intro hazard hhazard who hface
    have hcube := hbox hhazard
    have hsigma := sigmaValue_lower_bound_of_conditionalRange
      hrange hazard hcube who
    have hcontinue := excludedValue_le_one_sub_continueMass_mul
      (weightOfReward reward) hazard who hcube (continueUpper who) (by
        intro coalition hcoalition
        have hsubset := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hcoalition)
        have hnonempty : coalition.Nonempty := by
          exact Finset.nonempty_iff_ne_empty.mpr
            (Finset.ne_of_mem_erase hcoalition)
        have hwho : who ∉ coalition := fun hmem =>
          Finset.ne_of_mem_erase (hsubset hmem) rfl
        simpa [weightOfReward, hnonempty] using
          (hrange.2.2.1 who ⟨coalition, hnonempty⟩ hwho).2)
    have hcontracts := continueMassExcl_lt_one_of_blocker_positive
      hazard hcube who (blocker who) (hrange.1 who) (by
        rw [hface]
        exact hblockerLower who)
    unfold quittingFaceNumerator
    rw [hface] at hsigma
    have hmix := hrange.2.2.2.1 who
    have hmass : 0 < 1 - continueMassExcl hazard who := sub_pos.mpr hcontracts
    nlinarith [mul_pos hmass (sub_pos.mpr hmix)]
  · intro hazard hhazard who hface
    have hcube := hbox hhazard
    have hsigma := sigmaValue_upper_bound_of_conditionalRange
      hrange hazard hcube who
    have hcontinue := one_sub_continueMass_mul_le_excludedValue
      (weightOfReward reward) hazard who hcube (continueLower who) (by
        intro coalition hcoalition
        have hsubset := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hcoalition)
        have hnonempty : coalition.Nonempty := by
          exact Finset.nonempty_iff_ne_empty.mpr
            (Finset.ne_of_mem_erase hcoalition)
        have hwho : who ∉ coalition := fun hmem =>
          Finset.ne_of_mem_erase (hsubset hmem) rfl
        simpa [weightOfReward, hnonempty] using
          (hrange.2.2.1 who ⟨coalition, hnonempty⟩ hwho).1)
    unfold quittingFaceNumerator
    rw [hface] at hsigma
    have hmix := hrange.2.2.2.2 who
    have hmass : 0 ≤ 1 - continueMassExcl hazard who := by
      unfold continueMassExcl
      apply sub_nonneg.mpr
      exact Finset.prod_le_one
        (fun other _ => sub_nonneg.mpr (hcube.2 other))
        (fun other _ => by linarith [hcube.1 other])
    nlinarith [mul_nonneg hmass (sub_nonneg.mpr hmix)]

/-- A literal finite reward-range screen produces a complete exact stationary
certificate.  The upper mixture inequality may bind. -/
theorem exists_stationaryCertificate_of_conditionalFaceGapRange [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper : ι → ℝ)
    (continueLower continueUpper : ι → ℝ)
    (hblockerLower : ∀ who, 0 < lower (blocker who))
    (hgap : ∀ who, lower who < upper who)
    (hupper : ∀ who, upper who ≤ 1)
    (hrange : IsQuittingConditionalFaceGapRange reward lower upper blocker
      quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper
      continueLower continueUpper) :
    Nonempty (QuittingConditionalFaceGapStationaryCertificate reward lower upper) := by
  have hlower : ∀ who, 0 ≤ lower who := by
    intro who
    have h := (hblockerLower (blocker.symm who)).le
    simpa using h
  obtain ⟨hlowerFace, hupperFace⟩ := conditionalFaceSigns_of_rewardRange
    reward lower upper blocker quitWithoutLower quitWithoutUpper
      quitWithLower quitWithUpper continueLower continueUpper hblockerLower
      hupper hrange
  exact exists_stationaryCertificate_of_conditionalFaceGap reward lower upper
    blocker hlower hgap hupper hlowerFace hupperFace

/-- Direct uniform-payoff consequence of the literal reward-range screen. -/
theorem exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (lower upper : ι → ℝ) (blocker : Equiv.Perm ι)
    (quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper : ι → ℝ)
    (continueLower continueUpper : ι → ℝ)
    (hblockerLower : ∀ who, 0 < lower (blocker who))
    (hgap : ∀ who, lower who < upper who)
    (hupper : ∀ who, upper who ≤ 1)
    (hrange : IsQuittingConditionalFaceGapRange reward lower upper blocker
      quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper
      continueLower continueUpper) :
    ∃ value : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  let certificate := (exists_stationaryCertificate_of_conditionalFaceGapRange
    reward lower upper blocker quitWithoutLower quitWithoutUpper quitWithLower
      quitWithUpper continueLower continueUpper hblockerLower hgap hupper
      hrange).some
  exact ⟨certificate.value, certificate.uniformEquilibriumPayoff⟩

end GameTheory
