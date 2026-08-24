/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Finset.PowersetBernoulliWeight
import UniformEquilibrium.Quitting.Classification.Existence.OddBlockerCore

/-!
# Literal coalition-row adapter for the three-player odd blocker core

The source predicate in this file is the finite coalition-table check from
the mathematical odd-blocker statement.  Passive continuation is checked on
every nonempty row omitting the core player.  Each strict blocker switch is
checked on every background omitting the owner and its blocker.  The adapter
proves the stationary-face predicate consumed by `OddBlockerCore.lean`.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def blockerBackground (who blocker : ι) : Finset ι :=
  (Finset.univ.erase who).erase blocker

private theorem erase_eq_insert_blockerBackground
    {who blocker : ι} (hne : blocker ≠ who) :
    Finset.univ.erase who = insert blocker (blockerBackground who blocker) := by
  ext other
  simp [blockerBackground, hne]

private theorem blocker_not_mem_background (who blocker : ι) :
    blocker ∉ blockerBackground who blocker := by
  simp [blockerBackground]

private theorem who_not_mem_blockerBackground (who blocker : ι) :
    who ∉ blockerBackground who blocker := by
  simp [blockerBackground]

/-- Literal finite reward-table conditions for a strict passive three-cycle.
No condition is imposed on the payoff coordinate of any outside player. -/
structure IsLiteralStrictThreeBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (first second third : ι) : Prop where
  first_ne_second : first ≠ second
  second_ne_third : second ≠ third
  third_ne_first : third ≠ first
  passive : ∀ (S : {S : Finset ι // S.Nonempty}) (who : ι),
    who = first ∨ who = second ∨ who = third →
    who ∉ S.1 → reward S who = baseline who
  first_switch : ∀ background : Finset ι,
    first ∉ background → second ∉ background →
    baseline first <
        reward ⟨insert first background, Finset.insert_nonempty _ _⟩ first ∧
      reward ⟨insert second (insert first background),
        Finset.insert_nonempty _ _⟩ first < baseline first
  second_switch : ∀ background : Finset ι,
    second ∉ background → third ∉ background →
    baseline second <
        reward ⟨insert second background, Finset.insert_nonempty _ _⟩ second ∧
      reward ⟨insert third (insert second background),
        Finset.insert_nonempty _ _⟩ second < baseline second
  third_switch : ∀ background : Finset ι,
    third ∉ background → first ∉ background →
    baseline third <
        reward ⟨insert third background, Finset.insert_nonempty _ _⟩ third ∧
      reward ⟨insert first (insert third background),
        Finset.insert_nonempty _ _⟩ third < baseline third

omit [Fintype ι] in
private theorem oddCoreBernoulliWeight_nonneg
    {hazard : ι → ℝ}
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier subset : Finset ι) :
    0 ≤ bernoulliWeight hazard carrier subset := by
  exact mul_nonneg
    (Finset.prod_nonneg fun who _ => hhazard.1 who)
    (Finset.prod_nonneg fun who _ => sub_nonneg.mpr (hhazard.2 who))

omit [Fintype ι] in
private theorem exists_oddCoreBernoulliWeight_pos
    {hazard : ι → ℝ}
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) :
    ∃ subset ∈ carrier.powerset,
      0 < bernoulliWeight hazard carrier subset := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset = 0 := by
    intro subset hsubset
    exact le_antisymm (hnone subset hsubset)
      (oddCoreBernoulliWeight_nonneg hhazard carrier subset)
  have hsum := sum_bernoulliWeight hazard carrier
  rw [Finset.sum_eq_zero hzero] at hsum
  norm_num at hsum

omit [Fintype ι] in
private theorem baseline_lt_oddCoreWeightedAverage
    {hazard : ι → ℝ}
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) (value : Finset ι → ℝ) (baseline : ℝ)
    (hvalue : ∀ subset ∈ carrier.powerset, baseline < value subset) :
    baseline < ∑ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset * value subset := by
  have hpositive : 0 < ∑ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset * (value subset - baseline) := by
    obtain ⟨subset, hsubset, hweight⟩ :=
      exists_oddCoreBernoulliWeight_pos hhazard carrier
    apply Finset.sum_pos'
    · intro other hother
      exact mul_nonneg
        (oddCoreBernoulliWeight_nonneg hhazard carrier other)
        (sub_nonneg.mpr (hvalue other hother).le)
    · exact ⟨subset, hsubset,
        mul_pos hweight (sub_pos.mpr (hvalue subset hsubset))⟩
  have hmass := sum_bernoulliWeight hazard carrier
  calc
    baseline = ∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset * baseline := by
      rw [← Finset.sum_mul, hmass, one_mul]
    _ < ∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset * value subset := by
      rw [← sub_pos]
      simpa only [← Finset.sum_sub_distrib, ← mul_sub] using hpositive

omit [Fintype ι] in
private theorem oddCoreWeightedAverage_lt_baseline
    {hazard : ι → ℝ}
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier : Finset ι) (value : Finset ι → ℝ) (baseline : ℝ)
    (hvalue : ∀ subset ∈ carrier.powerset, value subset < baseline) :
    (∑ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset * value subset) < baseline := by
  have h := baseline_lt_oddCoreWeightedAverage hhazard carrier
    (fun subset => -value subset) (-baseline)
    (fun subset hsubset => neg_lt_neg (hvalue subset hsubset))
  have hneg :
      (∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset * -value subset) =
      -(∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset * value subset) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro subset _
    ring
  rw [hneg] at h
  linarith

private theorem oddCoreSigmaValue_blocker_face_zero
    (weight : Finset ι → ι → ℝ) (hazard : ι → ℝ)
    (who blocker : ι) (hne : blocker ≠ who) (hface : hazard blocker = 0) :
    sigmaValue weight hazard who =
      ∑ background ∈ (blockerBackground who blocker).powerset,
        bernoulliWeight hazard (blockerBackground who blocker) background *
          weight (insert who background) who := by
  unfold sigmaValue bernoulliWeight
  rw [erase_eq_insert_blockerBackground hne,
    Finset.sum_powerset_insert (blocker_not_mem_background who blocker)]
  have hblockerNotMem := blocker_not_mem_background who blocker
  have hsecondZero :
      (∑ background ∈ (blockerBackground who blocker).powerset,
        (∏ player ∈ insert blocker background, hazard player) *
          (∏ player ∈ insert blocker (blockerBackground who blocker) \
              insert blocker background, (1 - hazard player)) *
            weight (insert who (insert blocker background)) who) = 0 := by
    apply Finset.sum_eq_zero
    intro background hbackground
    have hsubset := Finset.mem_powerset.mp hbackground
    have hblockerBackground : blocker ∉ background := fun hmem =>
      hblockerNotMem (hsubset hmem)
    rw [Finset.prod_insert hblockerBackground, hface]
    ring
  rw [hsecondZero, add_zero]
  apply Finset.sum_congr rfl
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hblockerBackground : blocker ∉ background := fun hmem =>
    hblockerNotMem (hsubset hmem)
  have hsdiff : insert blocker (blockerBackground who blocker) \ background =
      insert blocker (blockerBackground who blocker \ background) := by
    ext other
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hother | hother, hnot⟩
      · exact Or.inl hother
      · exact Or.inr ⟨hother, hnot⟩
    · rintro (hother | ⟨hother, hnot⟩)
      · exact ⟨Or.inl hother, hother ▸ hblockerBackground⟩
      · exact ⟨Or.inr hother, hnot⟩
  rw [hsdiff]
  rw [Finset.prod_insert]
  · simp [hface]
  · intro hmem
    exact hblockerNotMem (Finset.mem_sdiff.mp hmem).1

private theorem oddCoreSigmaValue_blocker_face_one
    (weight : Finset ι → ι → ℝ) (hazard : ι → ℝ)
    (who blocker : ι) (hne : blocker ≠ who) (hface : hazard blocker = 1) :
    sigmaValue weight hazard who =
      ∑ background ∈ (blockerBackground who blocker).powerset,
        bernoulliWeight hazard (blockerBackground who blocker) background *
          weight (insert blocker (insert who background)) who := by
  unfold sigmaValue bernoulliWeight
  rw [erase_eq_insert_blockerBackground hne,
    Finset.sum_powerset_insert (blocker_not_mem_background who blocker)]
  have hblockerNotMem := blocker_not_mem_background who blocker
  have hfirstZero :
      (∑ background ∈ (blockerBackground who blocker).powerset,
        (∏ player ∈ background, hazard player) *
          (∏ player ∈ insert blocker (blockerBackground who blocker) \
              background, (1 - hazard player)) *
            weight (insert who background) who) = 0 := by
    apply Finset.sum_eq_zero
    intro background hbackground
    have hsubset := Finset.mem_powerset.mp hbackground
    have hblockerBackground : blocker ∉ background := fun hmem =>
      hblockerNotMem (hsubset hmem)
    have hsdiff : insert blocker (blockerBackground who blocker) \ background =
        insert blocker (blockerBackground who blocker \ background) := by
      ext other
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hother | hother, hnot⟩
        · exact Or.inl hother
        · exact Or.inr ⟨hother, hnot⟩
      · rintro (hother | ⟨hother, hnot⟩)
        · exact ⟨Or.inl hother, hother ▸ hblockerBackground⟩
        · exact ⟨Or.inr hother, hnot⟩
    rw [hsdiff]
    rw [Finset.prod_insert]
    · simp [hface]
    · intro hmem
      exact hblockerNotMem (Finset.mem_sdiff.mp hmem).1
  rw [hfirstZero, zero_add]
  apply Finset.sum_congr rfl
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hblockerBackground : blocker ∉ background := fun hmem =>
    hblockerNotMem (hsubset hmem)
  rw [Finset.prod_insert hblockerBackground, hface, one_mul]
  have hsdiff :
      insert blocker (blockerBackground who blocker) \
          insert blocker background =
        blockerBackground who blocker \ background := by
    ext other
    by_cases hother : other = blocker
    · subst other
      simp [hblockerNotMem]
    · simp [hother]
  rw [hsdiff, Finset.insert_comm blocker who]

private theorem excludedValue_eq_passiveBaseline
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} (who : ι)
    (hpassive : ∀ (S : {S : Finset ι // S.Nonempty}),
      who ∉ S.1 → reward S who = baseline who)
    (hazard : ι → ℝ) :
    excludedValue (weightOfReward reward) hazard who =
      (1 - continueMassExcl hazard who) * baseline who := by
  let carrier := Finset.univ.erase who
  have hreward : ∀ background ∈ carrier.powerset.erase ∅,
      weightOfReward reward background who = baseline who := by
    intro background hbackground
    have hpow := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hbackground)
    have hnonempty : background.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hbackground)
    have hwho : who ∉ background := fun hmem =>
      (Finset.ne_of_mem_erase (hpow hmem)) rfl
    simpa [weightOfReward, hnonempty] using
      hpassive ⟨background, hnonempty⟩ hwho
  have hsumReward :
      (∑ background ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier background *
          weightOfReward reward background who) =
        (∑ background ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier background) * baseline who := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro background hbackground
    rw [hreward background hbackground]
  have hempty : (∅ : Finset ι) ∈ carrier.powerset :=
    Finset.empty_mem_powerset _
  have hmass :
      (∑ background ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier background) +
          continueMassExcl hazard who = 1 := by
    have htotal := sum_bernoulliWeight hazard carrier
    have hsplit := Finset.sum_erase_add carrier.powerset
      (fun background => bernoulliWeight hazard carrier background) hempty
    have hemptyWeight :
        bernoulliWeight hazard carrier ∅ = continueMassExcl hazard who := by
      simp [bernoulliWeight, continueMassExcl, carrier]
    rw [hemptyWeight] at hsplit
    linarith
  unfold excludedValue
  change
    (∑ background ∈ carrier.powerset.erase ∅,
      bernoulliWeight hazard carrier background *
        weightOfReward reward background who) =
      (1 - continueMassExcl hazard who) * baseline who
  rw [hsumReward]
  congr 1
  linarith

private theorem strictBlockerLowerFace_of_rows
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {who blocker : ι} (hne : blocker ≠ who)
    (hswitch : ∀ background : Finset ι,
      who ∉ background → blocker ∉ background →
        baseline who <
          reward ⟨insert who background, Finset.insert_nonempty _ _⟩ who)
    (hazard : ι → ℝ) (hhazard0 : ∀ player, 0 ≤ hazard player)
    (hhazard1 : ∀ player, hazard player ≤ 1)
    (hface : hazard blocker = 0) :
    baseline who < sigmaValue (weightOfReward reward) hazard who := by
  rw [oddCoreSigmaValue_blocker_face_zero
    (weightOfReward reward) hazard who blocker hne hface]
  apply baseline_lt_oddCoreWeightedAverage ⟨hhazard0, hhazard1⟩
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hwho : who ∉ background := fun hmem =>
    who_not_mem_blockerBackground who blocker (hsubset hmem)
  have hblocker : blocker ∉ background := fun hmem =>
    blocker_not_mem_background who blocker (hsubset hmem)
  simpa [weightOfReward] using hswitch background hwho hblocker

private theorem strictBlockerUpperFace_of_rows
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {who blocker : ι} (hne : blocker ≠ who)
    (hswitch : ∀ background : Finset ι,
      who ∉ background → blocker ∉ background →
        reward ⟨insert blocker (insert who background),
          Finset.insert_nonempty _ _⟩ who < baseline who)
    (hazard : ι → ℝ) (hhazard0 : ∀ player, 0 ≤ hazard player)
    (hhazard1 : ∀ player, hazard player ≤ 1)
    (hface : hazard blocker = 1) :
    sigmaValue (weightOfReward reward) hazard who < baseline who := by
  rw [oddCoreSigmaValue_blocker_face_one
    (weightOfReward reward) hazard who blocker hne hface]
  apply oddCoreWeightedAverage_lt_baseline ⟨hhazard0, hhazard1⟩
  intro background hbackground
  have hsubset := Finset.mem_powerset.mp hbackground
  have hwho : who ∉ background := fun hmem =>
    who_not_mem_blockerBackground who blocker (hsubset hmem)
  have hblocker : blocker ∉ background := fun hmem =>
    blocker_not_mem_background who blocker (hsubset hmem)
  simpa [weightOfReward] using hswitch background hwho hblocker

/-- The literal finite row check supplies the polynomial stationary-face
source consumed by the compact odd-core theorem. -/
theorem IsLiteralStrictThreeBlockerCore.toStationaryFace
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {first second third : ι}
    (hcore : IsLiteralStrictThreeBlockerCore
      reward baseline first second third) :
    IsStrictThreeBlockerCore reward baseline first second third where
  first_ne_second := hcore.first_ne_second
  second_ne_third := hcore.second_ne_third
  third_ne_first := hcore.third_ne_first
  passive_first := fun hazard _ _ =>
    excludedValue_eq_passiveBaseline first
      (fun S => hcore.passive S first (Or.inl rfl)) hazard
  passive_second := fun hazard _ _ =>
    excludedValue_eq_passiveBaseline second
      (fun S => hcore.passive S second (Or.inr (Or.inl rfl))) hazard
  passive_third := fun hazard _ _ =>
    excludedValue_eq_passiveBaseline third
      (fun S => hcore.passive S third (Or.inr (Or.inr rfl))) hazard
  first_lower := fun hazard h0 h1 hface =>
    strictBlockerLowerFace_of_rows hcore.first_ne_second.symm
      (fun background hfirst hsecond =>
        (hcore.first_switch background hfirst hsecond).1)
      hazard h0 h1 hface
  first_upper := fun hazard h0 h1 hface =>
    strictBlockerUpperFace_of_rows hcore.first_ne_second.symm
      (fun background hfirst hsecond =>
        (hcore.first_switch background hfirst hsecond).2)
      hazard h0 h1 hface
  second_lower := fun hazard h0 h1 hface =>
    strictBlockerLowerFace_of_rows hcore.second_ne_third.symm
      (fun background hsecond hthird =>
        (hcore.second_switch background hsecond hthird).1)
      hazard h0 h1 hface
  second_upper := fun hazard h0 h1 hface =>
    strictBlockerUpperFace_of_rows hcore.second_ne_third.symm
      (fun background hsecond hthird =>
        (hcore.second_switch background hsecond hthird).2)
      hazard h0 h1 hface
  third_lower := fun hazard h0 h1 hface =>
    strictBlockerLowerFace_of_rows hcore.third_ne_first.symm
      (fun background hthird hfirst =>
        (hcore.third_switch background hthird hfirst).1)
      hazard h0 h1 hface
  third_upper := fun hazard h0 h1 hface =>
    strictBlockerUpperFace_of_rows hcore.third_ne_first.symm
      (fun background hthird hfirst =>
        (hcore.third_switch background hthird hfirst).2)
      hazard h0 h1 hface

/-- Literal rowwise three-core conditions produce the complete stationary
all-behavior certificate. -/
theorem exists_stationaryCertificate_of_literalStrictThreeBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (first second third : ι)
    (hcore : IsLiteralStrictThreeBlockerCore
      reward baseline first second third) :
    Nonempty (ThreeBlockerCoreStationaryCertificate
      reward baseline first second third) :=
  exists_stationaryCertificate_of_strictThreeBlockerCore
    reward baseline first second third hcore.toStationaryFace

/-- Headline uniform-payoff consequence of the literal finite row check. -/
theorem isUniformEquilibriumPayoff_of_literalStrictThreeBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (first second third : ι)
    (hcore : IsLiteralStrictThreeBlockerCore
      reward baseline first second third) :
    ∃ value : Payoff ι,
      value first = baseline first ∧
      value second = baseline second ∧
      value third = baseline third ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value :=
  isUniformEquilibriumPayoff_of_strictThreeBlockerCore
    reward baseline first second third hcore.toStationaryFace

end GameTheory
