/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.ConditionalFaceGapRange

/-!
# A five-player conditional-face-gap regression

This file records an explicit reward table whose direct conditional face signs
produce an exact stationary uniform-equilibrium payoff, although the coarse
literal reward-range sufficient criterion does not apply.
-/

noncomputable section

namespace GameTheory
namespace ConditionalFaceGapFivePlayer

open StochasticGame Math.Topology Set
open Math.Finset

abbrev Player := Fin 5

/-- The designated blocker is the next player in the five-cycle. -/
def blocker : Equiv.Perm Player := finRotate 5

/-- Singleton payoff offsets. -/
def singletonOffset : Player → Player → ℝ :=
  ![![0, -1, 2, 1, 1],
    ![2, 0, -1, 1, 1],
    ![-1, 2, 0, 1, 1],
    ![1, 1, 1, 0, 1],
    ![1, 1, 1, 1, 0]]

/-- The literal terminal reward table, extended harmlessly to the empty set. -/
def weight (coalition : Finset Player) (who : Player) : ℝ :=
  if coalition.card = 1 then
    1 + ∑ owner ∈ coalition, singletonOffset who owner
  else if who ∉ coalition then 1
  else if blocker who ∈ coalition then -63
  else 65

/-- The terminal reward table on nonempty quitting coalitions. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  rewardOfWeight weight

def lower : Player → ℝ := fun _ => 1 / 8

def upper : Player → ℝ := fun _ => 3 / 4

theorem blocker_apply (who : Player) :
    blocker who = who + 1 := by
  exact finRotate_apply who

@[simp] theorem weightOfReward_eq (coalition : Finset Player)
    (hcoalition : coalition.Nonempty) (who : Player) :
    weightOfReward reward coalition who = weight coalition who := by
  exact weightOfReward_rewardOfWeight weight coalition hcoalition who

@[simp] theorem weight_singleton (owner who : Player) :
    weight {owner} who = 1 + singletonOffset who owner := by
  simp [weight]

theorem blocker_ne (who : Player) : blocker who ≠ who := by
  fin_cases who <;> decide

/-- Probability that at least one opponent other than the blocker Quits. -/
def backgroundQuitMass (hazard : Player → ℝ) (who : Player) : ℝ :=
  1 - ∏ other ∈ (Finset.univ.erase who).erase (blocker who),
    (1 - hazard other)

private def background (who : Player) : Finset Player :=
  (Finset.univ.erase who).erase (blocker who)

private lemma erase_who_eq_insert_blocker_background (who : Player) :
    Finset.univ.erase who = insert (blocker who) (background who) := by
  ext other
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert,
    background]
  have hne := blocker_ne who
  constructor
  · intro hwho
    by_cases hblocker : other = blocker who
    · exact Or.inl hblocker
    · exact Or.inr ⟨hblocker, hwho⟩
  · rintro (hblocker | ⟨_, hwho⟩)
    · subst other
      exact hne
    · exact hwho

private lemma blocker_not_mem_background (who : Player) :
    blocker who ∉ background who := by
  simp [background]

private lemma who_not_mem_background (who : Player) :
    who ∉ background who := by
  simp [background]

private lemma sigmaValue_eq_blocker_mixture
    (hazard : Player → ℝ) (who : Player) :
    sigmaValue (weightOfReward reward) hazard who =
      (1 - hazard (blocker who)) *
          (∑ subset ∈ (background who).powerset,
            bernoulliWeight hazard (background who) subset *
              weight (insert who subset) who) +
        hazard (blocker who) *
          (∑ subset ∈ (background who).powerset,
            bernoulliWeight hazard (background who) subset *
              weight (insert (blocker who) (insert who subset)) who) := by
  unfold sigmaValue bernoulliWeight
  rw [erase_who_eq_insert_blocker_background,
    Finset.sum_powerset_insert (blocker_not_mem_background who)]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro subset hsubset
    have hsubset' := Finset.mem_powerset.mp hsubset
    have hblocker : blocker who ∉ subset := fun hmem =>
      blocker_not_mem_background who (hsubset' hmem)
    have hdiff :
        insert (blocker who) (background who) \ subset =
          insert (blocker who) (background who \ subset) := by
      ext other
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    rw [hdiff, Finset.prod_insert]
    · simp only [weightOfReward_eq (insert who subset)
          (Finset.insert_nonempty who subset) who]
      ring
    · intro hmem
      exact blocker_not_mem_background who (Finset.mem_sdiff.mp hmem).1
  · apply Finset.sum_congr rfl
    intro subset hsubset
    have hsubset' := Finset.mem_powerset.mp hsubset
    have hblocker : blocker who ∉ subset := fun hmem =>
      blocker_not_mem_background who (hsubset' hmem)
    rw [Finset.prod_insert hblocker]
    have hdiff :
        insert (blocker who) (background who) \
            insert (blocker who) subset =
          background who \ subset := by
      ext other
      by_cases hother : other = blocker who
      · subst other
        simp [blocker_not_mem_background]
      · simp [hother]
    rw [hdiff, Finset.insert_comm (blocker who) who]
    simp only [weightOfReward_eq
      (insert who (insert (blocker who) subset))
      (Finset.insert_nonempty who _) who]
    ring

private lemma weight_without_blocker_empty (who : Player) :
    weight (insert who ∅) who = 1 := by
  have hdiag : singletonOffset who who = 0 := by
    fin_cases who <;> rfl
  simp [weight, hdiag]

private lemma weight_without_blocker_nonempty (who : Player)
    (subset : Finset Player) (hsubset : subset ⊆ background who)
    (hne : subset.Nonempty) :
    weight (insert who subset) who = 65 := by
  have hwho : who ∉ subset := fun hmem => who_not_mem_background who (hsubset hmem)
  have hblocker : blocker who ∉ subset := fun hmem =>
    blocker_not_mem_background who (hsubset hmem)
  have hcard : (insert who subset).card ≠ 1 := by
    rw [Finset.card_insert_of_notMem hwho]
    have hpos : 0 < subset.card := Finset.card_pos.mpr hne
    omega
  simp [weight, hcard, hblocker, blocker_ne who]

private lemma weight_with_blocker (who : Player) (subset : Finset Player) :
    weight (insert (blocker who) (insert who subset)) who = -63 := by
  have hcard : (insert (blocker who) (insert who subset)).card ≠ 1 := by
    have hne := blocker_ne who
    have htwo : ({blocker who, who} : Finset Player).card = 2 := by
      simp [hne]
    have hsubset : {blocker who, who} ⊆
        insert (blocker who) (insert who subset) := by simp
    have hle := Finset.card_le_card hsubset
    omega
  rw [weight]
  simp only [if_neg hcard]
  simp

private lemma without_blocker_average (hazard : Player → ℝ) (who : Player) :
    (∑ subset ∈ (background who).powerset,
      bernoulliWeight hazard (background who) subset *
        weight (insert who subset) who) =
      65 - 64 * ∏ other ∈ background who, (1 - hazard other) := by
  have hempty :
      bernoulliWeight hazard (background who) ∅ =
        ∏ other ∈ background who, (1 - hazard other) := by
    simp [bernoulliWeight]
  have hsplit := Finset.sum_erase_add (background who).powerset
    (fun subset => bernoulliWeight hazard (background who) subset *
      weight (insert who subset) who)
    (Finset.empty_mem_powerset (background who))
  rw [weight_without_blocker_empty, mul_one, hempty] at hsplit
  have hnonempty :
      (∑ subset ∈ (background who).powerset.erase ∅,
        bernoulliWeight hazard (background who) subset *
          weight (insert who subset) who) =
        (1 - ∏ other ∈ background who, (1 - hazard other)) * 65 := by
    calc
      _ = ∑ subset ∈ (background who).powerset.erase ∅,
          bernoulliWeight hazard (background who) subset * 65 := by
        apply Finset.sum_congr rfl
        intro subset hsubset
        rw [weight_without_blocker_nonempty who subset
          (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hsubset))
          (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hsubset))]
      _ = (1 - ∏ other ∈ background who, (1 - hazard other)) * 65 := by
        rw [← Finset.sum_mul]
        have hmass := sum_bernoulliWeight hazard (background who)
        have hmassSplit := Finset.sum_erase_add (background who).powerset
          (bernoulliWeight hazard (background who))
          (Finset.empty_mem_powerset (background who))
        rw [hempty, hmass] at hmassSplit
        rw [show ∑ x ∈ (background who).powerset.erase ∅,
          bernoulliWeight hazard (background who) x =
            1 - ∏ other ∈ background who, (1 - hazard other) by linarith]
  rw [hnonempty] at hsplit
  linarith

private lemma with_blocker_average (hazard : Player → ℝ) (who : Player) :
    (∑ subset ∈ (background who).powerset,
      bernoulliWeight hazard (background who) subset *
        weight (insert (blocker who) (insert who subset)) who) = -63 := by
  calc
    _ = ∑ subset ∈ (background who).powerset,
        bernoulliWeight hazard (background who) subset * (-63) := by
      apply Finset.sum_congr rfl
      intro subset _
      rw [weight_with_blocker]
    _ = -63 := by
      rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

/-- The pure-Quit endpoint has a uniform closed form. -/
theorem sigmaValue_eq (hazard : Player → ℝ) (who : Player) :
    sigmaValue (weightOfReward reward) hazard who =
      1 + 64 * ((1 - hazard (blocker who)) * backgroundQuitMass hazard who -
        hazard (blocker who)) := by
  rw [sigmaValue_eq_blocker_mixture, without_blocker_average,
    with_blocker_average]
  simp only [backgroundQuitMass, background]
  ring

private lemma backgroundQuitMass_bounds
    (hazard : Player → ℝ) (hhazard : hazard ∈ Icc lower upper)
    (who : Player) :
    169 / 512 ≤ backgroundQuitMass hazard who ∧
      backgroundQuitMass hazard who ≤ 63 / 64 := by
  have hfactor : ∀ other, (1 / 4 : ℝ) ≤ 1 - hazard other ∧
      1 - hazard other ≤ 7 / 8 := by
    intro other
    constructor
    · have := hhazard.2 other
      norm_num [upper] at this ⊢
      linarith
    · have := hhazard.1 other
      norm_num [lower] at this ⊢
      linarith
  have hblockerMem : blocker who ∈ Finset.univ.erase who := by
    simp [blocker_ne who]
  have hcard : (background who).card = 3 := by
    rw [background, Finset.card_erase_of_mem hblockerMem,
      Finset.card_erase_of_mem (Finset.mem_univ who)]
    norm_num
  have hproductLower :
      (1 / 64 : ℝ) ≤ ∏ other ∈ background who, (1 - hazard other) := by
    calc
      (1 / 64 : ℝ) = (1 / 4) ^ (background who).card := by
        rw [hcard]
        norm_num
      _ = ∏ _other ∈ background who, (1 / 4 : ℝ) := by
        rw [Finset.prod_const]
      _ ≤ ∏ other ∈ background who, (1 - hazard other) := by
        exact Finset.prod_le_prod (fun _ _ => by norm_num)
          (fun other _ => (hfactor other).1)
  have hproductUpper :
      (∏ other ∈ background who, (1 - hazard other)) ≤ 343 / 512 := by
    calc
      _ ≤ ∏ _other ∈ background who, (7 / 8 : ℝ) := by
        exact Finset.prod_le_prod
          (fun other _ => by linarith [(hfactor other).1])
          (fun other _ => (hfactor other).2)
      _ = (7 / 8 : ℝ) ^ (background who).card := by
        rw [Finset.prod_const]
      _ = 343 / 512 := by rw [hcard]; norm_num
  unfold backgroundQuitMass
  change (169 / 512 : ℝ) ≤
      1 - ∏ other ∈ background who, (1 - hazard other) ∧
    1 - ∏ other ∈ background who, (1 - hazard other) ≤ 63 / 64
  constructor <;> linarith

private lemma continue_weight_bounds (coalition : Finset Player) (who : Player)
    (hnonempty : coalition.Nonempty) (hwho : who ∉ coalition) :
    0 ≤ weight coalition who ∧ weight coalition who ≤ 3 := by
  by_cases hcard : coalition.card = 1
  · obtain ⟨owner, rfl⟩ := Finset.card_eq_one.mp hcard
    fin_cases who <;> fin_cases owner <;>
      norm_num [weight, singletonOffset]
  · simp [weight, hcard, hwho]

private lemma bernoulliWeight_nonneg
    (hazard : Player → ℝ)
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (carrier subset : Finset Player) :
    0 ≤ bernoulliWeight hazard carrier subset := by
  exact mul_nonneg
    (Finset.prod_nonneg fun who _ => hhazard.1 who)
    (Finset.prod_nonneg fun who _ => sub_nonneg.mpr (hhazard.2 who))

private lemma excludedValue_bounds
    (hazard : Player → ℝ)
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (who : Player) :
    0 ≤ excludedValue (weightOfReward reward) hazard who ∧
      excludedValue (weightOfReward reward) hazard who ≤
        (1 - continueMassExcl hazard who) * 3 := by
  let carrier := Finset.univ.erase who
  have hcoefficient (coalition : Finset Player) :
      0 ≤ bernoulliWeight hazard carrier coalition :=
    bernoulliWeight_nonneg hazard hhazard carrier coalition
  have hmass :
      ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition =
        1 - continueMassExcl hazard who := by
    have hempty :
        bernoulliWeight hazard carrier ∅ = continueMassExcl hazard who := by
      simp [bernoulliWeight, continueMassExcl, carrier]
    have hsplit := Finset.sum_erase_add carrier.powerset
      (bernoulliWeight hazard carrier)
      (Finset.empty_mem_powerset carrier)
    rw [hempty, sum_bernoulliWeight] at hsplit
    linarith
  unfold excludedValue
  constructor
  · exact Finset.sum_nonneg fun coalition hcoalition =>
      mul_nonneg (hcoefficient coalition)
        (by
          have hsubset := Finset.mem_powerset.mp
            (Finset.mem_of_mem_erase hcoalition)
          have hnonempty := Finset.nonempty_iff_ne_empty.mpr
            (Finset.ne_of_mem_erase hcoalition)
          have hwho : who ∉ coalition := fun hmem =>
            Finset.ne_of_mem_erase (hsubset hmem) rfl
          simpa [weightOfReward, reward, rewardOfWeight, hnonempty] using
            (continue_weight_bounds coalition who hnonempty hwho).1)
  · calc
      _ ≤ ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition * 3 := by
        apply Finset.sum_le_sum
        intro coalition hcoalition
        apply mul_le_mul_of_nonneg_left _ (hcoefficient coalition)
        have hsubset := Finset.mem_powerset.mp
          (Finset.mem_of_mem_erase hcoalition)
        have hnonempty := Finset.nonempty_iff_ne_empty.mpr
          (Finset.ne_of_mem_erase hcoalition)
        have hwho : who ∉ coalition := fun hmem =>
          Finset.ne_of_mem_erase (hsubset hmem) rfl
        simpa [weightOfReward, reward, rewardOfWeight, hnonempty] using
          (continue_weight_bounds coalition who hnonempty hwho).2
      _ = (1 - continueMassExcl hazard who) * 3 := by
        rw [← Finset.sum_mul, hmass]

private lemma continueMassExcl_lt_one
    (hazard : Player → ℝ)
    (hhazard : hazard ∈ Icc (fun _ => 0) (fun _ => 1))
    (who : Player) (hpositive : 0 < hazard (blocker who)) :
    continueMassExcl hazard who < 1 := by
  have hmem : blocker who ∈ Finset.univ.erase who := by
    simp [blocker_ne who]
  have hrestLe :
      (∏ other ∈ (Finset.univ.erase who).erase (blocker who),
        (1 - hazard other)) ≤ 1 :=
    Finset.prod_le_one
      (fun other _ => sub_nonneg.mpr (hhazard.2 other))
      (fun other _ => by linarith [hhazard.1 other])
  have hfactorNonneg : 0 ≤ 1 - hazard (blocker who) :=
    sub_nonneg.mpr (hhazard.2 (blocker who))
  unfold continueMassExcl
  calc
    ∏ other ∈ Finset.univ.erase who, (1 - hazard other) =
        (∏ other ∈ (Finset.univ.erase who).erase (blocker who),
          (1 - hazard other)) * (1 - hazard (blocker who)) := by
      exact (Finset.prod_erase_mul (Finset.univ.erase who)
        (fun other => 1 - hazard other) hmem).symm
    _ ≤ 1 * (1 - hazard (blocker who)) :=
      mul_le_mul_of_nonneg_right hrestLe hfactorNonneg
    _ < 1 := by linarith

private lemma box_mem_unitCube
    {hazard : Player → ℝ} (hhazard : hazard ∈ Icc lower upper) :
    hazard ∈ Icc (fun _ => 0) (fun _ => 1) := by
  constructor
  · intro who
    have := hhazard.1 who
    norm_num [lower] at this ⊢
    linarith
  · intro who
    have := hhazard.2 who
    norm_num [upper] at this ⊢
    linarith

/-- The direct numerator signs hold on the designated lower and upper faces. -/
theorem directFaceSigns :
    (∀ hazard ∈ Icc lower upper, ∀ who,
      hazard (blocker who) = lower (blocker who) →
        0 < quittingFaceNumerator (weightOfReward reward) hazard who) ∧
      ∀ hazard ∈ Icc lower upper, ∀ who,
        hazard (blocker who) = upper (blocker who) →
          quittingFaceNumerator (weightOfReward reward) hazard who < 0 := by
  constructor
  · intro hazard hhazard who hface
    have hcube := box_mem_unitCube hhazard
    have hbackground := backgroundQuitMass_bounds hazard hhazard who
    have hsigma : 3 < sigmaValue (weightOfReward reward) hazard who := by
      rw [sigmaValue_eq, hface]
      norm_num [lower]
      nlinarith [hbackground.1]
    have hexcluded := excludedValue_bounds hazard hcube who
    have hpositive : 0 < hazard (blocker who) := by
      rw [hface]
      norm_num [lower]
    have hmass : 0 < 1 - continueMassExcl hazard who :=
      sub_pos.mpr (continueMassExcl_lt_one hazard hcube who hpositive)
    unfold quittingFaceNumerator
    have hstrict : 0 <
        (1 - continueMassExcl hazard who) *
          (sigmaValue (weightOfReward reward) hazard who - 3) :=
      mul_pos hmass (sub_pos.mpr hsigma)
    nlinarith
  · intro hazard hhazard who hface
    have hcube := box_mem_unitCube hhazard
    have hbackground := backgroundQuitMass_bounds hazard hhazard who
    have hsigma : sigmaValue (weightOfReward reward) hazard who < 0 := by
      rw [sigmaValue_eq, hface]
      norm_num [upper]
      nlinarith [hbackground.2]
    have hexcluded := excludedValue_bounds hazard hcube who
    have hpositive : 0 < hazard (blocker who) := by
      rw [hface]
      norm_num [upper]
    have hmass : 0 < 1 - continueMassExcl hazard who :=
      sub_pos.mpr (continueMassExcl_lt_one hazard hcube who hpositive)
    unfold quittingFaceNumerator
    have hstrict :
        (1 - continueMassExcl hazard who) *
            sigmaValue (weightOfReward reward) hazard who < 0 :=
      mul_neg_of_pos_of_neg hmass hsigma
    linarith

/-- The direct face producer supplies a complete exact stationary certificate. -/
theorem exists_stationaryCertificate :
    ∃ certificate : QuittingConditionalFaceGapStationaryCertificate reward lower upper,
      ∀ who, certificate.hazard who < upper who := by
  exact exists_stationaryCertificate_of_strictConditionalFaceGap
    reward lower upper blocker
    (by intro who; norm_num [lower])
    (by intro who; norm_num [lower, upper])
    (by intro who; norm_num [upper])
    directFaceSigns.1 directFaceSigns.2

/-- In particular, the literal five-player game has an exact stationary
uniform-equilibrium payoff against arbitrary behavioral unilateral deviations. -/
theorem exists_uniformEquilibriumPayoff :
    ∃ value : Payoff Player,
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  obtain ⟨certificate, _⟩ := exists_stationaryCertificate
  exact ⟨certificate.value, certificate.uniformEquilibriumPayoff⟩

/-- Continuers are not passive: player zero receives a nonzero payoff when
players one and two Quit. -/
theorem nonpassive_continuer_witness :
    reward ⟨{1, 2}, by simp⟩ 0 = 1 := by
  simp [reward, rewardOfWeight, weight]

/-- No supplied literal bounds can make the coarse reward-range screen hold
on this box.  The direct face argument is therefore genuinely sharper than
that sufficient screen. -/
theorem not_isQuittingConditionalFaceGapRange
    (quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper :
      Player → ℝ)
    (continueLower continueUpper : Player → ℝ) :
    ¬ IsQuittingConditionalFaceGapRange reward lower upper blocker
      quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper
      continueLower continueUpper := by
  intro hrange
  have hwithout := (hrange.2.1 0 ∅ (by simp) (by simp [blocker])).1
  have hwith := (hrange.2.1 0 ∅ (by simp) (by simp [blocker])).2.2.1
  have hcontinue := (hrange.2.2.1 0 ⟨{2}, by simp⟩ (by simp)).2
  have hmixture := hrange.2.2.2.1 0
  norm_num [reward, rewardOfWeight, weight, singletonOffset, lower, blocker,
    Matrix.cons_val_two]
    at hwithout hwith hcontinue hmixture
  linarith

end ConditionalFaceGapFivePlayer
end GameTheory
