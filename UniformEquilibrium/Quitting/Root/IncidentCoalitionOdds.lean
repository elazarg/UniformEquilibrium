/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Incident coalition odds for quitting roots

Elementary product-law estimates compare a nonsingleton coalition atom with
any incident singleton atom when total one-stage absorption is small.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One-stage absorption is the sum of all nonempty exact coalition masses. -/
theorem quittingRootAbsorptionMass_eq_sum_nonemptyCoalitionMass
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root =
      ∑ coalition : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass root coalition.1 := by
  rw [← Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι))]
  · rw [quittingRootAbsorptionMass,
      quittingRootCoalitionMass_sum_nonempty]
  · intro coalition
    simp [Finset.nonempty_iff_ne_empty]

/-- A low-absorption independent Bernoulli row has every nonsingleton atom
bounded by the absorption odds times any incident singleton atom. -/
theorem quittingRootIncidentCoalitionMass_le_absorptionOdds_mul_singleton
    (root : ι → PMF Bool) {δ : ℝ}
    (hδhalf : δ ≤ 1 / 2)
    (habsorption : quittingRootAbsorptionMass root ≤ δ)
    (coalition : Finset ι) (player : ι)
    (hcard : 2 ≤ coalition.card) (hplayer : player ∈ coalition) :
    quittingRootCoalitionMass root coalition ≤
      (δ / (1 - δ)) * quittingRootCoalitionMass root {player} := by
  let x : ι → ℝ := fun who ↦ (root who true).toReal
  let others := coalition.erase player
  have hothersNonempty : others.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsubset : coalition ⊆ {player} := by
      intro who hwho
      by_contra hne
      have hnePlayer : who ≠ player := by
        simpa only [Finset.mem_singleton] using hne
      have hwhoOthers : who ∈ others :=
        Finset.mem_erase.mpr ⟨hnePlayer, hwho⟩
      rw [hempty] at hwhoOthers
      simp at hwhoOthers
    have hcardLe : coalition.card ≤ 1 := by
      exact (Finset.card_le_card hsubset).trans_eq
        (Finset.card_singleton player)
    omega
  obtain ⟨other, hother⟩ := hothersNonempty
  have hδltOne : δ < 1 := hδhalf.trans_lt (by norm_num)
  have hdenominatorPos : 0 < 1 - δ := sub_pos.mpr hδltOne
  have hxnonneg (who : ι) : 0 ≤ x who := ENNReal.toReal_nonneg
  have hxleδ (who : ι) : x who ≤ δ :=
    (quittingQuitProbability_le_absorptionMass root who).trans habsorption
  have hxleone (who : ι) : x who ≤ 1 :=
    (hxleδ who).trans (hδhalf.trans (by norm_num))
  have hxlecontinue (who : ι) : x who ≤ 1 - x who := by
    linarith [hxleδ who, hδhalf]
  have hotherOdds : x other ≤ (δ / (1 - δ)) * (1 - x other) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdenominatorPos).2
    have hxother := hxleδ other
    nlinarith [hxnonneg other]
  have hrestComparison :
      (∏ who ∈ others.erase other, x who) ≤
        ∏ who ∈ others.erase other, (1 - x who) :=
    Finset.prod_le_prod
      (fun who _ ↦ hxnonneg who)
      (fun who _ ↦ hxlecontinue who)
  have hcontinueRestNonneg :
      0 ≤ ∏ who ∈ others.erase other, (1 - x who) :=
    Finset.prod_nonneg fun who _ ↦ sub_nonneg.mpr (hxleone who)
  have hothersProduct :
      (∏ who ∈ others, x who) ≤
        (δ / (1 - δ)) * ∏ who ∈ others, (1 - x who) := by
    rw [show (∏ who ∈ others, x who) =
        x other * ∏ who ∈ others.erase other, x who by
      simpa [mul_comm] using (Finset.prod_erase_mul others x hother).symm]
    rw [show (∏ who ∈ others, (1 - x who)) =
        (1 - x other) * ∏ who ∈ others.erase other, (1 - x who) by
      simpa [mul_comm] using
        (Finset.prod_erase_mul others (fun who ↦ 1 - x who) hother).symm]
    calc
      x other * ∏ who ∈ others.erase other, x who ≤
          x other * ∏ who ∈ others.erase other, (1 - x who) :=
        mul_le_mul_of_nonneg_left hrestComparison (hxnonneg other)
      _ ≤ ((δ / (1 - δ)) * (1 - x other)) *
          ∏ who ∈ others.erase other, (1 - x who) :=
        mul_le_mul_of_nonneg_right hotherOdds hcontinueRestNonneg
      _ = (δ / (1 - δ)) *
          ((1 - x other) *
            ∏ who ∈ others.erase other, (1 - x who)) := by ring
  have hinside :
      (∏ who ∈ coalition, x who) =
        x player * ∏ who ∈ others, x who := by
    simpa [others, mul_comm] using
      (Finset.prod_erase_mul coalition x hplayer).symm
  have hsingletonComplement :
      ({player} : Finset ι)ᶜ = others ∪ coalitionᶜ := by
    ext who
    simp only [Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_union, Finset.mem_erase, others]
    constructor
    · intro hne
      by_cases hwho : who ∈ coalition
      · exact Or.inl ⟨hne, hwho⟩
      · exact Or.inr hwho
    · rintro (⟨hne, _⟩ | hnot)
      · exact hne
      · exact fun heq ↦ hnot (heq ▸ hplayer)
  have hdisjoint : Disjoint others coalitionᶜ := by
    refine Finset.disjoint_left.mpr ?_
    intro who hwho hcomplement
    have hnotCoalition : who ∉ coalition := by
      simpa only [Finset.mem_compl] using hcomplement
    exact hnotCoalition (Finset.mem_erase.mp hwho).2
  have hsingletonOutside :
      (∏ who ∈ ({player} : Finset ι)ᶜ, (1 - x who)) =
        (∏ who ∈ others, (1 - x who)) *
          ∏ who ∈ coalitionᶜ, (1 - x who) := by
    rw [hsingletonComplement, Finset.prod_union hdisjoint]
  have hcommonNonneg :
      0 ≤ x player * ∏ who ∈ coalitionᶜ, (1 - x who) :=
    mul_nonneg (hxnonneg player) <|
      Finset.prod_nonneg fun who _ ↦ sub_nonneg.mpr (hxleone who)
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  change
    ((∏ who ∈ coalition, x who) *
      ∏ who ∈ coalitionᶜ, (1 - x who)) ≤
      (δ / (1 - δ)) *
        ((∏ who ∈ ({player} : Finset ι), x who) *
          ∏ who ∈ ({player} : Finset ι)ᶜ, (1 - x who))
  rw [hinside, hsingletonOutside]
  simp only [Finset.prod_singleton]
  calc
    (x player * ∏ who ∈ others, x who) *
          ∏ who ∈ coalitionᶜ, (1 - x who) =
        (x player * ∏ who ∈ coalitionᶜ, (1 - x who)) *
          ∏ who ∈ others, x who := by ring
    _ ≤ (x player * ∏ who ∈ coalitionᶜ, (1 - x who)) *
          ((δ / (1 - δ)) *
            ∏ who ∈ others, (1 - x who)) :=
      mul_le_mul_of_nonneg_left hothersProduct hcommonNonneg
    _ = (δ / (1 - δ)) *
        (x player * ((∏ who ∈ others, (1 - x who)) *
          ∏ who ∈ coalitionᶜ, (1 - x who))) := by ring

end GameTheory
