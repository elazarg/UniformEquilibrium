/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.KActiveCompactPath
import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Coalition mass in the one-active quitting stratum

A positive opponent-coalition atom can use only active quitting coordinates. When at
most one player is active, every positive atom is empty or a singleton, and a positive
singleton identifies the entire root. Its mass equals the unique hazard, the total
one-stage absorption mass, and the corresponding literal terminal-coalition mass.
-/

noncomputable section

namespace GameTheory

open Finset Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
/-- A positive exact opponent-coalition atom can only use active Quit
coordinates. -/
theorem quittingOpponentCoalition_subset_positiveHazardSupport_of_mass_pos
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι)
    (hmass : 0 < quittingOpponentCoalitionMass root who coalition) :
    coalition ⊆ quittingPositiveHazardSupport root := by
  intro player hplayer
  simp only [quittingPositiveHazardSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_contra hnonpos
  have hzero : hazardOfRoot root player = 0 :=
    le_antisymm (le_of_not_gt hnonpos) (hazardOfRoot_nonneg root player)
  have hquit : (root player true).toReal = 0 := by
    simpa [hazardOfRoot] using hzero
  have hproduct :
      (∏ member ∈ coalition, (root member true).toReal) = 0 := by
    exact Finset.prod_eq_zero hplayer hquit
  rw [quittingOpponentCoalitionMass, hproduct, zero_mul] at hmass
  exact (lt_irrefl 0) hmass

/-- In the one-active stratum, every positive opponent-coalition atom has
rank at most one. -/
theorem quittingOpponentCoalition_card_le_one_of_oneActive_of_mass_pos
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass root who coalition) :
    coalition.card ≤ 1 := by
  exact (Finset.card_le_card
    (quittingOpponentCoalition_subset_positiveHazardSupport_of_mass_pos
      root who coalition hmass)).trans hactive

/-- Hence a positive one-active polarity atom is either the solo-versus-tail
atom or one literal player-pair insertion toggle. -/
theorem quittingOpponentCoalition_eq_empty_or_singleton_of_oneActive_of_mass_pos
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass root who coalition) :
    coalition = ∅ ∨ ∃ partner, coalition = {partner} := by
  by_cases hempty : coalition = ∅
  · exact Or.inl hempty
  · right
    have hnonempty : coalition.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨partner, hpartner⟩ := hnonempty
    refine ⟨partner, Finset.Subset.antisymm ?_ ?_⟩
    · intro player hplayer
      have hcard :=
        quittingOpponentCoalition_card_le_one_of_oneActive_of_mass_pos
          root who coalition hactive hmass
      by_contra hne
      have hpair : ({partner, player} : Finset ι) ⊆ coalition := by
        intro member hmember
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmember
        rcases hmember with rfl | rfl
        · exact hpartner
        · exact hplayer
      have htwo : ({partner, player} : Finset ι).card = 2 := by
        apply Finset.card_pair
        intro heq
        apply hne
        simp [heq]
      have := Finset.card_le_card hpair
      omega
    · intro player hplayer
      simp only [Finset.mem_singleton] at hplayer
      subst player
      exact hpartner

/-- A positive singleton atom in the one-active stratum identifies the whole
root: its partner is the unique possible quitter. -/
theorem quittingRoot_eq_soloStationaryRoot_of_oneActive_singletonMass_pos
    (root : ι → PMF Bool) (who partner : ι)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass root who {partner}) :
    root = quittingSoloStationaryRoot partner (root partner) := by
  apply eq_quittingSoloStationaryRoot_of_others_continue
  intro other hother
  apply quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport
  intro hotherSupport
  have hpartnerSupport : partner ∈ quittingPositiveHazardSupport root :=
    quittingOpponentCoalition_subset_positiveHazardSupport_of_mass_pos
      root who {partner} hmass (by simp)
  have hpair : ({partner, other} : Finset ι) ⊆
      quittingPositiveHazardSupport root := by
    intro player hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
    rcases hplayer with rfl | rfl
    · exact hpartnerSupport
    · exact hotherSupport
  have htwo : ({partner, other} : Finset ι).card = 2 :=
    Finset.card_pair hother.symm
  have hcard := Finset.card_le_card hpair
  have hactiveCard := hactive
  unfold HasQuittingSupportCardAtMost at hactiveCard
  omega

/-- More sharply, the marked singleton mass is exactly the unique active
hazard; no hidden product of passive Continue coordinates remains. -/
theorem quittingOpponentCoalitionMass_singleton_eq_hazard_of_oneActive
    (root : ι → PMF Bool) (who partner : ι)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass root who {partner}) :
    quittingOpponentCoalitionMass root who {partner} =
      hazardOfRoot root partner := by
  have hroot :=
    quittingRoot_eq_soloStationaryRoot_of_oneActive_singletonMass_pos
      root who partner hactive hmass
  rw [hroot]
  unfold quittingOpponentCoalitionMass
  simp only [Finset.prod_singleton]
  have hcontinue : ∀ player ∈ Finset.univ.erase who \ {partner},
      ((quittingSoloStationaryRoot partner (root partner) player) false).toReal =
        1 := by
    intro player hplayer
    have hne : player ≠ partner := by
      have hnot := (Finset.mem_sdiff.mp hplayer).2
      simpa only [Finset.mem_singleton] using hnot
    rw [quittingSoloStationaryRoot_apply_other hne]
    simp
  rw [Finset.prod_eq_one hcontinue, mul_one]
  rfl

/-- Consequently the singleton atom also equals the whole one-stage
absorption probability.  Persistence of the edge is persistence of a literal
clock, not merely persistence of a conditional label. -/
theorem quittingOpponentCoalitionMass_singleton_eq_absorption_of_oneActive
    (root : ι → PMF Bool) (who partner : ι)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass root who {partner}) :
    quittingOpponentCoalitionMass root who {partner} =
      quittingRootAbsorptionMass root := by
  have hmassHazard :=
    quittingOpponentCoalitionMass_singleton_eq_hazard_of_oneActive
      root who partner hactive hmass
  have hroot :=
    quittingRoot_eq_soloStationaryRoot_of_oneActive_singletonMass_pos
      root who partner hactive hmass
  calc
    quittingOpponentCoalitionMass root who {partner} =
        hazardOfRoot root partner := hmassHazard
    _ = (root partner true).toReal := rfl
    _ = quittingRootAbsorptionMass root := by
      rw [hroot, quittingRootAbsorptionMass_soloStationaryRoot]
      simp

/-- The opponent-coalition notation and the literal terminal-coalition
notation coincide on a positive singleton atom in the one-active stratum. -/
theorem quittingOpponentCoalitionMass_singleton_eq_rootCoalitionMass_of_oneActive
    (root : ι → PMF Bool) (who partner : ι)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass root who {partner}) :
    quittingOpponentCoalitionMass root who {partner} =
      quittingRootCoalitionMass root {partner} := by
  have hroot :=
    quittingRoot_eq_soloStationaryRoot_of_oneActive_singletonMass_pos
      root who partner hactive hmass
  rw [quittingOpponentCoalitionMass_singleton_eq_hazard_of_oneActive
      root who partner hactive hmass,
    hroot,
    quittingRootCoalitionMass_solo_of_nonempty partner (root partner)
      {partner} (by simp)]
  simp [hazardOfRoot, quittingSoloStationaryRoot_apply_owner]


end GameTheory
