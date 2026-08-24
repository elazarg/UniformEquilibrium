/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.TwoCycleLassoArmConsumers

/-!
# Choice-invariant shared-helper contraction for a hard two-cycle

The helper labels in `FinFourHardCardTwoCrossing` are existential choices.
Equality of one selected pair of helpers is therefore not an invariant
chamber.  On `Fin 4`, either the two positive helpers can be reselected to be
distinct, or the complement of the hard pair has one common positive helper
and one label whose entries in both harmed rows are nonpositive.

The source-facing capstone reruns the terminal-gap dispatch with a reselected
distinct crossing.  Thus its shared-helper branch is the rigid, choice-free
relation rather than equality of arbitrary witnesses.  This remains a finite
same-table contraction, not an equilibrium compiler.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open Math.FiniteSerialRelation
open QuittingSureSetOwnerRepair

/-- The invariant residual behind failure to select two distinct positive
helpers for a hard pair.  The common helper is `crossing.firstHelper`; the
other outside label is nonpositive in both harmed rows. -/
structure FinFourHardCardTwoUniqueSharedHelper
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (players : Finset (Fin 4)) where
  crossing : FinFourHardCardTwoCrossing residual players
  helpers_eq : crossing.firstHelper = crossing.secondHelper
  other : Fin 4
  other_outside : other ∉ players
  other_ne_helper : other ≠ crossing.firstHelper
  complement_eq : playersᶜ = {crossing.firstHelper, other}
  first_other_nonpos :
    normalizedSoloMatrix reward crossing.first other ≤ 0
  second_other_nonpos :
    normalizedSoloMatrix reward crossing.second other ≤ 0

namespace FinFourHardCardTwoUniqueSharedHelper

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
variable {players : Finset (Fin 4)}

/-- Every outside label positive in the first harmed row is the common
helper. -/
theorem eq_helper_of_first_positive
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players)
    {helper : Fin 4} (houtside : helper ∉ players)
    (hpositive : 0 < normalizedSoloMatrix reward unique.crossing.first helper) :
    helper = unique.crossing.firstHelper := by
  have hmem : helper ∈ playersᶜ := by
    simpa only [Finset.mem_compl] using houtside
  rw [unique.complement_eq] at hmem
  have hcases : helper = unique.crossing.firstHelper ∨ helper = unique.other := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with hhelper | hother
  · exact hhelper
  · subst helper
    linarith [unique.first_other_nonpos]

/-- Every outside label positive in the second harmed row is the same common
helper. -/
theorem eq_helper_of_second_positive
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players)
    {helper : Fin 4} (houtside : helper ∉ players)
    (hpositive : 0 < normalizedSoloMatrix reward unique.crossing.second helper) :
    helper = unique.crossing.firstHelper := by
  have hmem : helper ∈ playersᶜ := by
    simpa only [Finset.mem_compl] using houtside
  rw [unique.complement_eq] at hmem
  have hcases : helper = unique.crossing.firstHelper ∨ helper = unique.other := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with hhelper | hother
  · exact hhelper
  · subst helper
    linarith [unique.second_other_nonpos]

end FinFourHardCardTwoUniqueSharedHelper

namespace FinFourQuantitativeFullSupportHardResidual

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}

/-- **Two-by-two Hall contraction.**  Positive helpers for the two harmed
rows either admit distinct representatives, or both rows have the same
unique positive outside label. -/
theorem cardTwoCrossing_distinctHelpers_or_uniqueSharedHelper
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {players : Finset (Fin 4)}
    (crossing : FinFourHardCardTwoCrossing residual players) :
    (∃ selected : FinFourHardCardTwoCrossing residual players,
      selected.firstHelper ≠ selected.secondHelper) ∨
      Nonempty (FinFourHardCardTwoUniqueSharedHelper residual players) := by
  by_cases hselected : crossing.firstHelper ≠ crossing.secondHelper
  · exact Or.inl ⟨crossing, hselected⟩
  · have hhelpers : crossing.firstHelper = crossing.secondHelper :=
      not_ne_iff.mp hselected
    have hplayersCard : players.card = 2 := by
      rw [crossing.players_eq]
      exact Finset.card_pair crossing.first_ne_second
    have hcomplementCard : playersᶜ.card = 2 := by
      rw [Finset.card_compl, hplayersCard]
      norm_num
    obtain ⟨other, hotherMem, hotherNe⟩ :=
      Finset.exists_mem_ne (by omega : 1 < playersᶜ.card)
        crossing.firstHelper
    have hotherOutside : other ∉ players := by
      simpa only [Finset.mem_compl] using hotherMem
    have hhelperMem : crossing.firstHelper ∈ playersᶜ := by
      simpa only [Finset.mem_compl] using crossing.firstHelper_outside
    have hpairSubset :
        ({crossing.firstHelper, other} : Finset (Fin 4)) ⊆ playersᶜ := by
      intro helper hhelper
      simp only [Finset.mem_insert, Finset.mem_singleton] at hhelper
      rcases hhelper with rfl | rfl
      · exact hhelperMem
      · exact hotherMem
    have hpairCard :
        ({crossing.firstHelper, other} : Finset (Fin 4)).card = 2 :=
      Finset.card_pair (Ne.symm hotherNe)
    have hcomplementEq :
        playersᶜ = {crossing.firstHelper, other} := by
      symm
      apply Finset.eq_of_subset_of_card_le hpairSubset
      rw [hpairCard, hcomplementCard]
    by_cases hfirstOther :
        0 < normalizedSoloMatrix reward crossing.first other
    · left
      let selected : FinFourHardCardTwoCrossing residual players := {
        first := crossing.first
        second := crossing.second
        firstHelper := other
        secondHelper := crossing.secondHelper
        first_ne_second := crossing.first_ne_second
        players_eq := crossing.players_eq
        firstHelper_outside := hotherOutside
        secondHelper_outside := crossing.secondHelper_outside
        first_harmed := crossing.first_harmed
        second_harmed := crossing.second_harmed
        first_helped := hfirstOther
        second_helped := crossing.second_helped }
      refine ⟨selected, ?_⟩
      dsimp [selected]
      rw [← hhelpers]
      exact hotherNe
    · by_cases hsecondOther :
          0 < normalizedSoloMatrix reward crossing.second other
      · left
        let selected : FinFourHardCardTwoCrossing residual players := {
          first := crossing.first
          second := crossing.second
          firstHelper := crossing.firstHelper
          secondHelper := other
          first_ne_second := crossing.first_ne_second
          players_eq := crossing.players_eq
          firstHelper_outside := crossing.firstHelper_outside
          secondHelper_outside := hotherOutside
          first_harmed := crossing.first_harmed
          second_harmed := crossing.second_harmed
          first_helped := crossing.first_helped
          second_helped := hsecondOther }
        exact ⟨selected, by
          dsimp [selected]
          exact Ne.symm hotherNe⟩
      · right
        exact ⟨{
          crossing := crossing
          helpers_eq := hhelpers
          other := other
          other_outside := hotherOutside
          other_ne_helper := hotherNe
          complement_eq := hcomplementEq
          first_other_nonpos := le_of_not_gt hfirstOther
          second_other_nonpos := le_of_not_gt hsecondOther }⟩

/-- With distinct selected helpers, the terminal toggle on the aligned pair
cannot disappear into a helper-equality branch.  It produces either the
owner-leave collision chain or a gap-sized join by one of those helpers. -/
theorem rootedTwoNext_ownerLeaveCollisionChain_or_hardHelperJoin_of_distinct
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : RootedTwoCycle
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner)
    (marker_eq : certificate.collider = geometry.next)
    (crossing : FinFourHardCardTwoCrossing residual
      {certificate.owner, certificate.collider})
    (hhelpers : crossing.firstHelper ≠ crossing.secondHelper) :
    (∃ chain :
        FinFourRootedTwoNextOwnerLeaveCollisionChain residual certificate,
      chain.spectator = crossing.firstHelper ∨
        chain.spectator = crossing.secondHelper) ∨
      ∃ helper,
        (helper = crossing.firstHelper ∨ helper = crossing.secondHelper) ∧
        helper ∉
          ({certificate.owner, certificate.collider} : Finset (Fin 4)) ∧
        quittingSetReward reward
              ({certificate.owner, certificate.collider} : Finset (Fin 4))
              helper + residual.witness.terminalGap ≤
          quittingSetReward reward
            (insert helper {certificate.owner, certificate.collider}) helper := by
  let players : Finset (Fin 4) :=
    {certificate.owner, certificate.collider}
  have hplayersCard : players.card = 2 := by
    exact Finset.card_pair (Ne.symm certificate.collider_ne_owner)
  have hcomplementCard : playersᶜ.card = 2 := by
    rw [Finset.card_compl, hplayersCard]
    norm_num
  have hhelpersSubset :
      ({crossing.firstHelper, crossing.secondHelper} : Finset (Fin 4)) ⊆
        playersᶜ := by
    intro helper hhelper
    simp only [Finset.mem_insert, Finset.mem_singleton] at hhelper
    simp only [Finset.mem_compl]
    rcases hhelper with hfirst | hsecond
    · subst helper
      exact crossing.firstHelper_outside
    · subst helper
      exact crossing.secondHelper_outside
  have hhelpersCard :
      ({crossing.firstHelper, crossing.secondHelper} :
        Finset (Fin 4)).card = 2 :=
    Finset.card_pair hhelpers
  have hhelpersEqComplement :
      ({crossing.firstHelper, crossing.secondHelper} : Finset (Fin 4)) =
        playersᶜ := by
    apply Finset.eq_of_subset_of_card_le hhelpersSubset
    rw [hcomplementCard, hhelpersCard]
  have outside_is_helper (outsider : Fin 4) (houtside : outsider ∉ players) :
      outsider = crossing.firstHelper ∨
        outsider = crossing.secondHelper := by
    have houtsideMem : outsider ∈ playersᶜ := by
      simpa only [Finset.mem_compl] using houtside
    rw [← hhelpersEqComplement] at houtsideMem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using houtsideMem
  rcases residual.witness.exists_leave_or_join_gain
      ({certificate.owner, certificate.collider} : Finset (Fin 4)) with
    hleave | hjoin
  · obtain ⟨member, hmember, hgain⟩ := hleave
    have hlabels : member = certificate.owner ∨
        member = certificate.collider := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmember
    rcases hlabels with howner | hcollider
    · left
      subst member
      have herase :
          ({certificate.owner, certificate.collider} : Finset (Fin 4)).erase
              certificate.owner = {certificate.collider} := by
        ext who
        simp [Ne.symm certificate.collider_ne_owner]
      rw [herase] at hgain
      obtain ⟨chain⟩ :=
        residual.ownerLeaveCollisionChain_of_rootedTwoNext
          certificate geometry marker_eq hgain
      exact ⟨chain, outside_is_helper chain.spectator (by
        simp only [players, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨chain.spectator_ne_owner, chain.spectator_ne_collider⟩)⟩
    · subst member
      have herase :
          ({certificate.owner, certificate.collider} : Finset (Fin 4)).erase
              certificate.collider = {certificate.owner} := by
        rw [Finset.pair_comm, Finset.erase_insert]
        simpa only [Finset.mem_singleton] using
          certificate.collider_ne_owner
      rw [herase, quittingSetReward_singleton_eq_soloReward,
        quittingSetReward_pair_right] at hgain
      linarith [certificate.collider_gain_floor,
        residual.witness.terminalGap_pos]
  · right
    obtain ⟨outsider, houtside, hgain⟩ := hjoin
    exact ⟨outsider, outside_is_helper outsider houtside, houtside, hgain⟩

/-- **Choice-invariant rooted-two-next dispatch.**  The former arbitrary
shared-helper arm is replaced by the exact unique-common-helper relation.
Otherwise the actual terminal toggle enters the collision chain or is paid
to one of two distinct selected helpers. -/
theorem rootedTwoNext_uniqueSharedHelper_or_ownerLeaveCollisionChain_or_hardHelperJoin
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : RootedTwoCycle
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner)
    (marker_eq : certificate.collider = geometry.next) :
    ∃ crossing : FinFourHardCardTwoCrossing residual
        {certificate.owner, certificate.collider},
      Nonempty (FinFourHardCardTwoUniqueSharedHelper residual
        {certificate.owner, certificate.collider}) ∨
        (∃ chain :
            FinFourRootedTwoNextOwnerLeaveCollisionChain residual certificate,
          chain.spectator = crossing.firstHelper ∨
            chain.spectator = crossing.secondHelper) ∨
        ∃ helper,
          (helper = crossing.firstHelper ∨
            helper = crossing.secondHelper) ∧
          helper ∉
            ({certificate.owner, certificate.collider} : Finset (Fin 4)) ∧
          quittingSetReward reward
                ({certificate.owner, certificate.collider} : Finset (Fin 4))
                helper + residual.witness.terminalGap ≤
            quittingSetReward reward
              (insert helper {certificate.owner, certificate.collider})
              helper := by
  have halignment := residual.rootedTwoNext_ownerCollider_alignment
    certificate geometry marker_eq
  dsimp only at halignment
  obtain ⟨initial⟩ := halignment.2.2
  rcases residual.cardTwoCrossing_distinctHelpers_or_uniqueSharedHelper
      initial with hdistinct | hunique
  · obtain ⟨crossing, hhelpers⟩ := hdistinct
    refine ⟨crossing, Or.inr ?_⟩
    exact residual.rootedTwoNext_ownerLeaveCollisionChain_or_hardHelperJoin_of_distinct
      certificate geometry marker_eq crossing hhelpers
  · exact ⟨initial, Or.inl hunique⟩

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
