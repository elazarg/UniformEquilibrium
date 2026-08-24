/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.TwoCycleLassoTerminalGapDispatch
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FiniteDispatch

/-!
# Semantic consumers for the rooted two-cycle arms

The owner-leave arm of the aligned `rootedTwo_next` pair enters the exact
collision-repair screen.  Full packet support supplies the required positive
blocker mass, so failed collision repair forces a distinct spectator to join
the collider singleton.  Applying terminal exploitability at that enlarged
pair produces a second gap-sized actual-table toggle.  The entering spectator
cannot be the leaving label.

This contracts one arm of the rooted two-cycle trichotomy.  The shared-helper
and hard-helper-join arms remain, and the second toggle is not by itself a
chronology or a uniform-equilibrium construction.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open Math.FiniteSerialRelation
open QuittingSureSetOwnerRepair

/-- Actual-table output forced when the collision owner is the leaving member
of the aligned `rootedTwo_next` pair.  Besides the two-gap owner deficit, a
distinct spectator joins the collider singleton.  The enlarged pair then has
either a collider leave or a further outsider join. -/
structure FinFourRootedTwoNextOwnerLeaveCollisionChain
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap) where
  owner_pair_to_colliderSolo :
    quittingSetReward reward {certificate.owner, certificate.collider}
          certificate.owner + residual.witness.terminalGap ≤
      quittingSetReward reward {certificate.collider} certificate.owner
  owner_double_gap :
    quittingSetReward reward {certificate.owner, certificate.collider}
          certificate.owner + 2 * residual.witness.terminalGap ≤
      quittingSoloReward reward certificate.owner certificate.owner
  spectator : Fin 4
  spectator_ne_owner : spectator ≠ certificate.owner
  spectator_ne_collider : spectator ≠ certificate.collider
  spectator_joins_collider :
    quittingSetReward reward {certificate.collider} spectator <
      quittingSetReward reward {spectator, certificate.collider} spectator
  second_gap_toggle :
    quittingSetReward reward {spectator, certificate.collider}
          certificate.collider + residual.witness.terminalGap ≤
        quittingSetReward reward {spectator} certificate.collider ∨
      ∃ outsider ∉ ({spectator, certificate.collider} : Finset (Fin 4)),
        quittingSetReward reward {spectator, certificate.collider} outsider +
            residual.witness.terminalGap ≤
          quittingSetReward reward
            (insert outsider {spectator, certificate.collider}) outsider

namespace FinFourQuantitativeFullSupportHardResidual

/-- The exact owner-leave inequality feeds the collision-repair screen and
then terminal exploitability at the enlarged pair.  This is the semantic
consumer omitted by the coarser double-gap dispatch. -/
theorem ownerLeaveCollisionChain_of_rootedTwoNext
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : RootedTwoCycle
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner)
    (marker_eq : certificate.collider = geometry.next)
    (hownerLeave :
      quittingSetReward reward {certificate.owner, certificate.collider}
            certificate.owner + residual.witness.terminalGap ≤
        quittingSetReward reward {certificate.collider} certificate.owner) :
    Nonempty
      (FinFourRootedTwoNextOwnerLeaveCollisionChain residual certificate) := by
  have hbackward := geometry.backward.2
  rw [← marker_eq] at hbackward
  have hownerLeaveSolo := hownerLeave
  rw [quittingSetReward_singleton_eq_soloReward] at hownerLeaveSolo
  have hdouble :
      quittingSetReward reward {certificate.owner, certificate.collider}
            certificate.owner + 2 * residual.witness.terminalGap ≤
        quittingSoloReward reward certificate.owner certificate.owner := by
    linarith
  have hmass : 0 < residual.packet.mass certificate.collider := by
    rw [← residual.packet.mem_support_iff,
      residual.packet_support_eq_univ]
    exact Finset.mem_univ certificate.collider
  have hstrict :
      quittingSetReward reward {certificate.owner, certificate.collider}
          certificate.owner <
        quittingSetReward reward {certificate.collider} certificate.owner := by
    linarith [residual.witness.terminalGap_pos]
  obtain ⟨spectator, hspectatorOwner, hspectatorCollider, hjoin⟩ :=
    residual.witness.exists_spectator_lowerCollisionDefect_pos_of_ownerPair_lt
      residual.packet (Ne.symm certificate.collider_ne_owner) hmass hstrict
  have hnotMem : spectator ∉ ({certificate.collider} : Finset (Fin 4)) := by
    simpa only [Finset.mem_singleton] using hspectatorCollider
  refine ⟨{
    owner_pair_to_colliderSolo := hownerLeave
    owner_double_gap := hdouble
    spectator := spectator
    spectator_ne_owner := hspectatorOwner
    spectator_ne_collider := hspectatorCollider
    spectator_joins_collider := hjoin
    second_gap_toggle := ?_ }⟩
  rcases residual.witness.exists_leave_or_join_gain
      ({spectator, certificate.collider} : Finset (Fin 4)) with
    hleave | hotherJoin
  · obtain ⟨member, hmember, hleave⟩ := hleave
    have hlabels : member = spectator ∨ member = certificate.collider := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmember
    rcases hlabels with hspectator | hcollider
    · subst member
      have herase :
          ({spectator, certificate.collider} : Finset (Fin 4)).erase spectator =
            {certificate.collider} := by
        rw [Finset.erase_insert hnotMem]
      rw [herase] at hleave
      linarith [residual.witness.terminalGap_pos]
    · subst member
      have herase :
          ({spectator, certificate.collider} : Finset (Fin 4)).erase
              certificate.collider = {spectator} := by
        rw [Finset.pair_comm, Finset.erase_insert]
        simpa only [Finset.mem_singleton] using Ne.symm hspectatorCollider
      exact Or.inl (by simpa only [herase] using hleave)
  · exact Or.inr hotherJoin

/-- **Refined rooted-two-next dispatch.**  The shared-helper arm remains.  In
the owner-leave arm the terminal-gap deficit now forces an actual spectator
collision join and a second toggle.  If neither occurs, the original
gap-sized outsider join is carried by one of the two hard helpers. -/
theorem rootedTwoNext_sharedHelper_or_ownerLeaveCollisionChain_or_hardHelperJoin
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : RootedTwoCycle
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner)
    (marker_eq : certificate.collider = geometry.next) :
    ∃ crossing : FinFourHardCardTwoCrossing residual
        {certificate.owner, certificate.collider},
      crossing.firstHelper = crossing.secondHelper ∨
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
  obtain ⟨crossing⟩ := halignment.2.2
  refine ⟨crossing, ?_⟩
  by_cases hhelpers : crossing.firstHelper = crossing.secondHelper
  · exact Or.inl hhelpers
  · right
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
          simp only [players, Finset.mem_insert, Finset.mem_singleton,
            not_or]
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

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
