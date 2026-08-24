/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.TwoCycleLassoHardPairAlignment
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles

/-!
# Terminal-gap dispatch on an aligned two-cycle hard pair

The terminal exploitability witness acts on the literal pair decoded from a
marked two-cycle.  Thus the same pair is both a nonprojective card-two
crossing and the source of a gap-sized nonsingleton leave-or-join toggle.

For `rootedTwo_next`, the pair is the collision owner/collider pair.  The
collision certificate rules out the collider as the leaving member, while
the reverse preemption edge adds another full gap if the owner leaves.  The
result is an exact split between a double-gap owner deficit at the pair and a
gap-sized profitable join by an outside player.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open Math.FiniteSerialRelation
open QuittingSureSetOwnerRepair

/-- Same-label algebraic and terminal-semantic output on a marked two-cycle. -/
structure FinFourAlignedTwoCycleTerminalGapResidual
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap}
    (geometry : MarkedRootedLasso
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner certificate.collider) where
  players : Finset (Fin 4)
  decoded_pair : geometry.twoCyclePair? = some players
  not_projective : ¬IsProjectiveQMatrix
    (principalMatrix (normalizedSoloMatrix reward) players)
  crossing : Nonempty (FinFourHardCardTwoCrossing residual players)
  terminal_gap_toggle :
    (∃ member ∈ players,
      quittingSetReward reward players member +
          residual.witness.terminalGap ≤
        quittingSetReward reward (players.erase member) member) ∨
    ∃ outsider ∉ players,
      quittingSetReward reward players outsider +
          residual.witness.terminalGap ≤
        quittingSetReward reward (insert outsider players) outsider

namespace FinFourQuantitativeFullSupportHardResidual

/-- The eight aligned two-cycle constructors carry an actual gap-sized
terminal toggle on the same hard pair.  The complementary branch remains
exactly the nine long-cycle constructors. -/
theorem alignedTwoCycleTerminalGapResidual_or_hasLongCycle
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    {certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap}
    (geometry : MarkedRootedLasso
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner certificate.collider) :
    Nonempty (FinFourAlignedTwoCycleTerminalGapResidual residual geometry) ∨
      geometry.HasLongCycle := by
  rcases residual.alignedTwoCycleHardPair_or_hasLongCycle geometry with
    haligned | hlong
  · left
    obtain ⟨players, hdecoded, hnot, hcrossing⟩ := haligned
    exact ⟨{
      players := players
      decoded_pair := hdecoded
      not_projective := hnot
      crossing := hcrossing
      terminal_gap_toggle := residual.witness.exists_leave_or_join_gain players
    }⟩
  · exact Or.inr hlong

/-- The final hard residual produces either a same-pair algebraic/semantic
two-cycle output or an actual marked long-cycle geometry. -/
theorem exists_collisionGeometry_with_alignedTwoCycleTerminalGap_or_long
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ certificate : QuittingImmediateSingletonCollision reward
        residual.witness.terminalGap,
      ∃ geometry : MarkedRootedLasso
          (QuittingSoloPreempts reward residual.witness.terminalGap)
          certificate.owner certificate.collider,
        Nonempty
            (FinFourAlignedTwoCycleTerminalGapResidual residual geometry) ∨
          geometry.HasLongCycle := by
  obtain ⟨certificate, ⟨geometry⟩⟩ :=
    residual.witness.exists_collisionAnchoredPreemptionGeometry_of_card_eq_four
      (by norm_num)
  exact ⟨certificate, geometry,
    residual.alignedTwoCycleTerminalGapResidual_or_hasLongCycle geometry⟩

/-- **Sharp `rootedTwo_next` semantic dispatch.**  The literal hard pair is
the collision owner/collider pair.  Either the owner's pair payoff lies two
terminal gaps below its own solo payoff, or an outsider has a gap-sized gain
from joining the pair.  The collider cannot be the leaving member. -/
theorem rootedTwoNext_hardPair_doubleGap_or_outsiderJoin
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : RootedTwoCycle
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner)
    (marker_eq : certificate.collider = geometry.next) :
    ¬IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward)
          {certificate.owner, certificate.collider}) ∧
      Nonempty (FinFourHardCardTwoCrossing residual
        {certificate.owner, certificate.collider}) ∧
      (quittingSetReward reward
            ({certificate.owner, certificate.collider} : Finset (Fin 4))
            certificate.owner +
            2 * residual.witness.terminalGap ≤
          quittingSoloReward reward certificate.owner certificate.owner ∨
        ∃ outsider ∉
            ({certificate.owner, certificate.collider} : Finset (Fin 4)),
          quittingSetReward reward
                ({certificate.owner, certificate.collider} : Finset (Fin 4))
                outsider + residual.witness.terminalGap ≤
            quittingSetReward reward
              (insert outsider {certificate.owner, certificate.collider})
              outsider) := by
  have halignment := residual.rootedTwoNext_ownerCollider_alignment
    certificate geometry marker_eq
  dsimp only at halignment
  refine ⟨halignment.2.1, halignment.2.2, ?_⟩
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
      rw [herase, quittingSetReward_singleton_eq_soloReward] at hgain
      have hbackward := geometry.backward.2
      rw [← marker_eq] at hbackward
      linarith
    · subst member
      have herase :
          ({certificate.owner, certificate.collider} : Finset (Fin 4)).erase
              certificate.collider = {certificate.owner} := by
        ext who
        simp only [Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hnot, howner | hcollider⟩
          · exact howner
          · exact (hnot hcollider).elim
        · intro howner
          subst who
          exact ⟨Ne.symm certificate.collider_ne_owner, Or.inl rfl⟩
      rw [herase, quittingSetReward_singleton_eq_soloReward,
        quittingSetReward_pair_right] at hgain
      linarith [certificate.collider_gain_floor,
        residual.witness.terminalGap_pos]
  · exact Or.inr hjoin

/-- The hard crossing makes the outsider arm more precise.  Either its two
positive singleton helpers coincide, or the double-gap owner deficit holds,
or the profitable outsider is one of those two helpers.  When the helpers
are distinct they exhaust the complement of the aligned pair on `Fin 4`. -/
theorem rootedTwoNext_sharedHelper_or_doubleGap_or_hardHelperJoin
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
        quittingSetReward reward
              ({certificate.owner, certificate.collider} : Finset (Fin 4))
              certificate.owner +
              2 * residual.witness.terminalGap ≤
            quittingSoloReward reward certificate.owner certificate.owner ∨
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
  obtain ⟨_hnot, ⟨crossing⟩, hsemantic⟩ :=
    residual.rootedTwoNext_hardPair_doubleGap_or_outsiderJoin
      certificate geometry marker_eq
  refine ⟨crossing, ?_⟩
  by_cases hhelpers : crossing.firstHelper = crossing.secondHelper
  · exact Or.inl hhelpers
  · right
    rcases hsemantic with hdouble | hjoin
    · exact Or.inl hdouble
    · right
      obtain ⟨outsider, houtside, hgain⟩ := hjoin
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
      have houtsideMem : outsider ∈ playersᶜ := by
        simp only [Finset.mem_compl]
        exact houtside
      rw [← hhelpersEqComplement] at houtsideMem
      have hlabel : outsider = crossing.firstHelper ∨
          outsider = crossing.secondHelper := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using houtsideMem
      exact ⟨outsider, hlabel, houtside, hgain⟩

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
